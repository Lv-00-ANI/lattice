"""gov/check_coverage_claim.py -- the coverage table in PROOF-DEBT.md must equal the measurement.

## Why this file exists

Round 27 found `PROOF-DEBT.md` stating the coverage of the load-bearing set **three different ways in one
page**: the table said 682/872 = **78.2%**, the paragraph below it said **100%**, and the caveat at line 83
said the set itself was computed with a **defective** in-degree (docstring mentions and same-named
declarations counted as references) and that the corrected size is 839.

Three numbers for one quantity, and no instrument anywhere that computed the corrected one. That is the same
defect class as the debt counter (round 5), `audit_duplicates` (round 11) and the census (round 26): **a number
in a document that nothing checks**.

## The definition, stated so it can be argued with

  1. **theorem+lemma only** -- `def`/`structure` have no proof to audit;
  2. **code only** -- comments and docstrings stripped, so a name mentioned in prose is not a reference;
  3. **the citing file must `import` the defining module** -- so a same-short-name declaration in another
     namespace is not a reference.

Rule 3 is what the caveat at line 83 asks for. Together they give a **corrected** in-degree.

## What it gates

  - the four numbers in `PROOF-DEBT.md`'s coverage table must equal the computed ones;
  - the zero-in-degree sampling **ratio must be recorded** (the doc must state it), so "we sampled" cannot
    silently become "we covered".

`--self-test` exercises the comparison with synthetic tables, so the gate can demonstrate its own failure.
"""

import io
import json
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ROOT, "Lattice")
REV = os.path.join(ROOT, "agent-tmp", "review")
DOC = os.path.join(ROOT, "PROOF-DEBT.md")

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([A-Za-z0-9_'.]+)")
IMPORT = re.compile(r"(?m)^import\s+(Lattice\.[A-Za-z0-9_.]+)")
TOKEN = re.compile(r"[A-Za-z0-9_']+")


def strip_comments(src):
    """Remove `--` line comments and nested `/- ... -/` blocks. Docstrings are block comments."""
    out = []
    i, n = 0, len(src)
    depth = 0
    while i < n:
        two = src[i:i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if two == "/-":
            depth = 1
            i += 2
            continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def measure():
    """Return a dict of the four numbers plus the audited-but-stale count."""
    files = []
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            mod = "Lattice." + rel[:-5].replace("/", ".")
            raw = io.open(p, encoding="utf-8").read()
            code = strip_comments(raw)
            files.append((mod, rel, code, set(TOKEN.findall(code)),
                          set(IMPORT.findall(code))))

    owner = {}
    for mod, rel, code, _tok, _imp in files:
        for m in DECL.finditer(code):
            owner.setdefault(m.group(2).split(".")[-1], (mod, rel))

    # in-degree: a file counts as citing iff it imports the defining module AND its CODE mentions the name
    indeg = {}
    for name, (mod, _rel) in owner.items():
        k = 0
        for other, _orel, _ocode, tok, imp in files:
            if other == mod or mod not in imp:
                continue
            if name in tok:
                k += 1
        indeg[name] = k

    audited = set()
    for fn in sorted(os.listdir(REV)):
        if not (fn.startswith("verdicts_") and fn.endswith(".jsonl")):
            continue
        for ln in io.open(os.path.join(REV, fn), encoding="utf-8"):
            ln = ln.strip()
            if ln:
                audited.add(json.loads(ln).get("name"))

    total = len(owner)
    load = {n for n, k in indeg.items() if k >= 1}
    zero = set(owner) - load
    return {
        "total": total,
        "load": len(load),
        "load_audited": len(load & audited),
        "zero": len(zero),
        "zero_audited": len(zero & audited),
        "unaudited_load_bearing": sorted(load - audited),
    }


def pct(a, b):
    return 100.0 * a / b if b else 0.0


def compare(doc_nums, measured):
    """`(ok, messages)`. Factored out so `--self-test` can exercise it."""
    msgs = []
    ok = True
    for key, label in (("total", "theorem+lemma"),
                       ("load", "load-bearing"),
                       ("load_audited", "load-bearing audited"),
                       ("zero", "zero-in-degree"),
                       ("zero_audited", "zero-in-degree audited")):
        want = measured[key]
        got = doc_nums.get(key)
        if got is None:
            msgs.append("  the doc does not state %s" % label)
            ok = False
        elif got != want:
            msgs.append("  %-24s doc %s, measured %s" % (label, got, want))
            ok = False
    return ok, msgs


TABLE = re.compile(r"\|\s*(?:\*\*)?([^|*]+?)(?:\*\*)?\s*\|\s*(?:\*\*)?([\d,]+)(?:\*\*)?\s*\|")


def parse_doc(text):
    """Pull the four numbers out of the coverage table.

    Anchored on the row labels, which are stable, rather than on positions or line numbers.
    """
    out = {}
    for ln in text.split("\n"):
        cells = [c.strip().strip("*") for c in ln.strip().strip("|").split("|")]
        if len(cells) < 4:
            continue
        label = cells[0]
        # the last column is a percentage ("45.9%"); keep only cells that are pure integers, so the parser
        # cannot be derailed by it.  The self-test found exactly this bug: `int("45.9%")` raised and the
        # whole row was dropped, so the gate would have reported "the doc does not state X" for every row.
        ints = []
        for c in cells[1:]:
            c2 = c.replace(",", "").strip()
            if c2.isdigit():
                ints.append(int(c2))
        if len(ints) < 2:
            continue
        if "定理 + 引理" in label or "theorem+lemma" in label:
            out["total"] = ints[0]
        elif "入度 ≥ 1" in label:
            out["load"], out["load_audited"] = ints[0], ints[1]
        elif "入度 = 0" in label:
            out["zero"], out["zero_audited"] = ints[0], ints[1]
    return out


def self_test():
    ok = True
    m = {"total": 10, "load": 5, "load_audited": 4, "zero": 5, "zero_audited": 1}
    good = {"total": 10, "load": 5, "load_audited": 4, "zero": 5, "zero_audited": 1}
    bad = dict(good, load_audited=3)
    missing = {k: v for k, v in good.items() if k != "zero"}

    okk, _ = compare(good, m)
    if not okk:
        print("  agreeing table FAILED to pass")
        ok = False
    okk, msgs = compare(bad, m)
    if okk or not msgs:
        print("  disagreeing table FAILED to be caught")
        ok = False
    okk, msgs = compare(missing, m)
    if okk:
        print("  a table that omits a row FAILED to be caught")
        ok = False

    # the parser must read a table it was shown, and must not invent one
    parsed = parse_doc("| 定理 + 引理 | 1,234 | 567 | 45.9% |\n"
                       "| **入度 ≥ 1（承重集）** | **89** | **45** | **50.6%** |\n"
                       "| **入度 = 0** | **1,145** | **522** | **45.6%** |\n")
    if parsed.get("total") != 1234 or parsed.get("load") != 89 or parsed.get("zero") != 1145:
        print("  table parser FAILED: %r" % parsed)
        ok = False
    if parse_doc("no table here") != {}:
        print("  table parser invented numbers in a table-free document")
        ok = False

    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    m = measure()
    if not os.path.exists(DOC):
        print("COVERAGE CLAIM: PROOF-DEBT.md is absent")
        return 1
    doc = parse_doc(io.open(DOC, encoding="utf-8").read())
    ok, msgs = compare(doc, m)
    print("COVERAGE TRUTH (corrected in-degree: theorem+lemma, code only, citing file must import)")
    print("  theorem+lemma            : %d" % m["total"])
    print("  load-bearing (>=1)       : %d, audited %d (%.1f%%)"
          % (m["load"], m["load_audited"], pct(m["load_audited"], m["load"])))
    print("  zero-in-degree           : %d, audited %d (%.1f%%)"
          % (m["zero"], m["zero_audited"], pct(m["zero_audited"], m["zero"])))
    print("  load-bearing UNAUDITED   : %d" % len(m["unaudited_load_bearing"]))
    for n in m["unaudited_load_bearing"]:
        print("     %s" % n)
    if not ok:
        print()
        print("COVERAGE CLAIM: the document disagrees with the measurement")
        for s in msgs:
            print(s)
        return 1
    print("COVERAGE CLAIM: the document's table equals the measurement")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
