"""gov/check_verdict_freshness.py -- a verdict must point at a declaration that still exists.

## Why this file exists

`check_proof_debt_orphans.py` verifies that each verdict's **file** still resolves through `PATH_MAP`
(394/394 at round 28). It never looks at the **name**, so a verdict can claim a judgement about a theorem that
was renamed or deleted, and `PROOF-DEBT.md` will print it as if it were live.

Round 29 measured it: of **1,409** verdict records,

    exact          1,284  (91.1%)   line matches the declaration's line
    drift            113  ( 8.0%)   name resolves, line has moved (median 10, max 122)
    name_missing      12  ( 0.9%)   **the declaration is gone**
    file_missing       0  ( 0.0%)

The 12 are real: `Evidence/CompositionClass.evidence_kinds_differ` no longer exists (the file now declares
`compose_sequential` / `compose_bridged` / `signature_*`), `Evidence/ChainTransitivity.preserves_one` is gone
(now `preserves_foldl` / `preserves_two` / `preserves_three`), and so on. **Superseded declarations, verdicts
still citing them.**

## What this gate does, and what it deliberately does not

- **name_missing is a failure** unless baselined. A verdict about nothing is exactly the drift a prose ledger
  cannot see.
- **drift is NOT a failure.** A line moving is normal in a live tree; failing on it would mean editing a
  baseline after every edit. Instead the **line is resolved from the source** (`resolve_line`) and the ledger
  prints the true one, so drift cannot mislead a reader even though it is not an error.
- two-way: a **baselined entry that resolves again** also fails, so the baseline cannot rot.

## The lesson from the first measurement, recorded

The first version of the measurement reported **29** name-missing records. Twelve of those were the
checker's own fault: a qualified declaration reads `theorem Gated.comp`, and the search pattern did not allow a
namespace prefix. **A checker must not blame the data for its own limitation** -- the same defect as
`check_slots.py`'s `ch[:2000]` window (round 12). The pattern now allows a prefix.
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
BASE = os.path.join(HERE, "verdict-stale-baseline.txt")

sys.path.insert(0, HERE)
from _debt_path_map import PATH_MAP  # noqa: E402

#: a qualified declaration reads `theorem Gated.comp`; the prefix is optional and repeated
DECL_PAT = ("^\\s*(?:@\\[[^\\]]*\\]\\s*)?(?:private\\s+|protected\\s+|noncomputable\\s+)*"
            "(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\\s+"
            "(?:[A-Za-z0-9_']+\\.)*")


def resolve_line(rel, name):
    """The 1-based line where `name` is declared in `rel`, or None if it is not there.

    Exported so `gen_proof_debt.py` prints the TRUE line instead of the recorded one.
    """
    if not rel or not name:
        return None
    path = os.path.join(LAT, rel.replace("/", os.sep))
    if not os.path.exists(path):
        return None
    pat = re.compile(DECL_PAT + re.escape(name.split(".")[-1]) + r"\b")
    for i, ln in enumerate(io.open(path, encoding="utf-8", errors="replace"), 1):
        if pat.match(ln):
            return i
    return None


def records():
    """Yield `(source_file, file, name, recorded_line)` for every verdict."""
    for fn in sorted(os.listdir(REV)):
        if not (fn.startswith("verdicts_") and fn.endswith(".jsonl")):
            continue
        for raw in io.open(os.path.join(REV, fn), encoding="utf-8", errors="replace"):
            raw = raw.strip()
            if not raw:
                continue
            v = json.loads(raw)
            rel = PATH_MAP.get(v.get("file"), v.get("file"))
            yield fn, rel, (v.get("name") or "").split(".")[-1], v.get("line")


def classify():
    """`(stale, drifted, exact, file_missing)` -- lists of `(rel, name, recorded, actual)`."""
    stale, drifted, exact, file_missing = [], [], [], []
    for _fn, rel, name, rec in records():
        path = os.path.join(LAT, rel.replace("/", os.sep)) if rel else ""
        if not rel or not os.path.exists(path):
            file_missing.append((rel, name, rec, None))
            continue
        actual = resolve_line(rel, name)
        if actual is None:
            stale.append((rel, name, rec, None))
        elif actual == rec:
            exact.append((rel, name, rec, actual))
        else:
            drifted.append((rel, name, rec, actual))
    return stale, drifted, exact, file_missing


def compare(base, cur):
    """`(new, recovered)`. Factored out so `--self-test` can exercise both directions."""
    return sorted(cur - base), sorted(base - cur)


def read_baseline():
    if not os.path.exists(BASE):
        return set()
    out = set()
    for ln in io.open(BASE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            out.add((p[0], p[1]))
    return out


def self_test():
    ok = True
    b = {("A.lean", "gone"), ("B.lean", "kept")}
    new, rec = compare(b, {("B.lean", "kept"), ("C.lean", "fresh")})
    if new != [("C.lean", "fresh")]:
        print("  NEW direction FAILED: %r" % (new,))
        ok = False
    if rec != [("A.lean", "gone")]:
        print("  RECOVERED direction FAILED: %r" % (rec,))
        ok = False
    new, rec = compare(b, b)
    if new or rec:
        print("  identity comparison FAILED")
        ok = False
    # the resolver must find a qualified declaration and must not invent one
    if resolve_line("Evidence/CompositionClass.lean", "compose_sequential") is None:
        print("  resolver FAILED on a qualified-free declaration it should find")
        ok = False
    if resolve_line("Evidence/CompositionClass.lean", "evidence_kinds_differ") is not None:
        print("  resolver FOUND a declaration that does not exist")
        ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    stale, drifted, exact, file_missing = classify()
    total = len(stale) + len(drifted) + len(exact) + len(file_missing)
    print("VERDICT FRESHNESS (a verdict must point at a declaration that still exists)")
    print("  records        : %d" % total)
    print("  exact line     : %d  (%.1f%%)" % (len(exact), 100.0 * len(exact) / max(1, total)))
    print("  drifted line   : %d  (%.1f%%)  -- resolved from source, NOT a failure"
          % (len(drifted), 100.0 * len(drifted) / max(1, total)))
    print("  STALE (no decl): %d  (%.1f%%)" % (len(stale), 100.0 * len(stale) / max(1, total)))
    print("  file missing   : %d" % len(file_missing))

    cur = {(r, n) for r, n, _rec, _a in stale}

    if "--write-baseline" in argv:
        # keep the reason column from the existing file if present
        old = {}
        if os.path.exists(BASE):
            for ln in io.open(BASE, encoding="utf-8"):
                ln = ln.rstrip("\n")
                if ln and not ln.startswith("#"):
                    p = ln.split("\t")
                    if len(p) >= 3:
                        old[(p[0], p[1])] = p[2]
        io.open(BASE, "w", encoding="utf-8", newline="\n").write(
            "# verdicts whose declaration no longer exists.  Each line: file<TAB>name<TAB>reason.\n"
            "# A NEW stale verdict fails; a baselined one that RESOLVES AGAIN also fails.\n"
            + "".join("%s\t%s\t%s\n" % (r, n, old.get((r, n), "superseded or deleted; reason not yet recorded"))
                      for r, n in sorted(cur)))
        print("  baseline written: %d" % len(cur))
        return 0

    base = read_baseline()
    new, recovered = compare(base, cur)
    for r, n in new:
        print("   NEW STALE  %s :: %s" % (r, n))
    for r, n in recovered:
        print("   RECOVERED  %s :: %s  (delete it from the baseline)" % (r, n))

    if file_missing:
        print("VERDICT FRESHNESS: %d verdict(s) point at a file that does not exist" % len(file_missing))
        return 1
    if new:
        print("VERDICT FRESHNESS: %d verdict(s) now point at a declaration that is gone" % len(new))
        return 1
    if recovered:
        print("VERDICT FRESHNESS: %d baselined verdict(s) resolve again -- the baseline has rotted" % len(recovered))
        return 1
    print("VERDICT FRESHNESS: %d stale, all baselined; %d drifted lines resolved from source"
          % (len(stale), len(drifted)))
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
