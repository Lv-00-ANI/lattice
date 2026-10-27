"""gov/check_refutation_census.py -- keep REFUTATION-CENSUS's numbers honest.

The census was produced by a script run once (round 35). Nothing re-measured it since, which is
exactly the drift pattern that REPAIR-CENSUS suffered. This makes it a gate.

It re-implements the SAME rule the census documents: a declaration whose CONCLUSION TYPE
(the part after the last top-level `:`) starts with `¬`, `not `, or ends in `False`; or is
`¬ ∃ …`.

`--self-test` plants a wrong number in the document and asserts the checker reports it.

The numbers come from `REFUTATION-CENSUS.md` via `census_docs`, not from a constant here. The
constant said 285 / Geo 6 while the document said 284 / Geo 5, and the guard exited 0 -- so the
document could say anything.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

import census_docs

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

# the census document this guard keeps honest
CENSUS_MD = os.path.join(LAKE, "REFUTATION-CENSUS.md")

PAT = re.compile(r"^(?:theorem|lemma)\s+(\w+)(.*?):=", re.S | re.M)


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if not depth:
            out.append(src[i])
        i += 1
    return "".join(out)


def concl_of(stmt):
    s = stmt.lstrip(": ").strip()
    depth = 0
    last = -1
    for i, ch in enumerate(s):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            last = i
    return s[last + 1:].strip() if last >= 0 else s


def is_negative(stmt):
    """A conclusion counts as a refutation iff it DENIES something.

    Was: `re.match(r"^[¬\s]*\s*(∃|exists)", c)` -- the `*` allowed zero negations, so every
    positive existence theorem (`∃ c, forall i, a i = c * b i`, which is a characterisation, not a
    refutation) was counted. 110 theorems were miscounted. The `¬` is not optional.
    """
    c = concl_of(stmt)
    if c.startswith("¬") or c.startswith("not ") or c.endswith("False"):
        return True
    # `¬ ∃ ...` -- require the negation explicitly
    if re.match(r"^\s*¬\s*(∃|exists)", c):
        return True
    return False


def measure():
    from collections import Counter
    lay = Counter()
    total = 0
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            layer = rel.split("/")[0] if "/" in rel else "(root)"
            t = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
            for m in PAT.finditer(t):
                sig = " ".join(m.group(2).split())
                if is_negative(sig):
                    total += 1
                    lay[layer] += 1
    return total, lay


def main(argv):
    total, lay = measure()

    try:
        want_total, want_layers = census_docs.refutation_expected(CENSUS_MD)
    except census_docs.CensusDocError as e:
        # unreadable document => FAIL. Having nothing to compare is how the drift survived.
        print("refutation census check\n")
        print("REFUTATION CENSUS: cannot read %s -- %s"
              % (os.path.basename(CENSUS_MD), e))
        return 1

    planted = False
    if "--self-test" in argv:
        want_total = total + 1
        planted = True

    problems = 0
    print("refutation census check\n")
    ok = total == want_total
    print("%-8s %-10s %-10s %s" % ("metric", "in the doc", "actual", "verdict"))
    print("%-8s %-10d %-10d %s" % ("total", want_total, total, "ok" if ok else "DRIFT"))
    if not ok:
        problems += 1
    for layer in ("Lib", "Lift", "Audit", "Core", "Geo"):
        want = want_layers.get(layer, 0)
        got = lay.get(layer, 0)
        ok = want == got
        print("%-8s %-10d %-10d %s" % (layer, want, got, "ok" if ok else "DRIFT"))
        if not ok:
            problems += 1

    print("\n" + "=" * 56)
    if planted:
        if problems > 0:
            print("SELF-TEST PASS: a wrong number in the document is reported")
            return 1
        print("SELF-TEST FAIL: a wrong number was NOT reported")
        return 0
    print("REFUTATION CENSUS: %s" % ("consistent with REFUTATION-CENSUS.md" if problems == 0
                                     else "%d drift(s) -- update REFUTATION-CENSUS.md" % problems))
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
