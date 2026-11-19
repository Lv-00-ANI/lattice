#!/usr/bin/env python
"""gov/audit_type_duplication.py -- how many real definitions does a configured type have, and are they the same?

WHY THIS EXISTS

    The external audit claimed "`ConstraintSet` has 4 definitions and `IRWeights` has 3". Round 994 measured it
    and found the second half of that claim FALSE: `IRWeights` has exactly ONE real definition
    (`Core/IR/Compile.lean:74`); the other two occurrences are **docstring quotations of it**.

    => that is the same class of error this project keeps making: counting a NAME without asking whether the
       occurrence is a definition at all.

    => so the measurement is made repeatable here, and `--check` keeps it from growing.

WHAT IT MEASURES

    For each type in `TYPES`: comment-stripped occurrences of
        structure <Type>   /   abbrev <Type>   /   def <Type>
    with one exception that matters: an occurrence inside a DOCSTRING disappears once comments are stripped,
    because Lean docstrings ARE block comments (`/-- … -/`). That is exactly why this file uses the project's
    single comment-stripping authority instead of a regex over raw text.

    For `structure` sites it also records the field lines, so "are the copies the same shape?" is answered by
    data rather than by assertion.

WHAT IT DOES NOT DO

    It does not decide whether two copies SHOULD be merged, and it does not see through `namespace` nesting to
    produce fully-qualified names. It reports file:line and the field signature; the convergence decision is a
    separate, registered piece of work.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
LATTICE = os.path.join(REPO, "Lattice")
BASELINE = os.path.join(HERE, "type-duplication-baseline.txt")
sys.path.insert(0, HERE)
# Round 994: this scanner is LINE-ORIENTED -- it anchors on `^\s*structure` and reports file:line.
# `tools.lean_source.strip_comments` DROPS newlines inside block comments (round 969 recorded that
# difference deliberately), so using it here collapsed the source and found one definition per type
# with line numbers `:9`/`:10`. The newline-PRESERVING implementation in `sorry_axiom_census` is the
# right one for this consumer, which is exactly why round 969 kept both instead of merging them.
from tools.sorry_axiom_census import strip_comments  # noqa: E402

#: type name -> the keywords that can introduce it
TYPES = {
    "VectorConstraint": ("structure",),
    "ConstraintSet": ("abbrev", "def"),
    "IRWeights": ("abbrev", "def"),
}

DECL = re.compile(r"^\s*(structure|abbrev|def)\s+([A-Za-z_][A-Za-z0-9_']*)\b")
STOP = re.compile(r"^\s*(deriving|structure|abbrev|def|theorem|lemma|end)\b")


def sites(type_name, stripped_src):
    """[(line, kind, field-signature)] for every real declaration of `type_name`."""
    lines = stripped_src.split("\n")
    out = []
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if not m or m.group(2) != type_name:
            continue
        kind = m.group(1)
        fields = []
        if kind == "structure":
            for j in range(i + 1, min(i + 24, len(lines))):
                s = lines[j].strip()
                if not s:
                    continue
                if STOP.match(lines[j]):
                    break
                fields.append(s)
        out.append((i + 1, kind, " | ".join(fields)))
    return out


def measure():
    """type name -> [(relative file, line, kind, field signature)]."""
    table = {t: [] for t in TYPES}
    for root, _dirs, files in os.walk(LATTICE):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, REPO).replace(os.sep, "/")
            src = strip_comments(io.open(p, encoding="utf-8", errors="replace").read())
            for t in TYPES:
                for ln, kind, sig in sites(t, src):
                    table[t].append((rel, ln, kind, sig))
    return table


def baseline():
    got = {}
    if not os.path.isfile(BASELINE):
        return got
    for line in io.open(BASELINE, encoding="utf-8").read().split("\n"):
        if line.strip() and not line.startswith("#"):
            parts = line.split("\t")
            if len(parts) >= 2:
                got[parts[0]] = int(parts[1])
    return got


def main():
    table = measure()
    base = baseline()
    problems = []
    print("  type                 real definitions   distinct field signatures")
    print("  " + "-" * 66)
    for t in sorted(table):
        rows = table[t]
        sigs = {r[3] for r in rows if r[3]}
        print("  %-20s %3d                 %d" % (t, len(rows), len(sigs)))
        for rel, ln, kind, _sig in rows:
            print("      %s:%d  (%s)" % (rel, ln, kind))
        if t in base and len(rows) > base[t]:
            problems.append("%s: %d real definitions, baseline %d" % (t, len(rows), base[t]))
    for p in problems:
        print("  PROBLEM %s" % p)
    if problems:
        print("TYPE DUPLICATION: %d problem(s)" % len(problems))
        return 1
    print("TYPE DUPLICATION: no type grew past its recorded count")
    return 0


def _self_test():
    """The stripper must be what decides docstring from definition -- that is the whole point."""
    ok = True

    real = "structure VectorConstraint where\n  a : List Int\n  b : Int\n"
    if len(sites("VectorConstraint", real)) != 1:
        print("  SELF-TEST FAIL: a real structure was not counted")
        ok = False

    inside_doc = "/-- docs\n```lean\nstructure VectorConstraint where\n  a : List Int\n```\n-/\n"
    stripped = strip_comments(inside_doc)
    if len(sites("VectorConstraint", stripped)) != 0:
        print("  SELF-TEST FAIL: a structure quoted INSIDE a docstring was counted -- the stripper is not used")
        ok = False

    # and the raw text WOULD have counted it, which is exactly the mistake the audit made
    if len(sites("VectorConstraint", inside_doc)) != 1:
        print("  SELF-TEST FAIL: the control (unstripped) did not count the docstring copy")
        ok = False

    if "IRWeights" not in TYPES:
        print("  SELF-TEST FAIL: TYPES lost a configured type")
        ok = False

    print("TYPE DUPLICATION SELF-TEST: %s" % ("real counted, docstring not, control behaves" if ok else "FAILED"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(_self_test())
    sys.exit(main())
