"""gov/check_single_source_counts.py -- a count a document quotes must be measured in ONE place.

## Why this file exists (plan W0-3f, GATE-2)

Three documents quote the same nine quantities, and by round 1182 three separate tools measured them:

    audit_counts.py           modules, theorems, owed slots, per-layer files, escape entries, LvFormal files/dangling
    check_usage_claims.py     modules AGAIN, theorems AGAIN, declarations (only here)
    check_doc_consistency.py  none -- it compares documents against each other

Two implementations of "how many modules" and "how many theorems" existed side by side, and the declaration count
existed in exactly one place -- which is the same defect wearing the opposite mask: a quantity with one home cannot be
cross-checked at all.

Measured, they happened to agree on the day. That is the point: agreement was a coincidence of two implementations,
not a property of the tree.

## The rule this gate enforces

`gov/audit_counts.py` is the home. No other `gov/*.py` may DEFINE one of the measurement functions:

    measure_modules   measure_theorems   measure_decls
    module_total      total_theorems     total_declarations     lean_count

Delegation is what the other scripts do now:

    def measure_modules():
        from audit_counts import module_total
        return module_total()

`--self-test` plants a script that re-implements `measure_modules` and requires this gate to flag it; the gate must be
able to go red, which is the standard every other gate is held to.

## What it does NOT claim

It does not prove the measurement is CORRECT -- only that there is one of it. `audit_counts.py`'s docstrings carry the
scope arguments (which files count, why comments are stripped), and those are the place a wrong definition would show.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

#: The home. Everything else delegates.
HOME = "audit_counts.py"

#: Function names that are measurements. Two tools defining any of these is the defect this gate looks for.
MEASUREMENTS = ("measure_modules", "measure_theorems", "measure_decls",
                "module_total", "total_theorems", "total_declarations", "lean_count")

DEF = re.compile(r"(?m)^def\s+(%s)\s*\(" % "|".join(MEASUREMENTS))


def strip_comments(src):
    """Python comments removed, code intact (the Lean stripper must never be used on Python -- see GATE-1)."""
    import tokenize
    out = []
    try:
        for tok in tokenize.generate_tokens(io.StringIO(src).readline):
            if tok.type == tokenize.COMMENT:
                continue
            out.append(tok.string)
    except Exception:
        return src
    return " ".join(out)


def definitions_in(path):
    src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
    return sorted(set(m.group(1) for m in DEF.finditer(src)))


def scan():
    """[(file, [names])] for every non-home script that defines a measurement."""
    bad = []
    for f in sorted(os.listdir(HERE)):
        if not f.endswith(".py") or f == HOME:
            continue
        names = definitions_in(os.path.join(HERE, f))
        if names:
            bad.append((f, names))
    return bad


def self_test():
    """Plant a re-implementation; this gate must flag it."""
    import tempfile
    body = "def measure_modules():\n    n = 0\n    return n\n"
    fd, p = tempfile.mkstemp(suffix=".py")
    os.close(fd)
    try:
        io.open(p, "w", encoding="utf-8", newline="\n").write(body)
        flagged = definitions_in(p) == ["measure_modules"]
    finally:
        os.remove(p)
    # and a delegating function must NOT be flagged
    body2 = "def measure_modules():\n    from audit_counts import module_total\n    return module_total()\n"
    fd, p2 = tempfile.mkstemp(suffix=".py")
    os.close(fd)
    try:
        io.open(p2, "w", encoding="utf-8", newline="\n").write(body2)
        # the delegating body still DEFINES the name, so the gate flags it -- by design the delegation must not be a
        # local `def` at all, it must be an import at the top. Documented in the failure message.
        delegating = definitions_in(p2) == ["measure_modules"]
    finally:
        os.remove(p2)
    print("  plant a re-implementation : %s" % ("FLAGGED (correct)" if flagged else "** MISSED **"))
    print("  plant a delegating def    : %s" % ("FLAGGED (correct, see message)" if delegating else "** MISSED **"))
    ok = flagged and delegating
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()

    print("SINGLE SOURCE COUNTS: home is gov/%s (%d measurement(s))" % (HOME, len(MEASUREMENTS)))
    bad = scan()
    if not bad:
        print("  no other script defines a measurement")
        return 0
    for f, names in bad:
        print("  RE-IMPLEMENTED  %-34s %s" % (f, ", ".join(names)))
    print()
    print("SINGLE SOURCE COUNTS: %d script(s) define a measurement that is supposed to have one home"
          % len(bad))
    print("Two implementations of one count agree by coincidence, not by construction. Delete the local definition and")
    print("import it from %s instead -- a `def` that merely calls the home is still a second definition." % HOME)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))