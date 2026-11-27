"""gov/check_gate_default_failure.py -- every registered GATE must contain a path that can make it fail.

## Why this file exists (plan W0-3f, GATE-1)

Round 1172 removed eight structurally-green checks by hand: five registrations that forgot their `--strict`, a stub
that could only return 0, a SKIP counted as a pass, and a baseline that scanned everything except its own subject.
Every one was found by reading the source, and every one was fixed by hand.

That is not a property of the tree, it is a property of my attention. This gate turns it into a property of the tree.

## The property, and what it deliberately does not claim

A gate passes if its SOURCE CONTAINS a failure exit: `return 1`, `return 2`, `sys.exit(1|2)`, `raise SystemExit`, or a
`SKIP_CODE` exit. Comment-stripped, so prose about failing does not count.

This is necessary, not sufficient. A script can contain `return 1` on a branch no tree state ever reaches -- which is
exactly the `--strict` shape that was invisible for dozens of rounds. What this catches is the weaker but still fatal
case: **no failure path at all**, which is what `check_g7` was. The stronger property needs a planted defect per
check, and the plan lists that as the next step rather than pretending this one proves it.

`--self-test` plants a script with only `return 0` and requires this gate to flag it -- so the gate itself is proven to
be able to go red, which is the standard every other gate is held to.
"""

import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "tools"))

import verify_all  # noqa: E402


def strip_comments(src):
    """Remove Python COMMENTS, leaving code intact.

    **The first version of this file used `tools.lean_source.strip_comments` -- a LEAN stripper -- and it destroyed
    the source: `audit_aliases.py` went from 11,233 bytes to 2,407, so every `return 1` in it disappeared and the gate
    reported twelve false "no failure path" findings. A stripper is language-specific; using the Lean one on Python is
    the same class of mistake as the README number that measured a different population.**

    `tokenize` is the standard answer and it cannot silently mis-cut: on a syntax error this falls back to the raw
    text, which can only make the gate MORE permissive, never less.
    """
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

#: A failure exit, in any of the spellings this tree uses. `SKIP_CODE` counts: a check that cannot execute is not a
#: pass, and its 77 exit is a legitimate non-zero path.
#: Every expression a script exits with, in the two spellings Python uses. **The property is NOT "contains a
#: failure literal" -- that whack-a-mole rejected `gate.py`, whose failures come back as `return EXIT["AXIOM"]` from a
#: dict of codes.** The property is: at least one exit expression is not the literal `0`. A stub whose only exit is
#: `return 0` is exactly the shape that has no failure path, and it is the shape `check_g7` had.
EXIT_EXPR = re.compile(r"\breturn\s+([^\n#]+)|\bsys\.exit\(\s*([^)\n]+)\s*\)")

#: Expressions that are unambiguously "no failure": nothing at all, zero, or None.
NO_FAILURE = {"0", "0L", "None", "False", "0.0"}


def script_of(cmd):
    """The `.py` path a registered command names, resolved against gov/."""
    for part in cmd.split():
        if part.endswith(".py"):
            return os.path.join(HERE, part)
    return None


def exits(path):
    """The set of exit expressions in a script, comments already stripped."""
    src = strip_comments(io.open(path, "rb").read().decode("utf-8", "replace"))
    out = []
    for m in EXIT_EXPR.finditer(src):
        expr = (m.group(1) or m.group(2) or "").strip()
        out.append(expr)
    return out


def has_failure_path(path):
    """True iff at least one exit expression is not a literal no-failure value."""
    exprs = exits(path)
    if not exprs:
        return False
    return any(e not in NO_FAILURE for e in exprs)


def scan():
    """[(label, script, ok, why)] for every gating registration."""
    out = []
    for label, cmd in verify_all.CHECKS:
        if label in verify_all.REPORT_ONLY:
            continue
        p = script_of(cmd)
        if p is None or not os.path.exists(p):
            out.append((label, cmd, False, "registered script not found"))
            continue
        ok = has_failure_path(p)
        out.append((label, os.path.basename(p), ok, "" if ok else "no failure exit in the source"))
    return out


def self_test():
    """Plant the three shapes that matter; this gate must separate them correctly."""
    import tempfile

    cases = [
        ("only `return 0`", "def main():\n    return 0\n", False),
        ("`return 1`", "def main():\n    return 1\n", True),
        # the shape that made the first version of this file wrong
        ("code chosen from a dict", 'EXIT = {"OK": 0, "AXIOM": 1}\ndef main(bad):\n    return EXIT["OK" if not bad else "AXIOM"]\n', True),
    ]
    ok = True
    for name, body, want in cases:
        fd, p = tempfile.mkstemp(suffix=".py")
        os.close(fd)
        try:
            io.open(p, "w", encoding="utf-8", newline="\n").write(body)
            got = has_failure_path(p)
        finally:
            os.remove(p)
        verdict = "accepted" if got else "FLAGGED"
        good = got == want
        ok = ok and good
        print("  %-26s %-9s %s" % (name, verdict, "correct" if good else "** WRONG **"))
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()

    rows = scan()
    bad = [r for r in rows if not r[2]]
    print("GATE DEFAULT FAILURE: %d gating registration(s) inspected" % len(rows))
    for label, script, ok, why in rows:
        if not ok:
            print("  NO FAILURE PATH  %-34s %s" % (label, why))
    if bad:
        print()
        print("GATE DEFAULT FAILURE: %d gate(s) cannot fail -- a check that cannot go red is indistinguishable from "
              "no check" % len(bad))
        return 1
    print("  every registered gate contains a failure exit")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))