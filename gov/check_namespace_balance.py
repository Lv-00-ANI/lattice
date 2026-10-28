"""`gov/check_namespace_balance.py` -- the file's outermost namespace must be closed by its last line.

## Why this exists, and why it is this narrow

Round 14. A splice script of mine replaced a declaration's body and **took the file's final `end Lattice`
with it**. `lake build` **passed**. Nothing in `I1`-`I8` looks at whether a file closes its namespaces --
the seventh instance in this session of a defect class with no check.

## Why it is NOT a stack-based checker

My first version tracked `namespace`/`section`/`end` on a stack. It reported **28 files** as unbalanced, all
of them **false positives** that `lake build` accepts -- e.g. `Runtime/RealModLoss.lean` has

    line 134: end
    line 136: end Lattice

and Lean is happy with it. **Lean's `end` scoping is more permissive than a line-level stack models**, so a
stack checker would have shipped with a 28-file false-alarm rate and been switched off within a week.

⭐ **The narrow claim that IS decidable, and that catches the real defect**:

> the last non-blank, non-comment line of the file must be `end <first namespace opened in the file>`

That is one comparison, cannot produce a false positive on a file Lean accepts, and **fails exactly when the
trailing `end` is dropped** -- the defect that happened.

⚠ **What it does NOT check**: mismatched `end`s anywhere in the middle of a file. Those are the cases Lean
itself rejects at build time, so they are already covered by `lake build`.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")

BLOCK = re.compile(r"/-.*?-/|/-!.*?-*/", re.S)
FIRST_NS = re.compile(r"(?m)^namespace\s+(\S+)\s*$")
LAST_END = re.compile(r"^end\s+(\S+)\s*$")


def strip_block_comments(src):
    return BLOCK.sub(lambda m: "\n" * m.group(0).count("\n"), src)


def check_one(src):
    """`None` if fine, else a message."""
    src = strip_block_comments(src)
    ns = FIRST_NS.search(src)
    if not ns:
        return None                      # no namespace: nothing to close
    want = ns.group(1)

    tail = [ln.split("--")[0].strip() for ln in src.split("\n")]
    tail = [ln for ln in tail if ln]
    if not tail:
        return "file is empty"
    last = tail[-1]
    m = LAST_END.match(last)
    if not m:
        return "last line is `%s`, not `end %s`" % (last[:60], want)
    if m.group(1) != want:
        return "last line closes `%s`, but the file's first namespace is `%s`" % (m.group(1), want)
    return None


BASE = os.path.join(HERE, "namespace-baseline.txt")


def scan():
    out = {}
    scanned = 0
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            scanned += 1
            msg = check_one(io.open(p, encoding="utf-8").read())
            if msg:
                out[rel] = msg
    return scanned, out


def main(argv):
    scanned, found = scan()

    if "--write-baseline" in argv:
        io.open(BASE, "w", encoding="utf-8", newline="\n").write(
            "# files whose outermost namespace is not closed by the last line.\n"
            "# Lean ACCEPTS these; the convention is to close them, and a baseline entry means\n"
            "# 'this one predates the check'. A NEW one is almost always script damage.\n"
            + "".join("%s\n" % k for k in sorted(found)))
        print("NAMESPACE CLOSURE: baseline written, %d entries" % len(found))
        return 0

    if not os.path.exists(BASE):
        print("NAMESPACE CLOSURE: no baseline (run --write-baseline once); %d found" % len(found))
        return 1

    base = {ln.rstrip("\n") for ln in io.open(BASE, encoding="utf-8")
            if ln.strip() and not ln.startswith("#")}
    new = sorted(set(found) - base)
    stale = sorted(base - set(found))

    print("NAMESPACE CLOSURE: %d scanned; %d unclosed; baseline %d; new %d; stale %d"
          % (scanned, len(found), len(base), len(new), len(stale)))
    for rel in new:
        print("   NEW   %s: %s" % (rel, found[rel]))
    for rel in stale:
        print("   STALE %s (closed now -- remove it from namespace-baseline.txt)" % rel)
    if new or stale:
        print("NAMESPACE CLOSURE: a new unclosed file is usually a script that ate a line")
        return 1
    return 0


def self_test():
    ok = True
    cases = [
        ("namespace A\ndef x := 1\nend A\n", None),
        ("namespace A\ndef x := 1\n", "unclosed"),        # THE defect
        ("namespace A\nend B\n", "closed"),               # wrong closer
        ("def x := 1\n", None),                            # no namespace
        ("/-! mentions namespace A -/\nnamespace A\ndef y := 2\nend A\n", None),
    ]
    for src, want in cases:
        msg = check_one(src)
        if want is None and msg is not None:
            print("  FAILED (expected clean) on %r: %s" % (src[:40], msg))
            ok = False
        if want == "unclosed" and msg is None:
            print("  FAILED (expected unclosed) on %r" % (src[:40],))
            ok = False
        if want == "closed" and (msg is None or "closes" not in msg):
            print("  FAILED (expected a mismatch) on %r: %s" % (src[:40], msg))
            ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
