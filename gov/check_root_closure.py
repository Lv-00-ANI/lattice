"""gov/check_root_closure.py -- every layer aggregator must be reachable from `Lattice.lean`.

## The defect this closes

Round 43 found `Lattice/Compose.lean` **was never built by `lake build Lattice`**: the root did not import it.
Five rounds of Compose work (rounds 37-42) had been compiled **only because those modules were named
explicitly** on the command line. Two things followed, and the second is the serious one:

1. **843 modules were counted while the root closure contained fewer.** `audit_counts` counts files on disk;
   it does not ask what `lake build Lattice` actually reaches.
2. **`Lattice/Compose.lean` had a real syntax error** -- three `import` lines had been appended **after** the
   module docstring, which Lean rejects. **It sat there for five rounds because the file was unreachable.**
   An unreachable module hides whatever is wrong with it.

`gate.py`'s I7 did not catch this either: it checks that `.olean` files **exist**, and they did -- because the
modules had been built by name. **A check for existence cannot see reachability.**

## What this checks

For every `Lattice/<Name>.lean` there is a directory `Lattice/<Name>/` (so it is a layer aggregator), and
`Lattice.lean` must contain `import Lattice.<Name>`. A layer that is on disk but not in the root is a failure:
its theorems are in the tree and not in the build.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ROOT, "Lattice")
ENTRY = os.path.join(ROOT, "Lattice.lean")


def layers():
    """`[name]` for every top-level `Lattice/<Name>.lean`.

    Round 44 corrected this: a layer is the **file**, not the directory. `Slots` is a single-file layer whose
    directory (`Lattice/Slots/`) was empty and untracked and has been removed -- and while it existed, a
    file-enumerating scan silently skipped the whole layer. Requiring a directory made the gate call a
    legitimate import "EXTRA" once the directory was gone, which is the same confusion in the other direction.
    """
    return [f[:-5] for f in sorted(os.listdir(LAT)) if f.endswith(".lean")]


def imported():
    """The set of `Lattice.<name>` imported by the root."""
    if not os.path.exists(ENTRY):
        return set()
    src = io.open(ENTRY, encoding="utf-8").read()
    return set(re.findall(r"(?m)^import\s+Lattice\.([A-Za-z0-9_]+)\s*$", src))


def compare(have, want):
    """`(missing, extra)` -- factored out so `--self-test` can exercise both directions."""
    return sorted(want - have), sorted(have - want)


def self_test():
    ok = True

    # a layer on disk but not imported must be reported
    missing, extra = compare({"Core"}, {"Core", "Compose"})
    if missing != ["Compose"]:
        print("  MISSING direction FAILED: %r" % (missing,))
        ok = False
    if extra:
        print("  an import with no layer directory should not be 'extra' here: %r" % (extra,))
        ok = False

    # an import naming something that is not a layer is a different failure; it must be visible
    missing, extra = compare({"Core", "Ghost"}, {"Core"})
    if extra != ["Ghost"]:
        print("  EXTRA direction FAILED: %r" % (extra,))
        ok = False

    # the identity case
    if compare({"A", "B"}, {"A", "B"}) != ([], []):
        print("  identity comparison FAILED")
        ok = False

    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    want = set(layers())
    have = imported()
    missing, extra = compare(have, want)

    print("ROOT CLOSURE (every layer aggregator must be reachable from `Lattice.lean`)")
    print("  layer aggregators on disk : %d  %s" % (len(want), ", ".join(sorted(want))))
    print("  imported by `Lattice.lean`: %d" % len(have))

    for m in missing:
        print("   MISSING  Lattice.%s  -- the layer exists on disk but `lake build Lattice` never reaches it"
              % m)
    for e in extra:
        print("   EXTRA    Lattice.%s  -- imported by the root but there is no `Lattice/%s.lean`"
              % (e, e))

    if missing or extra:
        print("ROOT CLOSURE: %d missing, %d extra" % (len(missing), len(extra)))
        return 1
    print("ROOT CLOSURE: all %d layer(s) reachable" % len(want))
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
