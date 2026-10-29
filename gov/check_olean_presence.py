"""gov/check_olean_presence.py -- every non-`Reference` module must have been built at least once.

## The family this belongs to

Three rounds of the same defect, each one step further out:

| round | the check | what it could not see |
|:--|:--|:--|
| 43 | I7: does the `.olean` exist? | **reachability** -- `Compose` was on disk and built by name, but not in the root closure |
| 44 | reachability from the root / from the layer aggregator | **an empty layer directory made a scan skip the whole layer** |
| 45 | this file | **whether a module was ever built at all** |

## Two measurements, and one of them corrects the forwarded list

The list's `P0-11` says "310 oleans older than their sources" and treats that as a defect. Measured:

    sources (.lean)         : 964
      olean missing         : 121   <- ALL of them under `Reference/`
      olean older than src  : 310   <- the list's number, exactly
      olean at least as new : 533

**The 310 is a real count and not a defect.** `lake` decides what to rebuild from **content hashes**, not
mtimes: an olean whose mtime is older than its source may still have been produced *from* that source. The
proof that this is not a correctness problem is that `lake build Lattice` **passes** with all 310 as they are.
**A gate on mtime would fire after every `git checkout`, every `touch`, every clock change** -- it would be a
false-alarm generator, which is its own kind of broken check.

**The 121 are the real item**, and they are all `Reference/` -- a subtree that is **never built** (the list's
`P0-17`). That is a **known boundary**, not a regression, so it is **reported** here and **not gated**: a gate
that fails on a boundary nobody is going to move is a gate that gets baselined into silence.

**What IS gated**: a **non-`Reference`** module with no olean. That means it was never built at all, and the
count is 0 today.

## Why this is worth having after rounds 43 and 44

Both of those were about *which* modules a build reaches. This one is about whether a module entered a build
**at all** -- the weakest of the three questions, and the one nothing was asking.
"""

import io
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ROOT, "Lattice")
BUILD = os.path.join(ROOT, ".lake", "build", "lib", "Lattice")


def sources():
    out = []
    for root, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if f.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(root, f), LAT).replace("\\", "/"))
    return sorted(out)


def olean_of(rel):
    return os.path.join(BUILD, rel.replace("/", os.sep)[:-5] + ".olean")


def classify():
    """`(missing_nonref, missing_ref, stale_mtime, fresh)`."""
    mn, mr, stale, fresh = [], [], 0, 0
    for rel in sources():
        obj = olean_of(rel)
        if not os.path.exists(obj):
            (mr if rel.startswith("Reference/") else mn).append(rel)
            continue
        if os.path.getmtime(os.path.join(LAT, rel.replace("/", os.sep))) > os.path.getmtime(obj):
            stale += 1
        else:
            fresh += 1
    return mn, mr, stale, fresh


def self_test():
    ok = True
    # the missing direction, exercised on a name that cannot exist
    if os.path.exists(olean_of("This/Does/Not/Exist.lean")):
        print("  SELF-TEST: an absent module reported an olean")
        ok = False
    # `olean_of` must place the artifact under `.lake/build/lib/Lattice/`
    p = olean_of("Core/Net.lean")
    if ".lake" not in p.replace("\\", "/") or not p.replace("\\", "/").endswith("Lattice/Core/Net.olean"):
        print("  SELF-TEST: olean_of produced %r" % p)
        ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


def main(argv):
    mn, mr, stale, fresh = classify()
    total = len(mn) + len(mr) + stale + fresh

    print("OLEAN PRESENCE (`lake build` must have seen every non-Reference module)")
    print("  sources                     : %d" % total)
    print("  built, olean >= source      : %d" % fresh)
    print("  built, olean older by mtime : %d   (NOT a defect -- `lake` uses content hashes)" % stale)
    print("  no olean, non-Reference     : %d   <-- gated" % len(mn))
    print("  no olean, under Reference/  : %d   (a known boundary: that subtree is never built)"
          % len(mr))
    for rel in mn[:10]:
        print("       %s" % rel)
    if len(mn) > 10:
        print("       ... and %d more" % (len(mn) - 10))

    if mn:
        print()
        print("OLEAN PRESENCE: %d non-Reference module(s) were never built" % len(mn))
        return 1
    print()
    print("OLEAN PRESENCE: every non-Reference module has an olean; %d Reference module(s) unbuilt and"
          " reported, not gated" % len(mr))
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
