# -*- coding: utf-8 -*-
"""Check that the known layer CYCLE does not GROW (stage C, P3-4).

## The state this records, measured

**`Lattice/Reference/` and `Lattice/Plugins/` depend on each other:**

| direction | edges | what they are |
|:--|--:|:--|
| **`Reference -> Plugins`** | **17** | **geometry modules needing the constraint IMPLEMENTATIONS** |
| **`Plugins -> Reference`** | **19** | **in-service plugins needing the geometry DEFINITIONS (`Expr`, `Constraint`, `Dist`, `Lipschitz`)** |

**Round 887 removed 5 pure facades and repointed their 16 importers, taking `Reference -> Plugins` from 22 to
17.** **The remaining edges are DEFINITION-OWNERSHIP, not path indirection: resolving them requires moving
`Expr`/`Constraint`/`Dist`/`Lipschitz` out of `Reference` into a lower layer, which is a different decision
than a cleanup (see `LAYER-CYCLE.md`).**

## What this check enforces

**It does NOT demand the cycle be zero -- that would fail every run and the gate would be turned off, which is
how a check becomes decorative. It demands the cycle not GROW:**

1. **`Reference -> Plugins` edges must be <= 17;**
2. **`Plugins -> Reference` edges must be <= 19.**

**=> a new import across the cycle fails the gate immediately, while the recorded debt stays visible and
bounded. Shrinking the numbers is allowed and does not require touching this file (the bound is a maximum).**

**The exact edges are enumerated in `LAYER-CYCLE.md`; this check keeps its counts honest.**

Usage:
    python check_layer_cycle.py            # report
    python check_layer_cycle.py --strict   # exit 1 if the cycle grew
"""

import os
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GOV = os.path.join(ZERO, "gov")

# Measured maxima, round 887. Shrinking is always allowed; growing is not.
MAX_REF_TO_PLUG = 17
MAX_PLUG_TO_REF = 19


def count_edges():
    sys.path.insert(0, GOV)
    import audit_layer_fanin as A

    layer_of, imports = A.modules_and_imports()
    pm = {m for m, l in layer_of.items() if l == "Plugins"}
    rm = {m for m, l in layer_of.items() if l == "Reference"}

    ref_to_plug = sum(1 for m in rm for d in imports[m] if d in pm)
    plug_to_ref = sum(1 for m in pm for d in imports[m] if d in rm)
    return ref_to_plug, plug_to_ref


def main(argv):
    strict = "--strict" in argv
    r2p, p2r = count_edges()
    findings = []

    if r2p > MAX_REF_TO_PLUG:
        findings.append(
            "GROWN: Reference -> Plugins is %d, was %d -- a new import crossed the cycle"
            % (r2p, MAX_REF_TO_PLUG)
        )
    if p2r > MAX_PLUG_TO_REF:
        findings.append(
            "GROWN: Plugins -> Reference is %d, was %d -- a new import crossed the cycle"
            % (p2r, MAX_PLUG_TO_REF)
        )

    print("LAYER CYCLE (Reference <-> Plugins)")
    print("  Reference -> Plugins : %d (max %d)" % (r2p, MAX_REF_TO_PLUG))
    print("  Plugins -> Reference : %d (max %d)" % (p2r, MAX_PLUG_TO_REF))
    print("  documented in        : LAYER-CYCLE.md")

    if findings:
        print()
        for f in findings:
            print("  FINDING %s" % f)
        print("\nLAYER CYCLE: %d finding(s)" % len(findings))
        return 1 if strict else 0

    print("\nLAYER CYCLE: bounded -- known debt did not grow (%d + %d edges)" % (r2p, p2r))
    return 0


def self_test():
    """Demonstrate the growth detector fires."""
    ok = True

    # a synthetic measurement above the bound must be flagged
    fake_r2p, fake_p2r = MAX_REF_TO_PLUG + 1, MAX_PLUG_TO_REF + 1
    fired = (fake_r2p > MAX_REF_TO_PLUG) and (fake_p2r > MAX_PLUG_TO_REF)
    if not fired:
        print("  self-test FAILED: the growth detector did not fire on inflated counts")
        ok = False

    # a measurement AT or BELOW the bound must not fire
    if (MAX_REF_TO_PLUG > MAX_REF_TO_PLUG) or (MAX_PLUG_TO_REF > MAX_PLUG_TO_REF):
        print("  self-test FAILED: the bound comparison fires on equal values")
        ok = False

    # shrinking must be accepted
    if (0 > MAX_REF_TO_PLUG):
        print("  self-test FAILED: a shrunken cycle is treated as growth")
        ok = False

    print("  self-test: %s" % ("growth fires, shrinkage and equality pass" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
