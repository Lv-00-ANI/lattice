# -*- coding: utf-8 -*-
"""Check that the pipeline's FIVE STAGES are actually connected (stage C, P4).

## The finding this check keeps visible

**Measured: the pipeline has five stages, but they are not one chain.**

| stage | location | modules | imported from outside its layer? |
|:--|:--|--:|:--|
| **data** | `Core/Data` | 7 | yes (`Reference`) |
| **token** | `Core/IR` | 31 | yes (`Runtime`, `Lib`, `Compose`, `Plugins`) |
| **symbolic model** | `Core/CIC` | **91** | **only 5 importers, ALL inside `Core`** |
| **weight compiler** | `Lib/Compiler` | 49 | within `Lib` |
| **quantisation** | `Lib/Quantization` | 25 | within `Lib` |

**=> `Core/CIC` and `Lib/Compiler` have NO import relationship at all.** The 91-module symbolic model is
consumed only by `Core`'s own aggregator, two `Core/Data` modules, `Core/IR/Parse`, and one archived
`Reference` file. **Nothing on the weight side reads it.**

**The closed loop that DOES exist is `Lib/Editing/RealCompileExtractClosed.lean`, and its carrier is
`VectorConstraint` (from `Core/IR`, the TOKEN layer) -- not `Core/CIC`.** **So the proven loop covers
`token <-> weight`, not `symbolic model <-> weight`.**

## What this check enforces

**It does not demand the stages be connected -- closing the CIC->weight gap is a design decision about what a
CIC term SHOULD mean as a constraint set, not a mechanical fix (see PIPELINE-COVERAGE.md).**

**It demands the MEASUREMENT not silently change:**

1. **`Core/CIC` must still exist and must still be reachable;**
2. **the number of modules importing `Core/CIC` from outside `Core` must be REPORTED every run, so a bridge
   that is built (or a consumer that disappears) is visible immediately;**
3. **`Core/Data`, `Core/IR`, `Core/CIC`, `Lib/Compiler`, `Lib/Quantization` must all exist** -- a missing stage
   is a real regression.

**=> item 2 is the point: the gap is recorded as a NUMBER, not as a paragraph someone has to reread.**

Usage:
    python check_pipeline_stages.py
    python check_pipeline_stages.py --strict   # exit 1 if a stage vanished
"""

import os
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GOV = os.path.join(ZERO, "gov")
LATTICE = os.path.join(ZERO, "Lattice")

STAGES = [
    ("data", "Core/Data"),
    ("token", "Core/IR"),
    ("symbolic model", "Core/CIC"),
    ("weight compiler", "Lib/Compiler"),
    ("quantisation", "Lib/Quantization"),
]


def count_lean(path):
    n = 0
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        n += sum(1 for f in filenames if f.endswith(".lean"))
    return n


def main(argv):
    strict = "--strict" in argv
    findings = []
    sys.path.insert(0, GOV)
    import audit_layer_fanin as A

    layer_of, imports = A.modules_and_imports()

    rows = []
    for label, rel in STAGES:
        path = os.path.join(LATTICE, *rel.split("/"))
        n = count_lean(path) if os.path.isdir(path) else 0
        if n == 0:
            findings.append("MISSING STAGE: %s has no modules under %s" % (label, rel))
        rows.append((label, rel, n))

    # consumers of Core/CIC from OUTSIDE Core
    cic = {m for m in layer_of if m.startswith("Lattice.Core.CIC")}
    outside = set()
    for m, deps in imports.items():
        if m in cic:
            continue
        if layer_of.get(m) == "Core":
            continue
        if any(d in cic for d in deps):
            outside.add(m)

    print("PIPELINE STAGES")
    for label, rel, n in rows:
        print("  %-16s %-20s %4d module(s)" % (label, rel, n))
    print()
    print("  symbolic-model consumers OUTSIDE Core : %d" % len(outside))
    for m in sorted(outside):
        print("    %s" % m)
    print("  closed-loop carrier                   : VectorConstraint (Core/IR, the token layer)")
    print("  see PIPELINE-COVERAGE.md for what this means")

    if findings:
        print()
        for f in findings:
            print("  FINDING %s" % f)
        print("\nPIPELINE STAGES: %d finding(s)" % len(findings))
        return 1 if strict else 0

    # The consumer count is REPORTED, not gated: it is currently 1 (an archived Reference file).
    # When a real bridge is built this number rises; if a consumer disappears it falls.
    print("\nPIPELINE STAGES: all five stages present; symbolic-model fan-out is %d" % len(outside))
    return 0


def self_test():
    """Demonstrate the stage-presence detector fires."""
    ok = True

    # a stage directory that does not exist must produce 0 modules
    if count_lean(os.path.join(LATTICE, "DefinitelyNotALayer")) != 0:
        print("  self-test FAILED: counting a nonexistent directory did not return 0")
        ok = False

    # a real stage must produce a positive count
    if count_lean(os.path.join(LATTICE, "Core", "CIC")) <= 0:
        print("  self-test FAILED: Core/CIC counted as empty")
        ok = False

    # the stage table must name all five
    if len(STAGES) != 5:
        print("  self-test FAILED: the stage table lost an entry")
        ok = False

    print("  self-test: %s" % ("stage presence is measurable both ways" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
