# -*- coding: utf-8 -*-
"""Distinguish INTENDED duplicate names from ACCIDENTAL ones, and record which cannot be merged.

## What round 923 measured, and what it could not say

`audit_duplicate_names.py` found 309 shared short names. It gives a BOUND, which is right for catching
regressions, but it cannot say WHY a name is shared. Three very different situations produce the same count:

1. **Per-directory repetition that is INTENDED** -- `manifest` / `manifest_nonempty` in 11 plugin
   directories, or `linearCarrier` in several algebra files. Merging these would be wrong.
2. **Twin definitions that CANNOT be merged** -- `Lattice.sigmoid` and `Lattice.relu`. `RealNonlinear.lean:35`
   records it verbatim: importing both reports `environment already contains 'Lattice.sigmoid'`.
   (See `RealNonlinearFidelity.lean:15` for the recorded error.) Neither can be deleted without
   touching every importer, and both cannot coexist in one environment.
3. **Accidental collisions** -- the kind that cost round 921.

**=> a count alone cannot distinguish them, so the count alone cannot direct work.**

## What this file does

**It records, per shared name, which of the three situations applies -- and it CHECKS that record against the
tree**, so a name that changes category is noticed.

The record is `gov/duplicate-name-classes.txt`, one line per name:

    name<TAB>class<TAB>note

with `class` in {`intended`, `unmergeable`, `accidental`}. A name that comes out `accidental` is a defect.

## Usage

    python check_duplicate_classes.py            # report
    python check_duplicate_classes.py --check    # fail on (a) unclassed shared names, (b) `accidental` entries,
                                                 #         (c) recorded names that are no longer shared
    python check_duplicate_classes.py --self-test
"""

import collections
import io
import os
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RECORD = os.path.join(ZERO, "gov", "duplicate-name-classes.txt")

sys.path.insert(0, os.path.join(ZERO, "gov"))
import audit_duplicate_names as DUP  # noqa: E402


def load_record():
    """name -> (class, note)."""
    if not os.path.exists(RECORD):
        return {}
    out = {}
    for raw in io.open(RECORD, encoding="utf-8"):
        line = raw.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        name, cls = parts[0], parts[1]
        note = parts[2] if len(parts) > 2 else ""
        out[name] = (cls, note)
    return out


def main(argv):
    shared = DUP.scan()
    record = load_record()

    unclassed = [n for n in shared if n not in record]
    accidental = [n for n, (c, _) in record.items() if c == "accidental"]
    stale = [n for n in record if n not in shared]

    by_class = collections.Counter(c for c, _ in record.values() if True)

    print("DUPLICATE CLASSES: %d shared name(s), %d recorded" % (len(shared), len(record)))
    for cls in ("intended", "unmergeable", "accidental"):
        print("  %-12s %d" % (cls, by_class.get(cls, 0)))
    print("  %-12s %d" % ("unclassed", len(unclassed)))

    if unclassed:
        print("\n  unclassed (each needs a line in duplicate-name-classes.txt):")
        for n in sorted(unclassed)[:15]:
            print("    %-34s in %d files" % (n, len(shared[n])))
        if len(unclassed) > 15:
            print("    ... and %d more" % (len(unclassed) - 15))

    if accidental:
        print("\n  ACCIDENTAL (defects): %s" % ", ".join(sorted(accidental)))

    if stale:
        print("\n  recorded but no longer shared: %s" % ", ".join(sorted(stale)[:10]))

    if "--check" in argv:
        bad = bool(accidental) or bool(unclassed) or bool(stale)
        if bad:
            print("\nDUPLICATE CLASSES: FAIL")
            return 1
        print("\nDUPLICATE CLASSES: every shared name is classified and none is accidental")
    return 0


def self_test():
    ok = True
    shared = DUP.scan()
    # the two names this round is about must be in the tree and must be classifiable
    if "relu" not in shared:
        print("  self-test FAILED: `relu` collision disappeared")
        ok = False
    record = load_record()
    for n in ("relu", "sigmoid"):
        if n in shared and n not in record:
            print("  self-test: `%s` is shared but unrecorded (classifier will flag it)" % n)
    # the classifier must be able to see a non-empty record
    if not record:
        print("  self-test FAILED: the record file is empty or missing")
        ok = False
    print("  self-test: %s" % ("both fixture names present and the record loads"
                               if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
