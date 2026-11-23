"""gov/check_frozen_reference.py -- the geometry layer is FROZEN; bounded and enforced.

## Why this file exists

`Lattice/Reference/Geometry/` is a REFERENCE implementation of the geometric constraint domain: 100
modules, ~17.8k lines. It is not part of the objective's chain (data ⇄ token ⇄ symbol ⇄ weight); it is an
example domain that the chain is demonstrated on.

The user's instruction was to archive it and stop spending time on it. That instruction was measured
before it was obeyed, and the measurement says a physical archive is NOT possible without loss:

    modules in the geometry layer                       100
    mainline modules importing it directly               26
    mainline modules using a `Lattice.Geo.*` symbol       43
    transitive closure of those imports                 100   <- the whole layer
    LOC of the closure                            ~17,838
    files that import INTO the layer from outside         0   (the layer is closed)

A partial archive was attempted (68 of 100 modules, chosen as "not needed by any used symbol") and it
FAILED to build, because the directly imported modules pull in the rest. Restoring reproduced a green
build; the attempt is recorded in the branch history rather than repeated.

=> so "archive" cannot mean "move the files out". It means: **freeze the layer and make it stop costing
attention**. That is what this checker enforces, and it is the part that can be decided by a gate:

    * the set of mainline modules that import the geometry layer is a BASELINE;
    * a NEW importer fails, so the layer cannot grow its grip on the mainline;
    * a STALE entry also fails, so the baseline cannot quietly stop describing the tree.

Nothing here is about geometry being wrong. It is about geometry being an EXAMPLE: work spent on it is
work not spent on the chain.

## Interface

    python check_frozen_reference.py            # report
    python check_frozen_reference.py --check    # gate: exit 1 on NEW or STALE importer
    python check_frozen_reference.py --write    # rewrite the baseline (deliberate act)
    python check_frozen_reference.py --self-test
"""

import argparse
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LAT = os.path.join(ROOT, "Lattice")
BASELINE = os.path.join(HERE, "frozen-reference-baseline.txt")

IMPORT_REF = re.compile(r"(?m)^import\s+(Lattice\.Reference\.[\w.]+)\s*$")


def scan():
    """Return {mainline module path: sorted list of imported Reference modules}."""
    out = {}
    for root, _, fs in os.walk(LAT):
        if os.sep + "Reference" in root:
            continue
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, LAT).replace(os.sep, "/")
            try:
                t = io.open(p, "rb").read().decode("utf-8", errors="replace")
            except OSError:
                continue
            hits = IMPORT_REF.findall(t)
            if hits:
                out[rel] = sorted(set(hits))
    return out


def load_baseline():
    if not os.path.exists(BASELINE):
        return set()
    out = set()
    for line in io.open(BASELINE, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            out.add(line)
    return out


def write_baseline(found):
    lines = [
        "# gov/check_frozen_reference.py -- mainline modules importing the FROZEN geometry layer",
        "#",
        "# `Lattice/Reference/Geometry/` is an EXAMPLE domain, not part of the objective's chain.",
        "# Measured: 100 modules, ~17.8k lines, 26 direct importers, 43 users of `Lattice.Geo.*`, and the",
        "# transitive closure is all 100 -- so it cannot be archived without deleting real mainline code.",
        "# The decision taken instead is to FREEZE it: this list may only SHRINK.",
        "#",
        "# A new entry means some mainline module started depending on the example domain; that needs a",
        "# deliberate `--write` and a reason, because geometry work is time not spent on the chain.",
        "",
    ]
    lines += sorted(found)
    io.open(BASELINE, "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")


def self_test():
    bad = 0
    sample = "import Mathlib\nimport Lattice.Reference.Geometry.Constraints.Dist\n\ndef x := 1\n"
    got = IMPORT_REF.findall(sample)
    if got != ["Lattice.Reference.Geometry.Constraints.Dist"]:
        print("  SELF-TEST FAIL: importer scan -> %r" % got)
        bad += 1
    # an ordinary mainline import must not be mistaken for a geometry import
    if IMPORT_REF.findall("import Lattice.Lib.Penalty.Counterexample\n"):
        print("  SELF-TEST FAIL: non-geometry import matched")
        bad += 1
    # the module-level import must be at line start, not a substring inside a name
    if IMPORT_REF.findall("import Lattice.ReferenceX.Foo\n"):
        print("  SELF-TEST FAIL: prefix match leaked")
        bad += 1
    print("  frozen-reference self-test: %s" % ("ok" if bad == 0 else "%d FAILURES" % bad))
    return 0 if bad == 0 else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()

    found = scan()
    if args.write:
        write_baseline(found)
        print("  wrote %s (%d importer(s))" % (os.path.basename(BASELINE), len(found)))
        return 0

    base = load_baseline()
    today = set(found)
    new = sorted(today - base)
    stale = sorted(base - today)
    print("  frozen geometry layer: %d mainline importer(s), baseline %d" % (len(today), len(base)))
    modules = len(set(m for v in found.values() for m in v))
    print("  distinct Reference modules imported: %d" % modules)
    if new:
        print("  NEW importer(s) of the frozen layer (needs a reason, then --write):")
        for x in new:
            print("    " + x)
    if stale:
        print("  STALE baseline entr(ies) -- the baseline no longer describes the tree:")
        for x in stale:
            print("    " + x)
    if args.check and (new or stale):
        print("  FROZEN REFERENCE: %d new, %d stale -- the frozen set may only shrink" % (len(new), len(stale)))
        return 1
    if args.check:
        print("  FROZEN REFERENCE: baseline matches (%d)" % len(base))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())