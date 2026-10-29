"""`gov/check_cinterface_abi.py` -- the C ABI name table must equal the primitives that exist.

## Why this gate

`Lattice/CInterface/ABI.lean` lists the 11 primitives by **name string**. `Lattice/Compose/*` defines the
primitives **for real**. Nothing in Lean connects the two: a string list cannot be checked against
definitions, and `decide` can only prove the list against itself.

So a rename in `Compose` would leave the ABI table silently describing a function that no longer exists --
**and `lake build` would still pass**, because the ABI file never mentions the Lean definitions.

This is the same class as the eight gates this session had to add: **a claim that nothing compares against
reality**. Here the comparison is cheap and exact: the names `gen_primitive_matrix.py` extracts from
`Lattice/Compose` versus the names in `ABI.primitiveNames`.

## What it checks

1. the set of primitive names derived from `Compose` equals the set in `primitiveNames`;
2. there are no duplicates on either side (duplicates in the ABI are a real C symbol collision).

## Self-test

Both directions: a **missing** name and an **extra** name must both be reported.
"""

import io
import importlib.util
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
ABI = os.path.join(ZERO, "Lattice", "CInterface", "ABI.lean")

# Round 55: `ABI.lean` no longer keeps its own `primitiveNames`. It now proves
#     abiTable_names_eq_verified : abiTable.map CFunction.name = Compose.primitiveNames
# against the environment-checked list, so the strings this checker wants are the `name := "..."` fields
# of `abiTable` itself -- which is the real source of truth, not a second copy of it.
NAMES = re.compile(r"def abiTable : List CFunction :=\s*\[(.*?)\n\s*\]", re.S)
NAME_FIELD = re.compile(r"\bname := \"([^\"]+)\"")
STR = re.compile(r"\"([^\"]+)\"")


def compose_primitives():
    """The canonical names, using `gen_primitive_matrix.py`'s own extractor."""
    spec = importlib.util.spec_from_file_location(
        "gpm", os.path.join(HERE, "gen_primitive_matrix.py"))
    gpm = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gpm)
    return [p["name"] for p in gpm.primitives()]


def abi_names():
    src = io.open(ABI, encoding="utf-8").read()
    m = NAMES.search(src)
    if m:
        return NAME_FIELD.findall(m.group(1))
    if not m:
        return None
    return STR.findall(m.group(1))


def compare(compose, abi):
    """`(missing, extra, dup)` -- sets, so order does not matter."""
    cs, As = set(compose), set(abi)
    missing = sorted(cs - As)
    extra = sorted(As - cs)
    dup = sorted({n for n in abi if abi.count(n) > 1})
    return missing, extra, dup


def main(argv):
    compose = compose_primitives()
    abi = abi_names()
    if abi is None:
        print("CINTERFACE ABI: `primitiveNames` not found in %s" % ABI)
        return 1
    missing, extra, dup = compare(compose, abi)
    print("CINTERFACE ABI: %d primitive(s) in Compose, %d in the ABI table"
          % (len(compose), len(abi)))
    for n in missing:
        print("   MISSING from ABI  %s" % n)
    for n in extra:
        print("   EXTRA in ABI      %s" % n)
    for n in dup:
        print("   DUPLICATE in ABI  %s" % n)
    if missing or extra or dup:
        print("CINTERFACE ABI: the ABI table no longer matches the primitives that exist")
        return 1
    return 0


def self_test():
    ok = True
    base = ["a", "b", "c"]
    # exact
    if compare(base, ["c", "a", "b"]) != ([], [], []):
        print("  exact match FAILED")
        ok = False
    # missing
    m, e, d = compare(base, ["a", "b"])
    if m != ["c"] or e or d:
        print("  missing direction FAILED: %r %r %r" % (m, e, d))
        ok = False
    # extra
    m, e, d = compare(base, ["a", "b", "c", "d"])
    if m or e != ["d"] or d:
        print("  extra direction FAILED: %r %r %r" % (m, e, d))
        ok = False
    # duplicate
    m, e, d = compare(base, ["a", "a", "b", "c"])
    if d != ["a"]:
        print("  duplicate direction FAILED: %r" % (d,))
        ok = False
    print("SELF-TEST %s" % ("PASS" if ok else "FAIL"))
    return 0 if ok else 2


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
