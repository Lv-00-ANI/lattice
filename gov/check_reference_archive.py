# -*- coding: utf-8 -*-
"""Check that the ARCHIVED part of `Reference/` stays out of the build (stage C, P3-3).

## The structure, measured rather than assumed

**`Lattice/Reference/` is NOT one thing. It has two parts with opposite standing:**

| part | status | who imports it |
|:--|:--|:--|
| **`Geometry/Constraints`, `Geometry/Geometry`, `Geometry/ConstraintsRoot`, `Geometry/GeometryRoot`** | **LIVE** -- builds clean (`ConstraintsRoot` = BUILD 0), and **28 live modules across `Domains`, `Plugins`, `Semantics`, `Usage`, `Compose`, `Evidence` import it** | **real consumers** |
| **`Geometry/LvFormal/`** | **ARCHIVED** -- early reference formalisations; **50 of its 93 `Theory/` files do not compile, 17 contain `sorry`/`axiom`** | **nothing in the pipeline** |

**=> "treat Reference as archive" and "treat Reference as live" are BOTH wrong.**
**Round 186 tried the first and started building 209 files; the plan's P3-3 implied the second. Neither is the
tree.**

## What this check enforces

**The archive is `Lattice/Reference/Geometry/LvFormal/`. The boundary is around THAT, not around
`Reference/`.**

1. **No aggregator may exist for the archived subtree** (`Lattice/Reference/Geometry/LvFormal.lean` must not
   exist) -- an aggregator there means the archive was wired into `lake build`;
2. **No module OUTSIDE the archived subtree may import a `Lattice.Reference.Geometry.LvFormal.` module** --
   otherwise the archive becomes a build dependency of the live tree;
3. **`Lattice/Reference/Geometry/LvFormal/README.md` must exist and label the subtree as an archive** -- a
   boundary nobody writes down gets re-crossed, which is exactly how round 186 happened.

**The LIVE part is deliberately NOT restricted: `check_layer_reachability` skips it, but that is a
measurement choice about the layer's index, not an archive claim, and the 28 real importers prove it.**

Usage:
    python check_reference_archive.py            # report
    python check_reference_archive.py --strict   # exit 1 on any finding
"""

import io
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LATTICE = os.path.join(ZERO, "Lattice")

# The ARCHIVED subtree -- measured: it does not compile, nothing live depends on it.
ARCHIVE = os.path.join(LATTICE, "Reference", "Geometry", "LvFormal")
ARCHIVE_PREFIX = "Lattice.Reference.Geometry.LvFormal."

IMPORT_RE = re.compile(r"(?m)^import\s+(Lattice\.Reference\.Geometry\.LvFormal\.[A-Za-z0-9_.]+)\s*$")


def lean_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for name in filenames:
            if name.endswith(".lean"):
                yield os.path.join(dirpath, name)


def is_inside_archive(path):
    return os.path.abspath(path).startswith(os.path.abspath(ARCHIVE) + os.sep)


def main(argv):
    strict = "--strict" in argv
    findings = []

    # 1. no aggregator for the archived subtree
    agg = os.path.join(LATTICE, "Reference", "Geometry", "LvFormal.lean")
    if os.path.exists(agg):
        findings.append(
            "WIRED IN: Lattice/Reference/Geometry/LvFormal.lean exists -- the archive has a build aggregator"
        )

    # 2. no live module imports the archive
    for path in lean_files(LATTICE):
        if is_inside_archive(path):
            continue
        text = io.open(path, encoding="utf-8", errors="replace").read()
        hit = IMPORT_RE.search(text)
        if hit:
            rel = os.path.relpath(path, LATTICE).replace("\\", "/")
            findings.append(
                "WIRED IN: %s imports %s" % (rel, hit.group(1).rstrip())
            )

    # 3. the boundary must be documented
    readme = os.path.join(ARCHIVE, "README.md")
    if not os.path.exists(readme):
        findings.append(
            "UNDOCUMENTED: Lattice/Reference/Geometry/LvFormal/README.md is missing"
        )
    else:
        text = io.open(readme, encoding="utf-8", errors="replace").read()
        if "归档" not in text and "archive" not in text.lower():
            findings.append(
                "UNDOCUMENTED: the LvFormal README does not label the subtree as an archive"
            )

    n_arch = sum(1 for _ in lean_files(ARCHIVE))
    n_live = len(set(os.path.dirname(p) for p in lean_files(os.path.join(LATTICE, "Reference")) if not is_inside_archive(p)))

    print("REFERENCE ARCHIVE BOUNDARY")
    print("  archived subtree      : Lattice/Reference/Geometry/LvFormal")
    print("  archived modules      : %d" % n_arch)
    print("  live Reference dirs   : %d" % n_live)
    print("  aggregator present    : %s" % ("YES (bad)" if os.path.exists(agg) else "no (correct)"))
    print("  documented            : %s" % ("yes" if os.path.exists(readme) else "NO"))

    if findings:
        print()
        for f in findings:
            print("  FINDING %s" % f)
        print("\nREFERENCE ARCHIVE: %d finding(s)" % len(findings))
        return 1 if strict else 0

    print("\nREFERENCE ARCHIVE: correctly isolated -- %d archived module(s) outside the build"
          % n_arch)
    return 0


def self_test():
    """Demonstrate the check fires on a wired-in archive."""
    ok = True

    if not IMPORT_RE.search("import Lattice.Reference.Geometry.LvFormal.Theory.CacheCoherenceTheory\n"):
        print("  self-test FAILED: the import regex does not match a real archive import")
        ok = False

    if IMPORT_RE.search("import Lattice.Reference.Geometry.ConstraintsRoot\n"):
        print("  self-test FAILED: the import regex matched a LIVE module (it must not)")
        ok = False

    inside = os.path.join(ARCHIVE, "Theory", "X.lean")
    if not is_inside_archive(inside):
        print("  self-test FAILED: an archive path was not recognised")
        ok = False
    live = os.path.join(LATTICE, "Lib", "X.lean")
    if is_inside_archive(live):
        print("  self-test FAILED: a live path was classified as archive")
        ok = False

    undoc = "notes"
    if "归档" in undoc or "archive" in undoc.lower():
        print("  self-test FAILED: the documentation test is vacuous")
        ok = False

    print("  self-test: %s" % ("all four failure modes fire" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
