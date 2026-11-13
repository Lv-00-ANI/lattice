# -*- coding: utf-8 -*-
"""Check that the fully-ARCHIVED LvFormal geometry tree stays out of the build (stage C, P3-3).

## The decision, and the measurement behind it

**Round 186 read `check_layer_reachability`'s skip of `Reference/` as a bug and tried to wire all 209 modules
into the build. That was wrong.**

**Round 187 measured again and the user ruled on the content:**

- **`Lattice/Reference/Geometry/LvFormal/` had 103 modules and ~3110 declarations, and NOTHING in `Lattice/`
  imported it** -- dead code with no consumers;
- **the geometry content is OBSOLETE** (the user's words: "都是几何相关的用不到了");
- **therefore it was MOVED OUT of `Lattice/` entirely, to `archive/LvFormal/`.**

**=> this is a FULL archive, not a "keep it nearby and don't build it" arrangement. The directory is no longer
under `Lattice/`, so no Lean build, no layer aggregator, and no `gov/` measurement can reach it by accident.**

## What is NOT archived

**`Lattice/Reference/Geometry/Constraints`, `Geometry/Geometry`, `ConstraintsRoot`, `GeometryRoot` remain LIVE:**
**`ConstraintsRoot` builds clean and 28 modules across `Domains`, `Plugins`, `Semantics`, `Usage`, `Compose`,
`Evidence` import them.** **=> "Reference is an archive" is false; only the `LvFormal` subtree was.**

## What this check enforces

1. **`Lattice/Reference/Geometry/LvFormal/` must NOT exist** -- if it comes back, the archive was re-wired;
2. **no module under `Lattice/` may import `Lattice.Reference.Geometry.LvFormal.*`** -- importing a module that
   no longer exists would break the build, and importing a re-added one would silently re-enter the archive;
3. **`_archive/LvFormal/README.md` must exist and must label the directory as archived** -- an archive with no
   recorded reason gets re-crossed, which is exactly how round 186 happened.

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

# Where the archive USED to live; it must not come back.
OLD_ARCHIVE = os.path.join(LATTICE, "Reference", "Geometry", "LvFormal")

# Where it lives now.
ARCHIVE = os.path.join(ZERO, "archive", "LvFormal")

ARCHIVE_IMPORT_RE = re.compile(
    r"(?m)^import\s+(Lattice\.Reference\.Geometry\.LvFormal\.[A-Za-z0-9_.]+)\s*$"
)


def lean_files(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for name in filenames:
            if name.endswith(".lean"):
                yield os.path.join(dirpath, name)


def main(argv):
    strict = "--strict" in argv
    findings = []

    # 1. the old location must be empty
    if os.path.exists(OLD_ARCHIVE):
        findings.append(
            "RE-ADDED: Lattice/Reference/Geometry/LvFormal exists again -- the archive was moved back into the build tree"
        )

    # 2. nothing under Lattice/ may import it
    for path in lean_files(LATTICE):
        text = io.open(path, encoding="utf-8", errors="replace").read()
        hit = ARCHIVE_IMPORT_RE.search(text)
        if hit:
            rel = os.path.relpath(path, LATTICE).replace("\\", "/")
            findings.append("WIRED IN: %s imports %s" % (rel, hit.group(1).rstrip()))

    # 3. the archive must be documented where it now lives
    readme = os.path.join(ARCHIVE, "README.md")
    if not os.path.exists(readme):
        findings.append(
            "UNDOCUMENTED: _archive/LvFormal/README.md is missing -- the archive has no recorded reason"
        )
    else:
        text = io.open(readme, encoding="utf-8", errors="replace").read()
        if "归档" not in text and "archive" not in text.lower():
            findings.append(
                "UNDOCUMENTED: _archive/LvFormal/README.md does not label the directory as archived"
            )

    n_arch = sum(1 for _ in lean_files(ARCHIVE)) if os.path.isdir(ARCHIVE) else 0

    print("ARCHIVED LvFormal BOUNDARY")
    print("  archive location      : archive/LvFormal")
    print("  archived modules      : %d" % n_arch)
    print("  old location present  : %s" % ("YES (bad)" if os.path.exists(OLD_ARCHIVE) else "no (correct)"))
    print("  documented            : %s" % ("yes" if os.path.exists(readme) else "NO"))

    if findings:
        print()
        for f in findings:
            print("  FINDING %s" % f)
        print("\nARCHIVED LvFormal: %d finding(s)" % len(findings))
        return 1 if strict else 0

    print("\nARCHIVED LvFormal: fully archived -- %d module(s) outside Lattice/, zero importers"
          % n_arch)
    return 0


def self_test():
    """Demonstrate each failure mode fires, without touching the tree."""
    ok = True

    if not ARCHIVE_IMPORT_RE.search(
        "import Lattice.Reference.Geometry.LvFormal.Theory.CacheCoherenceTheory\n"
    ):
        print("  self-test FAILED: the archive import regex does not match a real archive import")
        ok = False

    if ARCHIVE_IMPORT_RE.search("import Lattice.Reference.Geometry.ConstraintsRoot\n"):
        print("  self-test FAILED: the regex matched a LIVE module (it must not)")
        ok = False

    undoc = "notes about files"
    if "归档" in undoc or "archive" in undoc.lower():
        print("  self-test FAILED: the documentation check is vacuous")
        ok = False

    if os.path.abspath(LATTICE).startswith(os.path.abspath(ARCHIVE)):
        print("  self-test FAILED: the archive contains Lattice/")
        ok = False

    print("  self-test: %s" % ("all four failure modes fire" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
