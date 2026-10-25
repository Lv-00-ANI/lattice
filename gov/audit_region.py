#!/usr/bin/env python3
"""Are the theorem names cited in documentation *kernel* theorems, or only reference-region ones?

## The error this exists for

A README table wrote `collinear_iff_signed_area_zero` as the exactness theorem for the `collinear`
constructor. The name exists -- in `Zero/Reference/LvFormal/Theory/GeometryTopologyTheory.lean`. The kernel's
actual theorem is `LayerExact.collinearPenalty_eq_zero_iff_of_ne`, in a different region, with a weaker
statement (it carries a non-degeneracy hypothesis).

`audit_docs` could not see the problem: it checks whether a name exists **anywhere** under `Zero/`, and the
reference region is under `Zero/`. So a citation of a reference-region theorem passes as if it were a kernel
theorem, and the two regions have different standing -- the kernel builds and is gated, the reference region
partly does not build at all (see `_archive/LVFORMAL-BUILD-TRUTH.md`).

## What is checked

For every backticked identifier in a documentation file that matches a declaration name, classify the regions
that declare it:

* **kernel** -- `Zero/Core`, `Zero/Lift`, `Zero/Lib`, `Zero/Slots`, `Zero/Geo`;
* **reference** -- anything else under `Zero/` (`Reference/`).

A name declared **only** in the reference region while being cited in a README sentence that also mentions the
kernel is reported. That heuristic is deliberately narrow: it flags the mixed citation, not every mention of a
reference name (the README legitimately discusses the reference region as a debt).

Exit code 0: report only. Whether a reference-only citation is wrong depends on the sentence, and this script
does not parse sentences -- the same limit `audit_tables` ran into.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
KERNEL_LAYERS = ["Core", "Lift", "Lib", "Slots", "Geo"]

DECL = re.compile(r"^[ \t]*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z0-9_']+)", re.M)
IDENT = re.compile(r"`([^`\n]+)`")


def declarations_by_region():
    """name -> set of regions ('kernel' or 'reference')."""
    where = {}
    for root, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d != ".lake"]
        rel = os.path.relpath(root, os.path.join(ZERO, "Lattice"))
        top = rel.split(os.sep)[0]
        region = "kernel" if top in KERNEL_LAYERS else "reference"
        for f in fs:
            if not f.endswith(".lean"):
                continue
            src = io.open(os.path.join(root, f), "rb").read().decode("utf-8", "replace")
            for m in DECL.finditer(src.replace("\r\n", "\n")):
                where.setdefault(m.group(1), set()).add(region)
    return where


def main():
    where = declarations_by_region()
    readme = os.path.join(ZERO, "README.md")
    if not os.path.exists(readme):
        print("README.md not found -- nothing to check")
        return 0
    lines = io.open(readme, encoding="utf-8", errors="replace").read().replace("\r\n", "\n").split("\n")

    kernel_only_missing = []
    reference_only = []
    for i, line in enumerate(lines, 1):
        # A sentence-level heuristic: the line is about the kernel if it names a kernel module or layer.
        about_kernel = bool(re.search(r"`(?:Geo|Core|Lift|Lib)\.[A-Za-z]", line)) or "内核" in line
        for m in IDENT.findall(line):
            name = m.split(".")[-1]
            if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", name):
                continue
            regions = where.get(name)
            if regions is None:
                continue
            # Only names shaped like a theorem or definition: a constructor or type shared by both
            # regions (`collinear`, `Loss`) is cited meaning the kernel's, and reports as noise.
            if "_" not in name:
                continue
            if "kernel" not in regions:
                reference_only.append((i, m, sorted(regions)))
                if about_kernel:
                    kernel_only_missing.append((i, m))

    print("documentation citations of names that exist only in the reference region")
    print("=" * 78)
    if not reference_only:
        print("  none: every cited declaration name is declared in the kernel")
    for ln, name, regions in reference_only:
        print("  README.md:%d  %s  (regions: %s)" % (ln, name, ", ".join(regions)))
    print()
    print("  of those, cited on a line that also talks about the kernel:", len(kernel_only_missing))
    for ln, name in kernel_only_missing:
        print("    README.md:%d  %s" % (ln, name))
    print("=" * 78)
    print("  The kernel builds and is gated; the reference region partly does not build at all.")
    print("  Citing a reference-region theorem where a kernel theorem is meant makes the kernel")
    print("  look stronger than it is -- that is the error this file was written after:")
    print("  a penalty table named `collinear_iff_signed_area_zero` (reference region) as the")
    print("  exactness theorem for a constructor, while the kernel has")
    print("  `collinearPenalty_eq_zero_iff_of_ne`, which additionally requires non-degeneracy.")
    print()
    print("  This script exits 0 regardless: it reports citations, it does not judge sentences.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
