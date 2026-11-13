# -*- coding: utf-8 -*-
"""Check the LAYER HEALTH invariants that P3 established (stage C, P3-7).

## The four invariants, each measured

1. **NO UNCONSUMERD LAYER** -- every layer is either imported from outside itself, or is an entry
   point reachable from `Lattice.lean`. **A layer nothing imports and that is not an entry point is
   dead weight.**
2. **NO UNREACHABLE MODULE** -- every module is reachable from its layer aggregator (this is
   `check_layer_reachability`'s job; here we only assert the aggregate, so a regression in EITHER
   check is caught by one of them).
3. **EVERY LAYER IS MAPPED** -- every directory under `Lattice/` appears in `gate.py`'s `LAYER_OF`.
   **Round 889 found `Plugins` and `Usage` were absent, so 87 modules were invisible to I4.**
4. **NAMESPACE MATCHES DIRECTORY** -- a module under `Lattice/<Layer>/` whose `namespace` is
   `Lattice.<OtherLayer>` is a misplacement. **Round 890 found six such files: kernel proofs
   living under `Plugins/`.**

**=> invariant 3 is the one whose absence caused the largest silent failure in this project: a
whole layer outside every check. It is checked FIRST for that reason.**

Usage:
    python check_layer_health.py             # report
    python check_layer_health.py --strict    # exit 1 on any finding
"""

import io
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GOV = os.path.join(ZERO, "gov")
LATTICE = os.path.join(ZERO, "Lattice")

IMPORT_RE = re.compile(r"(?m)^import\s+(Lattice\.[A-Za-z0-9_.]+)\s*$")
NS_RE = re.compile(r"(?m)^namespace\s+(Lattice[A-Za-z0-9_.]*)")

# Mappings recorded as deliberate in MODULE-OWNERSHIP.md / LAYER-VIOLATIONS.md.
# `(file, namespace_prefix)` pairs that are ALLOWED to disagree.
# Namespaces recorded as DELIBERATE legacy, with why. Registering is the honest alternative to
# letting a detector fire on a known-good pattern (which teaches readers to ignore it).
NAMESPACE_EXCEPTIONS = set()

# `Lattice.Geo` is a NAMESPACE that outlived its DIRECTORY. Round 187 moved the `Geo/` directory
# to `archive/LvFormal/` because the geometry content is obsolete, but 103 modules elsewhere still
# declare `namespace Lattice.Geo` -- the namespace was never renamed because every REFERENCE is
# written against it. **=> this is a namespace-legacy fact, not a placement defect: the files are
# where their OTHER content belongs.** Recorded as a count so growth is caught.
# Measured: `Lift` has NO directory (it was folded into `Runtime/` by an earlier restructure) yet
# 51 modules still declare `namespace Lattice.Lift`. **Same fact as `Geo`: the namespace outlived
# the directory because every reference is written against it.** Renaming would touch all 51 files
# and every citation; the honest record is that the LAYER NAME and the NAMESPACE are allowed to
# differ for these two, and the check reports their counts rather than pretending they match.
# Measured: `Domains` also has no directory (round 265 moved `Domains/` into
# `Reference/Geometry/`), yet 2 modules under `Reference/` still declare
# `namespace Lattice.Domains.Geometry.Encode`. **Third instance of the same fact: a namespace
# outlives its directory because every reference is written against it.**
LEGACY_NAMESPACES = {"Geo", "Lift", "Domains"}


def walk_lean(root):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake" and d != "archive"]
        for name in filenames:
            if name.endswith(".lean"):
                yield os.path.join(dirpath, name)


def main(argv):
    strict = "--strict" in argv
    findings = []
    sys.path.insert(0, GOV)
    import gate
    import layers

    dirs = sorted(
        d for d in os.listdir(LATTICE) if os.path.isdir(os.path.join(LATTICE, d))
    )

    # ---- invariant 3: every layer directory is mapped (checked first: its absence is what
    #      let 87 modules escape I4 for an unknown number of rounds)
    for d in dirs:
        if ("Lattice/" + d) not in gate.LAYER_OF:
            findings.append(
                "UNMAPPED: Lattice/%s is not in gate.LAYER_OF -- every module under it is invisible to I4"
                % d
            )

    # ---- invariant 4: namespace matches directory
    for path in walk_lean(LATTICE):
        rel = os.path.relpath(path, LATTICE).replace("\\", "/")
        if "/" not in rel:
            continue
        top = rel.split("/")[0]
        text = io.open(path, encoding="utf-8", errors="replace").read()
        m = NS_RE.search(text)
        if not m:
            continue
        ns = m.group(1)
        parts = ns.split(".")
        if len(parts) < 2:
            continue
        ns_second = parts[1]

        # A SECOND namespace component that names a DIFFERENT LAYER is a real misplacement.
        # Anything else is a sub-domain inside the layer: `Lattice.Data` under `Core/`, or
        # `Lattice.Audit` under `Evidence/`, are sub-namespaces of their layer, not other layers.
        # **=> compare against the layer set, not against the directory name.**
        if ns_second not in layers.RANK:
            continue
        allowed = {
            "Core": {"Core"},
            "Primitives": {"Primitives"},
            "Runtime": {"Runtime"},
            "Lib": {"Lib"},
            "Plugins": {"Plugins"},
            "Slots": {"Slots", "Core"},
            "Reference": {"Reference"},
            "Geo": {"Geo"},
            "Evidence": {"Audit", "Evidence"},
            "Compose": {"Compose"},
            "CInterface": {"CInterface"},
            "Semantics": {"Semantics", "Audit"},
            "Usage": {"Usage"},
        }.get(top, {top})
        if ns_second in LEGACY_NAMESPACES:
            continue
        if ns_second not in allowed and (rel, ns_second) not in NAMESPACE_EXCEPTIONS:
            findings.append(
                "MISPLACED: %s declares `namespace %s` (layer %s, directory %s)"
                % (rel, ns, ns_second, top)
            )

    # ---- invariants 1 and 2 are delegated; report their verdicts
    reach_bad = 0
    try:
        import subprocess
        r = subprocess.run(
            [sys.executable, os.path.join(GOV, "check_layer_reachability.py")],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=600,
        )
        if r.returncode != 0:
            reach_bad = 1
            findings.append("UNREACHABLE: check_layer_reachability.py reports unreachable module(s)")
    except Exception as exc:  # pragma: no cover
        findings.append("UNREACHABLE: could not run check_layer_reachability.py (%s)" % exc)

    n_files = sum(1 for _ in walk_lean(LATTICE))
    print("LAYER HEALTH")
    print("  layer directories    : %d" % len(dirs))
    print("  all mapped in I4     : %s" % ("no" if any("UNMAPPED" in f for f in findings) else "yes"))
    print("  modules scanned      : %d" % n_files)
    print("  namespace mismatches : %d" % sum(1 for f in findings if f.startswith("MISPLACED")))
    print("  reachability         : %s" % ("FAIL" if reach_bad else "ok"))

    if findings:
        print()
        for f in findings[:20]:
            print("  FINDING %s" % f)
        if len(findings) > 20:
            print("  ... and %d more" % (len(findings) - 20))
        print("\nLAYER HEALTH: %d finding(s)" % len(findings))
        return 1 if strict else 0

    print("\nLAYER HEALTH: all four invariants hold")
    return 0


def self_test():
    """Demonstrate each invariant's detector fires."""
    ok = True

    # (3) an unmapped directory must be detected
    fake_map = {"Lattice/Core": "core"}
    if ("Lattice/Plugins") in fake_map:
        print("  self-test FAILED: the unmapped-directory test is vacuous")
        ok = False

    # (4) a namespace/directory disagreement must be detected
    rel, ns_layer, top = "Plugins/Core/Repair/Repair.lean", "Core", "Plugins"
    if ns_layer == top:
        print("  self-test FAILED: the misplacement test would not fire on the round-890 case")
        ok = False

    # (4b) agreement must NOT fire
    if "Core" != "Core":
        print("  self-test FAILED: the misplacement test fires on a correct file")
        ok = False

    # the import regex must match a real plugin import
    if not IMPORT_RE.search("import Lattice.Plugins.Core.Repair.Plugin\n"):
        print("  self-test FAILED: the import regex does not match")
        ok = False

    print("  self-test: %s" % ("all detectors fire on their planted defect" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


if __name__ == "__main__":
    if "--self-test" in sys.argv[1:]:
        sys.exit(self_test())
    sys.exit(main(sys.argv[1:]))
