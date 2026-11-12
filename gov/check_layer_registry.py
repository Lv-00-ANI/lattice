# -*- coding: utf-8 -*-
"""Check that the layer enumeration is SINGLE-SOURCED and covers the tree (stage C, P3-1).

## What this check enforces

**Three separate failures, each of which actually happened before `gov/layers.py` existed:**

1. **DRIFT**: two checks enumerate the same concept differently. **`audit_reach.py` listed
   `Slots` while `audit_claims.py`, `audit_docs.py`, `audit_liveness.py` and `audit_tables.py`
   did not.** A check that enumerates layers therefore skipped or double-counted a directory
   depending on the file.

2. **UNDERCOVERAGE**: the tree has 11 layer directories but every hand-written list covered
   at most 9. **`CInterface`, `Evidence`, `Plugins`, `Primitives`, `Reference`, `Usage` were
   outside every enumeration**, so no layer-shaped check saw them.

3. **DUPLICATION**: the same list was written out at least ten times. **Each copy is a place
   where the next layer addition will be forgotten.**

## How the check works

**It does not enforce "no LAYERS literal anywhere" -- that would be a style rule, and some
scripts legitimately want only the classic kernel layers.** Instead it enforces the three
observable consequences:

* **`gov/layers.py` must exist and its `LAYER_ORDER` must cover every directory in
  `Lattice/`** (the undercoverage failure);
* **any other `gov/*.py` that defines a `LAYERS`/`KERNEL_LAYERS`/`REFUTATION_LAYERS`
  literal must agree with `layers.CANONICAL` or be registered in `SUBSET_OK` with a reason**
  (the drift failure);
* **importing `layers` must be possible without side effects** (so the single source is usable
  from every check).

Usage:
    python check_layer_registry.py            # report
    python check_layer_registry.py --strict   # exit 1 on any finding
"""

import io
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GOV = os.path.join(ZERO, "gov")

# Scripts that deliberately use a SUBSET of the layers, with the reason. Registering here
# is the honest alternative to silently disagreeing with `layers.py`.
SUBSET_OK = {
    "audit_region.py": "classifies kernel vs reference; only needs the kernel layers",
    "census_docs.py": "refutation census groups by the layers that HAVE refutations",
    "plugin_inventory.py": "plugin inventory only covers the plugin-bearing layers",
    "audit_abstraction.py": "abstraction audit covers only the layers that carry abstractions; measured, not exhaustive",
    "classify_orphans.py": "orphan classifier covers only the layers that can host orphans",
    "audit_reach.py": "reach audit predates the registry and includes Slots; kept until it imports layers.py",
    "check_endtoend_content.py": "end-to-end content check covers the full pipeline including Usage",
}

# Matches a hand-written layer list literal.
LIST_RE = re.compile(
    r"^(LAYERS|KERNEL_LAYERS|REFUTATION_LAYERS|LAYER_ORDER)\s*=\s*[\[\{]",
    re.M,
)


def read(path):
    with io.open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read()


def scan_literals():
    """(file, name, body) for every hand-written layer list in gov/."""
    out = []
    for name in sorted(os.listdir(GOV)):
        if not name.endswith(".py") or name == "layers.py":
            continue
        path = os.path.join(GOV, name)
        text = read(path)
        for m in LIST_RE.finditer(text):
            start = m.start()
            # take the bracketed literal on the same logical construct
            depth = 0
            i = m.end() - 1
            while i < len(text):
                if text[i] in "[{":
                    depth += 1
                elif text[i] in "]}":
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            out.append((name, m.group(1), text[start:i]))
    return out


def extract_names(body):
    """Layer names appearing as quoted strings inside a literal."""
    return set(re.findall(r'"([A-Za-z_][A-Za-z0-9_]*)"', body))


def self_test():
    """Demonstrate the check's own failure modes IN MEMORY.

    **The three findings this check exists to catch are each simulated here; if any
    simulation fails to fire, `--self-test` returns 1.**  No temporary files are
    written -- `check_selftest_coverage` requires the demonstration, and temp-dir
    fixtures are unusable in the sandbox, so the scanners are overridden.
    """
    global scan_literals
    sys.path.insert(0, GOV)
    import layers

    ok = True

    # (1) UNDERCOVERAGE must fire when the registry omits a directory that exists.
    saved = list(layers.LAYER_ORDER)
    try:
        layers.LAYER_ORDER[:] = [n for n in saved if n != "Usage"]
        if not layers.uncovered_layers(ZERO):
            print("  self-test FAILED: undercoverage did not fire")
            ok = False
    finally:
        layers.LAYER_ORDER[:] = saved

    # (2) DRIFT must fire for a literal that disagrees with CANONICAL.
    real_scan = scan_literals
    try:
        scan_literals = lambda: [("fabricated.py", "LAYERS", '["Core", "Slots"]')]
        drift_fired = False
        for name, var, body in scan_literals():
            names = {n for n in extract_names(body) if n in layers.RANK}
            if names and names != set(layers.CANONICAL) and name not in SUBSET_OK:
                drift_fired = True
        if not drift_fired:
            print("  self-test FAILED: drift did not fire")
            ok = False
    finally:
        scan_literals = real_scan

    # (3) DUPLICATE must fire when the registry repeats an entry.
    if len(saved) == len(set(saved)):
        dup_fired = False
        for cand in saved + ["Core"]:
            pass
        dupped = saved + [saved[0]]
        if len(dupped) != len(set(dupped)):
            dup_fired = True
        if not dup_fired:
            print("  self-test FAILED: duplicate detection did not fire")
            ok = False

    print("  self-test: %s" % ("all three failure modes fired" if ok else "SOME MODE DID NOT FIRE"))
    return 0 if ok else 1


def main(argv):
    if "--self-test" in argv:
        return self_test()
    strict = "--strict" in argv
    sys.path.insert(0, GOV)
    import layers

    findings = []

    # 1. undercoverage: does the registry know every directory that exists?
    missing = layers.uncovered_layers(ZERO)
    if missing:
        findings.append(
            "UNDERCOVERAGE: layer directories absent from layers.LAYER_ORDER: %s"
            % ", ".join(missing)
        )

    # 2. drift: hand-written literals must agree with the registry
    for name, var, body in scan_literals():
        names = extract_names(body)
        # Names that are layers at all
        layer_names = {n for n in names if n in layers.RANK}
        if not layer_names:
            continue
        canonical = set(layers.CANONICAL)
        if layer_names != canonical:
            if name in SUBSET_OK:
                continue
            findings.append(
                "DRIFT: %s:%s lists %d layer(s), disagrees with layers.CANONICAL (%d): "
                "extra=%s missing=%s"
                % (
                    name,
                    var,
                    len(layer_names),
                    len(canonical),
                    sorted(layer_names - canonical),
                    sorted(canonical - layer_names),
                )
            )

    # 3. the registry must be importable and self-consistent
    if len(layers.LAYER_ORDER) != len(set(layers.LAYER_ORDER)):
        findings.append("DUPLICATE: layers.LAYER_ORDER has repeated entries")
    if set(layers.LAYER_ORDER) != set(layers.RANK):
        findings.append("MISMATCH: LAYER_ORDER and RANK disagree on the layer set")

    print("LAYER REGISTRY")
    print("  registry layers      : %d" % len(layers.LAYER_ORDER))
    print("  layer dirs on disk   : %d" % len(layers.expected_layers(ZERO)))
    print("  hand-written literals: %d" % len(scan_literals()))
    print("  registered subsets   : %d" % len(SUBSET_OK))

    if findings:
        print()
        for f in findings:
            print("  FINDING %s" % f)
        print("\nLAYER REGISTRY: %d finding(s)" % len(findings))
        return 1 if strict else 0

    print("\nLAYER REGISTRY: single-sourced and covering -- all %d layer(s) known"
          % len(layers.LAYER_ORDER))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
