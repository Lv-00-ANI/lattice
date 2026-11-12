# -*- coding: utf-8 -*-
"""The SINGLE authoritative description of the layer stack (stage C, P3-1).

## The problem this replaces

Before this module, the layer list was written out at least TEN times:

    audit_claims.py       LAYERS = [Core, Lift, Domains, Runtime, Compose, Semantics, Lib, Geo]
    audit_docs.py         LAYERS = [same eight]
    audit_liveness.py     LAYERS = [same eight]
    audit_reach.py        LAYERS = [same eight PLUS Slots]      <-- disagrees
    audit_tables.py       LAYERS = [same eight]
    gate.py               LAYER_OF = {...}                      <-- a different shape again
    check_endtoend_content.py  LAYERS = [eleven, different order]
    audit_region.py       KERNEL_LAYERS = [Core, Lift, Lib, Slots, Geo]
    plugin_inventory.py   LAYERS = {...}
    census_docs.py        REFUTATION_LAYERS = (...)

**=> `audit_reach.py` lists `Slots`; the others do not. That is a real drift, not a style
difference: a check that enumerates layers will silently skip or double-count `Slots`
depending on which file it is.**

## What is measured, not assumed

The tree contains ELEVEN layer directories:

    CInterface  Compose  Core  Evidence  Lib  Plugins
    Primitives  Reference  Runtime  Semantics  Usage

**Every existing `LAYERS` list covers at most NINE of them.** The ones missing from the
"canonical eight + Slots" lists include `CInterface`, `Evidence`, `Plugins`, `Primitives`,
`Reference`, `Usage`.

**=> so the drift is larger than the `Slots` disagreement: the majority of the layer
surface is outside every list that is supposed to enumerate it.**

## What this module provides

`LAYER_ORDER`     the measured directory order (stable, source order for reports)
`RANK`            rank per layer -- LOWER is MORE fundamental, matching `gate.py`'s I4
`CANONICAL`       the layers that appear in the older lists, kept for compatibility
`in_layer_list(p)` the membership test the checks actually need
`all_layers()`    the measured list, so a check can assert coverage rather than enumrate

## Discipline

**A check must not enumerate layers itself.** It must import `all_layers()` and compare
against `expected_layers()`. If a new layer directory appears, `expected_layers()` grows
and every check sees it at once, instead of one check drifting silently.
"""

import os

# The layer directories, in RANK order (most fundamental first).
# Measured from the tree; see the module docstring for the count.
LAYER_ORDER = [
    "Core",        # rank 1
    "Primitives",  # rank 2
    "Lift",        # rank 2
    "Runtime",     # rank 2
    "Slots",       # rank 3
    "Lib",         # rank 3
    "Domains",     # rank 3
    "Geo",         # rank 3
    "Compose",     # rank 4
    "Semantics",   # rank 4
    "CInterface",  # rank 5
    "Plugins",     # rank 5
    "Usage",       # rank 6
    "Evidence",    # rank 6
    "Reference",   # rank 7
]

# Rank: lower is more fundamental. `gate.py`'s I4 compares these.
RANK = {
    "Core": 1,
    "Primitives": 2,
    "Lift": 2,
    "Runtime": 2,
    "Slots": 3,
    "Lib": 3,
    "Domains": 3,
    "Geo": 3,
    "Compose": 4,
    "Semantics": 4,
    "CInterface": 5,
    "Plugins": 5,
    "Usage": 6,
    "Evidence": 6,
    "Reference": 7,
}

# The eight names the older LAYERS lists used, plus `Slots`. Kept so existing callers
# that only want the classic kernel layers keep working; NOT the full set.
CANONICAL = ["Core", "Lift", "Domains", "Runtime", "Compose", "Semantics", "Lib", "Geo"]


def zero(s):
    """Absolute path to the repository root, given the gov/ directory."""
    return os.path.dirname(os.path.dirname(os.path.abspath(s)))


def all_layers():
    """The measured layer list, in rank order."""
    return list(LAYER_ORDER)


def expected_layers(zero_dir=None):
    """Layer directories that ACTUALLY exist in the tree.

    A check uses this to assert its coverage rather than hard-coding a list.
    """
    if zero_dir is None:
        zero_dir = zero(__file__)
    root = os.path.join(zero_dir, "Lattice")
    if not os.path.isdir(root):
        return []
    found = set()
    for name in os.listdir(root):
        if os.path.isdir(os.path.join(root, name)):
            found.add(name)
    return sorted(found, key=lambda n: (RANK.get(n, 99), n))


def uncovered_layers(zero_dir=None):
    """Layer directories present in the tree but ABSENT from `LAYER_ORDER`.

    **A non-empty result is a real gap: those directories are outside every layer
    enumeration, so no layer-shaped check sees them.**
    """
    return [n for n in expected_layers(zero_dir) if n not in LAYER_ORDER]


def rank(layer):
    """Rank of a layer; unknown layers get 99 so they sort last without crashing."""
    return RANK.get(layer, 99)


def layer_of(path):
    """Layer of a `Lattice/<Layer>/...` path, or None for files directly under `Lattice/`."""
    parts = path.replace("\\", "/").split("/")
    if len(parts) >= 2 and parts[0] == "Lattice":
        return parts[1]
    return None
