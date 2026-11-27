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


# **W0-2 (round 1181): this table is DERIVED, not stated.** It used to carry its own copy and call itself
# "SINGLE AUTHORITATIVE" while `gate.py`'s I4 -- the code that actually enforces layering -- read a different one.
# Measured, the two disagreed on EIGHT of fourteen zones:
#
#     Semantics 5 vs 4   Reference 4 vs 7   Plugins 3 vs 5   Usage 7 vs 6
#     Evidence 5 vs 6    Compose 6 vs 4     CInterface 6 vs 5   Slots 1 vs 3
#
# Two tables that both claim authority is the same defect as two values for one count in the docs. Now there is one
# table (`gate.RANK`), this module maps its zone names to the namespace names the older lists used, and
# `check_layer_registry.py` asserts the two agree so they cannot drift apart again.
import gate as _gate  # the authority

#: gate zone -> the namespace second component(s) it covers. `audit` covers two: `LAYER_OF` maps
#: `Lattice/Semantics` to `audit`, so a namespace called `Semantics` sits at the audit rank.
_ZONE_NAMES = {
    "core": ["Core"], "slots": ["Slots"], "runtime": ["Runtime"], "primitives": ["Primitives"],
    "lib": ["Lib"], "plugins": ["Plugins"], "usage": ["Usage"], "cinterface": ["CInterface"],
    "audit": ["Audit", "Semantics"], "evidence": ["Evidence"], "compose": ["Compose"],
    "reference": ["Reference"],
}

#: Rank: lower is more fundamental. DERIVED from `gate.RANK`; do not edit here, edit there.
RANK = {}
for _zone, _names in _ZONE_NAMES.items():
    for _n in _names:
        RANK[_n] = _gate.RANK[_zone]

# The layer directories, in RANK order (most fundamental first).
# Measured from the tree; see the module docstring for the count.
#: **W0-2: derived from RANK, not remembered.** The literal named `Lift`, which does not exist, and `check_layer_registry`
#: compared its SET against `RANK`'s -- so the two disagreed by construction. Ordered by rank (lower = more
#: fundamental), tie-broken by name so the order is stable; `top` is excluded because it is the fallthrough, not a layer.
LAYER_ORDER = [n for n, _ in sorted(RANK.items(), key=lambda kv: (kv[1], kv[0])) if n != "top"]

#: **W0-2: the layer set is DERIVED from the tree, not remembered.** The old literal named `Lift`, `Domains` and
#: `Geo`, three directories that do not exist (measured: `Lattice/` holds 11 subdirectories, and `Slots` is a file at
#: `Lattice/Slots.lean`, which is why it is appended). A remembered list of layers is exactly the kind of value that
#: goes stale without anything noticing -- `check_layer_registry` compares every hand-written list against this.
def _layer_dirs():
    import os as _os
    here = _os.path.dirname(_os.path.abspath(__file__))
    root = _os.path.join(_os.path.dirname(here), "Lattice")
    out = sorted(d for d in _os.listdir(root) if _os.path.isdir(_os.path.join(root, d)))
    if _os.path.exists(_os.path.join(root, "Slots.lean")):
        out.append("Slots")
    return out


CANONICAL = _layer_dirs()


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
