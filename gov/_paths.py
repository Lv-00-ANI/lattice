"""Resolve a path relative to `Lattice/` through the P2 `PATH_MAP`.

## Why this module exists

Rounds 234-241 moved `Lift/` modules to `Runtime/`. **Seven separate artifacts in `gov/` were keyed on
the file path and broke**, each in its own way:

| artifact | symptom |
|:--|:--|
| `PROOF-DEBT` verdict join | verdicts silently dropped, `in_degree` fell back to 0 |
| `check_proof_strength` baseline | same theorem reported as NEW **and** PAID OFF |
| `check_underscore_hypotheses` baseline | NEW + STALE for the same hypothesis |
| `check_chain_deps` table | theorems reported **MISSING** |
| `check_usage_claims` | `FileNotFoundError` on a hardcoded `Lift/...` read |
| `check_none_branches` | same |
| `check_refutation_census` layer list | per-layer rows stopped adding to the total |

**Every fix is the same one line**: map the path at lookup time, never edit the artifact for a move.
This module is that line, in ONE place, so the eighth artifact does not become an eighth copy.

## Contract

`resolve("Lift/Foo.lean")` -> the current location, e.g. `"Runtime/Foo.lean"`.
Paths are relative to `Lattice/`, matching the `file` field in `verdicts_*.jsonl`.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _debt_path_map import PATH_MAP


def resolve(rel):
    """Map a `Lattice/`-relative path to its current location."""
    return PATH_MAP.get(rel, rel)


def resolve_abs(lat, rel):
    """Absolute path for a `Lattice/`-relative path, after mapping."""
    return os.path.join(lat, resolve(rel).replace("/", os.sep))
