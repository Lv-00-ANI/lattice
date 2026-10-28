"""The `PATH_MAP`: old module path -> new module path, for PROOF-DEBT's key join.

## Why this is its own module

Round 234 first put `PATH_MAP` inside `gen_proof_debt.py` and had `check_proof_debt_orphans.py` do
`from gen_proof_debt import PATH_MAP`. **That made the checker regenerate `PROOF-DEBT.md` as a side
effect**, because `gen_proof_debt.py` writes the file at module scope. A checker must not write the
artifact it is checking.

This is the same lesson as `_debt_coverage.py` in round 226: **anything a checker imports must be safe to
import.** One module, one job.

## What it is for

`DIRECTORY-DESIGN.md` §2.8 says "`PROOF-DEBT` is regenerated with a `PATH_MAP`". **That mechanism did not
exist** until round 234. Without it, a `git mv` silently orphans every verdict for the moved file: the
inventory join misses, `in_degree` falls back to 0, and the ledger reports a reviewed file as unreviewed
**while the coverage table still claims 100% of the load-bearing set**.

Paths are relative to `Lattice/`, matching the `file` field in `verdicts_*.jsonl`.
"""

#: (old path relative to Lattice/) : (new path relative to Lattice/)
PATH_MAP = {
    # round 234, P2 pilot: the first module moved out of `Lift/`
    "Lift/ProgramAST.lean": "Runtime/ProgramAST.lean",
}
