/-
# Target Plugins -- the nine targets T0 … T8

This is the layer that makes `ProofComplete` mean what the plan intends.

## What it contains

**`Expressible.lean`** -- **`ExpressibleSpec`, the subtype T0 was missing.** **A spec CARRIES the proof
that every member is expressible, so a function taking it cannot be handed an inexpressible one.**

**`Statements.lean`** -- **the nine targets as `Prop`s, with a proved/open ledger.**
-/

import Lattice.Plugins.Targets.Expressible
import Lattice.Plugins.Targets.Statements
