/-
# Target Plugins -- the nine targets T0 … T8

This is the layer that makes `ProofComplete` mean what the plan intends.

## The problem it solves

`ProofComplete` was `:= PluginRegistryComplete`, and after `Compose` closed the last mandatory kind
that became PROVABLE while 33 of 41 plugins were unmigrated.

**A completion predicate that becomes true before the work is done is worse than no predicate: it
lets a reader stop.**

## What this layer adds

**`Statements.lean` names the nine targets and records which are proved (four) and which are open
(five).**
**The registry's `ProofComplete` now conjoins that ledger with the plugin census, so it cannot be
reached while either is incomplete.**
-/

import Lattice.Plugins.Targets.Statements
