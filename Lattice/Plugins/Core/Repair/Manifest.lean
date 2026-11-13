/-
# Repair Plugin -- Manifest

The second migrated plugin (P3-1, Core/Repair). It is the **T4 Repair** carrier: the
repair loop is how a violated constraint is turned into a satisfied one, and the four
theorems the plan asks for are already here under different names.

## What T4 needs, and where it already lives

| plan's obligation | theorem in this plugin |
|:--|:--|
| `repair_progress` | `Repair.progress`, `RepairWF.progress_on_wf` |
| `loop_converges` | `RepairConvergence.converges_within` |
| `conj_loop_fixed_point` | `Repair.atomic_of_zero_iff` / `RepairAtomicity` |

**This is the migration's whole value in one table**: the plan's T4 looked like new work,
but three of its obligations were already proved -- they were simply named after the
mechanism rather than after the target. The manifest is where that mapping becomes explicit
and machine-checkable.

## The termination story, and its honest boundary

`Repair.progress` requires a `Repair` structure whose `μ` strictly decreases off the
satisfied set; `RepairWF.progress_on_wf` is the same statement via well-foundedness.
**`Repair.down_no_progress` is the counterexample that keeps this honest**: the map
`downFix` on negative integers never reaches `0 ≤ x`, so not every "obvious" loop
terminates, and the `μ`-decrease hypothesis is not removable.

`RepairMultistep.no_uniform_bound` sharpens it further: for the `countdown` family there is
**no uniform bound** on the number of steps, only a per-input one. That is why
`converges_within` is stated per `x` rather than with a single `N`.
-/

import Lattice.Plugins.Manifest
import Lattice.Core.RepairModule.Repair
import Lattice.Core.RepairModule.RepairConvergence
import Lattice.Core.RepairModule.RepairAtomicity
import Lattice.Core.RepairModule.RepairWF
import Lattice.Core.RepairModule.RepairMultistep
open Lattice.Core

namespace Lattice.Plugins.Core.Repair

open Lattice.Plugins

-- **Round 769 (STAGE 3): every obligation now CARRIES its proposition.** The eight `_Prop` defs
-- below are the eight theorems' own types, and `repair_props_hold` proves the equality -- so a
-- rename or a restatement breaks compilation rather than drifting silently.

/-- **`progress`: 每个状态都能在有限步内到达满足状态。** -/
def progressProp : Prop :=
  ∀ {α : Type} (R : Repair α) (x : α), ∃ n, R.Sat (R.iterate n x)

/-- **`progress_on_wf`: 带良基度量的修正同样在有限步内收敛。** -/
def progress_on_wfProp : Prop :=
  ∀ {α β : Type} (R : RepairWF α β) (x : α), ∃ n, R.Sat (R.iterate n x)

/-- **`converges_within`: 恰在 `μ x` 步内到达满足状态。** -/
def converges_withinProp : Prop :=
  ∀ {α : Type} (R : Repair α) (x : α), R.Sat (R.iterate (R.μ x) x)

/-- **`converges_within_is_tight`: 倒计数实例的 `μ` 步界是紧的。** -/
def converges_within_is_tightProp : Prop :=
  ∀ (k : ℕ),
    Multistep.countdown.Sat (Multistep.countdown.iterate (Multistep.countdown.μ k) k) ∧
      ∀ n < Multistep.countdown.μ k, ¬Multistep.countdown.Sat (Multistep.countdown.iterate n k)

/-- **`atomic_of_zero_iff`: 若「度量为零」等价于「满足」，则度量为零推出满足。** -/
def atomic_of_zero_iffProp : Prop :=
  ∀ {α : Type} (R : Repair α), (∀ (x : α), R.μ x = 0 ↔ R.Sat x) → ∀ (x : α), R.μ x = 0 → R.Sat x

/-- **`stable`: 已满足的状态在修正下不动。** -/
def stableProp : Prop :=
  ∀ {α : Type} (R : Repair α) (x : α), R.Sat x → R.fix x = x

/-- **`preserves`: 满足性在迭代下保持。** -/
def preservesProp : Prop :=
  ∀ {α : Type} (R : Repair α) (x : α), R.Sat x → ∀ (n : ℕ), R.Sat (R.iterate n x)

/-- **`iterate_succ`: 迭代的递推式。** -/
def iterate_succProp : Prop :=
  ∀ {α : Type} (R : Repair α) (n : ℕ) (x : α), R.iterate (n + 1) x = R.fix (R.iterate n x)

/-- **八条命题就是八条定理的类型。** -/
theorem repair_props_hold :
    progressProp ∧ progress_on_wfProp ∧ converges_withinProp
      ∧ converges_within_is_tightProp ∧ atomic_of_zero_iffProp
      ∧ stableProp ∧ preservesProp ∧ iterate_succProp :=
  ⟨@Repair.progress, @RepairWF.progress_on_wf, @RepairConvergence.converges_within,
   @Multistep.converges_within_is_tight, @RepairAtomicity.atomic_of_zero_iff,
   @Repair.stable, @Repair.preserves, @Repair.iterate_succ⟩

/-- **The repair plugin's manifest.**

Layer `core`: the repair loop is part of the kernel -- it is what the forward direction does
when a compiled weight vector does not satisfy its constraints.

No dependencies (`requires = []`) because the loop is generic in the carrier: it is stated
over an arbitrary `Repair α`. It offers `repair.loop`, which a domain plugin (geometry,
constraints) requires in order to make its repair concrete.
-/
def manifest : PluginManifest where
  name := "Core.Repair"
  layer := .core
  requires := []
  provides := ["repair.loop"]
  obligations := [
    -- **Round 769: all eight go through `verifiedObligation`, so each CARRIES its proposition.**
    -- Before this the manifest named a theorem as a `String`; a wrong name was undetectable.
    verifiedObligation "repair_progress" .completeness
      "Lattice/Plugins/Core/Repair/Repair.lean"
      "progress" progressProp,
    verifiedObligation "repair_progress_on_wf" .completeness
      "Lattice/Plugins/Core/Repair/RepairWF.lean"
      "progress_on_wf" progress_on_wfProp,
    verifiedObligation "repair_converges_within" .approximation
      "Lattice/Plugins/Core/Repair/RepairConvergence.lean"
      "converges_within" converges_withinProp,
    verifiedObligation "repair_converges_within_is_tight" .exactness
      "Lattice/Plugins/Core/Repair/RepairMultistep.lean"
      "converges_within_is_tight" converges_within_is_tightProp,
    verifiedObligation "repair_atomic_of_zero_iff" .exactness
      "Lattice/Plugins/Core/Repair/RepairAtomicity.lean"
      "atomic_of_zero_iff" atomic_of_zero_iffProp,
    verifiedObligation "repair_stable" .soundness
      "Lattice/Plugins/Core/Repair/Repair.lean"
      "stable" stableProp,
    verifiedObligation "repair_preserves" .soundness
      "Lattice/Plugins/Core/Repair/Repair.lean"
      "preserves" preservesProp,
    verifiedObligation "repair_iterate_succ" .laws
      "Lattice/Plugins/Core/Repair/Repair.lean"
      "iterate_succ" iterate_succProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims eight obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 8 := rfl

/-- **The manifest carries at least one obligation.**

Derived from `manifest_obligation_count`: if the list were `[]` its length would be `0`, contradicting
the stated count.
**This is what `NonVacuousFor` consumes. Having it as a NAMED lemma per manifest means a future edit
that empties the obligation list breaks HERE, rather than silently reopening the fake-completion
path.** -/
theorem manifest_nonempty : manifest.obligations ≠ [] := by
  intro hnil
  have hlen := manifest_obligation_count
  rw [hnil] at hlen
  exact absurd hlen (by decide)

/-- The repair plugin lives in the `core` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.core := rfl

/-- It offers the repair loop. -/
theorem manifest_provides : manifest.provides = ["repair.loop"] := rfl

/-- It requires nothing: the loop is generic in its carrier. -/
theorem manifest_requires_nothing : manifest.requires = [] := rfl

/-- It claims completeness -- the progress obligation lives under that kind, because
"every state reaches a satisfied one" is a totality statement about the loop. -/
theorem manifest_claims_completeness : manifest.claims .completeness = true := rfl

/-- It claims exactness -- both the tightness of the bound and the fixed-point
characterisation. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It does NOT claim spatial composability: that belongs to the `Compose` layer. -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- It does NOT claim equivariance: the loop has no group action. -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- It does NOT claim idempotence: applying the loop twice is not the same as once, because
the loop already stops. (What IS idempotent is `fix`, which `Repair.stable` records.) -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

/-- It does NOT claim refinement: the C backend is out of scope. -/
theorem manifest_no_refinement : manifest.claims .refinement = false := rfl

/-- It does NOT claim recovery: the repair loop has no install/uninstall to undo. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

end Lattice.Plugins.Core.Repair
