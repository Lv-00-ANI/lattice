/-
# Compose Plugin -- Manifest

The COMPOSITION algebra (P3-7). It is the plugin that closes the last three mandatory kinds:
`recovery`, `spatial`, `confluence`.

## Why those three cannot live in any single-carrier plugin

**`recovery`, `spatial` and `confluence` are all properties of how plugins COMBINE:**
- **`spatial`**: independent sub-computations do not interfere;
- **`confluence`**: the order of independent effects does not matter;
- **`recovery`**: an identity/unit exists, so a step can be undone by not composing it.

**A carrier plugin (`Norm`, `GNN`, `Penalty`) is a single map; it has nothing to be confluent WITH.**
**=> the kinds are structurally unavailable until the composition layer is migrated, which is why
they were the last three.**

## The three witnesses

**`spatial`**: `parallel_comm_run` -- running `f ∥ g` on `(a,b)` equals running `g ∥ f` on `(b,a)`
and swapping. **The two orders agree, which is exactly non-interference.**

**`confluence`**: `compose_run_assoc` -- associativity of composition at the level of `run`.
**Re-associating a three-way composition does not change the result, so the order in which a chain
is built is immaterial.**

**`recovery`**: `identity_compose_run` and `compose_identity_right` -- `identity` is a two-sided unit
for composition. **A unit is what makes "undo" meaningful: a step can be cancelled by not composing
it, and the composite is unchanged.** **That is the operational content of temporal recovery, and it
is the honest witness for the kind -- NOT a claim that every plugin has an inverse, which the
project has already REFUTED (`no_extractor_preserves_both`).**

## What this manifest deliberately does NOT claim

**No `exactness`**: composition is not approximating anything.
**No `approximation`**: `compose_strength` and `compose_coverage` are exact equalities, not bounds.
-/

import Lattice.Plugins.Manifest
import Lattice.Compose.Proofs
import Lattice.Compose.Combinators
import Lattice.Compose.ComposeObligation
namespace Lattice.Plugins.Compose

open Lattice.Plugins
open Lattice.Compose

-- **Round 771 (STAGE 3): the ten obligations now CARRY their propositions.**

/-- **`parallel_comm_run`: 并行组合在交换意义下一致。** -/
def parallel_comm_runProp : Prop :=
  ∀ {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂) (a : I₁) (b : I₂),
    (parallel f g).run (a, b) = Option.map Prod.swap ((parallel g f).run (b, a))

/-- **`compose_run_assoc`: 组合的结合律（在 `run` 上）。** -/
def compose_run_assocProp : Prop :=
  ∀ {I A B C : Type} (f : Primitive I A) (g : Primitive A B) (k : Primitive B C)
    (h₁ : ∀ (x : I) (y : A), f.post x y → g.pre y),
    (∀ (y : A) (z : B), g.post y z → k.pre z) →
      ∀ (h₃ : ∀ (x : I) (z : B), (compose f g h₁).post x z → k.pre z) (x : I),
        (compose (compose f g h₁) k h₃).run x
          = (f.run x).bind fun y => (g.run y).bind fun z => k.run z

/-- **`identity_compose_run`: 单位在左侧。** -/
def identity_compose_runProp : Prop :=
  ∀ {I O : Type} (f : Primitive I O) (h : ∀ (x y : I), (identity I).post x y → f.pre y) (x : I),
    (compose (identity I) f h).run x = f.run x

/-- **`compose_identity_right`: 单位在右侧。** -/
def compose_identity_rightProp : Prop :=
  ∀ {I O : Type} (f : Primitive I O)
    (h : ∀ (x : I) (y : O), f.post x y → (identity O).pre y) (x : I),
    (compose f (identity O) h).run x = f.run x

/-- **`compose_sound`: 前条件成立则组合有结果且后条件成立。** -/
def compose_soundProp : Prop :=
  ∀ {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ (x : I) (y : M), f.post x y → g.pre y) (x : I),
    f.pre x → ∃ z, (compose f g h).run x = some z ∧ (compose f g h).post x z

/-- **`compose_strength`: 组合的强度是两段的较小者。** -/
def compose_strengthProp : Prop :=
  ∀ {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ (x : I) (y : M), f.post x y → g.pre y),
    (compose f g h).strength = f.strength.min g.strength

/-- **`compose_coverage`: 组合的覆盖是两段的交集。** -/
def compose_coverageProp : Prop :=
  ∀ {I M O : Type} (f : Primitive I M) (g : Primitive M O)
    (h : ∀ (x : I) (y : M), f.post x y → g.pre y),
    (compose f g h).coverage = f.coverage.inter g.coverage

/-- **`parallel_run`: 并行的 `run` 是两侧结果的配对。** -/
def parallel_runProp : Prop :=
  ∀ {I₁ O₁ I₂ O₂ : Type} (f : Primitive I₁ O₁) (g : Primitive I₂ O₂) (a : I₁) (b : I₂),
    (parallel f g).run (a, b) = (f.run a).bind fun y => Option.map (fun z => (y, z)) (g.run b)

/-- **`parallel_identity_run`: 两个单位的并行是恒等。** -/
def parallel_identity_runProp : Prop :=
  ∀ (I O : Type) (a : I) (b : O), (parallel (identity I) (identity O)).run (a, b) = some (a, b)

/-- **`compose_h_of_pre_true`: 后置条件恒真时义务自动成立。** -/
def compose_h_of_pre_trueProp : Prop :=
  ∀ {I M O : Type} (f : Primitive I M) (g : Primitive M O),
    (∀ y, g.pre y) → ∀ x y, f.post x y → g.pre y

/-- **十条命题就是十条定理的类型。** -/
theorem compose_props_hold :
    parallel_comm_runProp ∧ compose_run_assocProp ∧ identity_compose_runProp
      ∧ compose_identity_rightProp ∧ compose_soundProp ∧ compose_strengthProp
      ∧ compose_coverageProp ∧ parallel_runProp ∧ parallel_identity_runProp
      ∧ compose_h_of_pre_trueProp :=
  ⟨@parallel_comm_run, @compose_run_assoc, @identity_compose_run,
   @compose_identity_right, @compose_sound, @compose_strength,
   @compose_coverage, @parallel_run, parallel_identity_run,
   @compose_h_of_pre_true⟩

/-- **The composition-algebra plugin's manifest.**

Layer `compose`. It requires `core.primitive` (the `Primitive` structure it composes) and offers
`compose.binary` and `compose.parallel`.
-/
def manifest : PluginManifest where
  name := "Compose"
  layer := .compose
  requires := ["core.primitive"]
  provides := ["compose.binary", "compose.parallel"]
  obligations := [
    -- **Round 771: all ten go through `verifiedObligation`, so each CARRIES its proposition.**
    verifiedObligation "parallel_comm" .spatial
      "Lattice/Plugins/Compose/Proofs.lean"
      "parallel_comm_run" parallel_comm_runProp,
    verifiedObligation "compose_assoc" .confluence
      "Lattice/Plugins/Compose/Combinators.lean"
      "compose_run_assoc" compose_run_assocProp,
    verifiedObligation "identity_left_unit" .recovery
      "Lattice/Plugins/Compose/Combinators.lean"
      "identity_compose_run" identity_compose_runProp,
    verifiedObligation "identity_right_unit" .recovery
      "Lattice/Plugins/Compose/Proofs.lean"
      "compose_identity_right" compose_identity_rightProp,
    verifiedObligation "compose_sound" .soundness
      "Lattice/Plugins/Compose/Combinators.lean"
      "compose_sound" compose_soundProp,
    verifiedObligation "compose_strength" .laws
      "Lattice/Plugins/Compose/Combinators.lean"
      "compose_strength" compose_strengthProp,
    verifiedObligation "compose_coverage" .laws
      "Lattice/Plugins/Compose/Combinators.lean"
      "compose_coverage" compose_coverageProp,
    verifiedObligation "parallel_run" .laws
      "Lattice/Plugins/Compose/Proofs.lean"
      "parallel_run" parallel_runProp,
    verifiedObligation "parallel_identity" .laws
      "Lattice/Plugins/Compose/Proofs.lean"
      "parallel_identity_run" parallel_identity_runProp,
    verifiedObligation "compose_h_of_pre_true" .soundness
      "Lattice/Plugins/Compose/ComposeObligation.lean"
      "compose_h_of_pre_true" compose_h_of_pre_trueProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims ten obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 10 := rfl

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

/-- The plugin lives in the `compose` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.compose := rfl

/-- It requires the primitive structure. -/
theorem manifest_requires : manifest.requires = ["core.primitive"] := rfl

/-- It offers binary and parallel composition. -/
theorem manifest_provides : manifest.provides = ["compose.binary", "compose.parallel"] := rfl

/-- **It claims SPATIAL** -- parallel non-interference. -/
theorem manifest_claims_spatial : manifest.claims .spatial = true := rfl

/-- **It claims CONFLUENCE** -- associativity of composition. -/
theorem manifest_claims_confluence : manifest.claims .confluence = true := rfl

/-- **It claims RECOVERY** -- the identity is a two-sided unit. -/
theorem manifest_claims_recovery : manifest.claims .recovery = true := rfl

/-- It claims laws -- strength, coverage and parallel's unit. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- It claims soundness -- composition preserves the postcondition. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- **It does NOT claim exactness**: composition approximates nothing. -/
theorem manifest_no_exactness : manifest.claims .exactness = false := rfl

/-- **It does NOT claim approximation**: `compose_strength` and `compose_coverage` are exact
equalities, not bounds. -/
theorem manifest_no_approximation : manifest.claims .approximation = false := rfl

/-- **It does NOT claim equivariance**: no group acts on composition. -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- **It does NOT claim idempotence**: a composite is not re-applied to fix a point. -/
theorem manifest_no_idempotence : manifest.claims .idempotence = false := rfl

end Lattice.Plugins.Compose
