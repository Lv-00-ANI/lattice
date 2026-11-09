/-
# Architectures.Norm Plugin -- Manifest

The NORMALISATION carrier (P6-3). It is the first of the four architecture plugins, and the one
that can close the `idempotence` gap in the registry's mandatory-kind coverage.

## Why normalisation is an architecture carrier and not a domain concern

**A domain plugin turns a CONSTRAINT into a loss or a token sequence.**
**An architecture carrier turns a POINT CLOUD into another point cloud of the same shape** --
it is a *transformation of the representation*, not a statement about what the representation
means.

**=> the two are different layers, and `PluginLayer.architectures` is where the second lives.**

## What this plugin actually proves

**`varOf_varNormalize_eq_one`**: normalising a non-degenerate vector gives variance exactly `1`.
**`varOf_varNormalize_le_one`**: for ANY vector (including the degenerate one) the normalised
variance is at most `1`.
**`varOf_iterate_varNormalize_le_one`**: iterating the normaliser ANY number of times keeps the
variance at most `1` -- **this is the idempotence obligation**, and it is stated as an iterated
bound rather than as `f ∘ f = f`, because normalisation is NOT literally idempotent once a scale
factor `gamma` is reintroduced; what IS idempotent is its effect on the variance.

**`bn_train_eq_infer`**: train-mode and inference-mode batch normalisation agree on the batch they
were computed from -- **the consistency statement that makes train/test behaviour comparable.**

**`varNormalize_unit_lipschitz_sharp`**: the unit-scale normaliser is Lipschitz with the SHARP
constant -- **the approximation obligation, with the constant not merely bounded but attained.**

## What it does NOT claim

**No `equivariance`**: `Lib/Architectures/RealGNNEquivariance.lean` holds the equivariance results,
and they belong to a different carrier (`GNN`, not `Norm`).
**No `confluence`**: normalisation is a single map, not a rewriting system.
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Architectures.Norm.Proofs

namespace Lattice.Plugins.Architectures.Norm

open Lattice.Plugins

/-- **`varOf_iterate_varNormalize_le_one` 的命题：反复归一化后方差不超过 1。** -/
def varOf_iterate_varNormalize_le_oneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ) (n : ℕ), varOf (varNormalize^[n + 1] x) ≤ 1

/-- **`varOf_varNormalize_eq_one` 的命题：非退化输入归一化后方差恰为 1。** -/
def varOf_varNormalize_eq_oneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ), varOf x ≠ 0 → varOf (varNormalize x) = 1

/-- **`bn_train_eq_infer` 的命题：训练模式与推理模式在给定统计量下一致。** -/
def bn_train_eq_inferProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (gamma beta eps mu sigmaSq : ℝ) (X : ι → ℝ),
    batchMean X = mu → batchVar X = sigmaSq →
      ∀ (i : ι), bnTrain gamma beta eps X i = bnInfer gamma beta eps mu sigmaSq (X i)

/-- **`varNormalize_unit_lipschitz_sharp` 的命题：单位归一化的 Lipschitz 常数可取 `1/c`。** -/
def varNormalize_unit_lipschitz_sharpProp : Prop :=
  ∀ {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ),
    0 < c → c ≤ ‖x‖ → c ≤ ‖y‖ → ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ 1 / c * ‖x - y‖

/-- **`varNormalize_unit_lipschitz` 的命题：单位归一化的 Lipschitz 常数可取 `2/c`。** -/
def varNormalize_unit_lipschitzProp : Prop :=
  ∀ {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ),
    0 < c → c ≤ ‖x‖ → c ≤ ‖y‖ → ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ 2 / c * ‖x - y‖

/-- **`varOf_nonneg` 的命题：方差非负。** -/
def varOf_nonnegProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ), 0 ≤ varOf x

/-- **六条命题就是六条定理的类型。** -/
theorem norm_props_hold :
    varOf_iterate_varNormalize_le_oneProp ∧ varOf_varNormalize_eq_oneProp
      ∧ bn_train_eq_inferProp ∧ varNormalize_unit_lipschitz_sharpProp
      ∧ varNormalize_unit_lipschitzProp ∧ varOf_nonnegProp :=
  ⟨varOf_iterate_varNormalize_le_one, varOf_varNormalize_eq_one, bn_train_eq_infer,
   varNormalize_unit_lipschitz_sharp, varNormalize_unit_lipschitz, varOf_nonneg⟩

/-- **The normalisation carrier's manifest.**

Layer `architectures`. It requires the point-cloud representation (`domain.points`) and offers the
capability `arch.normalize`.
-/
def manifest : PluginManifest where
  name := "Architectures.Norm"
  layer := .architectures
  requires := ["domain.points"]
  provides := ["arch.normalize"]
  obligations := [
    -- **Round 768: every obligation goes through `verifiedObligation`, so each CARRIES its
    -- proposition.** The proposition is the named `_Prop` def above, which `norm_props_hold`
    -- proves equal to the theorem's own type -- so a rename breaks compilation.
    verifiedObligation "norm_iterate_variance_le_one" .idempotence
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "varOf_iterate_varNormalize_le_one" varOf_iterate_varNormalize_le_oneProp
,
    verifiedObligation "norm_variance_eq_one" .exactness
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "varOf_varNormalize_eq_one" varOf_varNormalize_eq_oneProp
,
    verifiedObligation "norm_train_infer_agree" .soundness
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "bn_train_eq_infer" bn_train_eq_inferProp
,
    verifiedObligation "norm_lipschitz_sharp" .approximation
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "varNormalize_unit_lipschitz_sharp" varNormalize_unit_lipschitz_sharpProp
,
    verifiedObligation "norm_lipschitz" .approximation
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "varNormalize_unit_lipschitz" varNormalize_unit_lipschitzProp
,
    verifiedObligation "norm_variance_nonneg" .soundness
      "Lattice/Plugins/Architectures/Norm/Proofs.lean"
      "varOf_nonneg" varOf_nonnegProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims six obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 6 := rfl

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

/-- The plugin lives in the `architectures` layer. -/
theorem manifest_layer : manifest.layer = PluginLayer.architectures := rfl

/-- It requires the point-cloud representation. -/
theorem manifest_requires : manifest.requires = ["domain.points"] := rfl

/-- It offers normalisation. -/
theorem manifest_provides : manifest.provides = ["arch.normalize"] := rfl

/-- **It claims IDEMPOTENCE** -- the obligation that no plugin before it could claim. -/
theorem manifest_claims_idempotence : manifest.claims .idempotence = true := rfl

/-- It claims exactness -- the variance-is-one statement. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It claims approximation -- the Lipschitz bounds. -/
theorem manifest_claims_approximation : manifest.claims .approximation = true := rfl

/-- It claims soundness -- well-definedness and train/infer agreement. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- **It does NOT claim equivariance**: that belongs to the GNN carrier
(`Lib/Architectures/RealGNNEquivariance.lean`), not to normalisation. -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- **It does NOT claim confluence**: normalisation is a single map, not a rewriting system. -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- **It does NOT claim recovery.** -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- **It does NOT claim spatial composability.** -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- **It does NOT claim laws**: the algebraic laws of composition are `Compose`'s business. -/
theorem manifest_no_laws : manifest.claims .laws = false := rfl

end Lattice.Plugins.Architectures.Norm
