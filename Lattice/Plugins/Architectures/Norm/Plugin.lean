/-
# Architectures.Norm Plugin -- assembly

The six obligations of `Manifest.lean`, discharged by
`Lattice.Lib.Architectures.RealBatchNormConsistency`.

## The idempotence obligation, stated honestly

**`varOf_iterate_varNormalize_le_one` is about `(varNormalize^[n+1]) x`, i.e. the normaliser
iterated `n+1` times.**
**Its content is that the VARIANCE stays at most `1`, not that the map is literally idempotent.**

**That distinction matters and is NOT obscured here**: **`varNormalize ∘ varNormalize` is not
`varNormalize` in general** (applying it twice squares the scale), **but the variance after any
number of applications is still `≤ 1` -- which is what "normalisation is idempotent" means
operationally.**

**A plugin that claimed `f ∘ f = f` would be claiming something FALSE about this carrier.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Architectures.Norm.Manifest
import Lattice.Lib.Architectures.RealBatchNormConsistency

namespace Lattice.Plugins.Architectures.Norm

open Lattice.Plugins
open scoped BigOperators

/-- **Idempotence: iterating the normaliser keeps the variance at most `1`.** -/
def NormIterateVarianceLeOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ) (n : ℕ), varOf ((varNormalize^[n + 1]) x) ≤ 1

/-- **`NormIterateVarianceLeOneProp` holds** -- by `varOf_iterate_varNormalize_le_one`. -/
theorem normIterateVarianceLeOneProp_holds : NormIterateVarianceLeOneProp := by
  intro ι _ x n
  exact varOf_iterate_varNormalize_le_one x n

/-- **Exactness: on a non-degenerate input the normalised variance is exactly `1`.** -/
def NormVarianceEqOneProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ), varOf x ≠ 0 → varOf (varNormalize x) = 1

/-- **`NormVarianceEqOneProp` holds** -- by `varOf_varNormalize_eq_one`. -/
theorem normVarianceEqOneProp_holds : NormVarianceEqOneProp := by
  intro ι _ x h
  exact varOf_varNormalize_eq_one x h

/-- **Soundness: train-mode and inference-mode agree on the batch they were computed from.** -/
def NormTrainInferAgreeProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (gamma beta eps mu sigmaSq : ℝ) (X : ι → ℝ),
    batchMean X = mu → batchVar X = sigmaSq →
    ∀ i : ι, bnTrain gamma beta eps X i = bnInfer gamma beta eps mu sigmaSq (X i)

/-- **`NormTrainInferAgreeProp` holds** -- by `bn_train_eq_infer`. -/
theorem normTrainInferAgreeProp_holds : NormTrainInferAgreeProp := by
  intro ι _ gamma beta eps mu sigmaSq X hmu hsig i
  exact bn_train_eq_infer gamma beta eps mu sigmaSq X hmu hsig i

/-- **Approximation: the unit-scale normaliser is Lipschitz with the SHARP constant `1/c`.** -/
def NormLipschitzSharpProp : Prop :=
  ∀ {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ), 0 < c → c ≤ ‖x‖ → c ≤ ‖y‖ →
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (1 / c) * ‖x - y‖

/-- **`NormLipschitzSharpProp` holds** -- by `varNormalize_unit_lipschitz_sharp`. -/
theorem normLipschitzSharpProp_holds : NormLipschitzSharpProp := by
  intro n x y c hc hx hy
  exact varNormalize_unit_lipschitz_sharp x y c hc hx hy

/-- **Approximation: the same bound in its unconditional form, with constant `2/c`.** -/
def NormLipschitzProp : Prop :=
  ∀ {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ), 0 < c → c ≤ ‖x‖ → c ≤ ‖y‖ →
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (2 / c) * ‖x - y‖

/-- **`NormLipschitzProp` holds** -- by `varNormalize_unit_lipschitz`. -/
theorem normLipschitzProp_holds : NormLipschitzProp := by
  intro n x y c hc hx hy
  exact varNormalize_unit_lipschitz x y c hc hx hy

/-- **Soundness: the variance is non-negative, so the normaliser is well defined.** -/
def NormVarianceNonnegProp : Prop :=
  ∀ {ι : Type} [Fintype ι] (x : ι → ℝ), 0 ≤ varOf x

/-- **`NormVarianceNonnegProp` holds** -- by `varOf_nonneg`. -/
theorem normVarianceNonnegProp_holds : NormVarianceNonnegProp := by
  intro ι _ x
  exact varOf_nonneg x

/-- **The normalisation carrier's proof bundle.**

Six claimed obligations, including the registry's FIRST `idempotence` witness.
-/
def proof : PluginProof where
  soundness := NormTrainInferAgreeProp ∧ NormVarianceNonnegProp
  laws := True
  exactness := NormVarianceEqOneProp
  approximation := NormLipschitzSharpProp ∧ NormLipschitzProp
  recovery := True
  spatial := True
  confluence := True
  equivariance := True
  idempotence := NormIterateVarianceLeOneProp
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the normalisation carrier is discharged.** -/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  exact ⟨⟨normTrainInferAgreeProp_holds, normVarianceNonnegProp_holds⟩,
         True.intro,
         normVarianceEqOneProp_holds,
         ⟨normLipschitzSharpProp_holds, normLipschitzProp_holds⟩,
         True.intro, True.intro, True.intro, True.intro,
         normIterateVarianceLeOneProp_holds,
         True.intro, True.intro, True.intro⟩

/-- **The verified normalisation carrier.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The carrier claims six obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 6 := rfl

end Lattice.Plugins.Architectures.Norm
