/-
# Extractors.ChainSlot Plugin -- assembly

The twelve obligations of `Manifest.lean`, discharged by `Lattice.Core.VariableDerivative`.

## What this file adds beyond citing

**Nothing new to prove.** The one theorem this plugin needed -- that a deep chain's final slot 0
is zero -- was proved in `Core/VariableDerivative.lean` (round 66,
`chainNatPoly_deep_coeff_zero`), precisely so that the manifest could cite it rather than gesture
at it.

## Why the extractor is nevertheless a real extractor

**It reads the INTERMEDIATE polynomial.** `chainNatPolyAfter_one_coeff` says: after ONE step,
slot 0 holds the first layer's weight, for a chain of ANY length.
**So the reverse direction works -- it needs the polynomial at step `k`, not at the end.**
**The `soundness` side of the bundle carries the matching impossibility
(`deep_chain_final_slot_dead`), so the two halves of the bundle say the same thing from both
directions: the slot is readable, and the WRONG slot is not.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Registry
import Lattice.Plugins.Extractors.ChainSlot.Manifest
import Lattice.Plugins.Extractors.ChainSlot.VariableDerivative
namespace Lattice.Plugins.Extractors.ChainSlot

open Lattice.Plugins
open Lattice.Core

/-- **Positional: the weight block ends where the bias block begins.** -/
def SlotWeightLtBiasProp : Prop :=
  ∀ {a b i j off : ℕ}, i < a → j < b → slotOf off b i j < off + a * b

/-- **`SlotWeightLtBiasProp` holds** -- by `slotOf_weight_lt`. -/
theorem slotWeightLtBiasProp_holds : SlotWeightLtBiasProp := by
  intro a b i j off hi hj
  exact slotOf_weight_lt hi hj

/-- **Positional: a weight slot plus the bias slot fit inside one layer's block.** -/
def SlotWithinBlockProp : Prop :=
  ∀ {a b i j : ℕ}, i < a → j < b → ∀ off : ℕ, slotOf off b i j < off + a * b + b

/-- **`SlotWithinBlockProp` holds** -- by `slotOf_lt_bound`. -/
theorem slotWithinBlockProp_holds : SlotWithinBlockProp := by
  intro a b i j hi hj off
  exact slotOf_lt_bound hi hj off

/-- **Law: the bias slot is the slot a weight slot would occupy at row `a`.** -/
def BiasSlotIsRowAProp : Prop :=
  ∀ (off a b j : ℕ), off + a * b + j = slotOf off b a j

/-- **`BiasSlotIsRowAProp` holds** -- by `bias_slot_eq_slotOf`. -/
theorem biasSlotIsRowAProp_holds : BiasSlotIsRowAProp := by
  intro off a b j
  exact bias_slot_eq_slotOf off a b j

/-- **Value: a one-layer polynomial's weight is readable at slot `off`.** -/
def OneLayerWeightReadableProp : Prop :=
  ∀ (off : ℕ) (c : ℝ), MvPolynomial.coeff (Finsupp.single off 1) (oneLayerPolyNat off c) = c

/-- **`OneLayerWeightReadableProp` holds** -- by `oneLayerPolyNat_coeff_weight`. -/
theorem oneLayerWeightReadableProp_holds : OneLayerWeightReadableProp := by
  intro off c
  exact oneLayerPolyNat_coeff_weight off c

/-- **Value: a step from a constant input records the weight at slot `off`.** -/
def StepWeightReadableProp : Prop :=
  ∀ (off : ℕ) (c : ℝ),
    MvPolynomial.coeff (Finsupp.single off 1) ((stepNat (off, MvPolynomial.C c)).2) = c

/-- **`StepWeightReadableProp` holds** -- by `stepNat_coeff_weight`. -/
theorem stepWeightReadableProp_holds : StepWeightReadableProp := by
  intro off c
  exact stepNat_coeff_weight off c

/-- **Soundness: the bias slot carries coefficient 1, not the bias value.** -/
def StepBiasPositionalProp : Prop :=
  ∀ (off : ℕ) (c : ℝ),
    MvPolynomial.coeff (Finsupp.single (off + 1) 1) ((stepNat (off, MvPolynomial.C c)).2) = 1

/-- **`StepBiasPositionalProp` holds** -- by `stepNat_coeff_bias`. -/
theorem stepBiasPositionalProp_holds : StepBiasPositionalProp := by
  intro off c
  exact stepNat_coeff_bias off c

/-- **Value at chain level: a ONE-element chain's output carries its weight at slot 0.** -/
def SingleChainWeightReadableProp : Prop :=
  ∀ (l : MLayer 1 1) (c : ℝ),
    MvPolynomial.coeff (Finsupp.single 0 1) (chainNatPoly [l] (MvPolynomial.C c)) = c

/-- **`SingleChainWeightReadableProp` holds** -- by `chainNatPoly_single_coeff_weight`. -/
theorem singleChainWeightReadableProp_holds : SingleChainWeightReadableProp := by
  intro l c
  exact chainNatPoly_single_coeff_weight l c

/-- **The negative positional fact: a step past offset 2 zeroes slot 0.** -/
def SlotZeroDeadPastTwoProp : Prop :=
  ∀ (off : ℕ), 2 ≤ off → ∀ (p : MvPolynomial ℕ ℝ),
    MvPolynomial.coeff (Finsupp.single 0 1) ((stepNat (off, p)).2) = 0

/-- **`SlotZeroDeadPastTwoProp` holds** -- by `stepNat_coeff_zero_irrelevant`. -/
theorem slotZeroDeadPastTwoProp_holds : SlotZeroDeadPastTwoProp := by
  intro off hoff p
  exact stepNat_coeff_zero_irrelevant off hoff p

/-- **Its lift to the foldl: slot 0 stays zero for the whole remaining list.** -/
def FoldlSlotZeroPreservedProp : Prop :=
  ∀ (ls : List (MLayer 1 1)) (off : ℕ) (p : MvPolynomial ℕ ℝ), 2 ≤ off →
    MvPolynomial.coeff (Finsupp.single 0 1) p = 0 →
    MvPolynomial.coeff (Finsupp.single 0 1)
      ((ls.foldl (fun acc _ => stepNat acc) (off, p)).2) = 0

/-- **`FoldlSlotZeroPreservedProp` holds** -- by `foldl_coeff_zero_irrelevant`. -/
theorem foldlSlotZeroPreservedProp_holds : FoldlSlotZeroPreservedProp := by
  intro ls off p hoff hz
  exact foldl_coeff_zero_irrelevant ls off p hoff hz

/-- **The general positional locality: a step at offset `m` touches only slots `m` and `m+1`.** -/
def PerSlotExtractionSoundProp : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial ℕ ℝ) (s : ℕ →₀ ℕ), s ≠ 0 →
    m ∉ s.support → m + 1 ∉ s.support →
    MvPolynomial.coeff s ((stepNat (m, p)).2) = 0

/-- **`PerSlotExtractionSoundProp` holds** -- by `stepNat_coeff_other_slot`. -/
theorem perSlotExtractionSoundProp_holds : PerSlotExtractionSoundProp := by
  intro m p s hs h1 h2
  exact stepNat_coeff_other_slot m p s hs h1 h2

/-- **The INTERMEDIATE-polynomial route: after one step, slot 0 holds the first weight.**

This is the extractor's positive half, and it holds for a chain of ANY length. -/
def IntermediatePolyReadableProp : Prop :=
  ∀ (l : MLayer 1 1) (rest : List (MLayer 1 1)) (c : ℝ),
    MvPolynomial.coeff (Finsupp.single 0 1)
      (chainNatPolyAfter (l :: rest) (MvPolynomial.C c) 1) = c

/-- **`IntermediatePolyReadableProp` holds** -- by `chainNatPolyAfter_one_coeff`. -/
theorem intermediatePolyReadableProp_holds : IntermediatePolyReadableProp := by
  intro l rest c
  exact chainNatPolyAfter_one_coeff l rest c

/-- **The impossibility: a chain of length >= 2 has final slot 0 equal to zero.**

The extractor's negative half. Together with `IntermediatePolyReadableProp` it says: read the
polynomial at step `k`, never at the end. -/
def DeepChainFinalSlotDeadProp : Prop :=
  ∀ (l l' : MLayer 1 1) (tl : List (MLayer 1 1)) (c : ℝ),
    MvPolynomial.coeff (Finsupp.single 0 1)
      (chainNatPoly (l :: l' :: tl) (MvPolynomial.C c)) = 0

/-- **`DeepChainFinalSlotDeadProp` holds** -- by `chainNatPoly_deep_coeff_zero`. -/
theorem deepChainFinalSlotDeadProp_holds : DeepChainFinalSlotDeadProp := by
  intro l l' tl c
  exact chainNatPoly_deep_coeff_zero l l' tl c

/-- **The chain-slot extractor's proof bundle.**

Twelve claimed obligations. `completeness`, `approximation`, `recovery`, `spatial`, `confluence`,
`equivariance`, `idempotence`, `invariants` and `refinement` are `True`, matching the manifest's
negative theorems.
-/
def proof : PluginProof where
  soundness := SlotZeroDeadPastTwoProp ∧ FoldlSlotZeroPreservedProp ∧
    PerSlotExtractionSoundProp ∧ StepBiasPositionalProp ∧ DeepChainFinalSlotDeadProp
  laws := BiasSlotIsRowAProp
  exactness := SlotWeightLtBiasProp ∧ SlotWithinBlockProp ∧ OneLayerWeightReadableProp ∧
    StepWeightReadableProp ∧ SingleChainWeightReadableProp ∧ IntermediatePolyReadableProp
  approximation := True
  recovery := True
  spatial := True
  confluence := True
  equivariance := True
  idempotence := True
  invariants := True
  completeness := True
  refinement := True

/-- **Every claimed obligation of the chain-slot extractor is discharged.**

The `soundness` conjunct carries FIVE facts, three of them negative -- which is the shape this
plugin's content takes: the extractor is defined as much by which slots are NOT readable as by
which are.
-/
theorem proof_holds : proof.Holds := by
  simp only [PluginProof.Holds, proof]
  refine ⟨⟨slotZeroDeadPastTwoProp_holds, foldlSlotZeroPreservedProp_holds,
           perSlotExtractionSoundProp_holds, stepBiasPositionalProp_holds,
           deepChainFinalSlotDeadProp_holds⟩, biasSlotIsRowAProp_holds,
          ⟨slotWeightLtBiasProp_holds, slotWithinBlockProp_holds,
           oneLayerWeightReadableProp_holds, stepWeightReadableProp_holds,
           singleChainWeightReadableProp_holds, intermediatePolyReadableProp_holds⟩,
          True.intro, True.intro, True.intro, True.intro, True.intro,
          True.intro, True.intro, True.intro, True.intro⟩

/-- **The verified chain-slot extractor.** -/
def verified : VerifiedPlugin where
  manifest := manifest
  proof := proof
  consistent := fun _ => proof_holds

/-- The registered plugin's manifest is the one in `Manifest.lean`. -/
theorem verified_manifest : verified.manifest = manifest := rfl

/-- The extractor carries twelve obligations. -/
theorem verified_obligations : verified.manifest.obligations.length = 12 := rfl

end Lattice.Plugins.Extractors.ChainSlot
