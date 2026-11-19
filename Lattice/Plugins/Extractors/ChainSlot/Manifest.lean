/-
# Extractors.ChainSlot Plugin -- Manifest

The reverse direction's mechanism (rounds 42-66, migrated at P3-3). It says: a chain's output
polynomial encodes its weights at KNOWN SLOTS, and those slots can be read.

## What makes this plugin different from the other three

`Core.Repair`, `Domains.Constraints.Penalty` and `Domains.Constraints.Tokens` all cite theorems
that existed before the plugin framework did. **This one also cites pre-existing theorems, but
its subject is the project's central difficulty** -- the symbol/weight hop -- so its obligations
are the ones that decide whether "extract back to symbols" is possible at all.

## The two layers of the answer

**POSITIONAL (which slot holds a weight).** `slotOf off b i j = off + i*b + j` with stride `b`
being the OUTPUT width. `slotOf_weight_lt` and `slotOf_lt_bound` say the weight block ends
exactly where the bias block begins, so a slot's classification is decided by ARITHMETIC ON THE
SHAPE alone -- no coefficient inspection needed.

**VALUE (what the weight is).** `oneLayerPolyNat_coeff_weight` / `stepNat_coeff_weight` read the
weight back out of its slot; `stepNat_coeff_bias` records that the bias slot carries coefficient
1 and its VALUE lives in `g`, not in the polynomial.

## The negative result that shapes everything

**`stepNat_coeff_zero_irrelevant`: a step at offset >= 2 zeroes slot 0 regardless of its input.**
**`chainNatPoly_deep_coeff_zero`: a chain of length >= 2 therefore has FINAL slot 0 equal to 0.**
**`chainNatPoly_deep_coeff_ne`: hence no nonzero weight is readable from a deep chain's final
polynomial.**

**=> the extractor must read INTERMEDIATE polynomials, which is what `chainNatPolyAfter` and
`chainNatPolyAfter_one_coeff` provide.** **This is why the manifest claims
`intermediate_poly_readable` and NOT `final_poly_readable`.**
-/

import Lattice.Plugins.Manifest
import Lattice.Core.RepairModule.VariableDerivative
namespace Lattice.Plugins.Extractors.ChainSlot

open Lattice.Plugins
open Lattice.Core

-- **Round 772 (STAGE 3, final batch): the twelve obligations now CARRY their propositions.**
-- **These are the ChainSlot extractor's SLOT-BOUND laws -- the reason a weight offset can be read
-- back from a polynomial coefficient without ambiguity.**

/-- **`slotOf_weight_lt`: 权重槽位落在 `off + a*b` 之内。** -/
def slotOf_weight_ltProp : Prop :=
  ∀ {a b i j off : ℕ}, i < a → j < b → slotOf off b i j < off + a * b

/-- **`slotOf_lt_bound`: 槽位与偏置的总界。** -/
def slotOf_lt_boundProp : Prop :=
  ∀ {a b i j : ℕ}, i < a → j < b → ∀ (off : ℕ), slotOf off b i j < off + a * b + b

/-- **`bias_slot_eq_slotOf`: 偏置槽位就是第 `a` 行的槽位。** -/
def bias_slot_eq_slotOfProp : Prop :=
  ∀ (off a b j : ℕ), off + a * b + j = slotOf off b a j

/-- **`oneLayerPolyNat_coeff_weight`: 单层多项式在权重槽上的系数就是权重本身。** -/
def oneLayerPolyNat_coeff_weightProp : Prop :=
  ∀ (off : ℕ) (c : ℝ),
    MvPolynomial.coeff (fun₀ | off => 1) (oneLayerPolyNat off c) = c

/-- **`stepNat_coeff_weight`: 一层的步进在权重槽上读出权重。** -/
def stepNat_coeff_weightProp : Prop :=
  ∀ (off : ℕ) (c : ℝ),
    MvPolynomial.coeff (fun₀ | off => 1) (stepNat (off, MvPolynomial.C c)).2 = c

/-- **`stepNat_coeff_bias`: 一层的步进在偏置槽上读出 1。** -/
def stepNat_coeff_biasProp : Prop :=
  ∀ (off : ℕ) (c : ℝ),
    MvPolynomial.coeff (fun₀ | off + 1 => 1) (stepNat (off, MvPolynomial.C c)).2 = 1

/-- **`chainNatPoly_single_coeff_weight`: 单层链在首槽上读出权重。** -/
def chainNatPoly_single_coeff_weightProp : Prop :=
  ∀ (l : MLayer 1 1) (c : ℝ),
    MvPolynomial.coeff (fun₀ | 0 => 1) (chainNatPoly [l] (MvPolynomial.C c)) = c

/-- **`stepNat_coeff_zero_irrelevant`: 深槽不影响首槽系数。** -/
def stepNat_coeff_zero_irrelevantProp : Prop :=
  ∀ (off : ℕ), 2 ≤ off → ∀ (p : MvPolynomial ℕ ℝ),
    MvPolynomial.coeff (fun₀ | 0 => 1) (stepNat (off, p)).2 = 0

/-- **`foldl_coeff_zero_irrelevant`: 折叠后首槽系数仍与深槽无关。** -/
def foldl_coeff_zero_irrelevantProp : Prop :=
  ∀ (ls : List (MLayer 1 1)) (off : ℕ) (p : MvPolynomial ℕ ℝ),
    2 ≤ off →
      MvPolynomial.coeff (fun₀ | 0 => 1) p = 0 →
        MvPolynomial.coeff (fun₀ | 0 => 1)
          (List.foldl (fun acc x => stepNat acc) (off, p) ls).2 = 0

/-- **`stepNat_coeff_other_slot`: 不涉及的槽位系数为零。** -/
def stepNat_coeff_other_slotProp : Prop :=
  ∀ (m : ℕ) (p : MvPolynomial ℕ ℝ) (s : ℕ →₀ ℕ),
    s ≠ 0 → m ∉ s.support → m + 1 ∉ s.support →
      MvPolynomial.coeff s (stepNat (m, p)).2 = 0

/-- **`chainNatPolyAfter_one_coeff`: 一层之后首槽读出权重。** -/
def chainNatPolyAfter_one_coeffProp : Prop :=
  ∀ (l : MLayer 1 1) (rest : List (MLayer 1 1)) (c : ℝ),
    MvPolynomial.coeff (fun₀ | 0 => 1)
      (chainNatPolyAfter (l :: rest) (MvPolynomial.C c) 1) = c

/-- **`chainNatPoly_deep_coeff_zero`: 两层以上的链首槽系数为零。** -/
def chainNatPoly_deep_coeff_zeroProp : Prop :=
  ∀ (l l' : MLayer 1 1) (tl : List (MLayer 1 1)) (c : ℝ),
    MvPolynomial.coeff (fun₀ | 0 => 1) (chainNatPoly (l :: l' :: tl) (MvPolynomial.C c)) = 0

/-- **十二条命题就是十二条定理的类型。** -/
theorem chainSlot_props_hold :
    slotOf_weight_ltProp ∧ slotOf_lt_boundProp ∧ bias_slot_eq_slotOfProp
      ∧ oneLayerPolyNat_coeff_weightProp ∧ stepNat_coeff_weightProp
      ∧ stepNat_coeff_biasProp ∧ chainNatPoly_single_coeff_weightProp
      ∧ stepNat_coeff_zero_irrelevantProp ∧ foldl_coeff_zero_irrelevantProp
      ∧ stepNat_coeff_other_slotProp ∧ chainNatPolyAfter_one_coeffProp
      ∧ chainNatPoly_deep_coeff_zeroProp :=
  ⟨@slotOf_weight_lt, @slotOf_lt_bound, bias_slot_eq_slotOf,
   oneLayerPolyNat_coeff_weight, stepNat_coeff_weight, stepNat_coeff_bias,
   chainNatPoly_single_coeff_weight, stepNat_coeff_zero_irrelevant,
   foldl_coeff_zero_irrelevant, stepNat_coeff_other_slot,
   chainNatPolyAfter_one_coeff, chainNatPoly_deep_coeff_zero⟩

/-- **The chain-slot extractor's manifest.**

Layer `extractors` -- the reverse direction. It requires the polynomial carrier
(`chain.poly`, a capability `Core` offers) and provides `extract.weights`.
-/
def manifest : PluginManifest where
  name := "Extractors.ChainSlot"
  layer := .extractors
  requires := ["chain.poly"]
  provides := ["extract.weights"]
  obligations := [
    -- **Round 772: all twelve go through `verifiedObligation`, so each CARRIES its proposition.**
    verifiedObligation "slot_weight_lt_bias" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "slotOf_weight_lt" slotOf_weight_ltProp,
    verifiedObligation "slot_within_block" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "slotOf_lt_bound" slotOf_lt_boundProp,
    verifiedObligation "bias_slot_is_row_a" .laws
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "bias_slot_eq_slotOf" bias_slot_eq_slotOfProp,
    verifiedObligation "one_layer_weight_readable" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "oneLayerPolyNat_coeff_weight" oneLayerPolyNat_coeff_weightProp,
    verifiedObligation "step_weight_readable" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "stepNat_coeff_weight" stepNat_coeff_weightProp,
    verifiedObligation "step_bias_positional" .soundness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "stepNat_coeff_bias" stepNat_coeff_biasProp,
    verifiedObligation "single_chain_weight_readable" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "chainNatPoly_single_coeff_weight" chainNatPoly_single_coeff_weightProp,
    verifiedObligation "slot_zero_dead_past_two" .soundness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "stepNat_coeff_zero_irrelevant" stepNat_coeff_zero_irrelevantProp,
    verifiedObligation "foldl_slot_zero_preserved" .soundness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "foldl_coeff_zero_irrelevant" foldl_coeff_zero_irrelevantProp,
    verifiedObligation "per_slot_extraction_sound" .soundness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "stepNat_coeff_other_slot" stepNat_coeff_other_slotProp,
    verifiedObligation "intermediate_poly_readable" .exactness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "chainNatPolyAfter_one_coeff" chainNatPolyAfter_one_coeffProp,
    verifiedObligation "deep_chain_final_slot_dead" .soundness
      "Lattice/Core/RepairModule/VariableDerivative.lean"
      "chainNatPoly_deep_coeff_zero" chainNatPoly_deep_coeff_zeroProp
  ]
  version := ⟨1, 0, 0⟩

/-- The manifest claims twelve obligations. -/
theorem manifest_obligation_count : manifest.obligations.length = 12 := rfl

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

/-- The plugin lives in the `extractors` layer -- the reverse direction. -/
theorem manifest_layer : manifest.layer = PluginLayer.extractors := rfl

/-- It requires the polynomial carrier. -/
theorem manifest_requires : manifest.requires = ["chain.poly"] := rfl

/-- It provides weight extraction. -/
theorem manifest_provides : manifest.provides = ["extract.weights"] := rfl

/-- It claims exactness -- the slot positions and the readable values. -/
theorem manifest_claims_exactness : manifest.claims .exactness = true := rfl

/-- It claims soundness -- including the three negative positional facts. -/
theorem manifest_claims_soundness : manifest.claims .soundness = true := rfl

/-- It claims laws -- the bias slot's row identity. -/
theorem manifest_claims_laws : manifest.claims .laws = true := rfl

/-- **It does NOT claim approximation**: extraction is exact or impossible, never approximate. -/
theorem manifest_no_approximation : manifest.claims .approximation = false := rfl

/-- **It does NOT claim recovery**: that belongs to the `Compose` layer. -/
theorem manifest_no_recovery : manifest.claims .recovery = false := rfl

/-- **It does NOT claim spatial composability.** -/
theorem manifest_no_spatial : manifest.claims .spatial = false := rfl

/-- **It does NOT claim confluence.** -/
theorem manifest_no_confluence : manifest.claims .confluence = false := rfl

/-- **It does NOT claim equivariance.** -/
theorem manifest_no_equivariance : manifest.claims .equivariance = false := rfl

/-- **It does NOT claim completeness**: totality of the extractor is not asserted, because the
negative result above shows it cannot be total on FINAL polynomials. -/
theorem manifest_no_completeness : manifest.claims .completeness = false := rfl

end Lattice.Plugins.Extractors.ChainSlot
