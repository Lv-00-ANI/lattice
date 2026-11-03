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

namespace Lattice.Plugins.Extractors.ChainSlot

open Lattice.Plugins

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
    -- POSITIONAL: the weight block ends where the bias block begins.
    { name := "slot_weight_lt_bias"
      kind := .exactness
      theoremName := "slotOf_weight_lt"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- POSITIONAL: every weight slot and the bias slot fit inside one layer's block.
    { name := "slot_within_block"
      kind := .exactness
      theoremName := "slotOf_lt_bound"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- POSITIONAL law: the bias slot is the slot a weight slot would occupy at row `a`.
    { name := "bias_slot_is_row_a"
      kind := .laws
      theoremName := "bias_slot_eq_slotOf"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- VALUE: the weight is readable from a one-layer polynomial.
    { name := "one_layer_weight_readable"
      kind := .exactness
      theoremName := "oneLayerPolyNat_coeff_weight"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- VALUE: the same for the chain-level step, from a constant input.
    { name := "step_weight_readable"
      kind := .exactness
      theoremName := "stepNat_coeff_weight"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- VALUE: the bias is recorded POSITIONALLY (coefficient 1), not by value.
    { name := "step_bias_positional"
      kind := .soundness
      theoremName := "stepNat_coeff_bias"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- VALUE at chain level, ONE element: the output polynomial carries its weight.
    { name := "single_chain_weight_readable"
      kind := .exactness
      theoremName := "chainNatPoly_single_coeff_weight"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- The NEGATIVE positional fact at step level: a step past offset 2 zeroes slot 0.
    { name := "slot_zero_dead_past_two"
      kind := .soundness
      theoremName := "stepNat_coeff_zero_irrelevant"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- Its lift to the foldl: slot 0 stays zero for the whole remaining list.
    { name := "foldl_slot_zero_preserved"
      kind := .soundness
      theoremName := "foldl_coeff_zero_irrelevant"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- The general positional locality: a step touches ONLY slots `m` and `m+1`.
    { name := "per_slot_extraction_sound"
      kind := .soundness
      theoremName := "stepNat_coeff_other_slot"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- The INTERMEDIATE-polynomial route: after `k` layers, slot `2k` holds layer `k`'s weight.
    { name := "intermediate_poly_readable"
      kind := .exactness
      theoremName := "chainNatPolyAfter_one_coeff"
      file := "Lattice/Core/VariableDerivative.lean" },
    -- The IMPOSSIBILITY: a deep chain's final slot 0 is zero, so no weight is readable there.
    { name := "deep_chain_final_slot_dead"
      kind := .soundness
      theoremName := "chainNatPoly_deep_coeff_zero"
      file := "Lattice/Core/VariableDerivative.lean" }
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
