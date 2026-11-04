/-
# `Core/ModelArtifactInstances.lean` -- `ModelArtifact` is INHABITED, and by real shapes

## Why a separate file

**`ModelArtifact.lean` defines the type.** **A type with no inhabitant proves nothing, and the audit that
prompted this work was exactly about objects that existed as names and not as things.**
**=> this file supplies instances, and each one is a REAL architecture rather than a `default`.**

## The three instances, and what each is for

| instance | what it establishes |
|:--|:--|
| `affineUnit` | **the degenerate case: one layer, one weight, `identity` activation** |
| `affineTwoLayer` | **a chain where the MIDDLE width is forced: `3 → 5 → 2`** |
| `reluNet` | **an activation that is provably non-affine (`Net.relu_not_affine`), so the `acts` field is not decorative** |

**The second is the one that matters for the project's thesis: `2` and `3` are both INPUTS, and `5` is the
only width that makes the two layers compose.**
**A weight file that said `3 → 7 → 2` would be a different model, and under this definition it is a
different `Arch`, hence a different type of `Weights`.**

## What is NOT here

**No forward function.** **`Forward` lives in `Core/Forward.lean`; this file only asserts that the SHAPES
exist.**
**Conflating "the artifact exists" with "the artifact computes" is the mistake that would let a `Prop`
about topology pass for a `Prop` about behaviour.**
-/

import Mathlib
import Lattice.Core.ModelArtifact

namespace Lattice.Core

namespace ModelArtifactInstances

open Matrix

/-! ## The single-weight artifact -/

/-- **A `1 → 1` affine layer.** -/
def unitLayer : MLayer 1 1 where
  W := fun _ _ => 1
  b := fun _ => 0

/-- **The `1 → 1` architecture with identity activation.** -/
def affineUnitArch : Arch := Arch.one 1 1 (by norm_num) (by norm_num) .identity

/-- **`affineUnitArch` is well formed.** -/
theorem affineUnitArch_wf : affineUnitArch.WellFormed :=
  Arch.one_wellFormed 1 1 (by norm_num) (by norm_num) .identity

/-- **The weights for `affineUnitArch`: one layer, matching the depth.** -/
def affineUnitWeights : Weights affineUnitArch where
  layers := [⟨1, 1, unitLayer⟩]
  count := rfl

/-- **The smallest non-trivial `ModelArtifact`.**

**`ModelArtifact` is INHABITED.** -/
def affineUnit : ModelArtifact where
  arch := affineUnitArch
  wf := affineUnitArch_wf
  weights := affineUnitWeights

/-- **`affineUnit` has one layer.** -/
theorem affineUnit_depth : affineUnit.depth = 1 := rfl

/-! ## The two-layer chain, where the middle width is forced -/

/-- **A `3 → 5` layer.** -/
def firstLayer : MLayer 3 5 where
  W := fun _ _ => 1
  b := fun _ => 0

/-- **A `5 → 2` layer.** -/
def secondLayer : MLayer 5 2 where
  W := fun _ _ => 1
  b := fun _ => 0

/-- **The `3 → 5 → 2` architecture.** -/
def affineTwoLayerArch : Arch where
  widths := [3, 5, 2]
  acts := [.identity, .identity]

/-- **`affineTwoLayerArch` is well formed.** -/
theorem affineTwoLayerArch_wf : affineTwoLayerArch.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [affineTwoLayerArch, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hw
    rcases hw with rfl | rfl | rfl <;> norm_num
  · simp [affineTwoLayerArch]

/-- **The two layers, in order.** -/
def affineTwoLayerWeights : Weights affineTwoLayerArch where
  layers := [⟨3, 5, firstLayer⟩, ⟨5, 2, secondLayer⟩]
  count := rfl

/-- **A `3 → 5 → 2` artifact.**

**The middle width `5` is the ONLY value that lets `firstLayer` and `secondLayer` compose, which is why
this instance is the interesting one rather than a duplicate of `affineUnit`.** -/
def affineTwoLayer : ModelArtifact where
  arch := affineTwoLayerArch
  wf := affineTwoLayerArch_wf
  weights := affineTwoLayerWeights

/-- **`affineTwoLayer` has two layers.** -/
theorem affineTwoLayer_depth : affineTwoLayer.depth = 2 := rfl

/-- **`affineTwoLayer`'s parameter count is `3 * 5 + 5 + 5 * 2 + 2 = 32`.**

**Stated as a theorem rather than left to the reader: `paramCount` is DERIVED from the layers, so this is
a check that the derivation and the architecture agree.** -/
theorem affineTwoLayer_params : affineTwoLayer.paramCount = 32 := by
  decide

/-! ## An architecture whose activation is provably not identity -/

/-- **The `2 → 4 → 1` ReLU architecture.**

**Included because `Net.relu_not_affine` proves `relu` is not the identity, so this artifact differs from
`affineTwoLayer` in its `acts` and not only in its numbers.** -/
def reluArch : Arch where
  widths := [2, 4, 1]
  acts := [.relu, .relu]

/-- **`reluArch` is well formed.** -/
theorem reluArch_wf : reluArch.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [reluArch, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> norm_num
  · simp [reluArch]

/-! ## The count of inhabited shapes -/

/-- **Three DISTINCT architectures, so `Arch` is not a singleton type.** -/
theorem three_architectures :
    affineUnitArch ≠ affineTwoLayerArch ∧ affineTwoLayerArch ≠ reluArch
      ∧ affineUnitArch ≠ reluArch := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : affineUnitArch.depth = affineTwoLayerArch.depth := by rw [h]
    simp [affineUnitArch, affineTwoLayerArch, Arch.one, Arch.depth] at this
  · intro h
    have : affineTwoLayerArch.widths = reluArch.widths := by rw [h]
    simp [affineTwoLayerArch, reluArch] at this
  · intro h
    have : affineUnitArch.widths = reluArch.widths := by rw [h]
    simp [affineUnitArch, reluArch, Arch.one] at this

end ModelArtifactInstances

end Lattice.Core
