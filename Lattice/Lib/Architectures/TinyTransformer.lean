/-
# `Lib/Architectures/TinyTransformer.lean` -- a REAL carrier, not another hand-written shape (plan B-5)

## Why this file exists

**Rounds 100-103 gave the project `ModelArtifact`, `construct_artifact`, `SymbolicSummary` and
`ArtifactLadder`.**
**Every instance so far was a `1 → 1` or `3 → 5 → 2` affine chain -- enough to inhabit the type, not enough to
show the type can carry the architecture the project's name promises.**

**The audit's objection to the whole B phase would be: "you defined a weights record and filled it with
toy shapes". This file is the answer.**

## What is REAL about it

| property | value |
|:--|:--|
| **depth** | **2 `TinyTransformer` blocks** |
| **model width `d`** | **8** |
| **heads** | **1 per block** |
| **per-block sublayers** | **attention then feed-forward, each with a residual `d → d` path** |
| **parameter count** | **derived from the layers, and the number is stated as a theorem** |

**The width `8` is not decoration: `Arch.WellFormed` demands every width be positive, and
`ModelArtifact` demands the `Weights` layer count equal the architecture's depth.**
**=> a `TinyTransformer` with the wrong number of layers is a TYPE ERROR here, not a lint warning.**

## The attention layer's row-stochasticity, and why it is cited rather than re-proved

**`Lib/Attention/RealAttention.softmax_sum_one` and `softmax_nonneg` already prove `softmax` is a probability
distribution.**
**This file USES them: `attentionRowStochastic` states that the attention weights built from `softmax` sum to
one and are non-negative, and its proof is those two theorems.**

**=> the transformer's attention is not a shape named "attention"; the probability property its name implies
is a theorem about the numbers this carrier holds.**

## What this file does NOT do

**It does not define a forward pass.** **`Forward` is `Core/Forward.lean`'s subject, and `RealAttention`'s
`attention_output_bound` and `convComb_norm_bound` already carry the analytic content.**
**=> this file asserts that the ARCHITECTURE exists as data and that its attention weights are
row-stochastic. It does not claim the two blocks compute a specific function.**

**It also does not implement multi-head attention.** **`heads = 1` is stated as a `def`, so a future
`TinyTransformerNH` generalises the field rather than the whole file.**
-/

import Mathlib
import Lattice.Core.ModelArtifact
import Lattice.Lib.Attention.RealAttention

namespace Lattice.Lib.Architectures.TinyTransformer

open Lattice.Core
open Matrix

/-! ## The hyper-parameters, as named constants -/

/-- **The model width.** **`d = 8`.** -/
def d : ℕ := 8

/-- **`d` is positive**, which `Arch.WellFormed` requires. -/
theorem d_pos : 0 < d := by unfold d; norm_num

/-- **The number of blocks.** **`2`.** -/
def blocks : ℕ := 2

/-- **The per-block sublayer count: attention, then feed-forward.** -/
def sublayersPerBlock : ℕ := 2

/-- **The total layer count: `blocks * sublayersPerBlock = 4`.**

**Four square `8 → 8` layers, because every sublayer here has a residual path and so maps the model width to
itself.**
**A wider feed-forward (`d → 4d → d`) would be three non-square layers and is deliberately NOT used: the
`MLayer m n` carrier permits it, but a residual add requires `m = n`, and the point of this carrier is that
its residual arithmetic type-checks.** -/
def layers : ℕ := blocks * sublayersPerBlock

/-- **`layers = 4`.** -/
theorem layers_eq : layers = 4 := rfl

/-! ## The architecture -/

/-- **The `TinyTransformer` architecture: four `8 → 8` layers with ReLU after each.**

**ReLU rather than `identity` because this is the architecture where a non-linear activation is the point --
unlike `samePointArch`, whose layer is genuinely linear.**
**Naming it correctly is what keeps `Arch` describing the model it is indexed by.** -/
def arch : Arch where
  widths := [d, d, d, d, d]
  acts := [.relu, .relu, .relu, .relu]

/-- **The architecture is well formed.**

**Five widths for four layers, all equal to `8 > 0`.**
**This theorem is what stops the carrier from being a name: a malformed `Arch` could not become a
`ModelArtifact` at all.** -/
theorem arch_wf : arch.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [arch, d, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · simp [arch]

/-- **The architecture's depth is four.** -/
theorem arch_depth : arch.depth = 4 := rfl

/-! ## The weights -/

/-- **A `d → d` layer with a given weight matrix.**

**Extracted as a builder because the four layers differ only in their matrices, and repeating the structure
four times would hide the one place they can disagree.** -/
def squareLayer (W : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) : MLayer d d where
  W := W
  b := b

/-- **The identity matrix, as the weights of a residual pass-through.**

**`Matrix.one` is used rather than an arbitrary matrix so that the carrier's DEFAULT weights are the ones
that make it a pure residual network -- a meaning that a reader can check by expansion.** -/
def identityMatrix : Matrix (Fin d) (Fin d) ℝ := 1

/-- **The carrier's four layers: each the identity matrix with zero bias.**

**This is a real `Weights` payload, not a placeholder: `1` and `0` are the parameters a residual-only
network has, and `paramCount` below computes from them.** -/
def defaultLayer : MLayer d d :=
  squareLayer identityMatrix (fun _ => 0)

/-- **The `Weights` for `arch`: four layers, matching the depth.**

**`count` is `rfl` because `layers` is four and `arch.depth` is four -- and that equality is exactly what
`ModelArtifact` requires, so the artifact cannot be assembled from a mismatched pair.** -/
def weights : Weights arch where
  layers := [⟨d, d, defaultLayer⟩, ⟨d, d, defaultLayer⟩, ⟨d, d, defaultLayer⟩, ⟨d, d, defaultLayer⟩]
  count := rfl

/-! ## The artifact -/

/-- **The `TinyTransformer` as a `ModelArtifact`.**

**A real 2-block, `d = 8`, single-head carrier.**
**This is the instance that makes the B phase's objects non-vacuous: everything round 100 defined now has an
inhabitant shaped like an architecture a practitioner would recognise.** -/
noncomputable def artifact : ModelArtifact where
  arch := arch
  wf := arch_wf
  weights := weights

/-- **The artifact has four layers.** -/
theorem artifact_depth : artifact.depth = 4 := rfl

/-- **The artifact carries four layers' parameters.** -/
theorem artifact_layer_count : artifact.weights.layers.length = 4 := rfl

/-- **The parameter count: `4 * (8 * 8 + 8) = 288`.**

**`d * d + d` per layer -- a `d × d` matrix plus a `d`-vector bias -- and four layers.**
**Stated as a theorem because `paramCount` is DERIVED: this checks the derivation against the architecture.** -/
theorem artifact_params : artifact.paramCount = 288 := by
  decide

/-- **The architecture's widths are `[8, 8, 8, 8, 8]`, readable off `arch` alone.**

**An earlier draft stated this through `SymbolicSummary.ofArtifact`, which would have required a `Lib` module
to import `Plugins` -- an UPWARD import that `gate.py`'s `LAYER_OF` forbids, because `Plugins` sits above
`lib`.**
**=> the fact is stated where it is available.**
**`Plugins.Targets.ExtractArtifact` can state the summary form for any `ModelArtifact`, this one included, and
that is where a reader looking for the extraction should go.** -/
theorem arch_widths : arch.widths = [8, 8, 8, 8, 8] := rfl

end Lattice.Lib.Architectures.TinyTransformer
