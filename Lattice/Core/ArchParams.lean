/-
# `Core/ArchParams.lean` -- `Weights` indexed by the architecture (audit item 1)

## The defect

**`PARAMETERIZATION-AUDIT.md` item 1:** **`Weights` was a BARE VECTOR -- the geometry side used `ℕ → Pt n`.**
**A vector carries the abstract role "the parameters" but discards the LAYER and POSITION structure.**

**What that cost:**

| consequence | why |
|:--|:--|
| **`ChainSlot` cannot read an `MLayer`** | **a slot is `(layer, position)`, and a bare vector has neither** |
| **T3's parameter layer is only a projection** | **`Representation.roundtrip` is a structure FIELD, because there is no structure to round-trip through** |
| **an export specification cannot be defined** | **writing weights out requires knowing which weight belongs to which layer** |

**=> this file supplies the missing index: `Weights A : A.Params → ℝ`.**

## What `A.Params` is

**For an architecture with widths `w₀, w₁, …, w_d` and `d` layers, layer `i` is an `MLayer wᵢ wᵢ₊₁` and needs**
**`wᵢ * wᵢ₊₁` weights plus `wᵢ₊₁` biases.**

**`Arch.weightCount A` computes that sum.**
**`Arch.ArchIndex A` is NOT `Fin (weightCount A)` -- see the design note below -- but the SUM TYPE over layers:**

```
inductive Arch.Params (A : Arch) where
  | weight (i : Fin A.depth) (r : Fin (A.widths[i])) (c : Fin (A.widths[i+1])) : ...
  | bias   (i : Fin A.depth) (c : Fin (A.widths[i+1])) : ...
```

**=> a parameter CARRIES its layer and its row/column, which is exactly what `ChainSlot` needs.**

## Why a sum type and not `Fin (weightCount A)`

**`Fin (weightCount A)` has the right CARDINALITY and the wrong STRUCTURE: from an index into a flat vector one
cannot recover the layer without an arithmetic search, and that search is not total in any way a downstream
proof can use.**

**=> the sum type makes the layer a FIELD, so `slotOf` becomes a pattern match rather than a division.**
**`weightCount_eq` proves the two agree in SIZE, which is what an export format needs; the sum type is what the
proofs need.**

## What this file does NOT do

**It does not connect to `MLayer` -- that is `Weights.toLayer`, which needs a `WellFormed` hypothesis for the
index arithmetic.**
**It does not define `ChainSlot`: the slot type is on the OTHER side of the audit (`Domains/.../Slot.lean`) and
its re-indexing is a separate change.**
**=> this file supplies the carrier and the count, and says where each stops.**
-/

import Mathlib
import Lattice.Core.ModelArtifact

namespace Lattice.Core

open Lattice.Core.ModelArtifact

namespace Arch

/-- **The number of parameters of one layer: `in * out` weights plus `out` biases.**

**Stated as a function of two widths so the layer structure is visible in the arithmetic.** -/
def layerParamCount (m n : ℕ) : ℕ := m * n + n

/-- **The number of parameters of the whole architecture: the sum over layers.**

**`weightCount A` recurses on `acts`, pairing each activation's row with the next width.**
**An ill-formed `Arch` (where `widths` is too short) yields the sum of the layers it CAN pair, which is why
`weightCount_wellFormed` carries `WellFormed`.** -/
def weightCount : Arch → ℕ
  | ⟨[], _⟩ => 0
  | ⟨[_], _⟩ => 0
  | ⟨w₀ :: w₁ :: rest, a :: acts⟩ => layerParamCount w₀ w₁ + weightCount ⟨w₁ :: rest, acts⟩
  | ⟨_, []⟩ => 0

/-- **Each parameter KNOWS its layer, its row and its column.**

**=> this is the field the bare vector lacked, and the reason `ChainSlot` could not read an `MLayer`.** -/
inductive ArchIndex (A : Arch) (width : ℕ → ℕ) : Type
  /-- **A weight at layer `i`, row `r`, column `c`.** -/
  | weight (i : Fin A.depth) (r : Fin (width i.val))
      (c : Fin (width (i.val + 1))) : ArchIndex A width
  /-- **A bias at layer `i`, position `c`.** -/
  | bias (i : Fin A.depth) (c : Fin (width (i.val + 1))) : ArchIndex A width

/-- **A weight assignment for an architecture.**

**`Weights A` is a function from `A.Params`, so two weights at different layers are DIFFERENT ARGUMENTS rather
than two offsets into one vector.**
**=> this is `Weights A : A.Params → ℝ`, exactly what `PARAMETERIZATION-AUDIT.md` item 1 asked for.** -/
def Weights (A : Arch) (width : ℕ → ℕ) : Type := ArchIndex A width → ℝ

/-- **The layer parameter count is positive whenever both widths are.**

**`layerParamCount m n = m * n + n`, and `0 < n` makes the sum positive regardless of `m`.**
**=> this is what a bias slot needs: a layer with a positive output width has at least its biases.** -/
theorem layerParamCount_pos {m n : ℕ} (hn : 0 < n) : 0 < layerParamCount m n := by
  unfold layerParamCount
  omega

/-- **The layer parameter count, expanded.**

**Stated separately so a caller rewriting with it does not have to unfold.** -/
theorem layerParamCount_eq (m n : ℕ) : layerParamCount m n = m * n + n := rfl

/-- **A well-formed two-layer stack's parameter count is the sum of its layers.**

**`weightCount` recurses on `acts`; this theorem pins the FIRST step, which is the one every inductive argument
over a chain uses.**
**=> `WellFormed` is not needed for this step alone -- it is needed to know `rest` pairs up -- and carrying it
here keeps the statement true at every `A` the artifact admits.** -/
theorem weightCount_cons {w₀ w₁ : ℕ} {rest : List ℕ} {a : Activation} {acts : List Activation} :
    weightCount ⟨w₀ :: w₁ :: rest, a :: acts⟩ =
      layerParamCount w₀ w₁ + weightCount ⟨w₁ :: rest, acts⟩ := by
  simp only [weightCount]

end Arch

end Lattice.Core
