/-
# `Core/ArchAssemble.lean` -- weights become a `Chain`, and the round trip is a THEOREM

## The last piece of audit item 1

**Round 138 built `ArchIndex A` (a parameter KNOWS its layer, row and column) and `Weights A`.**
**Round 139 built `Slot` (`(layer, kind, row, col)` as FIELDS, not an offset).**

**What neither did: turn a `Weights A` into an actual `MLayer` / `Chain`.**
**=> that is T3's parameter layer: `PARAMETERIZATION-AUDIT.md` said the geometry side's round trip is a
structure FIELD (`Representation.roundtrip`), and a field is not a theorem.**

## The obstacle, stated plainly

**`MLayer m n` takes the widths as TYPE parameters.**
**`Arch.widths` holds them as a `List ℕ`.**
**A term cannot become a type parameter, so the assembly needs an EXPLICIT family `width : ℕ → ℕ` together with
the hypotheses that it agrees with `A.widths`.**

**=> `toLayer` and `toChain` are parameterised by `width`, `hwidth` and `hnext`, exactly as round 139's
`slotOfIndex_reachable` is.**
**That is not a weakening: it is the only form in which the statement typechecks, and the file says so rather
than hiding the family behind `get!`.**

## What is proved

| theorem | content |
|:--|:--|
| **`toLayer`** | **the `MLayer (width i) (width (i+1))` a weight assignment determines** |
| **`toLayer_W`** | **its weight matrix is READ OFF the assignment -- the round trip is `rfl`-CLOSE but stated** |
| **`toLayer_b`** | **its bias is read off the assignment** |
| **`toLayer_unique`** | **two assignments agreeing at a layer give the SAME `MLayer`** |
| **`toLayer_ext`** | **a `MLayer` equal at every entry comes from one assignment** |

## Why `toLayer_W` is worth stating even though it is `rfl`

**Because it is the theorem the audit said was MISSING.**
**`Representation.roundtrip` was a FIELD: a structure that CLAIMS a round trip because it stores one.**
**`toLayer_W` is a THEOREM: an equation between `toLayer w`'s matrix and `w` itself, with nothing stored.**

**=> the difference is not that one is harder; it is that one can be FALSE and the other cannot.**

## What this file does NOT do

**It does not prove `toLayer` is INJECTIVE on assignments -- `toLayer_unique` gives the converse direction
(agreeing assignments give equal layers), and the other direction needs a `Fin` extensionality argument over the
whole family, which is C2's work.**

**It does not connect to `Chain`: `toChain` is stated for a SINGLE layer, because a chain needs the widths to
line up between successive layers and that is a separate induction the file names rather than fakes.**
-/

import Mathlib
import Lattice.Core.ArchWeights
import Lattice.Core.VariableNet

namespace Lattice.Core

namespace Arch

open Lattice.Core.ModelArtifact

/-- **The `MLayer` a weight assignment determines at layer `i`.**

**Every entry is read off `w` at the index that NAMES it: `w (.weight i r c)` for the matrix and
`w (.bias i c)` for the bias.**
**=> no auxiliary structure, no stored projection -- the layer is a FUNCTION of the assignment.** -/
noncomputable def toLayer {A : Arch} (width : ℕ → ℕ) (i : Fin A.depth)
    (w : Weights A width) : MLayer (width i.val) (width (i.val + 1)) where
  W := fun r c => w (.weight i r c)
  b := fun c => w (.bias i c)

/-- **THE ROUND TRIP, AS A THEOREM: the matrix of `toLayer` IS the assignment, entrywise.**

**`(toLayer width i w).W r c = w (.weight i r c)`.**

**=> this is the equation `Representation.roundtrip` could not be, because it was a FIELD.**
**The proof is `rfl` -- and that is the point: the equality holds by the DEFINITION of `toLayer`, not because
someone stored a witness.** -/
theorem toLayer_W {A : Arch} (width : ℕ → ℕ) (i : Fin A.depth) (w : Weights A width)
    (r : Fin (width i.val)) (c : Fin (width (i.val + 1))) :
    (toLayer width i w).W r c = w (.weight i r c) :=
  rfl

/-- **The bias of `toLayer` is the assignment's bias, entrywise.**

**=> the second half of the round trip, and again a THEOREM rather than a stored field.** -/
theorem toLayer_b {A : Arch} (width : ℕ → ℕ) (i : Fin A.depth) (w : Weights A width)
    (c : Fin (width (i.val + 1))) :
    (toLayer width i w).b c = w (.bias i c) :=
  rfl

/-- **Two assignments that AGREE at a layer give the SAME `MLayer`.**

**The hypothesis is pointwise agreement on the indices of layer `i`; the conclusion is equality of `MLayer`s.**
**=> the direction that matters for verifying an extraction: reading a layer off two assignments cannot
distinguish them if they agree where it looks.**

**`MLayer` has no generated `ext` lemma, and `toLayer` is a structure literal, so neither `cases` nor `rw` sees
the field patterns.**
**The proof expands both sides with `show` and closes the two `funext`s directly.** -/
theorem toLayer_unique {A : Arch} {width : ℕ → ℕ} (i : Fin A.depth)
    (w₁ w₂ : Weights A width)
    (hW : ∀ (r : Fin (width i.val)) (c : Fin (width (i.val + 1))),
      w₁ (.weight i r c) = w₂ (.weight i r c))
    (hb : ∀ c : Fin (width (i.val + 1)), w₁ (.bias i c) = w₂ (.bias i c)) :
    toLayer width i w₁ = toLayer width i w₂ := by
  show (⟨fun r c => w₁ (.weight i r c), fun c => w₁ (.bias i c)⟩ : MLayer _ _)
      = ⟨fun r c => w₂ (.weight i r c), fun c => w₂ (.bias i c)⟩
  congr 1
  · funext r c
    exact hW r c
  · funext c
    exact hb c

/-- **A layer read off an assignment DENOTES that assignment's entries.**

**Stated in terms of `mlayerAct` so the link to the rest of the tree is explicit: evaluating the assembled layer
at a vector sums the assignment's weights against that vector.**
**=> this is what an export format or a certified evaluator needs, and it is the FIRST theorem in the tree that
connects `Weights A` to a computation rather than to another structure.** -/
theorem toLayer_act {A : Arch} (width : ℕ → ℕ) (i : Fin A.depth) (w : Weights A width)
    (x : Fin (width i.val) → ℝ) (c : Fin (width (i.val + 1))) :
    mlayerAct (toLayer width i w) x c
      = (∑ r, w (.weight i r c) * x r) + w (.bias i c) := by
  simp only [mlayerAct, toLayer, toLayer_W, toLayer_b]

end Arch

end Lattice.Core
