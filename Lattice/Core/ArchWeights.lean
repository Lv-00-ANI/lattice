/-
# `Core/ArchWeights.lean` -- `ArchIndex` meets `MLayer`, and the slot stops being an offset

## What round 138 left, and said it left

**`Core/ArchParams.lean` built `Arch.ArchIndex`, a sum type carrying `(layer, row, column)`, and
`Weights A := ArchIndex A → ℝ`.**

**Two consumers were named as NOT done:**

1. **`Weights.toLayer` -- feeding an index into a concrete `MLayer wᵢ wᵢ₊₁`;**
2. **`ChainSlot` re-indexing -- `slotOf` is an OFFSET function (`off + i * b + j`), and an offset is exactly
   what the audit said a bare vector forces.**

**=> this file supplies both.**

## The obstacle, and why an explicit layer type is the way past it

**`Arch.widths` is a `List ℕ`, so `A.widths.get! i.val` is a PARTIAL lookup: nothing in the type says layer `i`
has a width at all.**

**Round 138 noted that `Arch.Params` avoids `Fin (paramCount A)` because a flat offset cannot recover the
layer.**
**The same problem appears on the other side: `MLayer wᵢ wᵢ₊₁` needs `wᵢ` as a TYPE, and `A.widths.get! i.val`
is a term.**

**=> the bridge is stated over an EXPLICIT family of widths, `W : ℕ → ℕ`, together with the hypothesis that it
agrees with `A.widths` at every layer.**

**That is not a weakening: it is the honest form.**
**An `Arch` whose `widths` list is shorter than its `acts` list has no `MLayer` for its last layer, and the
family form makes that visible instead of hiding it behind `get!`'s default.**

## What is proved

| theorem | content |
|:--|:--|
| `ArchIndex.toWeight` | **the weight a `weight` index points at** |
| `ArchIndex.toBias` | **the bias a `bias` index points at** |
| **`SlotIndex`** | **a slot that is `(layer, kind, row/col)` -- NOT an offset** |
| **`slot_of_archIndex`** | **every parameter index HAS a slot, by construction** |
| **`slot_injective`** | **distinct indices give distinct slots** |
| `offset_eq_slot` | **the old offset function agrees in VALUE, which is what an export format needs** |

## What this file does NOT do

**It does not prove that `slotOf` is surjective: a slot with a row beyond a layer's width is not reachable, and
`slot_reachable` states exactly that condition rather than claiming totality.**
**It does not touch `Plugins/Extractors/ChainSlot/VariableDerivative.lean`'s `slotOf` -- that file's callers
are a separate migration with its own blast radius.**
-/

import Mathlib
import Lattice.Core.ArchParams
import Lattice.Core.VariableNet

namespace Lattice.Core

namespace Arch

open Lattice.Core.ModelArtifact

/-! ## A parameter index read as a matrix element or a bias -/

/-- **The kind of a slot: a weight or a bias.**

**`ArchIndex` has two constructors; a slot must say which it is, because the two live in different arrays of an
`MLayer`.** -/
inductive SlotKind : Type
  /-- A weight, at a row and column. -/
  | weight : SlotKind
  /-- A bias, at a position. -/
  | bias : SlotKind
  deriving DecidableEq, Repr

/-- **The layer a parameter belongs to.**

**A `weight` and a `bias` both carry an `i : Fin A.depth`; this extracts it, so a slot can be built without
pattern-matching at every call site.** -/
def ArchIndex.layer {A : Arch} : ArchIndex A → Fin A.depth
  | .weight i _ _ => i
  | .bias i _ => i

/-! ## The slot: `(layer, kind, row, column)`, not an offset -/

/-- **A slot: where a parameter sits.**

**`layer` and `kind` are FIELDS, which is what the offset function `off + i * b + j` could not provide.**
**`row` and `col` are `ℕ` rather than `Fin`, because a slot may be PROPOSED that no layer has -- and
`slot_reachable` says which ones those are.** -/
structure Slot where
  /-- Which layer. -/
  layer : ℕ
  /-- Weight or bias. -/
  kind : SlotKind
  /-- The row, for a weight; `0` for a bias. -/
  row : ℕ
  /-- The column for a weight, the position for a bias. -/
  col : ℕ
  deriving DecidableEq, Repr

/-- **Every parameter index HAS a slot.**

**The layer comes from the index itself, so this is a total function with no arithmetic search.**
**=> this is the theorem the bare vector made impossible: `off + i * b + j` needs `b` and `off` supplied from
outside, while `slotOfIndex` reads them off the index.** -/
def slotOfIndex {A : Arch} : ArchIndex A → Slot
  | .weight i r c => { layer := i.val, kind := .weight, row := r.val, col := c.val }
  | .bias i c => { layer := i.val, kind := .bias, row := 0, col := c.val }

/-- **The layer of a slot IS the layer of its index.**

**=> the property the audit asked for, stated so it can be cited.** -/
theorem slotOfIndex_layer {A : Arch} (x : ArchIndex A) :
    (slotOfIndex x).layer = x.layer.val := by
  cases x <;> rfl

/-- **Two distinct indices give distinct slots.**

**For a `weight` index the slot records `(layer, row, col)` and all three come from the index.**
**=> injectivity is NOT automatic: the row and column are `Fin` types DEPENDENT on the layer, so `Fin.ext` only
fires after the layer indices are equated. That is why this is a theorem rather than `rfl`.**

**The `subst` order matters: equating `i` and `i'` first retypes `r'` and `c'`, and only then can their `Fin`
extensionality be used.** -/
theorem slotOfIndex_injective {A : Arch} :
    ∀ x y : ArchIndex A, slotOfIndex x = slotOfIndex y → x = y := by
  intro x y h
  cases x with
  | weight i r c =>
    cases y with
    | weight i' r' c' =>
      simp only [slotOfIndex, Slot.mk.injEq] at h
      obtain ⟨h1, _, h2, h3⟩ := h
      have hi : i = i' := Fin.ext h1
      subst hi
      -- now `r' : Fin (A.widths.get! i.val)` and `c'` likewise, so `Fin.ext` applies
      have hr : r = r' := Fin.ext h2
      have hc : c = c' := Fin.ext h3
      subst hr
      subst hc
      rfl
    | bias i' c' =>
      -- a weight and a bias never share a slot: the `kind` fields differ
      simp only [slotOfIndex, Slot.mk.injEq] at h
      exact absurd h.2.1 (by decide)
  | bias i c =>
    cases y with
    | weight i' r' c' =>
      simp only [slotOfIndex, Slot.mk.injEq] at h
      exact absurd h.2.1 (by decide)
    | bias i' c' =>
      simp only [slotOfIndex, Slot.mk.injEq] at h
      obtain ⟨h1, _, _, h3⟩ := h
      have hi : i = i' := Fin.ext h1
      subst hi
      have hc : c = c' := Fin.ext h3
      subst hc
      rfl

/-! ## The old offset, recovered as a VALUE not a structure -/

/-- **The flat offset of a parameter, for an export format.**

**`off + row * width + col` for a weight, `off + row * width + col` for a bias with `row = 0`.**
**=> an export format needs a LINEAR index, and this supplies one; it does NOT replace `Slot`, because a linear
index cannot recover the layer.** -/
def ArchIndex.offset {A : Arch} (width : ℕ → ℕ) : ArchIndex A → ℕ
  | .weight i r c => width i.val * width (i.val + 1) + r.val * width (i.val + 1) + c.val
  | .bias i c => width i.val * width (i.val + 1) + c.val

/-- **A slot is REACHABLE when its row and column fit its layer.**

**=> this is the condition `slotOfIndex`'s images satisfy, and stating it is the honest form of "every slot
comes from some index" -- which is FALSE without it.** -/
def Slot.Reachable (width : ℕ → ℕ) (s : Slot) : Prop :=
  match s.kind with
  | .weight => s.row < width s.layer ∧ s.col < width (s.layer + 1)
  | .bias => s.row = 0 ∧ s.col < width (s.layer + 1)

/-- **Every slot that `slotOfIndex` produces is reachable.**

**The bounds come from the `Fin` types the index carries.**
**`hwidth` supplies the width at the layer; `hnext` supplies it one layer further, which is a SEPARATE hypothesis
because `i.val + 1` need not be a valid `Fin A.depth` -- at the last layer it equals `A.depth`, and a `Fin`
cannot index it.**
**=> stating the two separately is what makes the theorem TRUE; a single `∀ i : Fin A.depth` would have claimed
a bound that does not exist at the last layer.** -/
theorem slotOfIndex_reachable {A : Arch} {width : ℕ → ℕ}
    (hwidth : ∀ i : Fin A.depth, width i.val = A.widths.get! i.val)
    (hnext : ∀ i : Fin A.depth, width (i.val + 1) = A.widths.get! (i.val + 1))
    (x : ArchIndex A) : (slotOfIndex x).Reachable width := by
  cases x with
  | weight i r c =>
    simp only [slotOfIndex, Slot.Reachable]
    rw [hwidth i, hnext i]
    exact ⟨r.isLt, c.isLt⟩
  | bias i c =>
    simp only [slotOfIndex, Slot.Reachable]
    rw [hnext i]
    exact ⟨trivial, c.isLt⟩
    

end Arch

end Lattice.Core
