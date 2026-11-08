import Mathlib
import Lattice.Core.IR.Skeleton
import Lattice.Core.IR.Basic
import Lattice.Core.IR.Depends

/-!
# `Core/IR/Materialize.lean` -- producing `Tensor.data` from a skeleton (round 197, P1-4)

## The gap this closes

`Tensor.data : Fin shape.prod -> Real` has NO finite code, which is why round 180 factored an IR into a codeable
SKELETON plus numeric content.

**That factoring left a question the IR layer had not answered: given a skeleton, does an IR with that skeleton
EXIST?**

**=> "existential over `data`" is not obvious, because `data`'s type depends on `shape`'s product, and a skeleton
fixes `shape` only as a `List Nat`.**

**This file answers it: YES, and the witness is the ZERO field.**

## Why the zero field is the right witness, and not a placeholder

**A skeleton says WHICH tensors exist and WHAT their extents are. It says NOTHING about their values.**
**=> any `data` of the right type is equally consistent with the skeleton, and the zero field is the canonical one.**

**The honest reading: this file proves EXISTENCE, which is what `IsIR`'s covering condition needs.**
**It does not claim the zero field is the RIGHT data for a particular model -- that is `compile`'s job, and
`compile` produces numbers from the structure rather than reading them.**

**=> the distinction matters: an existence proof with the zero witness is a theorem about the SHAPE's consistency,
not a claim that models have zero weights.**

## What is proved

| theorem | content |
|:--|:--|
| **`zerosOf`** | **a tensor of the given shape, whose entries are all zero** |
| **`output`** | **producing data preserves id and shape** |
| **`fillZeros`** | **a whole skeleton's tensor list, materialised** |
| **`materialize_empty`** | **the empty skeleton materialises to an empty relation IR** |
| **`skeleton_of_fillZeros`** | **the skeleton of a materialised list IS the original list** |

## What this file does NOT do

**It does not produce `Relation.hold` witnesses.**

**A `Relation` carries a proof that its predicate holds, and whether `equal`/`zero`/`depends` holds of the zero data
is a NUMERIC question that depends on the `read` and `dep` contexts.**
**=> the relations of a materialised IR are EMPTY here, and that is honest: a structure whose values are all zero
satisfies `zero` relations only for the positions that really are zero, and asserting more would be false.**

**The consequence: `materialize` produces an IR whose tensors are the skeleton's and whose relations are none.**
**That is the IR a skeleton alone justifies, and `compile`/`parse` add relations when they have proof.**
-/

namespace Lattice.Core.IR

/-- **A tensor of the given shape whose entries are ALL ZERO.**

**The witness for "`data` exists for this shape": `data`'s type is `Fin shape.prod -> Real`, and the constant zero
function has that type for every shape.** -/
def zerosOf (s : TensorShape) : Tensor where
  id := s.id
  shape := s.shape
  data := fun _ => 0

/-- **`readOf ts id ix`: the value a position holds.**

Looks `id` up in `ts` and reads its single-axis index. An absent tensor, an out-of-range index, or a multi-axis index
all read as `0`.

=> `readOf` is TOTAL, and this docstring says exactly where the zeros are CONVENTIONAL rather than data. -/
def readOf (ts : List Tensor) : TensorId → List ℕ → ℝ :=
  fun id ix =>
    match ts.find? (fun t => t.id = id) with
    | none => 0
    | some t =>
      match ix with
      | [i] => if h : i < t.shape.prod then t.data ⟨i, h⟩ else 0
      | _ => 0

/-- **A list whose tensors all carry zero data reads as zero everywhere.**

This is the lemma that makes the skeleton-alone IR's covering condition vacuous, and it is stated for ANY such list
so a caller can apply it without knowing how the list was built. -/
theorem readOf_zero_data (ts : List Tensor) (hzero : ∀ t ∈ ts, t.data = fun _ => (0 : ℝ)) :
    ∀ (id : TensorId) (ix : List ℕ), readOf ts id ix = 0 := by
  intro id ix
  unfold readOf
  split
  · rfl
  · rename_i t ht
    rw [hzero t (List.mem_of_find?_eq_some ht)]
    split <;> simp

/-- **PRODUCING DATA PRESERVES THE SKELETON'S INFORMATION.**

**`id` and `shape` are copied unchanged, so the materialised tensor's skeleton is the one it came from.**
**=> this is what makes `skeleton_of_fillZeros` below go through.**
**The `data` field is the ONLY thing added, which is the whole content of the factoring.** -/
theorem output (s : TensorShape) :
    (zerosOf s).id = s.id ∧ (zerosOf s).shape = s.shape :=
  ⟨rfl, rfl⟩

/-- **A skeleton's tensor list, materialised.** -/
def fillZeros (k : IRSkeleton) : List Tensor :=
  k.tensors.map zerosOf

/-- **THE SKELETON OF A MATERIALISED LIST IS THE ORIGINAL LIST.**

**`(fillZeros k).map (fun t => ⟨t.id, t.shape⟩) = k.tensors`.**

**=> materialising and then forgetting the numbers returns what we started with.**
**That is the property `skeleton_of_materialize` needs, and it holds by `map_map` plus the definition of
`zerosOf`.** -/
theorem skeleton_of_fillZeros (k : IRSkeleton) :
    (fillZeros k).map (fun t => (⟨t.id, t.shape⟩ : TensorShape)) = k.tensors := by
  unfold fillZeros
  rw [List.map_map]
  -- `(fun t => ⟨t.id, t.shape⟩) ∘ zerosOf` is the identity on `TensorShape`.
  have hid : ((fun t : Tensor => (⟨t.id, t.shape⟩ : TensorShape)) ∘ zerosOf) = id := by
    funext s
    rfl
  rw [hid, List.map_id]

/-- **MATERIALISING A SKELETON GIVES AN IR WITH ITS TENSORS AND NO RELATIONS.**

**The relations are empty because a `Relation` needs a `hold` proof, and the zero data justifies only the `zero`
relations at positions that really are zero.**
**=> this is the IR a skeleton ALONE justifies; `parse` and `compile` add relations when they can prove them.** -/
def materialize {H : RelKind → List (TensorId × List ℕ) → Prop} (k : IRSkeleton) :
    LatticeIR H where
  tensors := fillZeros k
  relations := []

/-- **THE MATERIALISED IR'S SKELETON IS THE ORIGINAL.**

**`(materialize k).tensors.length = k.tensors.length`, and its shapes agree pointwise.**
**=> the materialisation loses nothing about the STRUCTURE, which is what the factoring promised.** -/
theorem materialize_tensors_length {H : RelKind → List (TensorId × List ℕ) → Prop}
    (k : IRSkeleton) : (materialize (H := H) k).tensors.length = k.tensors.length := by
  unfold materialize fillZeros
  simp

/-- **THE EMPTY SKELETON MATERIALISES TO THE EMPTY IR.** -/
theorem materialize_empty {H : RelKind → List (TensorId × List ℕ) → Prop} :
    (materialize (H := H) ⟨[], []⟩).tensors = [] ∧
    (materialize (H := H) ⟨[], []⟩).relations = [] :=
  ⟨rfl, rfl⟩

/-- **EVERY SKELETON HAS A MATERIALISATION: the existential that `IsIR`'s covering condition needs.**

**`∃ (S : LatticeIR H), S.tensors.length = k.tensors.length`.**
**=> this is the honest existence statement: an IR with the given structure EXISTS, and its tensor count is the
skeleton's.**
**It does NOT say the relations are populated -- a skeleton alone cannot justify them.** -/
theorem materialize_exists {H : RelKind → List (TensorId × List ℕ) → Prop} (k : IRSkeleton) :
    ∃ S : LatticeIR H, S.tensors.length = k.tensors.length :=
  ⟨materialize k, materialize_tensors_length k⟩


/-! ## Supplying real data

`fillZeros` gives every tensor the constant-zero function, which makes `covered` VACUOUS -- there is no nonzero
reading for a relation to name.

**This section supplies the other half: a way to give each tensor REAL data, and the characterisation of when such a
structure is `covered`.**

**The design point: `Tensor.data : Fin shape.prod -> Real` has no finite encoding (round 194's observation), so no
function can COMPUTE it from the skeleton.**
**=> the data must be SUPPLIED, and this file takes a function `TensorShape -> Fin s.shape.prod -> Real` as that
supply.**
**The skeleton says WHICH tensors and WHAT their shapes are; the data function says what they hold.** -/

/-- **`fillWith k f`: the structure's tensors, with data supplied by `f`.**

**Each tensor keeps the skeleton's `id` and `shape`; only `data` comes from `f`.**
**=> `fillZeros` is the special case `f = fun _ _ => 0`.**

**The data function takes the TensorShape so it can look at `shape.prod` and produce a value of the right index
type.** -/
def fillWith (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ) : List Tensor :=
  k.tensors.map (fun s => { id := s.id, shape := s.shape, data := f s })

/-- **`fillZeros` IS `fillWith` AT THE ZERO FUNCTION.**

**=> the zero-data materialisation is not a separate design, it is this construction's degenerate case.** -/
theorem fillWith_zero (k : IRSkeleton) :
    fillWith k (fun _ _ => (0 : ℝ)) = fillZeros k := by
  unfold fillWith fillZeros zerosOf
  simp [List.map_map]

/- The faithfulness of fillWith is stated, not proved:

   t mem fillWith k f -> i < t.shape.prod ->
     readOf (fillWith k f) t.id [i] = f <t.id, t.shape> <i, _>

   The obstacle is List.find? : readOf searches the list for the tensor whose id matches,
   and the proof must show the search lands on t itself. That needs a
   find-returns-the-element-you-know-is-there lemma, which this tree lacks for id-indexed tensors.
   Recorded rather than shipping an unproved exact. -/

end Lattice.Core.IR
