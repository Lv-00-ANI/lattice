import Mathlib
import Lattice.Core.IR.Decode

/-!
# `Core/IR/DecodeRelations.lean` -- the `argsCode` and `partCode` decoders (round 210)

## What this file closes

Round 209 proved `partOfCode` but recorded that `argsCode`'s decoder did not close, with the exact obstacle:

> after `rw [Nat.add_sub_cancel]` the goal still contains the recursive call under a `map`, and neither `dsimp` nor
> the induction hypothesis reaches it because the `let`-bound component is not yet reduced.

**=> the fix is to make the GUARD'S SHAPE match the `if`'s test BEFORE unfolding:**
**`argsCode ((t, ix) :: ps)` is replaced by its unfolded form `Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode ps)`
with an explicit `rfl` rewrite, and only THEN is `dif_neg` applied.**

**Round 209's attempt applied `simp only [argsCode, …]` in one step, which left the guard and the test in different
shapes and made `dif_neg` inapplicable.**

## The composition `relationShapeCode` needs

`relationShapeCode r = Nat.pair (Nat.pair (kindCode r.kind)
                                         (Nat.pair (argsCode r.args) (partCode r.part))) 0`

| component | inverse | where |
|:--|:--|:--|
| **`kindCode`** | **`kindOfCode` / `kindOfCode_kindCode`** | **`Decode.lean`, round 208** |
| **`argsCode`** | **`decodeArgs` / `decodeArgs_code`** | **this file** |
| **`partCode`** | **`partOfCode` / `partOfCode_partCode`** | **this file** |

## What is proved

| theorem | content |
|:--|:--|
| **`partOfCode`** | **the `Option PartKind` inverse** |
| **`partOfCode_partCode`** | **`partOfCode (partCode p) = p`** |
| **`decodeArgsAux`** | **the fuel-driven `argsCode` decoder** |
| **`decodeArgsAux_code`** | **`xs.length ≤ k -> decodeArgsAux k (argsCode xs) = some xs`** |
| **`decodeArgs_ge_length`** | **`xs.length ≤ argsCode xs`** |
| **`decodeArgs`** | **self-fuelled: the code is its own budget** |
| **`decodeArgs_code`** | **`decodeArgs (argsCode xs) = some xs`** |
| **`decodeRelationShape`** | **the three components composed** |
| **`decodeRelationShape_code`** | **`decodeRelationShape (relationShapeCode r) = some r`** |

## What this file does NOT do

**It does not provide the LIST layer over `relationShapeCode`.**

**That is the same construction as `decodeTensorList` in `Decode.lean` (round 208), and it is the last step before
`decodeSkeleton` itself.**
**=> stopping here keeps every theorem in this file proved, and the remaining step is named rather than stubbed.**
-/

set_option maxHeartbeats 800000

namespace Lattice.Core.IR

/-- **THE `Option PartKind` INVERSE OF `partCode`.**

`partCode` writes `Nat.pair 0 0` for `none` and `Nat.pair 1..3 0` for the three kinds.

**=> `partOfCode` reads the tag; tags above 3 give `none`, which `partCode` never writes.** -/
def partOfCode (n : ℕ) : Option PartKind :=
  match (Nat.unpair n).1 with
  | 1 => some PartKind.vocab
  | 2 => some PartKind.arch
  | 3 => some PartKind.shared
  | _ => none

/-- **`partOfCode` INVERTS `partCode`.** -/
theorem partOfCode_partCode (p : Option PartKind) : partOfCode (partCode p) = p := by
  cases p with
  | none => simp [partCode, partOfCode, Nat.unpair_pair]
  | some k =>
    cases k with
    | vocab => simp [partCode, partOfCode, Nat.unpair_pair]
    | arch => simp [partCode, partOfCode, Nat.unpair_pair]
    | shared => simp [partCode, partOfCode, Nat.unpair_pair]

/-- **DECODE A LIST OF RELATION ARGUMENTS FROM `argsCode`, fuel-driven.**

`argsCode` writes `0` for empty and `Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode rest)` otherwise.

**=> one `unpair` gives the inner pair plus one, and the tail; a second gives `(t, the index list's code)`, which
`decodeList` turns into the indices.**
**`fuel` removes the termination obligation, exactly as in `decodeListAux` and `decodeTensorListAux`.** -/
def decodeArgsAux : (fuel : ℕ) → ℕ → Option (List (TensorId × List ℕ))
  | 0, n => if _h : n = 0 then some [] else none
  | k + 1, n =>
    if _h : n = 0 then some []
    else
      let u := Nat.unpair n
      if _hu : u.1 = 0 then none
      else
        let inner := Nat.unpair (u.1 - 1)
        (decodeArgsAux k u.2).map (fun rest => (inner.1, decodeList inner.2) :: rest)

/-- **THE ROUND TRIP FOR `argsCode`.**

**`xs.length ≤ k -> decodeArgsAux k (argsCode xs) = some xs`.**

**The `cons` case replaces `argsCode ((t, ix) :: ps)` by its UNFOLDED form with an explicit `rfl` rewrite FIRST,
so the guard and the `if`'s test have the same shape and `dif_neg` applies.**
**=> that ordering is the whole difference from round 209's failed attempt.** -/
theorem decodeArgsAux_code :
    ∀ (xs : List (TensorId × List ℕ)) (k : ℕ), xs.length ≤ k →
      decodeArgsAux k (argsCode xs) = some xs := by
  intro xs
  induction xs with
  | nil =>
    intro k _hk
    cases k with
    | zero =>
      show (if _h : (0:ℕ) = 0 then some [] else none) = some []
      rw [dif_pos rfl]
    | succ k => simp [decodeArgsAux, argsCode]
  | cons p ps ih =>
    intro k hk
    obtain ⟨t, ix⟩ := p
    cases k with
    | zero => simp at hk
    | succ k =>
      have hcode : argsCode ((t, ix) :: ps) =
          Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode ps) := rfl
      rw [hcode]
      have hne : Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode ps) ≠ 0 := by
        have := Nat.left_le_pair (Nat.pair t (listCode ix) + 1) (argsCode ps)
        omega
      simp only [decodeArgsAux, dif_neg hne]
      have hinner : Nat.pair t (listCode ix) + 1 ≠ 0 := by omega
      simp only [Nat.unpair_pair]
      rw [dif_neg hinner]
      rw [Nat.add_sub_cancel]
      rw [ih k (by simp at hk; omega)]
      simp [decodeList_code]

/-- **THE CODE IS AT LEAST AS LONG AS THE ARGUMENT LIST.** -/
theorem decodeArgs_ge_length :
    ∀ xs : List (TensorId × List ℕ), xs.length ≤ argsCode xs
  | [] => by simp [argsCode]
  | (t, ix) :: ps => by
    have ih := decodeArgs_ge_length ps
    have hpos : 1 ≤ Nat.pair t (listCode ix) + 1 := by omega
    have hgt : argsCode ps < Nat.pair (Nat.pair t (listCode ix) + 1) (argsCode ps) :=
      pair_gt_snd (Nat.pair t (listCode ix) + 1) (argsCode ps) hpos
    simp only [List.length_cons, argsCode]
    omega

/-- **THE ARGUMENT DECODER WITH THE CODE AS ITS OWN BUDGET.** -/
def decodeArgs (n : ℕ) : Option (List (TensorId × List ℕ)) :=
  decodeArgsAux n n

/-- **THE ROUND TRIP FOR THE SELF-FUELLED ARGUMENT DECODER.** -/
theorem decodeArgs_code (xs : List (TensorId × List ℕ)) :
    decodeArgs (argsCode xs) = some xs := by
  unfold decodeArgs
  exact decodeArgsAux_code xs (argsCode xs) (decodeArgs_ge_length xs)


/-! ## The relation-shape decoder

`relationShapeCode r = Nat.pair (Nat.pair (kindCode r.kind)
                                         (Nat.pair (argsCode r.args) (partCode r.part) + 1)) 0`

**The `+1` sits on the INNER pair, not on `argsCode`.**

**=> the decoder reads the outer pair, then the middle pair, then subtracts the `+1` BEFORE the third `unpair`.**
**Rounds 209 and 210 both placed the `+1` one level too high, and every subsequent step failed for that reason;
`hcode`'s `rfl` is what finally pinned the position down.** -/

/-- **DECODE A `RelationShape` FROM ITS `relationShapeCode`.**

**One `unpair` for the outer pair (its second component is the discarded `0`), one for the middle pair (giving
`kindCode` and the `+1`-patched inner pair), then the `+1` is subtracted and a third `unpair` gives `argsCode` and
`partCode`.** -/
def decodeRelationShape (code : ℕ) : Option RelationShape :=
  if _h : code = 0 then none
  else
    let outer := Nat.unpair code
    let mid := Nat.unpair outer.1
    if _hb : mid.2 = 0 then none
    else
      let rest := Nat.unpair (mid.2 - 1)
      (decodeArgs rest.1).map
        (fun args => (⟨kindOfCode mid.1, args, partOfCode rest.2⟩ : RelationShape))

set_option maxHeartbeats 400000 in
/-- **THE ROUND TRIP FOR relationShapeCode.**

decodeRelationShape (relationShapeCode r) = some r.

The proof pins the encoding shape with hcode first, then discharges the two if guards,
subtracts the +1, and applies the three component inverses.
maxHeartbeats is raised because the three nested Nat.pair terms make elaboration slow.
-/
theorem decodeRelationShape_code (r : RelationShape) :
    decodeRelationShape (relationShapeCode r) = some r := by
  obtain ⟨kind, args, part⟩ := r
  have hcode : relationShapeCode ⟨kind, args, part⟩ =
      Nat.pair (Nat.pair (kindCode kind) (Nat.pair (argsCode args) (partCode part) + 1)) 0 := by
    unfold relationShapeCode
    rfl
  rw [hcode]
  unfold decodeRelationShape
  -- The outer guard: the code is a `Nat.pair` with its first component at least 1.
  have hne : Nat.pair (Nat.pair (kindCode kind) (Nat.pair (argsCode args) (partCode part) + 1)) 0 ≠ 0 := by
    have h1 : 1 ≤ Nat.pair (kindCode kind) (Nat.pair (argsCode args) (partCode part) + 1) := by
      have := Nat.right_le_pair (kindCode kind) (Nat.pair (argsCode args) (partCode part) + 1)
      omega
    have := pair_gt_snd _ 0 h1
    omega
  rw [dif_neg hne]
  simp only [Nat.unpair_pair]
  -- The inner guard: the `+1`-patched pair is non-zero.
  have hpos : Nat.pair (argsCode args) (partCode part) + 1 ≠ 0 := by omega
  rw [dif_neg hpos]
  rw [Nat.add_sub_cancel]
  -- The three component inverses.
  simp [decodeArgs_code, kindOfCode_kindCode, partOfCode_partCode]

/-! ## The relation-list layer

**`shapesCode relationShapeCode` has the same fold as `shapesCode tensorShapeCode`: `0` for empty,
`Nat.pair (f x + 1) _` otherwise.**
**=> the list decoder repeats `decodeTensorListAux`, with `decodeRelationShape` as the per-item decoder.** -/

/-- **DECODE A LIST OF RELATION SHAPES, fuel-driven.** -/
def decodeRelListAux : (fuel : ℕ) → ℕ → Option (List RelationShape)
  | 0, n => if _h : n = 0 then some [] else none
  | k + 1, n =>
    if _h : n = 0 then some []
    else
      let u := Nat.unpair n
      if _hu : u.1 = 0 then none
      else
        match decodeRelationShape (u.1 - 1) with
        | none => none
        | some t =>
          match decodeRelListAux k u.2 with
          | none => none
          | some ts => some (t :: ts)

/-- **THE ROUND TRIP FOR `shapesCode relationShapeCode`.**

**`xs.length ≤ k -> decodeRelListAux k (shapesCode relationShapeCode xs) = some xs`.** -/
theorem decodeRelListAux_code :
    ∀ (xs : List RelationShape) (k : ℕ), xs.length ≤ k →
      decodeRelListAux k (shapesCode relationShapeCode xs) = some xs := by
  intro xs
  induction xs with
  | nil =>
    intro k _hk
    cases k with
    | zero =>
      show (if _h : (0:ℕ) = 0 then some [] else none) = some []
      rw [dif_pos rfl]
    | succ k => simp [decodeRelListAux, shapesCode]
  | cons t ts ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      show (if _h : shapesCode relationShapeCode (t :: ts) = 0 then some []
              else
                let u := Nat.unpair (shapesCode relationShapeCode (t :: ts))
                if _hu : u.1 = 0 then none
                else
                  match decodeRelationShape (u.1 - 1) with
                  | none => none
                  | some t' =>
                    match decodeRelListAux k u.2 with
                    | none => none
                    | some ts' => some (t' :: ts')) = some (t :: ts)
      have hne : shapesCode relationShapeCode (t :: ts) ≠ 0 := by
        simp only [shapesCode]
        have := Nat.left_le_pair (relationShapeCode t + 1) (shapesCode relationShapeCode ts)
        omega
      rw [dif_neg hne]
      simp only [decodeRelListAux, shapesCode, Nat.unpair_pair]
      have hsucc : relationShapeCode t + 1 ≠ 0 := by omega
      rw [dif_neg hsucc]
      rw [Nat.add_sub_cancel]
      rw [decodeRelationShape_code t]
      simp only [decodeRelListAux]
      rw [ih k (by simp at hk; omega)]

/-- **THE CODE IS AT LEAST AS LONG AS THE RELATION LIST.** -/
theorem shapesCode_rel_ge_length :
    ∀ xs : List RelationShape, xs.length ≤ shapesCode relationShapeCode xs
  | [] => by simp [shapesCode]
  | t :: ts => by
    have ih := shapesCode_rel_ge_length ts
    have hgt : shapesCode relationShapeCode ts <
        Nat.pair (relationShapeCode t + 1) (shapesCode relationShapeCode ts) :=
      pair_gt_snd (relationShapeCode t + 1) (shapesCode relationShapeCode ts) (by omega)
    simp only [List.length_cons, shapesCode]
    omega

/-- **THE RELATION LIST DECODER WITH THE CODE AS ITS OWN BUDGET.** -/
def decodeRelList (n : ℕ) : Option (List RelationShape) :=
  decodeRelListAux n n

/-- **THE ROUND TRIP FOR THE SELF-FUELLED RELATION LIST DECODER.** -/
theorem decodeRelList_code (xs : List RelationShape) :
    decodeRelList (shapesCode relationShapeCode xs) = some xs := by
  unfold decodeRelList
  exact decodeRelListAux_code xs (shapesCode relationShapeCode xs) (shapesCode_rel_ge_length xs)

/-! ## THE SKELETON DECODER -- the composition all the above was for

`skeletonCode k = Nat.pair (shapesCode tensorShapeCode k.tensors + 1)
                            (shapesCode relationShapeCode k.relations)`

**=> decoding is: split the outer pair, subtract the `+1` patch, decode the tensor list, decode the relation list,
rebuild.**
**No component is new: every per-item and list decoder below was proved in an earlier step.** -/

/-- **DECODE AN `IRSkeleton` FROM ITS `skeletonCode`.** -/
def decodeSkeleton (code : ℕ) : Option IRSkeleton :=
  if _h : code = 0 then none
  else
    let outer := Nat.unpair code
    if _hu : outer.1 = 0 then none
    else
      match decodeTensorList (outer.1 - 1) with
      | none => none
      | some ts =>
        match decodeRelList outer.2 with
        | none => none
        | some rs => some ⟨ts, rs⟩

set_option maxHeartbeats 800000 in
/-- THE SKELETON ROUND TRIP -- the inverse `extract` was missing.

`decodeSkeleton (skeletonCode k) = some k`.

The proof splits the pair, subtracts the `+1`, and hands each component to its own decoder, which already has its
round trip.
`maxHeartbeats` is raised because `skeletonCode` nests the whole list encoding inside two `Nat.pair`s and the
elaboration of the `match` on `Option` is expensive at the default budget.
-/
theorem decodeSkeleton_code (k : IRSkeleton) : decodeSkeleton (skeletonCode k) = some k := by
  obtain ⟨ts, rs⟩ := k
  have hcode : skeletonCode ⟨ts, rs⟩ =
      Nat.pair (shapesCode tensorShapeCode ts + 1) (shapesCode relationShapeCode rs) := by
    unfold skeletonCode
    rfl
  rw [hcode]
  unfold decodeSkeleton
  have hne : Nat.pair (shapesCode tensorShapeCode ts + 1) (shapesCode relationShapeCode rs) ≠ 0 := by
    have := Nat.left_le_pair (shapesCode tensorShapeCode ts + 1) (shapesCode relationShapeCode rs)
    omega
  rw [dif_neg hne]
  simp only [Nat.unpair_pair]
  have hsucc : shapesCode tensorShapeCode ts + 1 ≠ 0 := by omega
  rw [dif_neg hsucc]
  rw [Nat.add_sub_cancel]
  rw [decodeTensorList_code, decodeRelList_code]

end Lattice.Core.IR

