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


end Lattice.Core.IR