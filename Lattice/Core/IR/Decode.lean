import Mathlib
import Lattice.Core.IR.Skeleton

/-!
# `Core/IR/Decode.lean` -- `decode : Nat -> Option IRSkeleton`, via fuel (round 206)

## The gap

`extractCode (W : IRWeights) : Option Nat := some (weightCodeIR W)` ALWAYS returns `some`, so it cannot be a
decoder.

**A real decoder must return `none` on codes that no skeleton produces.**

## Why fuel, and why that is not a retreat

**Round 204's design record proposed an `unpair`-based inverse with no fuel, on the grounds that `Nat.unpair` "is
available and not recursive".**
**Round 205 tried that (route A) and found the termination proof needs NONLINEAR arithmetic: `Nat.pair a b` is
`b*b + a` or `a*a + a + b` depending on `a < b`, and neither `omega` nor `nlinarith` crosses it cleanly.**

**=> route B, taken here: a `fuel` parameter. `decodeListAux 0 _ = []`, `decodeListAux (k+1) n` peels one `unpair`,
and NO termination proof is needed because the recursion is on `fuel`.**

**The cost is that `fuel` must be large enough; the round trip below shows `xs.length` always suffices.**
**The benefit is that the proof is an ordinary induction with no nonlinear step, which is why it goes through.**

## What is proved

| theorem | content |
|:--|:--|
| **`decodeListAux`** | **the fuel-driven list decoder** |
| **`decodeListAux_code`** | **`xs.length ≤ k -> decodeListAux k (listCode xs) = xs`** |
| **`decodeList`** | **the same with `fuel := xs.length`, a derived parameter** |
| **`decodeList_code`** | **`decodeList (listCode xs) = xs` -- the round trip** |

## What this file does NOT do

**It does not yet decode a whole `IRSkeleton`.**

**The list layer is the base case of that composition, and it is the layer whose round trip needed the fuel decision
to be made first.**
**=> the skeleton layer is the next step, and this file says so rather than shipping a `decodeSkeleton` whose round
trip is unproved.**
-/

namespace Lattice.Core.IR

/-- **Decode a `List Nat` from a code, given a FUEL budget.**

**`0` fuel gives `[]`; `k+1` fuel peels one `Nat.unpair` and recurses on `k`.**
**=> the recursion is on the fuel, so there is no termination obligation.**
**`0` as a code is the empty list, matching `listCode`'s empty branch.** -/
def decodeListAux : (fuel : ℕ) → ℕ → List ℕ
  | 0, _ => []
  | k + 1, n =>
    if _h : n = 0 then []
    else
      let u := Nat.unpair n
      (u.1 - 1) :: decodeListAux k u.2

/-- **THE ROUND TRIP FOR `listCode`, WITH A SUFFICIENT FUEL BUDGET.**

**`xs.length ≤ k -> decodeListAux k (listCode xs) = xs`.**

**=> the fuel is not a guess: the list's own length is always enough, because each `unpair` consumes one constructor.**
**The proof is an induction on `xs` and then on `k`, with no nonlinear arithmetic anywhere -- which is exactly what
route A could not achieve.** -/
theorem decodeListAux_code : ∀ (xs : List ℕ) (k : ℕ), xs.length ≤ k →
    decodeListAux k (listCode xs) = xs := by
  intro xs
  induction xs with
  | nil =>
    intro k _hk
    cases k with
    | zero => rfl
    | succ k => simp [decodeListAux, listCode]
  | cons x xs ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [decodeListAux, listCode]
      have hne : Nat.pair (x + 1) (listCode xs) ≠ 0 := by
        have := Nat.left_le_pair (x + 1) (listCode xs)
        omega
      rw [dif_neg hne]
      simp only [Nat.unpair_pair]
      rw [Nat.add_sub_cancel, ih k (by simp at hk; omega)]


/-- **`Nat.pair a b > b` FOR `a ≥ 1`.**

**This is the step that blocked rounds 204 and 205: `Nat.pair` is `b*b + a` when `a < b` and `a*a + a + b`
otherwise, and neither `omega` nor `nlinarith` crosses the `if` without it being unfolded first.**

**=> `unfold Nat.pair` then `by_cases` on the branch, and each side is an ordinary nonlinear inequality in plain
`Nat`s.**
**`a ≥ 1` is what makes both sides strict: in the first branch `b ≥ a ≥ 1` gives `b*b ≥ b`, and in the second `a*a +
a ≥ 1`.** -/
theorem pair_gt_snd (a b : ℕ) (ha : 1 ≤ a) : b < Nat.pair a b := by
  unfold Nat.pair
  by_cases hab : a < b
  · rw [if_pos hab]
    nlinarith
  · rw [if_neg hab]
    nlinarith

/-- **THE CODE IS ALWAYS AT LEAST AS LONG AS THE LIST IT ENCODES.**

**`xs.length ≤ listCode xs`.**

**=> this is the bound the self-fuelled decoder needs, and it is a strict comparison at each step:
`listCode (x :: xs) = Nat.pair (x+1) (listCode xs) > listCode xs` by `pair_gt_snd`, so the length grows by at least
one per constructor.**
**That is what makes `decodeList` (below) total without an explicit fuel argument.** -/
theorem listCode_ge_length : ∀ xs : List ℕ, xs.length ≤ listCode xs
  | [] => by simp [listCode]
  | x :: xs => by
    have ih := listCode_ge_length xs
    have hgt : listCode xs < Nat.pair (x + 1) (listCode xs) :=
      pair_gt_snd (x + 1) (listCode xs) (by omega)
    simp only [List.length_cons, listCode]
    omega

/-- **THE SELF-FUELLED DECODER: no explicit fuel argument.**

**`decodeList code := decodeListAux code code` -- the code is its own budget.**
**=> total on `Nat`, and `decodeList_code` shows it inverts `listCode`.** -/
def decodeList (n : ℕ) : List ℕ :=
  decodeListAux n n

/-- **THE ROUND TRIP FOR THE SELF-FUELLED DECODER.**

**`decodeList (listCode xs) = xs`.**

**=> `listCode_ge_length` supplies the budget `xs.length ≤ listCode xs` that `decodeListAux_code` demands, so this is
the composition of the two and nothing else.** -/
theorem decodeList_code (xs : List ℕ) : decodeList (listCode xs) = xs := by
  unfold decodeList
  exact decodeListAux_code xs (listCode xs) (listCode_ge_length xs)

/-- **A `TensorShape` DECODER, given the shape list already decoded.**

**`tensorShapeCode t = Nat.pair (Nat.pair t.id (listCode t.shape) + 1) 0`.**
**=> one `unpair` gives `(the inner pair + 1, a discarded 0)`, and a second gives `(id, the shape's code)`, which
`decodeList` turns into the shape itself.**
**The `+1` patch is why the inner component is subtracted: `tensorShapeCode` adds it to separate the empty template
from a real one.** -/
def decodeTensorShape (code : ℕ) : Option TensorShape :=
  if code = 0 then none
  else
    let outer := Nat.unpair code
    if outer.1 = 0 then none
    else
      let inner := Nat.unpair (outer.1 - 1)
      some ⟨inner.1, decodeList inner.2⟩

/-- **THE ROUND TRIP FOR `tensorShapeCode`.**

**`decodeTensorShape (tensorShapeCode t) = some t`.**

**=> the composition of `decodeList_code` with two `unpair`s, and the `if` guards are discharged by the `+1` patch:
`Nat.pair (t.id, shape's code) + 1 ≠ 0` always.** -/
theorem decodeTensorShape_code (t : TensorShape) :
    decodeTensorShape (tensorShapeCode t) = some t := by
  obtain ⟨tid, shape⟩ := t
  show decodeTensorShape (Nat.pair (Nat.pair tid (listCode shape) + 1) 0) = some ⟨tid, shape⟩
  unfold decodeTensorShape
  have hne : Nat.pair (Nat.pair tid (listCode shape) + 1) 0 ≠ 0 := by
    have := Nat.left_le_pair (Nat.pair tid (listCode shape) + 1) 0
    omega
  rw [if_neg hne]
  simp only [Nat.unpair_pair]
  have hne2 : Nat.pair tid (listCode shape) + 1 ≠ 0 := by omega
  rw [if_neg hne2]
  rw [Nat.add_sub_cancel]
  simp [decodeList_code]

end Lattice.Core.IR
