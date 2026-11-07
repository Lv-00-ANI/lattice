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

/-- **THE `RelKind` INVERSE OF `kindCode`.**

**`kindCode` writes `Nat.pair tag 0` for the fifteen nullary tags and `Nat.pair 15 n` for `other n`.**
**=> `kindOfCode` reads the tag from the pair's first component and, for tag `15`, the payload from the second.**
**Tags above 15 fall to `other`, which is the honest total answer: `kindCode` never writes them, so a value produced
by a real skeleton always decodes exactly.** -/
def kindOfCode (n : ℕ) : RelKind :=
  match (Nat.unpair n).1 with
  | 0 => RelKind.equal
  | 1 => RelKind.zero
  | 2 => RelKind.lowRank
  | 3 => RelKind.block
  | 4 => RelKind.symmetry
  | 5 => RelKind.depends
  | 6 => RelKind.ordered
  | 7 => RelKind.scaled
  | 8 => RelKind.transposed
  | 9 => RelKind.shared
  | 10 => RelKind.tokenOf
  | 11 => RelKind.merges
  | 12 => RelKind.specialToken
  | 13 => RelKind.contiguous
  | 14 => RelKind.sorted
  | _ => RelKind.other (Nat.unpair n).2

/-- **`kindOfCode` INVERTS `kindCode`.**

**`kindOfCode (kindCode k) = k`, by cases on `k`.**
**Each nullary tag reads back to itself (`Nat.unpair_pair` plus the tag's own branch), and `other n` reads `n` out of
the pair's second component.** -/
theorem kindOfCode_kindCode (k : RelKind) : kindOfCode (kindCode k) = k := by
  cases k with
  | equal => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | zero => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | lowRank => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | block => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | symmetry => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | depends => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | ordered => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | scaled => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | transposed => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | shared => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | tokenOf => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | merges => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | specialToken => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | contiguous => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | sorted => simp [kindCode, kindOfCode, Nat.unpair_pair]
  | other n => simp [kindCode, kindOfCode, Nat.unpair_pair]

/-- **DECODE A LIST OF TENSOR SHAPES, fuel-driven.**

**The per-item decoder is `decodeTensorShape` (already proved to invert `tensorShapeCode`), so this is the list layer
with a REAL per-item decoder rather than the identity -- which is what the withdrawn generic version lacked.**

**`fuel` removes the termination obligation, exactly as in `decodeListAux`.** -/
def decodeTensorListAux : (fuel : ℕ) → ℕ → Option (List TensorShape)
  | 0, n => if _h : n = 0 then some [] else none
  | k + 1, n =>
    if _h : n = 0 then some []
    else
      let u := Nat.unpair n
      if _hu : u.1 = 0 then none
      else
        match decodeTensorShape (u.1 - 1) with
        | none => none
        | some t =>
          match decodeTensorListAux k u.2 with
          | none => none
          | some ts => some (t :: ts)

/-- **THE ROUND TRIP FOR THE TENSOR LIST.**

**`xs.length ≤ k -> decodeTensorListAux k (shapesCode tensorShapeCode xs) = some xs`.**

**=> an induction on `xs` and then on `k`, using `decodeTensorShape_code` for the head and the induction hypothesis
for the tail.**
**The `+1` patch makes the `if` guards discharge: `Nat.pair (tensorShapeCode t + 1) _ ≠ 0`.** -/
theorem decodeTensorListAux_code :
    ∀ (xs : List TensorShape) (k : ℕ), xs.length ≤ k →
      decodeTensorListAux k (shapesCode tensorShapeCode xs) = some xs := by
  intro xs
  induction xs with
  | nil =>
    intro k _hk
    cases k with
    | zero =>
      show (if _h : (0:ℕ) = 0 then some [] else none) = some []
      rw [dif_pos rfl]
    | succ k => simp [decodeTensorListAux, shapesCode]
  | cons t ts ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      show (if _h : shapesCode tensorShapeCode (t :: ts) = 0 then some []
              else
                let u := Nat.unpair (shapesCode tensorShapeCode (t :: ts))
                if _hu : u.1 = 0 then none
                else
                  match decodeTensorShape (u.1 - 1) with
                  | none => none
                  | some t' =>
                    match decodeTensorListAux k u.2 with
                    | none => none
                    | some ts' => some (t' :: ts')) = some (t :: ts)
      have hne : shapesCode tensorShapeCode (t :: ts) ≠ 0 := by
        simp only [shapesCode]
        have := Nat.left_le_pair (tensorShapeCode t + 1) (shapesCode tensorShapeCode ts)
        omega
      rw [dif_neg hne]
      simp only [decodeTensorListAux, shapesCode, Nat.unpair_pair]
      have hsucc : tensorShapeCode t + 1 ≠ 0 := by omega
      rw [dif_neg hsucc]
      rw [Nat.add_sub_cancel]
      rw [decodeTensorShape_code t]
      simp only [decodeTensorListAux]
      rw [ih k (by simp at hk; omega)]

/-- **THE CODE IS AT LEAST AS LONG AS THE TENSOR LIST.** -/
theorem shapesCode_tensor_ge_length :
    ∀ xs : List TensorShape, xs.length ≤ shapesCode tensorShapeCode xs
  | [] => by simp [shapesCode]
  | t :: ts => by
    have ih := shapesCode_tensor_ge_length ts
    have hgt : shapesCode tensorShapeCode ts <
        Nat.pair (tensorShapeCode t + 1) (shapesCode tensorShapeCode ts) :=
      pair_gt_snd (tensorShapeCode t + 1) (shapesCode tensorShapeCode ts) (by omega)
    simp only [List.length_cons, shapesCode]
    omega

/-- **THE TENSOR LIST DECODER WITH THE CODE AS ITS OWN BUDGET.** -/
def decodeTensorList (n : ℕ) : Option (List TensorShape) :=
  decodeTensorListAux n n

/-- **THE ROUND TRIP FOR THE SELF-FUELLED TENSOR LIST DECODER.** -/
theorem decodeTensorList_code (xs : List TensorShape) :
    decodeTensorList (shapesCode tensorShapeCode xs) = some xs := by
  unfold decodeTensorList
  exact decodeTensorListAux_code xs (shapesCode tensorShapeCode xs)
    (shapesCode_tensor_ge_length xs)

end Lattice.Core.IR


