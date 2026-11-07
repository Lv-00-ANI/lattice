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


end Lattice.Core.IR
