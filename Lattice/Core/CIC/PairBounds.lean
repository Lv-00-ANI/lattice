import Mathlib

/-!
# `Core/CIC/PairBounds.lean` -- the two `Nat.unpair` bounds, corrected (round 171)

## The correction

**Rounds 169 and 170 tried EIGHT times to prove**

```
unpair_snd_lt : 0 < n -> (Nat.unpair n).2 < n
```

**and failed every time.**

**Round 171 checked it empirically first:**

```
#eval (List.range 30).map (fun n => ((Nat.unpair n).2, n))
-- [(0,0), (1,1), (0,2), (1,3), (2,4), ...]
```

**=> at `n = 0` the second component is `0`, and at `n = 1` it is `1`.**
**=> the statement is FALSE as written, because the hypothesis `0 < n` is too weak.**

**With `2 <= n` it proves in two `nlinarith` calls.**

## Why this belongs in the record

**Round 148 established the rule "evaluate at concrete terms BEFORE writing the statement".**
**Round 171 applied it to `Nat.unpair`'s concrete values, and one `#eval` disproved a hypothesis that eight
rounds had assumed.**

**=> the rule's reach is wider than "terms": it covers the HYPOTHESES of auxiliary lemmas too.**

## What is proved here

| theorem | content |
|:--|:--|
| **`unpair_fst_lt`** | **`0 < n -> (unpair n).1 < n`** |
| **`unpair_snd_lt`** | **`2 <= n -> (unpair n).2 < n`** |
| **`pair_dominates_fst`** | **`a <= Nat.pair a b`** |
| **`pair_dominates_snd`** | **`b <= Nat.pair a b`** |

**=> these are the four inequalities a terminating decoder needs, and all four are now available.**
-/

namespace Lattice.Core.CIC

/-- **The first component of `Nat.unpair` is strictly below `n`.**

**Immediate from `Nat.unpair_lt`, which needs `1 <= n`.** -/
theorem unpair_fst_lt {n : ℕ} (h : 0 < n) : (Nat.unpair n).1 < n :=
  Nat.unpair_lt (by omega : 1 ≤ n)

/-- **The second component of `Nat.unpair` is strictly below `n`, for `n >= 2`.**

**The hypothesis is `2 <= n` and it CANNOT be weakened to `0 < n`: at `n = 0` the second component equals `n`, and
at `n = 1` it also equals `n`.**

**`Nat.pair a b` is `if a < b then b*b + a else a*a + a + b`, and each branch exceeds `b` once `n >= 2`.** -/
theorem unpair_snd_lt {n : ℕ} (h : 2 ≤ n) : (Nat.unpair n).2 < n := by
  set a := (Nat.unpair n).1
  set b := (Nat.unpair n).2
  have hp : Nat.pair a b = n := Nat.pair_unpair n
  rcases Nat.lt_or_ge a b with hlt | hge
  · -- `a < b`: `n = b*b + a`, so `n > b` because `b >= 2` here
    have he : n = b * b + a := by rw [Nat.pair, if_pos hlt] at hp; omega
    nlinarith
  · -- `a >= b`: `n = a*a + a + b`, which exceeds `b` unconditionally
    have he : n = a * a + a + b := by rw [Nat.pair, if_neg (by omega)] at hp; omega
    nlinarith

/-- **The first component is dominated by the pair.** -/
theorem pair_dominates_fst (a b : ℕ) : a ≤ Nat.pair a b := by
  rw [Nat.pair]
  split_ifs <;> omega

/-- **The second component is dominated by the pair.** -/
theorem pair_dominates_snd (a b : ℕ) : b ≤ Nat.pair a b := by
  rw [Nat.pair]
  split_ifs <;> nlinarith

end Lattice.Core.CIC
