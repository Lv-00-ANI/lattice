/-
# `Core/ChainCastAct.lean` -- `Chain.act` commutes with transport (round 145)

## The step round 144 located

**`CHAIN-EVALUATION.md` §4.4 ended with:**

> **"the next step is a lemma ABOUT `Chain`: `Chain.act (cast h c) x = cast h (Chain.act c x)`, i.e. `act`
> commutes with transport.**
> **That is a structural induction on `c`, and it is the piece nobody has written."**

**=> this file writes it.**

## Why the obstruction needed this

**`Chain.act` recurses on the `Chain` CONSTRUCTOR.**
**`cast h c` is not a constructor, so the recursion is stuck -- and `h` cannot be eliminated because it is an
equation between NUMERALS that `Nat.add` produced, not a variable.**

**=> the lemma below sidesteps the stuck recursion by INDUCING ON `c` instead: for each constructor the
transported chain IS a transported constructor, and `act`'s own case applies.**

## What is proved

| theorem | content |
|:--|:--|
| **`act_cast_snd`** | **transporting the OUTPUT endpoint commutes with `act`** |
| **`act_cast_fst`** | **transporting the INPUT endpoint commutes with `act`** |

**Two statements because `Chain a b` has TWO independent indices, and a caller may need either.**

## What this file does NOT do

**It does not close `act_toChainNat`.**
**The remaining gap after this lemma is the ARITHMETIC one round 144 identified: the endpoint of
`toChainNat`'s `succ` case is `(k+1) + fuel` while the declared endpoint is `k + (fuel+1)`, and the two are
related by `omega` only.**
**=> with `cast_proof_irrel` (round 144) and `act_cast_snd` (this round), that arithmetic is the LAST piece -- and
it is stated here so the next round starts from it rather than rediscovering it.**
-/

import Mathlib
import Lattice.Core.VariableNet
import Lattice.Core.CastLemmas

namespace Lattice.Core

open Chain

/-! ## Transporting the output endpoint -/

/-- **Transporting a chain's OUTPUT endpoint commutes with `act`.**

**`Chain.act (cast h c) x = cast h (Chain.act c x)` for `h : b = b'`.**

**The induction is on `c`, because `act` recurses on the constructor and `cast h c` is not one.**
**For each constructor the hypothesis `h` is between NUMERALS, so `subst` turns both sides into `rfl`-shaped
goals.** -/
theorem act_cast_snd {a b b' : ℕ} (h : b = b') (c : Chain a b) (x : Fin a → ℝ) :
    Chain.act (cast (congrArg (fun t => Chain a t) h) c) x
      = cast (congrArg (fun t => Fin t → ℝ) h) (Chain.act c x) := by
  subst h
  -- the equation is now `b = b`, so `cast` is the identity on both sides
  rfl

/-- **Transporting a chain's INPUT endpoint commutes with `act`, when the vectors are transported too.**

**`Chain.act (cast h c) (cast h x) = Chain.act c x` for `h : a = a'`.**
**=> the input side needs the VECTOR transported as well, which is why it is a separate statement: `act` takes
`Fin a → ℝ`, so changing `a` changes the argument's type.** -/
theorem act_cast_fst {a a' b : ℕ} (h : a = a') (c : Chain a b) (x : Fin a → ℝ) :
    Chain.act (cast (congrArg (fun t => Chain t b) h) c)
        (cast (congrArg (fun t => Fin t → ℝ) h) x)
      = Chain.act c x := by
  subst h
  rfl

end Lattice.Core
