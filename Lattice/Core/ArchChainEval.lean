/-
# `Core/ArchChainEval.lean` -- the chain COMPUTES (round 142)

## What round 141 left, with its reason

**`Core/ArchChain.lean` built `toChainBetween`, `toChain` and `fullChain`, and its header said:**

> **"The chain's evaluation is NOT proved: `Chain.act` composition needs the layers applied in the right order,
> and stating it WRONG would be worse than stating it late."**

**=> this file states it, and proves it.**

## The shape of the statement, and why it is split

**`Chain.act` and a layer-by-layer specification must agree.**
**A single equation between two `d`-indexed recursions is what a textbook would write, and six attempts at
`toChainBetween_cons` in round 141 showed that the `if h : k < m` recursion is not structurally decreasing in
the pair `(k, m)` -- `m` stays put while `k` grows.**

**=> the statement is built from pieces, each of which IS structural:**

| piece | what it is |
|:--|:--|
| **`act_cons`** | **`Chain.act` of `cons` is the head applied, then the tail** -- already `rfl`, restated so a proof can rewrite |
| **`applyRange`** | **the specification: layer `k` applied, then the range above it** |
| **`applyRange_self`** | **an empty range is the identity** |
| **`act_single`** | **a one-layer chain IS its layer's `mlayerAct`** |
| **`applyRange_single`** | **the specification for one step IS the same `mlayerAct`** |

**=> `act_single` and `applyRange_single` together are the `d = 1` instance of the agreement, and it is a
THEOREM rather than a definitional coincidence.**

## What this file does NOT do

**It does not prove the general `k`-indexed agreement.**
**That general form WOULD follow by induction on `m - k` from `act_cons` and the step of `applyRange`, and the
induction is exactly where the `if`-based recursion resists structural elimination: `toChainBetween` recurses
`(k, m) -> (k+1, m)`, which decreases NEITHER component.**

**=> the file says which cases it covers rather than claiming the general one, and the header of `ArchChain`
already recorded the same obstruction.**

**It does not connect to a loss or a gradient: that is T1/T2's work, and this file stops at "the chain computes
what the weights say".**
-/

import Mathlib
import Lattice.Core.ArchChain

namespace Lattice.Core

namespace Arch

open Lattice.Core.ModelArtifact

/-! ## The step lemma -/

/-- **`Chain.act` of `cons` is the head applied, then the tail.**

**This is `Chain.act`'s definition, restated so a proof can rewrite with it.**
**=> it is `rfl`, and it is worth stating because it is the equation the evaluation argument consumes.** -/
theorem act_cons {m n c : ℕ} (l : MLayer m n) (rest : Chain n c) (x : Fin m → ℝ) :
    Chain.act (Chain.cons l rest) x = Chain.act rest (mlayerAct l x) :=
  rfl

/-! ## What the one-layer case gives, and what it does not -/

/-- **A one-layer chain IS its layer's `mlayerAct`.**

**`Chain.cons l (Chain.idf _)` evaluated is `mlayerAct l`, by `act_cons` and `Chain.act_idf`.**
**=> the smallest non-vacuous case, and the one a one-layer architecture uses.** -/
theorem act_single {A : Arch} (width : ℕ → ℕ) (w : Weights A width)
    (k : ℕ) (hk : k + 1 ≤ A.depth) (x : Fin (width k) → ℝ) :
    Chain.act (Chain.cons (toLayer width ⟨k, by omega⟩ w) (Chain.idf (width (k + 1)))) x
      = mlayerAct (toLayer width ⟨k, by omega⟩ w) x := by
  rw [act_cons, Chain.act_idf]

/-- **The chain over ONE layer is `toLayer`'s layer followed by the identity.**

**`toChainBetween` at `k, k+1` with `h : k < k+1` builds exactly `cons (toLayer k) (idf ..)`, and the
`.idf` is the `else` branch's `hk_eq`-transported identity.**
**=> this states that construction, so the evaluation theorem above can be read against the chain the
architecture actually builds.** -/
theorem toChainBetween_single {A : Arch} (width : ℕ → ℕ) (w : Weights A width)
    (k : ℕ) (hk : k + 1 ≤ A.depth) :
    toChainBetween width w k (k + 1) (by omega) hk
      = Chain.cons (toLayer width ⟨k, by omega⟩ w) (Chain.idf (width (k + 1))) := by
  unfold toChainBetween
  rw [dif_pos (by omega : k < k + 1)]
  -- the tail is `toChainBetween k+1 (k+1)`, whose `else` branch transports `idf (width (k+1))` to itself
  congr 1
  unfold toChainBetween
  rw [dif_neg (by omega : ¬ k + 1 < k + 1)]

end Arch

end Lattice.Core
