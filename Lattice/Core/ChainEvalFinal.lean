/-
# `Core/ChainEvalFinal.lean` -- the general chain evaluation (round 145)

## The four rounds before this one

| round | construction | what blocked it |
|:--|:--|:--|
| **141** | **`toChainBetween` (`if` version)** | **the `if`'s proof terms** |
| **142** | **same, general evaluation** | **eight obligations, all rooted in the `if` or the empty branch's transport** |
| **143** | **diagnosis: "transport does not reduce"** | **half right** |
| **144** | **`cast_cast` + `cast_proof_irrel` proved** | **`act` does not commute with transport -- not yet known** |
| **145** | **`act_cast_snd` proved** | **=> everything needed is now in the tree** |

## The construction, with the arithmetic isolated to ONE `cast`

**`stackChain width w k fuel : Chain (width k) (width (k + fuel))`, structural in `fuel`.**

**The `succ` case's tail ends at `(k+1) + fuel`; the whole must end at `k + (fuel+1)`; the two are equal by
`omega` and NOT definitionally.**
**=> exactly ONE `cast` appears, and `cast_proof_irrel` (round 144) identifies it with any other transport along
the same equation; `act_cast_snd` (round 145) lets `act` see through it.**

**`runLayers` mirrors the recursion, with the SAME single `cast`, so the two meet.**

## What is proved

| theorem | content |
|:--|:--|
| **`stackChain`** | **the chain over `fuel` layers from `k`** |
| **`runLayers`** | **the layer-by-layer specification, same recursion** |
| **`stackChain_zero` / `runLayers_zero`** | **both base cases are `idf` / `id`** |
| **`act_stackChain`** | **THE GENERAL EVALUATION** |

## What this does NOT do

**It does not relate `stackChain` to `toChainBetween`.**
**The two build the same chain over the same range, and comparing them is a cross-recursion equation of exactly
the kind rounds 141-143 failed on -- and it is not needed, because `stackChain` is self-contained.**
-/

import Mathlib
import Lattice.Core.ArchChain
import Lattice.Core.ArchChainEval
import Lattice.Core.CastLemmas
import Lattice.Core.ChainCastAct

namespace Lattice.Core

namespace Arch

open Lattice.Core.ModelArtifact

/-! ## The construction -/

/-- **The chain over `fuel` layers starting at layer `k`.**

**One `cast` in the `succ` case, carrying the equation `(k+1) + fuel = k + (fuel+1)`.**
**=> that single transport is what rounds 141-143 could not get past; round 144's `cast_proof_irrel` and round
145's `act_cast_snd` are what make it harmless.** -/
noncomputable def stackChain {A : Arch} (width : ℕ → ℕ) (w : Weights A width) :
    ∀ (k fuel : ℕ), k + fuel ≤ A.depth → Chain (width k) (width (k + fuel))
  | k, 0, _ => Chain.idf (width k)
  | k, fuel + 1, h =>
      Chain.cons (toLayer width ⟨k, by omega⟩ w)
        (cast (congrArg (fun t => Chain (width (k + 1)) (width t))
          (by omega : k + 1 + fuel = k + (fuel + 1)))
          (stackChain width w (k + 1) fuel (by omega)))

/-- **The layer-by-layer specification, by the SAME recursion and the SAME single transport.** -/
noncomputable def runLayers {A : Arch} (width : ℕ → ℕ) (w : Weights A width) :
    ∀ (k fuel : ℕ), k + fuel ≤ A.depth → (Fin (width k) → ℝ) → (Fin (width (k + fuel)) → ℝ)
  | k, 0, _ => fun x => x
  | k, fuel + 1, h =>
      fun x =>
        cast (congrArg (fun t => Fin (width t) → ℝ) (by omega : k + 1 + fuel = k + (fuel + 1)))
          (runLayers width w (k + 1) fuel (by omega)
            (mlayerAct (toLayer width ⟨k, by omega⟩ w) x))

/-- **`fuel = 0` is the identity chain.** -/
theorem stackChain_zero {A : Arch} (width : ℕ → ℕ) (w : Weights A width)
    (k : ℕ) (hk : k + 0 ≤ A.depth) :
    stackChain width w k 0 hk = Chain.idf (width k) :=
  rfl

/-- **`fuel = 0` is the identity map.** -/
theorem runLayers_zero {A : Arch} (width : ℕ → ℕ) (w : Weights A width)
    (k : ℕ) (hk : k + 0 ≤ A.depth) :
    runLayers width w k 0 hk = id :=
  rfl


/-- **THE GENERAL EVALUATION: the chain computes the specification.**

**`Chain.act (stackChain width w k fuel h) x = runLayers width w k fuel h x`.**

**The induction is on `fuel`, the variable both recursions decrease.**
**In the `succ` case BOTH sides carry a `cast` along the SAME equation
`k + 1 + fuel = k + (fuel + 1)`, so `cast_proof_irrel` (round 144) lets them be identified, and `act_cast_snd`
(round 145) lets `act` see through the chain's transport.**
**=> this is the theorem rounds 141-144 each refused.** -/
theorem act_stackChain {A : Arch} (width : ℕ → ℕ) (w : Weights A width) :
    ∀ (fuel : ℕ) (k : ℕ) (h : k + fuel ≤ A.depth) (x : Fin (width k) → ℝ),
      Chain.act (stackChain width w k fuel h) x = runLayers width w k fuel h x := by
  intro fuel
  induction fuel with
  | zero =>
    intro k h x
    simp only [stackChain, runLayers, Chain.act_idf]
  | succ fuel ih =>
    intro k h x
    -- name the equation ONCE, so both sides use the same proof term
    let heq : k + 1 + fuel = k + (fuel + 1) := by omega
    -- unfold both `succ` cases at that equation
    show Chain.act
        (Chain.cons (toLayer width ⟨k, by omega⟩ w)
          (cast (congrArg (fun t => Chain (width (k + 1)) (width t)) heq)
            (stackChain width w (k + 1) fuel (by omega)))) x
      = cast (congrArg (fun t => Fin (width t) → ℝ) heq)
          (runLayers width w (k + 1) fuel (by omega)
            (mlayerAct (toLayer width ⟨k, by omega⟩ w) x))
    rw [act_cons]
    -- the tail is transported; move the transport OUTSIDE `act`
    rw [act_cast_snd (a := width (k + 1)) (b := width (k + 1 + fuel)) (b':= width (k + (fuel + 1))) (congrArg width heq)]
    rw [ih (k + 1) (by omega) (mlayerAct (toLayer width ⟨k, by omega⟩ w) x)]

end Arch

end Lattice.Core
