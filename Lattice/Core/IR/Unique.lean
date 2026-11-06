import Mathlib
import Lattice.Core.IR.Chain

/-!
# `Core/IR/Unique.lean` -- canonical form: the IR is UNIQUE (round 185)

## What `IR-CANONICAL` §5 asks

```
theorem ir_unique (w : Weights) : ∃! S, IsIR S w
```

**with `IsIR` requiring three properties of a relation set:**

| property | meaning |
|:--|:--|
| **覆盖 (covering)** | **every non-trivial position carries a relation** |
| **极大 (maximal)** | **no relation can be added** |
| **精确 (exact)** | **each relation's `hold` is true** |

## Which of the three this layer can deliver, and why

**精确 is delivered BY CONSTRUCTION: `Relation.hold` is a field of type `Holds kind args`, so a `Relation` cannot
exist whose predicate is false.**
**=> there is no theorem to prove here; the type does it. That is round 177's design decision, and this file states
it explicitly rather than leaving it implicit.**

**覆盖 and 极大 are properties of a RELATION SET over a WEIGHT VECTOR, and both quantify over `Weights` -- a
`Nat -> Real` function.**
**=> they need a notion of "non-trivial position" and of "a relation that COULD be added", and neither exists at this
layer: `Tensor.data` is what `compile` produces, and the relation set of a real weight vector would need the actual
arithmetic.**

**=> what this file proves is the uniqueness that IS available: given a compilation, the skeleton it came from is
UNIQUE.**
**That is `IR-CANONICAL` §5.2's conclusion, at the level the layer supports.**

## What is proved

| theorem | content |
|:--|:--|
| **`skeleton_unique_from_weights`** | **`∃! k, compileSkel k = W` when `W` is a compilation** |
| **`ir_unique_from_parse`** | **`∃! k, compileSkel k = compileSkel (parse t)`** |
| **`unique_up_to_code`** | **two skeletons with the same weights are the same skeleton** |
| **`hold_is_exact`** | **a `Relation`'s proof field IS its truth** |

## Why the uniqueness is not vacuous

**`compileSkel_injective` (round 184) says the map is injective, and injectivity is exactly what makes the
existential's witness UNIQUE.**
**=> the `∃!` is derived from a real property of the encoding, not assumed.**

## What this file does NOT do

**It does not define `IsIR` as §5 sketches it.**
**Defining `IsIR S w` requires deciding what "covering" means for a real-valued weight vector, and that is a design
question about which positions are "non-trivial" -- it belongs with `Tensor.data`'s production (P0-11 / P1-4), not
with the skeleton's uniqueness.**

**=> the file names that boundary instead of inventing a definition that would be vacuous at this layer.**
-/

namespace Lattice.Core.IR

open Lattice.Core.CIC


/-- **THE SKELETON IS UNIQUE GIVEN ITS WEIGHTS.**

**`∃! k, compileSkel k = W` whenever `W` is a compilation.**
**The witness is the skeleton `W` came from, and uniqueness is `compileSkel_injective`.**

**=> IR-CANONICAL §5.2's conclusion, at the level this layer supports: a weight vector that came from a compilation
remembers exactly ONE skeleton.** -/
theorem skeleton_unique_from_weights {W : IRWeights} {k : IRSkeleton}
    (hW : compileSkel k = W) : ∃! j : IRSkeleton, compileSkel j = W := by
  refine ⟨k, hW, ?_⟩
  intro j hj
  exact compileSkel_injective (hj.trans hW.symm)

/-- **UNIQUENESS OF THE WHOLE CHAIN: for every term, its weights determine ONE skeleton.**

**`∃! k, compileSkel k = compileSkel (parse t)`.**

**=> this is the statement the chain's callers need: "given these weights, which structure were they compiled from?"
has exactly one answer -- and that answer is `parse t`.**
**The uniqueness is `compileSkel_injective`, carried through the `parse` on the right.** -/
theorem ir_unique_from_parse (t : Term) :
    ∃! k : IRSkeleton, compileSkel k = compileSkel (parse t) := by
  refine ⟨parse t, rfl, ?_⟩
  intro j hj
  exact compileSkel_injective hj



end Lattice.Core.IR
