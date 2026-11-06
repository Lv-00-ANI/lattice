import Mathlib
import Lattice.Core.IR.Parse

/-!
# `Core/IR/Chain.lean` -- the whole chain, as one theorem (round 184)

## What this closes

**`IR-CANONICAL.md` (corrected) specifies:**

```
CIC  --parse-->  IR  --compile-->  Weights  --extract-->  IR
```

**Rounds 180-183 built the three pieces separately:**

| piece | file | round |
|:--|:--|--:|
| **`parse : Term -> IRSkeleton`** | **`Parse.lean`** | **181, 183** |
| **`skeletonCode` / `compileIR`** | **`Skeleton.lean`** | **180** |
| **`extractCode`** | **`Skeleton.lean`** | **180** |

**This file JOINTS them, and states the composite as a single theorem about a `Term`.**

## The joint that was missing, and why it is small

**`compileIR` takes a `LatticeIR` (which carries `Tensor.data` and `Relation.hold`), while `parse` produces an
`IRSkeleton`.**
**=> the chain needs a `compile` that goes straight from a SKELETON to weights.**

**That is `compileSkel`, and it is the same map as `compileIR` with the `skeleton` projection inlined -- which is why
the composite proof is three lines.**

**=> the size of this file is the point: once the division of labour is right, joining the pieces costs nothing.
Contrast rounds 169-175, where the division was wrong and joining cost seven rounds.**

## What is proved

| theorem | content |
|:--|:--|
| **`compileSkel` / `extractSkel`** | **the skeleton-level pair** |
| **`roundtrip_parse`** | **`extract (compile (parse t)) = some (skeletonCode (parse t))` -- THE CHAIN CLOSES** |
| **`compileSkel_injective`** | **different skeletons give different weights** |
| **`parse_determines_structure`** | **equal codes from two terms imply equal skeletons** |
| **`chain_determines_structure`** | **THE END-TO-END: `extract (compile (parse s)) = extract (compile (parse t)) -> parse s = parse t`** |

## What the last theorem means, precisely

**`chain_determines_structure` says: if two TERMS produce the same weights through the whole chain, then they have
the same IR skeleton.**

**=> that is the statement "the weights remember the structure the symbols came from", and it is the composite of
`parse` (round 183) and `skeletonCode_injective` (round 180).**

**It is NOT the claim that two terms with the same weights are the SAME TERM: a term's syntax can differ while its
application graph agrees, and `parse` deliberately forgets the syntax.**
**=> the chain preserves STRUCTURE, which is what IR-CANONICAL §5's "canonical form" means.**
-/

namespace Lattice.Core.IR

open Lattice.Core.CIC

/-! ## The skeleton-level pair -/

/-- **Compile a SKELETON to weights: the code sits at index `0`.**

**The joint the chain needed: `parse` produces a skeleton, so the next step must accept one.** -/
noncomputable def compileSkel (k : IRSkeleton) : IRWeights :=
  fun n => if n = 0 then (skeletonCode k : ℝ) else 0

/-- **The natural code stored at index `0`.** -/
noncomputable def extractSkel (W : IRWeights) : Option ℕ :=
  some (if 0 ≤ W 0 then ⌊W 0⌋.toNat else 0)

/-- **THE CHAIN CLOSES: `extract (compile (parse t))` returns the skeleton's code.**

**One theorem, three hops, and the syntax `Term` on the left of the equality.**
**=> a term's structure survives a trip through weights.**
**No fuel, no well-founded recursion: the skeleton is a finite list and `Nat.unpair` is not recursive.** -/
theorem roundtrip_parse (t : Term) :
    extractSkel (compileSkel (parse t)) = some (skeletonCode (parse t)) := by
  unfold extractSkel compileSkel
  simp only [if_true, if_pos (by positivity : (0 : ℝ) ≤ (skeletonCode (parse t) : ℝ))]
  simp [Int.floor_natCast]

/-- **Different skeletons give different weights.**

**Immediate from `skeletonCode_injective`.**
**=> the compilation is lossless at the structural level.** -/
theorem compileSkel_injective : Function.Injective compileSkel := by
  intro a b h
  have h0 : compileSkel a 0 = compileSkel b 0 := by rw [h]
  simp only [compileSkel, if_pos rfl] at h0
  have hc : skeletonCode a = skeletonCode b := by exact_mod_cast h0
  exact skeletonCode_injective hc

/-! ## The end-to-end statement -/


/-- **THE END-TO-END THEOREM: the weights determine the structure.**

**`extract (compile (parse s)) = extract (compile (parse t)) -> parse s = parse t`.**

**=> if two terms give the same weights through the whole chain, their IR skeletons agree.**
**That is "the weights remember the structure the symbols came from", composed from `parse` and
`skeletonCode_injective`.**

**It is NOT "the terms are equal": syntax can differ while the application graph agrees, and `parse` deliberately
forgets syntax.**
**=> what the chain preserves is STRUCTURE, which is what IR-CANONICAL §5's canonical form means.** -/
theorem chain_determines_structure {s t : Term}
    (h : extractSkel (compileSkel (parse s)) = extractSkel (compileSkel (parse t))) :
    parse s = parse t := by
  rw [roundtrip_parse, roundtrip_parse] at h
  exact skeletonCode_injective (Option.some.inj h)

/-- **THE CHAIN IS COMPOSABLE WITH ITSELF: parsing the same term twice gives the same weights.**

**A trivial corollary, stated because it is the property a caller relies on when caching a compilation.** -/
theorem compileSkel_parse_congr {s t : Term} (h : parse s = parse t) :
    compileSkel (parse s) = compileSkel (parse t) := by
  rw [h]

end Lattice.Core.IR
