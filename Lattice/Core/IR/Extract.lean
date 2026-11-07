import Mathlib
import Lattice.Core.IR.Chain
import Lattice.Core.IR.DecodeRelations

/-!
# `Core/IR/Extract.lean` -- `extract : IRWeights -> Option IRSkeleton` (round 214)

## What was wrong, and what round 213 taught

`Skeleton.lean` has

```lean
noncomputable def extractCode (W : IRWeights) : Option Nat :=
  some (weightCodeIR W)
```

**It ALWAYS returns `some`, so on a weight vector no skeleton compiles to it reports success.**

**Round 213 wrote the real extractor and had to WITHDRAW it: its module was a LEAF, so `gen_lib_structure.py` refused
it -- "1.4 weight -> symbol: extract" had no reachable carrier.**

**The diagnosis was: the host module must import BOTH `Chain` (for `compileSkel`) and `Decode` (for
`decodeSkeleton`), and must itself be non-leaf.**

## This file's import graph

```
Extract -> Chain -> Parse -> Skeleton
Extract -> DecodeRelations -> Decode -> Skeleton
```

**=> acyclic, and `Extract` depends on NEITHER `Obligations` nor `Unique`, which is what lets `Obligations` import
it below.**

## What is proved

| theorem | content |
|:--|:--|
| **`extract`** | **`decodeSkeleton` after the code read-out -- it CAN return `none`** |
| **`weightCodeIR_compileSkel`** | **`weightCodeIR (compileSkel k) = skeletonCode k`** |
| **`extract_compile`** | **`extract (compileSkel k) = some k` -- T3's exact form** |
| **`extract_injective_on_compiled`** | **equal extracted results force equal skeletons** |

## Why `extract_compile` is not `rfl`

**Two steps, neither definitional:**
**1. `compileSkel k` writes `skeletonCode k` (a natural cast to `Real`) at index `0`, so the `floor` is exact;**
**2. `decodeSkeleton` then recovers `k` by its round trip (round 212).**

**=> the old `extractCode` stopped after step 1, which is why it could only report a CODE and never the structure.**
-/

namespace Lattice.Core.IR

/-- **THE REAL EXTRACTOR: read the code out of the weights, then decode it.**

**`decodeSkeleton (weightCodeIR W)`.**

**Unlike `extractCode`, this CAN return `none`, and `decodeSkeleton`'s rejection arms are what make that possible.** -/
noncomputable def extract (W : IRWeights) : Option IRSkeleton :=
  decodeSkeleton (weightCodeIR W)

/-- **`weightCodeIR` OF A COMPILED SKELETON IS ITS CODE.**

**`compileSkel k` writes `skeletonCode k` (a natural, cast to `Real`) at index `0`, so the floor is exact and the
`if 0 <= W 0` guard takes its positive branch.**
**=> the read-out loses nothing when the vector really is a compilation.** -/
theorem weightCodeIR_compileSkel (k : IRSkeleton) :
    weightCodeIR (compileSkel k) = skeletonCode k := by
  unfold weightCodeIR compileSkel
  simp only [if_pos (by positivity : (0:ℝ) ≤ (skeletonCode k : ℝ))]
  simp [Int.floor_natCast]

/-- **T3: `extract (compile k) = some k` -- the inverse `extractCode` never had.**

**The composition of `weightCodeIR_compileSkel` (arithmetic) with `decodeSkeleton_code` (the decoder's round trip).**
**=> neither step is definitional, which is what makes the statement non-trivial: `extractCode`'s version stopped at
`skeletonCode (skeleton S)`, one layer short of the skeleton itself.** -/
theorem extract_compile (k : IRSkeleton) :
    extract (compileSkel k) = some k := by
  unfold extract
  rw [weightCodeIR_compileSkel]
  exact decodeSkeleton_code k

/-- **`extract` IS INJECTIVE ON COMPILED VECTORS.**

**`extract (compileSkel k) = extract (compileSkel l) -> k = l`.**

**=> two different skeletons cannot produce weight vectors that extract to the same result, reached through the
DECODER -- the form a consumer needs: it can compare extracted results without comparing weight vectors.** -/
theorem extract_injective_on_compiled (k l : IRSkeleton)
    (h : extract (compileSkel k) = extract (compileSkel l)) : k = l := by
  rw [extract_compile k, extract_compile l] at h
  exact Option.some.inj h

end Lattice.Core.IR
