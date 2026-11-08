import Mathlib
import Lattice.Core.IR.Chain
import Lattice.Core.IR.Skeleton
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

/-! ## Compiling weights that CARRY THE DATA

`compileSkel` encodes only a `Nat` (`skeletonCode k`) at position `0` and `0` everywhere else, so `IRWeights` as it
stands carries the STRUCTURE and nothing else.

**This section adds the content half: a weight function whose position `0` is still the skeleton code, and whose
position `Nat.pair (id + 1) i + 1` is the tensor `id`'s reading at index `i`.**

**=> the `+ 1` outside the pair keeps position `0` free for the code, and the `id + 1` INSIDE the pair keeps the pair
from colliding with `Nat.pair 0 i`; both shifts are needed, and `pair_eq_zero` is what shows the second is safe.**

**Read-back is exact (`compileWith_read`), and the code half is unchanged (`compileWith_code`), so:
- the REVERSE direction still recovers the skeleton from position `0` alone;
- the FORWARD direction now also carries what the structure holds.

**The reading is stored for the tensor whose `id` is found in the skeleton, so `find_id_eq_some_of_nodup_shape` is what
makes the lookup deterministic.** -/

/-- **A pair whose first component is positive is never zero.**

**=> this is why `id + 1` is used rather than `id`: the encoded position must stay clear of `0`, which holds the
skeleton code.** -/
theorem pair_succ_pos_ne_zero (a b : ℕ) : Nat.pair (a + 1) b ≠ 0 := by
  intro h
  unfold Nat.pair at h
  split at h
  · have : b * b = 0 := by omega
    have hb : b = 0 := by nlinarith
    omega
  · have : a * a + a = 0 := by omega
    omega

/-- **`compileWith k f`: the skeleton's code at position `0`, and `f`'s readings at the paired positions.**

**`compileSkel` puts `skeletonCode k` at `0` and nothing elsewhere; this puts `f st ⟨i, _⟩` at
`Nat.pair (st.id + 1) i + 1` as well.**

**The outer `+ 1` keeps `0` free for the code; the inner `id + 1` keeps the encoded pair from being `Nat.pair 0 i`,
which could be `0` and would then collide with the code position.**

**The lookup `k.tensors.find? (fun s => s.id = id)` is deterministic precisely because the ids are `Nodup`, which is
`WellFormed`'s first conjunct.** -/
def compileWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) : IRWeights :=
  fun n =>
    if n = 0 then (skeletonCode k : ℝ)
    else
      match Nat.unpair (n - 1) with
      | (id1, i) =>
        match id1 with
        | 0 => 0
        | id + 1 =>
          match k.tensors.find? (fun s => s.id = id) with
          | some st => if hi : i < st.shape.prod then f st ⟨i, hi⟩ else 0
          | none => 0

/-- **`compileWith` KEEPS THE SKELETON CODE AT POSITION `0`.**

**=> the reverse direction (`weightCodeIR` then `extractCode`) still sees the same skeleton: `compileWith` adds content
WITHOUT disturbing the structure's encoding.** -/
theorem compileWith_code (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    weightCodeIR (compileWith k f) = skeletonCode k := by
  unfold weightCodeIR compileWith
  simp

/-- **`compileWith` IS READ BACK EXACTLY AT EVERY PAIRED POSITION.**

**`compileWith k f (Nat.pair (st.id + 1) i + 1) = f st ⟨i, hi⟩` for any tensor `st` of the skeleton and any in-range
index `i`.**

**=> the data half of the encoding is faithful, which is what makes `compileWith` a genuine CARRIER of content rather
than a placeholder.**
**Three steps: `if_neg` removes the code branch; `Nat.unpair_pair` recovers `(st.id + 1, i)`; and
`find_id_eq_some_of_nodup_shape` lands the lookup on `st` itself.** -/
theorem compileWith_read (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    {st : TensorShape} (hst : st ∈ k.tensors) {i : ℕ} (hi : i < st.shape.prod) :
    compileWith k f (Nat.pair (st.id + 1) i + 1) = f st ⟨i, hi⟩ := by
  unfold compileWith
  simp only [Nat.succ_ne_zero, if_false]
  have h2 : Nat.pair (st.id + 1) i + 1 - 1 = Nat.pair (st.id + 1) i := by omega
  rw [h2, Nat.unpair_pair]
  simp only
  rw [find_id_eq_some_of_nodup_shape k.tensors hnd hst]
  simp only
  rw [dif_pos hi]

/-! ## Reading the DATA back out of the weights

`compileWith` (round 242) writes the structure at position `0` and the readings at `Nat.pair (id + 1) i + 1`.

**This section reads the readings back: `extractWith W st i = W (Nat.pair (st.id + 1) i + 1)`.**

**=> the reverse direction is now complete on BOTH halves: `extract` recovers the skeleton from position `0`, and
`extractWith` recovers the data from the paired positions.**
**`extractWith` does not need the skeleton as an argument -- the position is determined by the SHAPE's own `id` and the
index -- which is what makes it a genuine decoding rather than a lookup table the caller has to supply.** -/

/-- **`extractWith W`: the readings encoded in `W`, as a function of a tensor's shape and an index.**

**The position read is exactly the one `compileWith` writes: `Nat.pair (st.id + 1) i + 1`.**
**=> the two are inverse on the data half, which `extractWith_compileWith` states.** -/
def extractWith (W : IRWeights) : (s : TensorShape) → Fin s.shape.prod → ℝ :=
  fun s i => W (Nat.pair (s.id + 1) (i : ℕ) + 1)

/-- **`extractWith` IS A LEFT INVERSE OF `compileWith` ON EVERY TENSOR OF THE SKELETON.**

**For a `Nodup`-id skeleton, a tensor `st` of it, `extractWith (compileWith k f) st = f st`.**

**=> the data half of the encoding round-trips EXACTLY: what went in at `compileWith` comes out at `extractWith`,
pointwise over the whole index type.**

**Two facts carry it: `compileWith_read` gives the value at every index, and `extractWith` reads that same position --
so the proof is a `funext` followed by one application, with `i.isLt` supplying the range hypothesis.**

**=> note what is NOT needed: the skeleton `k` is not passed to `extractWith`, and the proof never has to search the
skeleton's tensor list, because `compileWith_read` already did that ONCE and for all indices.** -/
theorem extractWith_compileWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    {st : TensorShape} (hst : st ∈ k.tensors) :
    extractWith (compileWith k f) st = f st := by
  funext i
  exact compileWith_read k f hnd hst i.isLt

/-- **THE WHOLE PICTURE: BOTH HALVES OF THE ENCODING ARE RECOVERABLE FROM THE WEIGHTS ALONE.**

**`weightCodeIR (compileWith k f) = skeletonCode k` (the structure)
AND `extractWith (compileWith k f) st = f st` for every `st` of the skeleton (the content).**

**=> the weight function carries the skeleton AND the data, and both are readable:
- `extract` / `extract_compile` recover the skeleton from position `0`;
- `extractWith` / `extractWith_compileWith` recover the readings from the paired positions.

**That is the round trip on the WEIGHTS side, which is the half of 符号 ⇄ 权重 that the objective calls the real
difficulty.** -/
theorem compileWith_roundtrip (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup) :
    weightCodeIR (compileWith k f) = skeletonCode k ∧
    ∀ (st : TensorShape), st ∈ k.tensors → extractWith (compileWith k f) st = f st :=
  ⟨compileWith_code k f, fun st hst => extractWith_compileWith k f hnd hst⟩

end Lattice.Core.IR
