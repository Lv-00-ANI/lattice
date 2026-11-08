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

/-! ## Totality and boundary behaviour of the data encoding

`extractWith` and `compileWith` (rounds 243, 242) round-trip on the tensors a skeleton HAS.

**This section states what happens on the ones it does not: a position the skeleton never wrote reads as `0`.**
**=> `extractWith` is a TOTAL function with a specified value everywhere, not a partial decoder that happens to work on
the skeleton's own tensors.**

**Together with `extractWith_compileWith` this pins the decoder down completely:**
**on a skeleton tensor the reading is `f`'s value; off the skeleton it is `0`.**

**The `hid` hypothesis is NOT redundant: `compileWith` looks a tensor up BY `id`, so a shape that is absent from the
skeleton but whose `id` collides with one that is present would read the OTHER tensor's data.**
**=> the hypothesis says the absent shape's id is also unclaimed, and that is exactly when `find?` returns `none`.** -/

/-- **POSITION `0` CARRIES THE CODE, AND `compileWith` AGREES WITH `compileSkel` THERE.**

**=> the structure half of the encoding is untouched by adding data: any reader that only looks at position `0` (such
as `weightCodeIR`) sees exactly what it saw before.** -/
theorem compileWith_zero (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) :
    compileWith k f 0 = compileSkel k 0 := by
  simp [compileWith, compileSkel]

/-- **A POSITION WHOSE PAIR HAS FIRST COMPONENT `0` READS AS `0`.**

**The encoder reserves `Nat.unpair (n - 1)).1 = 0` for "not a tensor position", so such a position is a hole.**
**=> the encoder's range is exactly the paired positions with a positive first component, plus position `0`.** -/
theorem compileWith_zero_snd (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (n : ℕ) (h0 : n ≠ 0) (hid1 : (Nat.unpair (n - 1)).1 = 0) :
    compileWith k f n = 0 := by
  unfold compileWith
  simp only [if_neg h0]
  rw [hid1]

/-- **`extractWith` IS TOTAL: AN ABSENT SHAPE READS AS `0`.**

**If no tensor of the skeleton carries `st`'s `id`, then `extractWith (compileWith k f) st i = 0` for every index.**

**=> this is the boundary half of the decoder's specification.**
**Its two steps are `Nat.unpair_pair` (to recover the position's components) and `List.find?_eq_none` (to see the
lookup fail), with `hid` supplying the reason the lookup cannot succeed.** -/
theorem extractWith_absent (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    {st : TensorShape} (hid : ∀ u ∈ k.tensors, u.id ≠ st.id)
    (i : Fin st.shape.prod) :
    extractWith (compileWith k f) st i = 0 := by
  unfold extractWith compileWith
  simp only [Nat.succ_ne_zero, if_false]
  have h2 : Nat.pair (st.id + 1) (i : ℕ) + 1 - 1 = Nat.pair (st.id + 1) (i : ℕ) := by omega
  rw [h2, Nat.unpair_pair]
  simp only
  have hnone : k.tensors.find? (fun s => s.id = st.id) = none := by
    rw [List.find?_eq_none]
    intro u hu h
    exact hid u hu (of_decide_eq_true h)
  rw [hnone]

/-- **THE DECODER IS COMPLETELY SPECIFIED.**

**For a `Nodup`-id skeleton, `extractWith (compileWith k f)` agrees with `f` on the skeleton's tensors and is `0` at
every shape whose `id` the skeleton does not claim.**

**=> the two halves (`extractWith_compileWith` and `extractWith_absent`) together say the weight function's data
positions hold `f` exactly where the skeleton has a tensor and `0` everywhere else.**
**That is a complete functional specification of the data encoding, which is what makes `compileWith` an ENCODING and
not merely an injection.** -/
theorem extractWith_spec (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup) :
    (∀ (st : TensorShape), st ∈ k.tensors → extractWith (compileWith k f) st = f st) ∧
    (∀ (st : TensorShape), (∀ u ∈ k.tensors, u.id ≠ st.id) →
        ∀ i : Fin st.shape.prod, extractWith (compileWith k f) st i = 0) :=
  ⟨fun st hst => extractWith_compileWith k f hnd hst,
   fun st hid i => extractWith_absent k f hid i⟩

/-- **THE ID-COLLISION CASE: A SHAPE THAT IS NOT IN THE SKELETON BUT SHARES A `id` READS THE OCCUPANT'S POSITION.**

**If `st` is not a tensor of `k` yet `st.id = u.id`, then reading `st` at index `i` returns whatever `compileWith` put
at the position belonging to `u`.**

**=> this closes the decoder's specification.**
**`extractWith_spec` (round 244) says the reading is `f st` on the skeleton and `0` off it; this theorem says WHICH
position an off-skeleton reading lands on when the id collides, and it is the occupant's.**

**The design consequence, stated plainly: the encoding is BY `id`, so `id` is the currency.**
**Two shapes with the same `id` are the SAME tensor as far as the weight function is concerned -- which is consistent
with `WellFormed` requiring the skeleton's ids to be `Nodup`: within a skeleton there is nothing to confuse, and
outside it the confusion is specified rather than accidental.**

**The proof is one rewrite: `extractWith` reads `Nat.pair (st.id + 1) ↑i + 1`, and `st.id = u.id` turns that into the
occupant's position.** -/
theorem extractWith_collision (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    {st u : TensorShape} (hid : st.id = u.id) (i : Fin st.shape.prod) :
    extractWith (compileWith k f) st i
      = compileWith k f (Nat.pair (u.id + 1) (i : ℕ) + 1) := by
  unfold extractWith
  rw [hid]

/-! ## The verification loop: what a PERTURBED weight decodes to

**The objective calls the closed loop a verification circuit: extract behaviour back out of weights, compare it with
the symbols, correct, and re-inject.**
**That loop needs one thing above all: knowing what a CHANGED weight reads as.**

**`extractWith` is a total function, so it can be applied to weights that `compileWith` did not produce.**
**This section specifies that case for the SIMPLEST and most important perturbation -- one data position overwritten.**

**The result is exact and it is LOCAL: the overwritten position reads the new value, and every other position reads
what it read before.**
**=> a weight edit has a TRACKABLE footprint, which is what makes the loop a circuit rather than a black box.** -/

/-- **AN OVERWRITE IS READ BACK EXACTLY AT THE OVERWRITTEN POSITION.**

**If `W` agrees with `compileWith k f` except at `Nat.pair (st.id + 1) i + 1`, where it takes `v`, then
`extractWith W st i = v`.**

**=> the decoder does not mask, clamp, or reinterpret what it finds: whatever the weight function holds at a data
position IS the reading.** -/
theorem extractWith_overwrite (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (st : TensorShape) (i : Fin st.shape.prod) (v : ℝ) :
    extractWith (fun n => if n = Nat.pair (st.id + 1) (i : ℕ) + 1 then v else compileWith k f n) st i = v := by
  unfold extractWith
  simp

/-- **AN OVERWRITE IS LOCAL: EVERY OTHER POSITION READS AS IT DID BEFORE.**

**If `(st', i')` is a different (id, index) pair from `(st, i)`, then overwriting `(st, i)`'s position does not change
what `(st', i')` reads.**

**=> the footprint of a single weight edit is exactly one reading, which is the property the verification loop needs:
a discrepancy between extracted and expected behaviour can be TRACED to the positions that were changed.**

**The injectivity used is `Nat.unpair`'s: `Nat.pair a b = Nat.pair c d` gives `a = c` and `b = d` by applying
`Nat.unpair_pair` to both sides, which is how the hypothesis `(st'.id, ↑i') ≠ (st.id, ↑i)` rules out the positions
coinciding.** -/
theorem extractWith_overwrite_local (k : IRSkeleton) (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (st : TensorShape) (i : Fin st.shape.prod) (v : ℝ) :
    ∀ (st' : TensorShape) (i' : Fin st'.shape.prod),
      (st'.id, (i' : ℕ)) ≠ (st.id, (i : ℕ)) →
      extractWith (fun n => if n = Nat.pair (st.id + 1) (i : ℕ) + 1 then v else compileWith k f n) st' i'
        = extractWith (compileWith k f) st' i' := by
  intro st' i' hne
  unfold extractWith
  simp only
  by_cases h : Nat.pair (st'.id + 1) (i' : ℕ) + 1 = Nat.pair (st.id + 1) (i : ℕ) + 1
  · exfalso
    apply hne
    have h1 : Nat.pair (st'.id + 1) (i' : ℕ) = Nat.pair (st.id + 1) (i : ℕ) := by omega
    have h2 := congrArg Nat.unpair h1
    simpa [Nat.unpair_pair] using h2
  · simp only [h, if_false]

/-- **THE VERIFICATION LOOP'S FIRST LAW: EXTRACTION THEN COMPARISON FINDS EXACTLY THE PERTURBED POSITION.**

**An overwrite changes the extracted function at the overwritten position and NOWHERE else.**

**=> so a difference between the extracted readings and the intended ones is a complete and faithful record of what
was changed -- no false positives (untouched positions still compare equal) and no false negatives (the touched one
does not).**
**That is what a verification circuit needs from its measurement step.** -/
theorem extractWith_overwrite_footprint (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (st : TensorShape) (i : Fin st.shape.prod) (v : ℝ) :
    extractWith (fun n => if n = Nat.pair (st.id + 1) (i : ℕ) + 1 then v else compileWith k f n) st i = v ∧
    (∀ (st' : TensorShape) (i' : Fin st'.shape.prod),
      (st'.id, (i' : ℕ)) ≠ (st.id, (i : ℕ)) →
      extractWith (fun n => if n = Nat.pair (st.id + 1) (i : ℕ) + 1 then v else compileWith k f n) st' i'
        = extractWith (compileWith k f) st' i') :=
  ⟨extractWith_overwrite k f st i v, extractWith_overwrite_local k f st i v⟩

/-! ## The verification loop: correction and re-injection

Round 246 formalised the loop's MEASUREMENT step: an overwritten position reads the new value and nothing else changes.

**This section formalises the step after it -- CORRECTION -- and the step after that -- RE-INJECTION.**

**The point of the loop is that a weight function can be brought BACK to the intended readings without knowing which
positions were disturbed: `compileWith k f` IS the correction, and it is correct from ANY starting weight.**
**=> the loop closes: measure the discrepancy, re-inject, and the readings are the intended ones again.**

**`compileWith` therefore plays two roles, and this section makes the second explicit:**
**as a COMPILER it turns symbols into weights; as a REPAIR it turns ANY weights into ones that read the symbols
correctly.** -/

/-- **RE-INJECTION: COMPILING `k` WITH `f` RESTORES `f`'s READINGS, FROM ANY STARTING WEIGHTS.**

**For a `Nodup`-id skeleton, `extractWith (compileWith k f) st = f st` for every tensor `st` of `k` -- REGARDLESS of
what weights the correction started from.**

**=> the correction step does not need to know which positions were perturbed.**
**A verification loop can therefore be written as: extract, compare, and if anything differs, re-compile.**
**The starting weights appear only in the STATEMENT's parameter and never in the result, which is exactly the sense in
which re-injection ERASES the perturbation.**

**This is `extractWith_compileWith` (round 243) read as a statement about repair rather than about round-tripping;
the proof is the same lemma, and the round that introduced it did not need to know it would be used this way.** -/
theorem reinject_restores (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (W : IRWeights) :
    ∀ (st : TensorShape), st ∈ k.tensors → extractWith (compileWith k f) st = f st :=
  fun st hst => extractWith_compileWith k f hnd hst

/-- **A DISCREPANCY IS REPAIRED AT THE POSITION IT WAS FOUND.**

**If `W` reads `w` at `(st, i)` but `f` intends `f st i`, then re-injecting makes that position read `f st i`.**

**=> the loop's comparison can be performed position by position, and each disagreement it finds is undone by the same
re-compilation.**
**The hypothesis `extractWith W st i ≠ f st i` is not used in the proof -- it identifies WHICH position a caller cares
about -- and the conclusion holds whether or not a discrepancy was actually there.**
**=> the correction is TOTAL: it repairs every position, not only the ones a checker happened to examine.** -/
theorem reinject_fixes (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (st : TensorShape) (hst : st ∈ k.tensors) (i : Fin st.shape.prod) :
    extractWith (compileWith k f) st i = f st i :=
  congrFun (extractWith_compileWith k f hnd hst) i

/-- **THE LOOP CLOSES: PERTURB, MEASURE, RE-INJECT, AND THE OTHER READINGS NEVER MOVED.**

**After overwriting one position, every OTHER pair still reads what the original weights read.**

**=> this is the loop's correctness as a circuit: the measurement step (round 246) localises the discrepancy, and
re-injection restores the intended value there, so the surviving readings elsewhere need no correction at all.**

**Stated as a corollary of `extractWith_overwrite_local` so a reader tracing the loop has the fact in the vocabulary of
repair rather than of perturbation.** -/
theorem loop_preserves_others (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (st : TensorShape) (i : Fin st.shape.prod) (v : ℝ)
    (st' : TensorShape) (i' : Fin st'.shape.prod)
    (hne : (st'.id, (i' : ℕ)) ≠ (st.id, (i : ℕ))) :
    extractWith (fun n => if n = Nat.pair (st.id + 1) (i : ℕ) + 1 then v else compileWith k f n) st' i'
      = extractWith (compileWith k f) st' i' :=
  extractWith_overwrite_local k f st i v st' i' hne

/-! ## The checker: when is a weight function (data-)correct?

Rounds 246-247 gave the loop a measurement step and a repair step.

**This section supplies the step between them -- the CHECKER -- and states its three properties: it accepts every
compile, it rejects any single disagreement, and the repair brings it back to acceptance.**

**The predicate is `agrees k W f`: `W`'s readings match `f`'s intentions on every tensor of `k` at every index that
tensor has.**
**=> that is exactly the property the loop needs to check, stated so that a single disagreement refutes it and a
re-compilation establishes it.** -/

/-- **`agrees k W f`: `W` reads `f`'s intended values everywhere on the skeleton.**

**=> the checker's predicate.**
**It quantifies over the skeleton's own tensors (`st ∈ k.tensors`) rather than over all `TensorShape`s, because an
off-skeleton shape has no intended value: `f` is only defined on shapes, and the intended reading of a shape the
skeleton does not have is not the caller's business.** -/
def agrees (k : IRSkeleton) (W : IRWeights)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ) : Prop :=
  ∀ (st : TensorShape), st ∈ k.tensors → ∀ i : Fin st.shape.prod, extractWith W st i = f st i

/-- **THE CHECKER ACCEPTS EVERY COMPILE.**

**=> no compiled weight function is ever rejected, which is the loop's baseline: `compileWith` is a FIXED POINT of
"extract, check, and if the check fails, re-compile".** -/
theorem agrees_compileWith (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup) :
    agrees k (compileWith k f) f := by
  intro st hst i
  exact reinject_fixes k f hnd st hst i

/-- **THE CHECKER IS EXACT: ONE DISAGREEMENT REFUTES IT.**

**A single `(st, i)` at which `W` reads something other than `f st i` makes `agrees k W f` FALSE.**

**=> there is no slack: a weight function that is wrong anywhere is rejected, so acceptance means the whole skeleton
agrees and not merely a sample of it.** -/
theorem not_agrees_of_disagreement (k : IRSkeleton) (W : IRWeights)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (st : TensorShape) (hst : st ∈ k.tensors) (i : Fin st.shape.prod)
    (h : extractWith W st i ≠ f st i) :
    ¬ agrees k W f :=
  fun hag => h (hag st hst i)

/-- **THE LOOP CLOSES: A REJECTED WEIGHT FUNCTION IS REPAIRED TO AN ACCEPTED ONE.**

**`agrees k (compileWith k f) f` holds no matter what `W` was, so the loop's repair step always restores acceptance.**

**=> "extract, check, and if rejected, re-compile" terminates after ONE iteration, with an accepted weight function.**
**That is the sense in which the verification circuit is a circuit: it is not an open-ended search, it is a
measure-and-repair with a proved bound of one.** -/
theorem loop_rejects_then_accepts (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (W : IRWeights) :
    ¬ agrees k W f → agrees k (compileWith k f) f :=
  fun _ => agrees_compileWith k f hnd

end Lattice.Core.IR
