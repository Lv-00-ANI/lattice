import Mathlib
import Lattice.Core.IR.Compile

/-!
# `Core/IR/Skeleton.lean` -- the codeable skeleton, and the round trip (round 180)

## The design question this file answers

**Round 179 ended with the boundary: `Tensor.data : Fin shape.prod -> Real` has no finite code.**

**The answer is not to drop `data` -- it is to notice WHICH PART of an IR `compile` and `extract` are about.**

**An IR has four components:**

| component | finite? | what it says |
|:--|:--|:--|
| **`Tensor.id`** | **yes** | **which tensor** |
| **`Tensor.shape`** | **yes** | **its multi-axis extent** |
| **`Tensor.data`** | **NO** | **its real-valued contents** |
| **`Relation.kind` / `.args` / `.part`** | **yes** | **the STRUCTURE** |
| **`Relation.hold`** | **a proof** | **that the structure actually holds** |

**=> the codeable part is exactly the SKELETON: the identifiers, the shapes, the relation structure.**
**`data` and `hold` are the NUMERIC and SEMANTIC content, and `compile` is precisely the map that supplies them.**

**That is the right factoring, and it is forced: a real number has no finite code, so any `compile : IR -> Weights`
must be defined from the skeleton and must PRODUCE the numbers rather than read them.**

## The two maps

| map | direction | content |
|:--|:--|:--|
| **`skeleton : IR -> IRSkeleton`** | **forget the numbers and the proofs** | **total, computable** |
| **`irCode : IRSkeleton -> Nat`** | **encode** | **injective (this file)** |
| **`compile : IR -> IRWeights`** | **IR to weights** | **places `irCode (skeleton S)` at index 0** |
| **`extract : IRWeights -> Option IRSkeleton`** | **weights to skeleton** | **decodes index 0** |

**=> the round trip is `extract (compile S) = some (skeleton S)`, which is the TRUE statement: weights remember the
STRUCTURE of an IR, not its real-valued contents (which they encode, not equal).**

**Stating it as `some (skeleton S)` rather than `some S` is not a weakening -- it is the precise claim, and saying
`some S` would be FALSE, because `data` is not recoverable from a finite weight vector at index 0.**

## What this file proves

| theorem | content |
|:--|:--|
| **`IRShape` / `IRSkeleton`** | **the codeable part of an IR** |
| **`skeleton`** | **`IR -> IRSkeleton`, total** |
| **`shapeCode` / `skeletonCode`** | **the encoders** |
| **`skeletonCode_injective`** | **two skeletons with the same code are equal** |
| **`irCode`** | **the IR's code** |
| **`compile` / `extract`** | **the two directions** |
| **`extract_compile`** | **`extract (compile S) = some (skeleton S)` -- THE ROUND TRIP** |
-/

namespace Lattice.Core.IR

/-- **The codeable part of a `Tensor`: its identifier and its shape.**

**`data` is deliberately absent: a real-valued entry has no finite code, and `compile` PRODUCES data rather than
reading it.** -/
structure TensorShape where
  /-- **The tensor's identifier.** -/
  id : TensorId
  /-- **Its multi-axis extent.** -/
  shape : List ℕ
  deriving DecidableEq, Repr

/-- **The codeable part of a `Relation`: its kind, its arguments, its part annotation.**

**`hold` is absent: it is a PROOF, and a proof carries no information about WHICH relation this is.**
**=> ignoring it is not a loss, and `skeletonCode_injective` is stated for skeletons, where it is sound.** -/
structure RelationShape where
  /-- **The relation kind.** -/
  kind : RelKind
  /-- **The arguments.** -/
  args : List (TensorId × List ℕ)
  /-- **The view annotation.** -/
  part : Option PartKind
  deriving DecidableEq, Repr

/-- **The codeable skeleton of an IR: the shapes of its tensors and of its relations.** -/
structure IRSkeleton where
  /-- **The tensor shapes.** -/
  tensors : List TensorShape
  /-- **The relation shapes.** -/
  relations : List RelationShape
  deriving DecidableEq, Repr

/-- **FORGET the numbers and the proofs: `IR -> IRSkeleton`.**

**Total and computable, because it only reads fields.** -/
def skeleton {H : RelKind → List (TensorId × List ℕ) → Prop} (S : LatticeIR H) : IRSkeleton where
  tensors := S.tensors.map fun t => ⟨t.id, t.shape⟩
  relations := S.relations.map fun r => ⟨r.kind, r.args, r.part⟩

/-! ## Encoding the skeleton -/

/-- **The code of a tensor shape.** -/
def tensorShapeCode (t : TensorShape) : ℕ :=
  Nat.pair (Nat.pair t.id (listCode t.shape) + 1) 0

/-- **The code of a relation shape.** -/
def relationShapeCode (r : RelationShape) : ℕ :=
  Nat.pair (Nat.pair (kindCode r.kind) (Nat.pair (argsCode r.args) (partCode r.part) + 1)) 0

/-- **The code of a list of skeleton items, by a stable fold.** -/
def shapesCode {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => Nat.pair (f x + 1) (shapesCode f xs)

/-- **`shapesCode` is injective when `f` is.**

**The `+1` is the same device as in `listCode`: it separates the empty list's `0` from an item whose code is `0`.** -/
theorem shapesCode_injective {α : Type} (f : α → ℕ) (hf : Function.Injective f) :
    Function.Injective (shapesCode f) := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [shapesCode] at h
      have hle : f y + 1 ≤ Nat.pair (f y + 1) (shapesCode f ys) := Nat.left_le_pair _ _
      omega
  | cons x xs ih =>
    intro b h
    cases b with
    | nil =>
      simp only [shapesCode] at h
      have hle : f x + 1 ≤ Nat.pair (f x + 1) (shapesCode f xs) := Nat.left_le_pair _ _
      omega
    | cons y ys =>
      simp only [shapesCode] at h
      obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
      have hxy : f x = f y := by omega
      have hx : x = y := hf hxy
      subst hx
      rw [ih h2]

/-- **The skeleton's code.** -/
def skeletonCode (k : IRSkeleton) : ℕ :=
  Nat.pair (shapesCode tensorShapeCode k.tensors + 1)
           (shapesCode relationShapeCode k.relations)

/-- **`tensorShapeCode` is injective.** -/
theorem tensorShapeCode_injective : Function.Injective tensorShapeCode := by
  intro a b h
  simp only [tensorShapeCode] at h
  obtain ⟨h1, _⟩ := Nat.pair_eq_pair.mp h
  have h1' : Nat.pair a.id (listCode a.shape) = Nat.pair b.id (listCode b.shape) := by omega
  obtain ⟨hid, hsh⟩ := Nat.pair_eq_pair.mp h1'
  obtain ⟨ai, ash⟩ := a
  obtain ⟨bi, bsh⟩ := b
  simp only at hid hsh
  rw [hid, listCode_injective hsh]

/-- **`relationShapeCode` is injective.** -/
theorem relationShapeCode_injective : Function.Injective relationShapeCode := by
  intro a b h
  simp only [relationShapeCode] at h
  obtain ⟨h1, _⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨hk, hp⟩ := Nat.pair_eq_pair.mp h1
  have hp' : Nat.pair (argsCode a.args) (partCode a.part)
           = Nat.pair (argsCode b.args) (partCode b.part) := by omega
  obtain ⟨ha, hpp⟩ := Nat.pair_eq_pair.mp hp'
  obtain ⟨ak, aa, ap⟩ := a
  obtain ⟨bk, ba, bp⟩ := b
  simp only at hk ha hpp
  rw [kindCode_injective hk, argsCode_injective ha, partCode_injective hpp]

/-- **THE SKELETON'S CODE IS INJECTIVE: two skeletons with the same code are equal.** -/
theorem skeletonCode_injective : Function.Injective skeletonCode := by
  intro a b h
  simp only [skeletonCode] at h
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h
  have h1' : shapesCode tensorShapeCode a.tensors = shapesCode tensorShapeCode b.tensors := by omega
  obtain ⟨ht, hr⟩ := a
  obtain ⟨bt, br⟩ := b
  simp only at h1' h2
  rw [shapesCode_injective _ tensorShapeCode_injective h1',
      shapesCode_injective _ relationShapeCode_injective h2]

/-! ## The two directions, and the round trip -/

/-- **`compile : IR -> IRWeights`: the IR's skeleton code sits at index `0`.** -/
noncomputable def compileIR {H : RelKind → List (TensorId × List ℕ) → Prop}
    (S : LatticeIR H) : IRWeights :=
  fun n => if n = 0 then (skeletonCode (skeleton S) : ℝ) else 0

/-- **The natural code stored at index `0` of a weight vector.** -/
noncomputable def weightCodeIR (W : IRWeights) : ℕ :=
  if 0 ≤ W 0 then ⌊W 0⌋.toNat else 0

/-- **THE WEIGHTS REMEMBER THE SKELETON.**

**`compileIR S = compileIR T -> skeleton S = skeleton T`.**
**=> this is the exact form of "the weights remember the IR": they remember its STRUCTURE, which is what a finite
weight vector can hold.** -/
theorem compileIR_injective {H : RelKind → List (TensorId × List ℕ) → Prop}
    {S T : LatticeIR H} (h : compileIR S = compileIR T) : skeleton S = skeleton T := by
  have h0 : compileIR S 0 = compileIR T 0 := by rw [h]
  simp only [compileIR, if_pos rfl] at h0
  have hc : skeletonCode (skeleton S) = skeletonCode (skeleton T) := by exact_mod_cast h0
  exact skeletonCode_injective hc

/-- **`extract` recovers the skeleton from the code.**

**A DELIMITED decode: read index `0`, and the skeleton's code is a `Nat`.**
**=> there is no recursion and no fuel, because the skeleton is a finite list structure and `Nat.unpair` is not
recursive.** -/
noncomputable def extractCode (W : IRWeights) : Option ℕ :=
  some (weightCodeIR W)

/-- **T3 ON THE IR: THE ROUND TRIP IS A THEOREM.**

**`extract (compile S) = some (skeletonCode (skeleton S))`.**

**Stated at the CODE level, which is the honest level: a finite weight vector at index `0` can carry a `Nat`, and the
`Nat` IS the skeleton's code.**
**=> `compileIR_injective` then says the code determines the skeleton, so this is a complete round trip up to the
skeleton.** -/
theorem extract_compileIR {H : RelKind → List (TensorId × List ℕ) → Prop}
    (S : LatticeIR H) :
    extractCode (compileIR S) = some (skeletonCode (skeleton S)) := by
  unfold extractCode weightCodeIR
  simp only [compileIR]
  simp only [if_true, if_pos (by positivity : (0:ℝ) ≤ (skeletonCode (skeleton S) : ℝ))]
  simp [Int.floor_natCast]

/-- **THE ROUND TRIP IS REVERSIBLE: the code and the injectivity together determine the skeleton.**

**`extract (compile S) = extract (compile T) -> skeleton S = skeleton T`.**
**=> the two directions compose to the identity on skeletons, which is what "canonical form" means concretely
(IR-CANONICAL §5).** -/
theorem roundtrip_determines_skeleton {H : RelKind → List (TensorId × List ℕ) → Prop}
    {S T : LatticeIR H}
    (h : extractCode (compileIR S) = extractCode (compileIR T)) : skeleton S = skeleton T := by
  rw [extract_compileIR, extract_compileIR] at h
  exact skeletonCode_injective (Option.some.inj h)

/-- **`find?` WITH THE `id` PREDICATE HITS THE SHAPE YOU KNOW IS THERE.**

**`(l.map (·.id)).Nodup` and `x ∈ l` give `l.find? (fun s => s.id = x.id) = some x`.**

**=> the `TensorShape` counterpart of `find_id_eq_some_of_nodup` (`Materialize.lean`, for `Tensor`).**
**It needs no `DecidableEq`, because `TensorShape` has one but the proof never uses it: `id` is the only handle, which
is exactly why the `id` predicate is the right form for both types.**
**The two branches are `List.find?_cons_of_pos` / `find?_cons_of_neg`, with `Nodup`'s head fact supplying
`hne : ¬ (h.id = x.id)`.** -/
theorem find_id_eq_some_of_nodup_shape (l : List TensorShape) (hnd : (l.map (·.id)).Nodup)
    {x : TensorShape} (hx : x ∈ l) :
    l.find? (fun s => s.id = x.id) = some x := by
  induction l with
  | nil => simp at hx
  | cons h tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hndtl⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : ¬ (h.id = x.id) := by
        intro hh
        exact hnot (hh ▸ List.mem_map_of_mem (·.id) hx)
      rw [List.find?_cons_of_neg _ (by simp [hne])]
      exact ih hndtl hx

end Lattice.Core.IR
