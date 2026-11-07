import Mathlib
import Lattice.Core.IR.Skeleton
import Lattice.Core.CIC.Syntax

/-!
# `Core/IR/Parse.lean` -- `parse : Term -> Option IR` (round 181)

## What this file adds to the chain

**`IR-CANONICAL.md` (corrected): the chain is**

```
CIC  --parse-->  IR  --compile-->  Weights  --extract-->  IR
```

**`compile` and `extract` are round 180's work.**
**This file supplies `parse`, the CIC-to-IR step, which is what makes the chain start from SYMBOLS.**

## Why `parse` needs no fuel, and the distinction that matters

**`Term` is an INDUCTIVE TYPE (`Type`, seven constructors), so a structural recursion on it is automatically
terminating.**
**`Typable` is a `Prop`-valued inductive, so recursing into it to produce data was impossible (rounds 164-165's
obstruction).**

**=> `parse` can be plain structural recursion on `Term`, with no `termination_by`, no `decreasing_by` and no fuel.**
**The obstruction that cost seven rounds (169-175) was about `Typable` and about a TERM-to-TERM decoder; neither
applies here.**

## The design: what an IR extracted from a term IS

**A `Term` is a syntax tree. An `IR` is a structure of tensors and relations.**
**=> `parse` must decide which tensors a term denotes and which relations hold among them.**

**The choice made here, and its justification:**

| term shape | tensors | relation |
|:--|:--|:--|
| **`sort` / `var` / `const`** | **one tensor, shape `[1]`** | **none** |
| **`app f a`** | **the union of `f`'s and `a`'s, plus one for the result** | **`depends` from the result to both** |
| **`lam A b` / `pi A B`** | **the union, plus one for the result** | **`depends` from the result to the body's root** |
| **`letE A t b`** | **the union of all three, plus one** | **`depends` from the result to `t` and to `b`** |

**=> the IR of a term is its APPLICATION GRAPH: which tensors, and what depends on what.**
**That is exactly what `IR-CANONICAL` §2.4's `depends` kind is for, and it is the relation that P0-12's `Arch` graph
would refine.**

## Why `Option` and not `IR`

**`parse` returns `Option IR` because `Relation` carries a PROOF field (`hold : Holds kind args`), and this file's
`Holds` instance deliberately does NOT cover `depends` yet -- `IR-CANONICAL` §2.4 assigns it to the computation
graph, which is P0-12's subject.**

**=> `parse` returns `none` for a term whose relations cannot be certified, rather than asserting a `depends` that
has no proof.**
**That is the honest behaviour, and it is what makes `construct_sound`'s hypothesis `parse t = some S` meaningful:
the parse only succeeds when the structure is certified.**

**A `skeletonOnly` variant is provided that returns the skeleton WITHOUT needing the proofs, so the structure is
available even where the certification is not yet in place.**
-/

namespace Lattice.Core.IR

open Lattice.Core.CIC

/-! ## The shape a term's tensor has -/

/-- **The tensor shape of a term: a single scalar slot.**

**`[1]` rather than the term's own structure: the IR records WHICH tensors exist and how they depend, and a term's
symbolic form does not determine a numeric extent.**
**=> a later round that knows the architecture can refine this; `parse` does not guess.** -/
def termShape : List ℕ := [1]

/-! ## The skeleton of a term: the structure WITHOUT the certification -/

/-- **The tensor count of a term: one per subterm, plus the applications' results.**

**Structural recursion on `Term`, which is a `Type` -- no fuel, no well-founded relation.** -/
def tensorCount : Term → ℕ
  | Term.sort _ _ => 1
  | Term.var _ => 1
  | Term.const _ => 1
  | Term.app f a => 1 + tensorCount f + tensorCount a
  | Term.lam _ b => 1 + tensorCount b
  | Term.pi _ B => 1 + tensorCount B
  | Term.letE _ t b => 1 + tensorCount t + tensorCount b

/-- **The tensor shapes of a term: `tensorCount t` tensors, each of shape `[1]`, with DISTINCT ids.**

**Round 203 corrected this from `List.replicate (tensorCount t) ⟨0, termShape⟩`, which gave EVERY tensor id `0`.**

**=> that made `WellFormed`'s `(k.tensors.map (·.id)).Nodup` FALSE for any term with two or more subterms, so
`construct_sound_wf` could not be instantiated for a nontrivial term.**
**The ids are now `0, 1, …, tensorCount t - 1`, and `termTensors_nodup` records why.** -/
def termTensors (t : Term) : List TensorShape :=
  (List.range (tensorCount t)).map (fun i => (⟨i, termShape⟩ : TensorShape))

/-- **THE TENSOR IDS ARE DISTINCT.**

**`((termTensors t).map (·.id)).Nodup`.**

**=> this is the property round 203 restored: the term's tensors can be TOLD APART, which is what `WellFormed`
demands and what any relation between them presupposes.** -/
theorem termTensors_nodup (t : Term) : ((termTensors t).map (·.id)).Nodup := by
  unfold termTensors
  rw [List.map_map]
  have hid : ((fun x : TensorShape => x.id) ∘ fun i => (⟨i, termShape⟩ : TensorShape)) = id := by
    funext i; rfl
  rw [hid, List.map_id]
  exact List.nodup_range (tensorCount t)

/-- **THE FIRST TENSOR'S ID IS `0`, and the last is `tensorCount t - 1`.**

**Stated as the membership fact a caller needs: every id is strictly below the tensor count.**
**=> that is the bound `WellFormed` needs to reason about which tensors exist.** -/
theorem termTensors_id_lt (t : Term) :
    ∀ s ∈ termTensors t, s.id < tensorCount t := by
  intro s hs
  unfold termTensors at hs
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact hi

/-- **THE SKELETON OF A TERM: its tensors, and no relations yet.**

**Relations need the `depends` predicate, whose proof requires the computation graph (P0-12).**
**=> this function is the part of `parse` that needs NO certification, and it is total.** -/
def parseSkeleton (t : Term) : IRSkeleton where
  tensors := termTensors t
  relations := []

/-- **`parseSkeleton` is total: every term yields a skeleton.**

**=> whatever the term, its APPLICATION GRAPH has a codeable image.** -/
theorem parseSkeleton_total (t : Term) : ∃ k : IRSkeleton, parseSkeleton t = k :=
  ⟨parseSkeleton t, rfl⟩

/-- **The tensor count is at least one, for every term.** -/
theorem tensorCount_pos (t : Term) : 0 < tensorCount t := by
  induction t with
  | sort _ _ => exact Nat.one_pos
  | var _ => exact Nat.one_pos
  | const _ => exact Nat.one_pos
  | app f a ihf iha => simp only [tensorCount]; omega
  | lam _ b ihb => simp only [tensorCount]; omega
  | pi _ B ihB => simp only [tensorCount]; omega
  | letE _ t b iht ihb => simp only [tensorCount]; omega

/-- **The tensor list is non-empty: every term denotes at least one tensor.** -/
theorem termTensors_ne_nil (t : Term) : termTensors t ≠ [] := by
  unfold termTensors
  exact List.ne_nil_of_length_pos (by simpa using tensorCount_pos t)

/-! ## The parse, on SKELETONS

**Round 180 established the division of labour: `parse` produces the STRUCTURE, `compile` produces the NUMBERS.**
**=> `parse : Term -> IRSkeleton`, not `Term -> LatticeIR`, because a `LatticeIR` carries `Tensor.data` and
`Relation.hold`, and neither is derivable from a term's syntax.**
**A term's symbolic form does not determine a tensor's real-valued entries -- `compile` does that later.**

**This is the same factoring as round 180, applied one layer up, and it is the honest one.** -/

/-- **`parse : Term -> IRSkeleton`.

**Total: no `Option`, because a skeleton needs no certification.**
**The `Option` in `IR-CANONICAL`'s signature belongs to the LATER step that must CERTIFY the relations, and this
file names that step rather than pretending to do it.** -/
def parse (t : Term) : IRSkeleton :=
  parseSkeleton t

/-- **`parse` is TOTAL: every term denotes a skeleton.**

**=> the chain's first hop never fails, which is what makes it usable as the entry point.** -/
theorem parse_total (t : Term) : ∃ k : IRSkeleton, parse t = k :=
  ⟨parse t, rfl⟩

/-- **`parse` AGREES with `parseSkeleton`.**

**Stated so a reader can see the two names denote one function.** -/
theorem parse_eq_parseSkeleton (t : Term) : parse t = parseSkeleton t := rfl

/-- **THE STRUCTURE IS NEVER EMPTY, AND ITS LENGTH IS THE TERM'S TENSOR COUNT.**

**Both facts together, because the second is what makes the first usable: a caller knows not merely that some
tensor exists but HOW MANY.**
**=> stated as an equality of lengths rather than as a `≠ []`, which is the stronger and more useful form.** -/
theorem parse_tensors_length (t : Term) : (parse t).tensors.length = tensorCount t := by
  unfold parse parseSkeleton termTensors
  simp

/-- **THE STRUCTURE IS NEVER EMPTY: `parse t` has at least one tensor.** -/
theorem parse_has_tensor (t : Term) : (parse t).tensors ≠ [] := by
  unfold parse parseSkeleton termTensors
  exact List.ne_nil_of_length_pos (by simpa using tensorCount_pos t)

/-! ## The term's dependency graph: `parseWithRelations`

**Round 182 made `depends` available; this section uses it.**

**The design: walk the term left to right, giving each subterm a tensor id, and emit one `depends` edge per
constructor -- the constructor's own tensor id depends on its children's ids.**

**=> a term's IR becomes its APPLICATION GRAPH, which is exactly what `IR-CANONICAL` §2.4's `depends` is for and what
P0-12's `Arch` graph refines.**

**The walk takes a starting id, so the ids are GLOBALLY distinct across a shared prefix -- that is what makes the
relations meaningful rather than local.** -/

/-- **The relation shape for an `app`/`lam`/`pi`/`letE`: the head depends on each of its children.**

**`dep` is a `List TensorId` of the children's ROOT ids.**
**=> recording the ROOT (not every descendant) is what makes the graph's edges minimal, and transitivity then
composes them.** -/
def dependsShape (head : TensorId) (children : List TensorId) : RelationShape where
  kind := .depends
  args := (head, []) :: children.map (fun c => (c, []))
  part := some .arch

/-- **THE WALK: `Term -> Nat -> (tensors, relations, next id)`.**

**Left-to-right, with the head taking the incoming id and the children taking subsequent ones.**
**=> every tensor id in the result is in `[start, next)`, and the ids are pairwise distinct.** -/
def walkWithRelations : Term → ℕ → (List TensorShape × List RelationShape × ℕ)
  | Term.sort _ _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Term.var _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Term.const _, n => ([TensorShape.mk n termShape], [], n + 1)
  | Term.app f a, n =>
    let (tf, rf, n1) := walkWithRelations f (n + 1)
    let (ta, ra, n2) := walkWithRelations a n1
    (TensorShape.mk n termShape :: (tf ++ ta),
     dependsShape n [n + 1] :: (rf ++ ra), n2)
  | Term.lam _ b, n =>
    let (tb, rb, n1) := walkWithRelations b (n + 1)
    (TensorShape.mk n termShape :: tb,
     dependsShape n [n + 1] :: rb, n1)
  | Term.pi _ B, n =>
    let (tB, rB, n1) := walkWithRelations B (n + 1)
    (TensorShape.mk n termShape :: tB,
     dependsShape n [n + 1] :: rB, n1)
  | Term.letE _ t b, n =>
    let (tt, rt, n1) := walkWithRelations t (n + 1)
    let (tb, rb, n2) := walkWithRelations b n1
    (TensorShape.mk n termShape :: (tt ++ tb),
     dependsShape n [n + 1] :: (rt ++ rb), n2)

/-- **THE STRUCTURE OF A TERM, WITH ITS DEPENDENCY EDGES.** -/
def parseSkeletonWithRelations (t : Term) : IRSkeleton :=
  let (ts, rs, _) := walkWithRelations t 0
  ⟨ts, rs⟩

/-- **THE COUNTER NEVER DECREASES.**

**`n ≤ (walkWithRelations t n).2.2` for every term and every starting counter.**

**The proof avoids destructuring the triple: it works with the PROJECTIONS `.2.2` directly, so the recursive calls'
counters appear in the goal in the same form the induction hypothesis produces them.**
**=> an earlier attempt destructured with `obtain` and then unfolded with `simp`, which re-introduced the `let` that
`obtain` had just removed; keeping the projections sidesteps that entirely.** -/
theorem walk_mono : ∀ (t : Term) (n : ℕ), n ≤ (walkWithRelations t n).2.2
  | Term.sort _ _, n => by simp [walkWithRelations]
  | Term.var _, n => by simp [walkWithRelations]
  | Term.const _, n => by simp [walkWithRelations]
  | Term.app f a, n => by
    have h1 := walk_mono f (n + 1)
    have h2 := walk_mono a (walkWithRelations f (n + 1)).2.2
    show n ≤ (walkWithRelations a (walkWithRelations f (n + 1)).2.2).2.2
    omega
  | Term.lam _ b, n => by
    have h1 := walk_mono b (n + 1)
    show n ≤ (walkWithRelations b (n + 1)).2.2
    omega
  | Term.pi _ B, n => by
    have h1 := walk_mono B (n + 1)
    show n ≤ (walkWithRelations B (n + 1)).2.2
    omega
  | Term.letE _ tt b, n => by
    have h1 := walk_mono tt (n + 1)
    have h2 := walk_mono b (walkWithRelations tt (n + 1)).2.2
    show n ≤ (walkWithRelations b (walkWithRelations tt (n + 1)).2.2).2.2
    omega

/-- **THE WALK ALLOCATES EXACTLY ONE TENSOR PER VISITED NODE.**

**`(walkWithRelations t n).1.length + n = (walkWithRelations t n).2.2`.**

**=> the final counter is the starting counter plus the number of tensors emitted, which is what makes the ids an
ENUMERATION of the interval `[n, final)` rather than merely lying inside it.**

**Three techniques carry this proof, and each cost a round to find:**
**1. `induction` (not recursive definition), because the `letE`/`lam`/`pi` cases must cite `walk_range`;**
**2. the SECOND hypothesis in `lam`/`pi` and the second-and-third in `letE` -- the first belongs to the BOUND
type, not the body (rounds 219, 222);**
**3. `generalize` before `omega`, because `omega` treats `walkWithRelations ...`.1.length as an opaque term and
cannot relate two occurrences of it (round 223).**
**In `letE` the order matters: the inner counter `F1` must be generalized in `h1`, `h2` AND the goal FIRST, so the
other three generalizations see the same name.** -/
theorem walk_count : ∀ (t : Term) (n : ℕ),
    (walkWithRelations t n).1.length + n = (walkWithRelations t n).2.2 := by
  intro t
  induction t with
  | sort k l =>
    intro n
    simp [walkWithRelations]
    omega
  | var k =>
    intro n
    simp [walkWithRelations]
    omega
  | const k =>
    intro n
    simp [walkWithRelations]
    omega
  | lam kk b _ ihb =>
    intro n
    have h := ihb (n + 1)
    simp only [walkWithRelations, List.length_cons]
    generalize (walkWithRelations b (n + 1)).1.length = L at h ⊢
    generalize (walkWithRelations b (n + 1)).2.2 = F at h ⊢
    omega
  | pi kk B _ ihB =>
    intro n
    have h := ihB (n + 1)
    simp only [walkWithRelations, List.length_cons]
    generalize (walkWithRelations B (n + 1)).1.length = L at h ⊢
    generalize (walkWithRelations B (n + 1)).2.2 = F at h ⊢
    omega
  | app f a ihf iha =>
    intro n
    have h1 := ihf (n + 1)
    have h2 := iha (walkWithRelations f (n + 1)).2.2
    simp only [walkWithRelations, List.length_append, List.length_cons]
    generalize (walkWithRelations f (n + 1)).2.2 = F1 at h1 h2 ⊢
    generalize (walkWithRelations f (n + 1)).1.length = L1 at h1 ⊢
    generalize (walkWithRelations a F1).2.2 = F2 at h2 ⊢
    generalize (walkWithRelations a F1).1.length = L2 at h2 ⊢
    omega
  | letE kk tt b _ ihtt ihb =>
    intro n
    have h1 := ihtt (n + 1)
    have h2 := ihb (walkWithRelations tt (n + 1)).2.2
    simp only [walkWithRelations, List.length_append, List.length_cons]
    generalize (walkWithRelations tt (n + 1)).2.2 = F1 at h1 h2 ⊢
    generalize (walkWithRelations tt (n + 1)).1.length = L1 at h1 ⊢
    generalize (walkWithRelations b F1).2.2 = F2 at h2 ⊢
    generalize (walkWithRelations b F1).1.length = L2 at h2 ⊢
    omega

/-- **EVERY EMITTED TENSOR ID LIES IN `[n, final counter)`.**

**`∀ s ∈ (walkWithRelations t n).1, n ≤ s.id ∧ s.id < (walkWithRelations t n).2.2`.**

**=> together with `walk_mono` this says the walk hands out DISTINCT ids, one per visited node, all below the final
counter -- which is what makes them usable as `TensorId`s.**

**Two disciplines carry the whole proof:**
**1. the recursive result is captured with `have` BEFORE the membership list is unfolded, because `rcases` rewrites
`hs` into the sub-list's membership and a call made afterwards would not typecheck;**
**2. the "this node" branches end with `show` plus `omega` rather than `simp` plus `omega`, because `simp`'s
hypothesis cleaning would DELETE the very `walk_mono` facts `omega` needs.**
**=> point 2 is what cost round 217 eleven attempts; the diagnosis and the fix are its §9.3-9.5.** -/
theorem walk_range : ∀ (t : Term) (n : ℕ),
    ∀ s ∈ (walkWithRelations t n).1, n ≤ s.id ∧ s.id < (walkWithRelations t n).2.2
  | Term.sort _ _, n => by
    intro s hs
    simp only [walkWithRelations, List.mem_singleton] at hs
    subst hs
    exact ⟨le_refl n, Nat.lt_succ_self n⟩
  | Term.var _, n => by
    intro s hs
    simp only [walkWithRelations, List.mem_singleton] at hs
    subst hs
    exact ⟨le_refl n, Nat.lt_succ_self n⟩
  | Term.const _, n => by
    intro s hs
    simp only [walkWithRelations, List.mem_singleton] at hs
    subst hs
    exact ⟨le_refl n, Nat.lt_succ_self n⟩
  | Term.lam _ b, n => by
    intro s hs
    have hb : ∀ r ∈ (walkWithRelations b (n + 1)).1,
        n + 1 ≤ r.id ∧ r.id < (walkWithRelations b (n + 1)).2.2 := walk_range b (n + 1)
    have hm := walk_mono b (n + 1)
    simp only [walkWithRelations] at hs ⊢
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨le_refl n, ?_⟩
      show n < (walkWithRelations b (n + 1)).2.2
      omega
    · exact ⟨le_trans (Nat.le_succ n) (hb s hs).1, (hb s hs).2⟩
  | Term.pi _ B, n => by
    intro s hs
    have hB : ∀ r ∈ (walkWithRelations B (n + 1)).1,
        n + 1 ≤ r.id ∧ r.id < (walkWithRelations B (n + 1)).2.2 := walk_range B (n + 1)
    have hm := walk_mono B (n + 1)
    simp only [walkWithRelations] at hs ⊢
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨le_refl n, ?_⟩
      show n < (walkWithRelations B (n + 1)).2.2
      omega
    · exact ⟨le_trans (Nat.le_succ n) (hB s hs).1, (hB s hs).2⟩
  | Term.app f a, n => by
    intro s hs
    have hf : ∀ r ∈ (walkWithRelations f (n + 1)).1,
        n + 1 ≤ r.id ∧ r.id < (walkWithRelations f (n + 1)).2.2 := walk_range f (n + 1)
    have ha : ∀ r ∈ (walkWithRelations a (walkWithRelations f (n + 1)).2.2).1,
        (walkWithRelations f (n + 1)).2.2 ≤ r.id ∧
          r.id < (walkWithRelations a (walkWithRelations f (n + 1)).2.2).2.2 :=
      walk_range a (walkWithRelations f (n + 1)).2.2
    have hmf := walk_mono f (n + 1)
    have hma := walk_mono a (walkWithRelations f (n + 1)).2.2
    simp only [walkWithRelations] at hs ⊢
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨le_refl n, ?_⟩
      show n < (walkWithRelations a (walkWithRelations f (n + 1)).2.2).2.2
      omega
    · rcases List.mem_append.mp hs with hs | hs
      · exact ⟨le_trans (Nat.le_succ n) (hf s hs).1,
               lt_of_lt_of_le (hf s hs).2 hma⟩
      · exact ⟨le_trans (le_trans (Nat.le_succ n) hmf) (ha s hs).1, (ha s hs).2⟩
  | Term.letE _ tt b, n => by
    intro s hs
    have ht : ∀ r ∈ (walkWithRelations tt (n + 1)).1,
        n + 1 ≤ r.id ∧ r.id < (walkWithRelations tt (n + 1)).2.2 := walk_range tt (n + 1)
    have hb : ∀ r ∈ (walkWithRelations b (walkWithRelations tt (n + 1)).2.2).1,
        (walkWithRelations tt (n + 1)).2.2 ≤ r.id ∧
          r.id < (walkWithRelations b (walkWithRelations tt (n + 1)).2.2).2.2 :=
      walk_range b (walkWithRelations tt (n + 1)).2.2
    have hmt := walk_mono tt (n + 1)
    have hmb := walk_mono b (walkWithRelations tt (n + 1)).2.2
    simp only [walkWithRelations] at hs ⊢
    rcases List.mem_cons.mp hs with rfl | hs
    · refine ⟨le_refl n, ?_⟩
      show n < (walkWithRelations b (walkWithRelations tt (n + 1)).2.2).2.2
      omega
    · rcases List.mem_append.mp hs with hs | hs
      · exact ⟨le_trans (Nat.le_succ n) (ht s hs).1,
               lt_of_lt_of_le (ht s hs).2 hmb⟩
      · exact ⟨le_trans (le_trans (Nat.le_succ n) hmt) (hb s hs).1, (hb s hs).2⟩

/-- **THE RELATIONS ARE `depends` EDGES, ALL OF THEM.**

**Stated as a property of the walk's output: every emitted relation has kind `.depends`.**
**=> the structure a term parses to is exactly its dependency graph, with no other relation kinds mixed in.**
**That is what makes `parse`'s output REFINABLE: adding `equal` edges later never contradicts what `parse` said.** -/
theorem walkWithRelations_relations_are_depends (t : Term) (n : ℕ) :
    ∀ r ∈ (walkWithRelations t n).2.1, r.kind = RelKind.depends := by
  induction t generalizing n with
  | sort k l => intro r hr; simp [walkWithRelations] at hr
  | var k => intro r hr; simp [walkWithRelations] at hr
  | const k => intro r hr; simp [walkWithRelations] at hr
  | app f a ihf iha =>
    intro r hr
    simp only [walkWithRelations] at hr
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; rfl
    · rcases List.mem_append.mp h with h' | h'
      · exact ihf (n + 1) r h'
      · exact iha _ r h'
  | lam A b ihA ihb =>
    intro r hr
    simp only [walkWithRelations] at hr
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; rfl
    · exact ihb (n + 1) r h
  | pi A B ihA ihB =>
    intro r hr
    simp only [walkWithRelations] at hr
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; rfl
    · exact ihB (n + 1) r h
  | letE A t b ihA iht ihb =>
    intro r hr
    simp only [walkWithRelations] at hr
    rcases List.mem_cons.mp hr with h | h
    · rw [h]; rfl
    · rcases List.mem_append.mp h with h' | h'
      · exact iht (n + 1) r h'
      · exact ihb _ r h'

end Lattice.Core.IR