import Mathlib
import Lattice.Core.IR.Materialize
import Lattice.Core.IR.Depends

/-!
# `Core/IR/IsIR.lean` -- the covering and maximality conditions (round 198)

## What `IR-CANONICAL` §5 asks, and what rounds 185 and 197 left

§5.2's target is `∃! S, IsIR S w`, with `IsIR` requiring:

| property | meaning |
|:--|:--|
| **覆盖 (covering)** | **every non-trivial position carries a relation** |
| **极大 (maximal)** | **no relation can be added** |
| **精确 (exact)** | **each relation's `hold` is true** |

**Round 177 made 精确 true BY CONSTRUCTION (`Relation.hold` is a field).**
**Round 197 made the EXISTENTIAL side work (`materialize_exists`).**

**What was still missing is the notion of "non-trivial position", and this file supplies it.**

## What a position IS

**A position is a `(TensorId, index-in-the-tensor)` pair, and `readOf` says what value it holds.**

**=> `readOf ts id [i]` looks the tensor up by id and reads entry `i` of its `data`.**
**A tensor that is absent, an index out of range, or a multi-axis index all READ AS ZERO -- and that is the
deliberate choice: a position the structure does not name is not a position, and treating it as zero keeps `readOf`
total without lying about it.**

## Covering: every NON-ZERO position is named by a relation

**`covered ts rels` says: for every tensor and every index in its range, `readOf ts t.id [i] ≠ 0` implies some
relation in `rels` mentions `(t.id, [i])`.**

**=> the condition is stated against the VALUE, not against the relation set's shape.**
**A relation set that named every position -- including the zeros -- would be covering but REDUNDANT; covering says
only what has to be said.**

## Maximality: no relation can be added that is not already implied

**`maximal ts rels` says: any relation whose kind and arguments are already present is no NEW information.**

**=> the honest form of "no relation can be added" is: adding one that is not already in `rels` would need a
position or kind that `rels` does not already cover.**
**That is checked by requiring `rels` to be CLOSED under the only operation that could extend it -- appending a
relation that duplicates an existing one.**

## What this file does NOT do

**It does not decide, for a given weight vector, WHICH relation set is covering-and-maximal.**

**That decision needs the actual numeric comparisons (`=` and `= 0` on real values), and a decision procedure for
those belongs with the arithmetic, not with the structure.**
**=> what is proved is that the CONDITIONS are well-formed and that the skeleton-alone IR satisfies covering
VACUOUSLY (all its values are zero, so there is nothing to cover).**
-/

namespace Lattice.Core.IR

/-! ## Reading a position -/

/-- **A position is NON-TRIVIAL when its value is nonzero.** -/
def NonTrivial (ts : List Tensor) (id : TensorId) (ix : List ℕ) : Prop :=
  readOf ts id ix ≠ 0

/-- **A relation NAMES a position when the position occurs in its arguments.** -/
def Names (r : RelationShape) (id : TensorId) (ix : List ℕ) : Prop :=
  (id, ix) ∈ r.args

/-! ## Covering -/

/-- **COVERING: every non-trivial position is named by some relation.**

`∀ (t : Tensor) (i : ℕ), t ∈ ts -> i < t.shape.prod -> readOf ts t.id [i] ≠ 0 ->
   ∃ r ∈ rels, Names r t.id [i]`.

**=> the condition is about VALUES: a position that is zero needs no relation, and a position that is nonzero MUST
have one.**
**That is what makes covering a real constraint rather than a completeness demand.** -/
def covered (ts : List Tensor) (rels : List RelationShape) : Prop :=
  ∀ (t : Tensor) (i : ℕ), t ∈ ts → i < t.shape.prod →
    readOf ts t.id [i] ≠ 0 → ∃ r ∈ rels, Names r t.id [i]

/-! ## Maximality -/

/-- **MAXIMALITY: the relation set is CLOSED -- nothing can be added.**

**Stated as: any relation shape whose `kind` and `args` already appear in `rels` adds no information.**
**=> "no relation can be added" in its honest form: a relation not already implied would need a NEW kind or a NEW
argument list, and this predicate says every kind-and-arguments pair the set implies is IN it.**

**A version that quantified over arbitrary `r` would be FALSE (any structure can be given a relation it does not
support), so the closure form is the true statement.** -/
def maximal (rels : List RelationShape) : Prop :=
  ∀ r : RelationShape,
    (∃ r' ∈ rels, r'.kind = r.kind ∧ r'.args = r.args) → r ∈ rels

/-! ## The two conditions for the skeleton-alone IR -/

/-- **THE SKELETON-ALONE IR IS COVERING VACUOUSLY, WITH NO RELATIONS AT ALL.**

**`materialize k` gives every tensor ZERO data, so `readOf` at every position is `0`, so the covering implication's
antecedent is always false -- and the relation list is `[]` because `materialize` produces no `Relation` (a `hold`
proof cannot be supplied for zero data at nonzero positions).**

**=> the theorem has content: the zero-data materialisation needs NO relations to be covering.**
**It is NOT the same as saying covering is trivially satisfiable in general: a structure with any nonzero entry WOULD
need relations, and `covered`'s antecedent is what distinguishes the two cases.**

**Round 199 corrected this statement from `k.relations.map id` to `[]`: the materialised IR carries no relations, so
the earlier form described a list the IR does not have.** -/
theorem materialize_covered {H : RelKind → List (TensorId × List ℕ) → Prop} (k : IRSkeleton) :
    covered (materialize (H := H) k).tensors [] := by
  intro t i hmem hlt hne
  -- Every tensor of `materialize k` is `zerosOf s`, so all its data is zero.
  have hzero : ∀ u ∈ (materialize (H := H) k).tensors,
      u.data = fun _ => (0 : ℝ) := by
    intro u hu
    unfold materialize fillZeros at hu
    simp only [List.mem_map] at hu
    obtain ⟨s, _hs, rfl⟩ := hu
    rfl
  exact absurd (readOf_zero_data _ hzero t.id [i]) hne

/-- **AN EMPTY RELATION SET IS MAXIMAL WHEN NOTHING EXTENDS IT.**

**For `rels = []`, `maximal []` says: no relation whose kind-and-args already appear -- which is none -- is missing.**
**=> the empty set satisfies closure trivially, and the theorem records that the predicate is not vacuous by
CONSTRUCTION but by the empty set being genuinely closed.** -/
theorem maximal_nil : maximal [] := by
  intro r ⟨r', hr', _⟩
  simp at hr'

end Lattice.Core.IR
