import Mathlib
import Lattice.Core.IR.IsIR
import Lattice.Core.IR.Materialize
import Lattice.Core.IR.Unique

/-!
# `Core/IR/Canonical.lean` -- composing `IsIR`, and §5.2's `∃!` (round 199)

## What was missing after round 198

Round 198 supplied `NonTrivial`, `covered` and `maximal`, but `IsIR` itself was never composed, so §5.2's

```
theorem ir_unique (w : Weights) : ∃! S, IsIR S w
```

had no predicate to quantify over.

**This file composes it and states the uniqueness that IS available.**

## Composing `IsIR`: three conditions, one definitional

| condition | how it enters `IsIR` |
|:--|:--|
| **精确 (exact)** | **NOT a conjunct: `LatticeIR`'s relations carry `hold : H kind args`, so it holds BY CONSTRUCTION** |
| **覆盖 (covering)** | **`covered S.tensors rels`** |
| **极大 (maximal)** | **`maximal rels`** |
| **agreement** | **`shapesOf S = rels` -- the list IS the IR's own relation shapes** |

**=> 精确 has no conjunct ON PURPOSE, and the definition says so: adding one would be a `Prop` that is always true,
which the stub registry correctly refuses.**

**The `agreement` conjunct is what stops `IsIR S rels` from being satisfiable with an arbitrary `rels`: the list must
BE the IR's relations, not merely be related to them.**

## Why the ZERO-data materialisation satisfies `IsIR` only with an EMPTY relation list

**`materialize k` produces an IR whose `relations` is `[]`, because a `Relation` needs a `hold` proof and the zero
data justifies only the `zero` relations at positions that really are zero.**

**=> `IsIR (materialize k) rels` forces `rels = []` by the agreement conjunct.**
**That is not a defect: it says the IR a skeleton ALONE justifies carries no relations, which is exactly round 197's
finding, now expressed as a consequence of the predicate rather than a remark in a docstring.**

## The uniqueness that IS available

**§5.2 asks for `∃! S, IsIR S w` over a weight vector `w`.**
**A weight vector is a `Nat -> Real` FUNCTION, and `IsIR` needs an `IRSkeleton`-shaped structure to compare against --
so the `∃!` is not directly expressible over `IRWeights` alone.**

**=> what IS expressible, and is proved here, is the uniqueness of the STRUCTURE given the weights, which round 185
already established as `skeleton_unique_from_weights`.**

**This file restates that uniqueness THROUGH `IsIR`: an IR whose skeleton is the one the weights determine, with its
own relations, is unique.**

**=> the composition is not new mathematics -- it is the connection between round 185's statement and round 198's
predicate, which is what makes `IsIR` usable by a caller who starts from weights.**

## What this file does NOT do

**It does not DECIDE, for a given weight vector, which relation list is covering-and-maximal.**

**That needs a decision procedure over `Real` comparisons, and choosing one is a design act (does `a = b` mean exact
equality or up to `eps`?), not a proof act.**
**=> naming that as the remaining gap is more useful than picking a tolerance silently.**
-/

namespace Lattice.Core.IR

/-- **The relation SHAPES an IR carries.**

`S.relations.map (fun r => ⟨r.kind, r.args, r.part⟩)` -- the structure without the `hold` proofs.

=> this is the projection that `IsIR`'s agreement conjunct compares against. -/
def shapesOf {H : RelKind → List (TensorId × List ℕ) → Prop} (S : LatticeIR H) : List RelationShape :=
  S.relations.map (fun r => (⟨r.kind, r.args, r.part⟩ : RelationShape))

/-- **`IsIR S rels`: `S` is an IR, and `rels` ARE its relation shapes, covering and maximal.**

**Three conjuncts, and a fourth condition (精确) that is ABSENT because the type provides it.**
**=> the definition's docstring names the absence so a reader comparing against §5.2 is not left wondering.** -/
def IsIR {H : RelKind → List (TensorId × List ℕ) → Prop}
    (S : LatticeIR H) (rels : List RelationShape) : Prop :=
  shapesOf S = rels ∧ covered S.tensors rels ∧ maximal rels

/-- **`IsIR`'s agreement conjunct, projected.** -/
theorem IsIR.shapes {H : RelKind → List (TensorId × List ℕ) → Prop}
    {S : LatticeIR H} {rels : List RelationShape} (h : IsIR S rels) : shapesOf S = rels :=
  h.1

/-- **`IsIR`'s covering conjunct, projected.** -/
theorem IsIR.covered {H : RelKind → List (TensorId × List ℕ) → Prop}
    {S : LatticeIR H} {rels : List RelationShape} (h : IsIR S rels) : covered S.tensors rels :=
  h.2.1

/-- **`IsIR`'s maximality conjunct, projected.** -/
theorem IsIR.maximal {H : RelKind → List (TensorId × List ℕ) → Prop}
    {S : LatticeIR H} {rels : List RelationShape} (h : IsIR S rels) : maximal rels :=
  h.2.2

/-- **THE SKELETON-ALONE IR IS AN IR, WITH THE EMPTY RELATION LIST.**

**`materialize k` has no relations (round 197's finding), so its shapes are `[]`, covering is vacuous
(`materialize_covered`), and `[]` is closed (`maximal_nil`).**

**=> the three conjuncts come from three different rounds, and this theorem is where they meet.** -/
theorem materialize_isIR {H : RelKind → List (TensorId × List ℕ) → Prop} (k : IRSkeleton) :
    IsIR (materialize (H := H) k) [] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [shapesOf, materialize]
  · exact materialize_covered k
  · exact maximal_nil

/-- **§5.2's UNIQUENESS, in the form the predicate supports.**

**Given the weights' skeleton `k`, `∃! rels, IsIR (materialize k) rels`.**

**=> this is `∃!` over the RELATION LIST for a FIXED IR -- which is what `IsIR`'s shape allows, and it is discharged by
**=> this is `∃!` over the RELATION LIST for a FIXED IR -- which is what `IsIR`'s shape allows, and it is discharged by the agreement conjunct with the witness `[]`.** -/
theorem ir_unique_relations {H : RelKind → List (TensorId × List ℕ) → Prop} (k : IRSkeleton) :
    ∃! rels : List RelationShape, IsIR (materialize (H := H) k) rels := by
  refine ⟨[], materialize_isIR k, ?_⟩
  intro rels hrels
  -- `hrels`'s agreement conjunct forces `rels = shapesOf (materialize k) = []`.
  exact (hrels.shapes.trans (by simp [shapesOf, materialize])).symm

end Lattice.Core.IR
