import Mathlib
import Lattice.Core.IR.Basic

/-!
# `Core/IR/Relations.lean` -- the relation predicates (round 178, P1-2)

## What this implements

**`IR-CANONICAL.md` §2.4 lists the initial relation set.**
**This file supplies `RelationHolds` for the two that need NO architecture graph: `equal` and `zero`.**
**`depends` needs the computation graph, which is P0-11's subject, so it is deliberately left out and named.**

## The shape of a relation predicate

**Each predicate takes the relation's arguments and asks whether the TENSOR SLICES they name agree in the way the
kind says.**

**An argument is `(TensorId, List Nat)` -- the tensor, plus the multi-axis index.**
**=> "the slice at index `i` of tensor `t`" is the primitive notion, and the predicates are comparisons of slices.**

**This is what makes the IR's relations CHECKABLE rather than asserted: a `Relation` carries a proof that its
predicate holds, and the predicate is a decidable comparison of real-valued slices.**

## What this file proves

| theorem | content |
|:--|:--|
| **`Slice`** | **a tensor plus the index at which it is read** |
| **`sliceValue`** | **the real number a slice denotes** |
| **`equalHolds`** | **two slices denote the same value** |
| **`zeroHolds`** | **a slice denotes zero** |
| **`equalHolds_refl`** | **`equal` is reflexive** |
| **`equalHolds_symm`** | **`equal` is symmetric** |
| **`equalHolds_trans`** | **`equal` is transitive** |
| **`equal_zero_consistent`** | **if `a` is zero and `a = b` then `b` is zero** |

**=> the three algebraic laws are what make `equal` usable as a relation, and the last theorem is the one that ties
the two kinds together.**

## What this file does NOT do

**It does not decide `Holds` for `lowRank`, `block`, `symmetry`, `ordered`, `scaled`, `transposed` or `shared`:**
**each needs its own mathematics (rank, block boundaries, group actions, order, ratios, transposition, aliasing), and
folding them into one file would make a file that is about the IR's SHAPE pretend to be about linear algebra.**

**=> `Holds` is a parameter of `Relation`, so new kinds can be added without touching the IR's definition -- which
is exactly what IR-CANONICAL §4.4 asks for.**
-/

namespace Lattice.Core.IR

/-- **A tensor read at one multi-axis index.**

**The index is a `List Nat` because a tensor's shape is multi-axis: `(t, [i, j])` means "the entry at row `i`,
column `j`".**
**=> the same relation kind applies at any arity, which is what "high-dimensional hyperedge" means concretely.** -/
structure Slice (read : TensorId → List ℕ → ℝ) where
  /-- **The tensor.** -/
  tensor : TensorId
  /-- **The multi-axis index.** -/
  index : List ℕ

/-- **The real number a slice denotes.** -/
def Slice.value {read : TensorId → List ℕ → ℝ} (s : Slice read) : ℝ :=
  read s.tensor s.index

/-- **`equal`: two slices denote the same value.** -/
def equalHolds {read : TensorId → List ℕ → ℝ} (args : List (TensorId × List ℕ)) : Prop :=
  match args with
  | [a, b] => read a.1 a.2 = read b.1 b.2
  | _ => False

/-- **`zero`: a slice denotes zero.**

**The predicate is about the VALUE, not about the tensor being zero everywhere -- a single index can be zero in an
otherwise nonzero tensor, and saying "the tensor is the zero tensor" would be a much stronger claim than
`IR-CANONICAL` §2.4 asks for.** -/
def zeroHolds {read : TensorId → List ℕ → ℝ} (args : List (TensorId × List ℕ)) : Prop :=
  match args with
  | [a] => read a.1 a.2 = 0
  | _ => False

/-- **`equal` is REFLEXIVE.**

**A slice equals itself, so `equal` over `[a, a]` always holds.**
**=> this is what lets an IR contain the trivial equality without a proof obligation.** -/
theorem equalHolds_refl {read : TensorId → List ℕ → ℝ} (a : TensorId × List ℕ) :
    equalHolds (read := read) [a, a] :=
  rfl

/-- **`equal` is SYMMETRIC.**

**The two sides of an `equal` relation can be swapped.**
**=> the IR does not need to record an orientation for equality, which keeps the relation set free of a symmetry
that carries no information.** -/
theorem equalHolds_symm {read : TensorId → List ℕ → ℝ} {a b : TensorId × List ℕ}
    (h : equalHolds (read := read) [a, b]) : equalHolds (read := read) [b, a] :=
  h.symm

/-- **`equal` is TRANSITIVE.**

**Two equalities through a common slice compose.**
**=> the relation set can be closed under transitivity without adding relations, because the closure is a theorem
about the predicate rather than a new element of the IR.** -/
theorem equalHolds_trans {read : TensorId → List ℕ → ℝ} {a b c : TensorId × List ℕ}
    (h1 : equalHolds (read := read) [a, b]) (h2 : equalHolds (read := read) [b, c]) :
    equalHolds (read := read) [a, c] :=
  h1.trans h2

/-- **THE TWO KINDS AGREE: zero travels along equality.**

**If `a` is zero and `a = b`, then `b` is zero.**
**=> this is the first theorem that relates two DIFFERENT relation kinds, and it is what makes the relation set more
than a list of independent facts: some kinds constrain others.** -/
theorem equal_zero_consistent {read : TensorId → List ℕ → ℝ} {a b : TensorId × List ℕ}
    (ha : zeroHolds (read := read) [a]) (he : equalHolds (read := read) [a, b]) :
    zeroHolds (read := read) [b] := by
  show read b.1 b.2 = 0
  rw [← he]
  exact ha

/-- **THE PREDICATE THE IR USES.**

**`RelationHolds` is a PARAMETER of `Relation` (`Basic.lean`), and this is the instance covering the two kinds this
file defines.**
**A kind not handled here yields `False`, which means no `Relation` of that kind can be constructed -- a
deliberate choice: a kind whose semantics is not yet defined cannot silently enter an IR.** -/
def basicHolds {read : TensorId → List ℕ → ℝ} :
    RelKind → List (TensorId × List ℕ) → Prop
  | .equal, args => equalHolds (read := read) args
  | .zero, args => zeroHolds (read := read) args
  | _, _ => False

/-- **`basicHolds` rejects every kind it does not define.**

**=> an IR built over `basicHolds` contains no `lowRank`, no `symmetry`, no `depends`, and that is visible as a
theorem rather than as a convention.** -/
theorem basicHolds_unhandled {read : TensorId → List ℕ → ℝ} (k : RelKind)
    (args : List (TensorId × List ℕ))
    (hnot : k ≠ .equal) (hnot2 : k ≠ .zero) : ¬ basicHolds (read := read) k args := by
  intro h
  cases k <;> simp_all [basicHolds]

end Lattice.Core.IR
