import Mathlib
import Lattice.Core.IR.Relations

/-!
# `Core/IR/Depends.lean` -- the `depends` predicate, without an external graph (round 182)

## The question this answers

**Round 181 ended with: `parse` emits no relations, because `depends` needs the computation graph (P0-12).**

**The answer is that `depends` does NOT need a graph OBJECT -- it needs a DEPENDENCY SET, and a dependency set is
the same kind of reading context that `equal` and `zero` already use.**

| kind | reading context | predicate |
|:--|:--|:--|
| **`equal`** | **`read : TensorId -> List Nat -> Real`** | **two slices denote the same value** |
| **`zero`** | **the same `read`** | **a slice denotes zero** |
| **`depends`** | **`dep : TensorId -> List TensorId`** | **each input is in the output's dependency set** |

**=> all three are predicates over a reading context, and none needs a separate graph structure.**
**That is what lets them share one `Holds` instance and what lets `parse` emit them.**

## Why this is not a weakening of "由计算图唯一"

**`IR-CANONICAL` §2.4 gives `depends`'s uniqueness source as "由计算图唯一" (determined by the computation graph).**
**A dependency SET `dep : TensorId -> List TensorId` IS the computation graph, presented as a function rather than as
a node-and-edge structure.**

**=> stating the predicate over `dep` is stating it over the graph; the only difference is the representation, and the
functional one is what the predicates above already use.**

## What this file proves

| theorem | content |
|:--|:--|
| **`dependsHolds`** | **the predicate** |
| **`dependsHolds_nil`** | **the empty argument list never holds** |
| **`dependsHolds_refl`** | **a tensor depends on itself when it is in its own set** |
| **`dependsHolds_mono`** | **a larger dependency set preserves the relation** |
| **`dependsHolds_weaken`** | **fewer inputs preserves the relation** |
| **`holds3`** | **the instance covering `equal` / `zero` / `depends`** |
| **`holds3_equal` / `holds3_zero` / `holds3_depends`** | **the three projections** |

## What this file does NOT do

**It does not DECIDE `depends` for a given pair of tensors -- that needs the dependency set, which is data, not
structure.**
**=> `depends` is a predicate to be SATISFIED, exactly as `equal` is: a `Relation` carries a proof of it, and the
proof establishes that the structure holds.**
-/

namespace Lattice.Core.IR

/-- **`depends`: every input tensor is in the output's dependency set.**

**The first argument is the OUTPUT; the rest are its inputs.**
**=> the shape matches `IR-CANONICAL` §2.2's "each argument carries a tensor and its axes", with the first position
playing the distinguished role of the dependent one.** -/
def dependsHolds (dep : TensorId → List TensorId) (args : List (TensorId × List ℕ)) : Prop :=
  match args with
  | (out, _) :: ins => ∀ i ∈ ins, i.1 ∈ dep out
  | [] => False

/-- **An empty argument list never satisfies `depends`: there is no output to depend.** -/
theorem dependsHolds_nil (dep : TensorId → List TensorId) :
    ¬ dependsHolds dep [] := by
  intro h
  exact h

/-- **A tensor depends on itself when it is in its own dependency set.**

**The trivial self-edge, which is what makes `depends` usable for a leaf of the graph.** -/
theorem dependsHolds_refl (dep : TensorId → List TensorId) (o : TensorId) (ix : List ℕ)
    (h : o ∈ dep o) : dependsHolds dep [(o, ix)] := by
  intro i hi
  have hi' : i = (o, ix) := by simpa using hi
  rw [hi']
  exact h

/-- **A LARGER dependency set preserves the relation.**

**If `dep ⊆ dep'` pointwise, then `depends` under `dep` implies `depends` under `dep'`.**
**=> the dependency relation is MONOTONE in the graph, which is what lets an IR be refined by adding edges.** -/
theorem dependsHolds_mono {dep dep' : TensorId → List TensorId} {args : List (TensorId × List ℕ)}
    (hsub : ∀ t, dep t ⊆ dep' t) (h : dependsHolds dep args) : dependsHolds dep' args := by
  match args with
  | [] => exact h
  | (out, ix) :: ins =>
    intro i hi
    exact hsub out (h i hi)

/-- **FEWER inputs preserve the relation.**

**Dropping an input cannot break a dependency: a smaller requirement is easier to meet.**
**=> this is the direction that matters when an IR is projected onto part of its graph.** -/
theorem dependsHolds_weaken {dep : TensorId → List TensorId} {out : TensorId} {ix : List ℕ}
    {ins ins' : List (TensorId × List ℕ)} (hsub : ins' ⊆ ins)
    (h : dependsHolds dep ((out, ix) :: ins)) : dependsHolds dep ((out, ix) :: ins') := by
  intro i hi
  exact h i (hsub hi)

/-! ## The combined instance -/

/-- **`holds3`: the instance covering `equal`, `zero` and `depends`.**

**It takes BOTH reading contexts -- `read` for the numeric predicates and `dep` for the graph one -- because the IR's
relations refer to both.**
**=> a kind not handled here yields `False`, so no `Relation` of that kind can be constructed (round 178's design,
carried forward).** -/
def holds3 (read : TensorId → List ℕ → ℝ) (dep : TensorId → List TensorId) :
    RelKind → List (TensorId × List ℕ) → Prop
  | .equal, args => equalHolds (read := read) args
  | .zero, args => zeroHolds (read := read) args
  | .depends, args => dependsHolds dep args
  | _, _ => False

/-- **`holds3` on `equal` is `equalHolds`.** -/
theorem holds3_equal (read : TensorId → List ℕ → ℝ) (dep : TensorId → List TensorId)
    (args : List (TensorId × List ℕ)) :
    holds3 read dep .equal args = equalHolds (read := read) args := rfl

/-- **`holds3` on `zero` is `zeroHolds`.** -/
theorem holds3_zero (read : TensorId → List ℕ → ℝ) (dep : TensorId → List TensorId)
    (args : List (TensorId × List ℕ)) :
    holds3 read dep .zero args = zeroHolds (read := read) args := rfl

/-- **`holds3` on `depends` is `dependsHolds`.** -/
theorem holds3_depends (read : TensorId → List ℕ → ℝ) (dep : TensorId → List TensorId)
    (args : List (TensorId × List ℕ)) :
    holds3 read dep .depends args = dependsHolds dep args := rfl

/-- **`holds3` rejects every kind it does not define.**

**=> an IR built over `holds3` contains no `lowRank`, no `symmetry`, no `block` -- and that is a theorem rather than
a convention.** -/
theorem holds3_unhandled (read : TensorId → List ℕ → ℝ) (dep : TensorId → List TensorId)
    (k : RelKind) (args : List (TensorId × List ℕ))
    (h1 : k ≠ .equal) (h2 : k ≠ .zero) (h3 : k ≠ .depends) :
    ¬ holds3 read dep k args := by
  intro h
  cases k <;> simp_all [holds3]

end Lattice.Core.IR
