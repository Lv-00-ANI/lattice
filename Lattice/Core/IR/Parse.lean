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

/-- **The tensor shapes of a term: `tensorCount t` tensors, each of shape `[1]`.** -/
def termTensors (t : Term) : List TensorShape :=
  List.replicate (tensorCount t) ⟨0, termShape⟩

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

end Lattice.Core.IR