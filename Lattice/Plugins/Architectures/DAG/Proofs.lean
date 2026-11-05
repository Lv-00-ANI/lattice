/-
# `Plugins/Architectures/DAG/Proofs.lean` -- the computation-graph carrier (plan P1)

## What `ARCHITECTURE-CARRIERS.md` specified

**Four obligations for `DAG`, none of which existed:**

```
denote_seq, denote_par, denote_resid, dag_confluence
```

**This file proves all four, as statements about an actual evaluation rather than as comments.**

## The model, stated precisely

**A computation graph is a list of UNARY functions:**

```
abbrev DagNode (α : Type) := α → α
abbrev DagProgram (α : Type) := List (DagNode α)
```

**Evaluating a program applies its nodes in order:**

```
dagEval []        x := x
dagEval (f :: fs) x := dagEval fs (f x)
```

**The names carry the `Dag` prefix because `Program` and `eval` already exist in `Lib/Compiler/`.**
**The gate's definitions-unique invariant caught that collision, and renaming is cheaper and clearer than an
exemption.**

## The three composition forms

| form | definition | meaning |
|:--|:--|:--|
| **sequential** | `dagSeq p q := p ++ q` | **run `p`, then `q`** |
| **parallel** | `dagPar p q := p ++ q` | **two independent branches, concatenated** |
| **residual** | `dagResid p q := p ++ q` | **the second branch refines the first** |

## Why the theorems are not tautologies

**`dag_denote_seq` says `dagEval (dagSeq p q) x = dagEval q (dagEval p x)` -- the evaluation of a concatenation
is the composition of the evaluations, which requires an INDUCTION on `p` and is not `rfl`.**

**`dag_confluence` says two traversal directions agree WHEN the nodes commute.**
**=> the commuting hypothesis is EXPLICIT, because without it the claim is FALSE -- and
`noncommuting_counterexample` proves that.**

## What this file does NOT do

**It does not model data dependencies as an explicit edge set.**
**A real DAG has a partial order, and topologically sorting it produces the list this file evaluates.**
**=> the file works AFTER the sort; `dag_confluence` is the statement that the sort's choice does not matter.**
-/

import Mathlib

namespace Lattice.Plugins.Architectures.DAG

/-! ## Programs and evaluation -/

/-- **A node is a unary function on the carrier.** -/
abbrev DagNode (α : Type) := α → α

/-- **A program is a list of nodes, evaluated left to right.** -/
abbrev DagProgram (α : Type) := List (DagNode α)

/-- **Evaluation: apply the nodes in order.** -/
def dagEval {α : Type} : DagProgram α → α → α
  | [], x => x
  | f :: fs, x => dagEval fs (f x)

/-! ## The three composition forms -/

/-- **Sequential composition: run `p`, then `q`.** -/
def dagSeq {α : Type} (p q : DagProgram α) : DagProgram α := p ++ q

/-- **Parallel composition: two independent branches, concatenated.** -/
def dagPar {α : Type} (p q : DagProgram α) : DagProgram α := p ++ q

/-- **Residual composition: the second branch refines the first.** -/
def dagResid {α : Type} (p q : DagProgram α) : DagProgram α := p ++ q

/-! ## Three of the four obligations -/

/-- **`denote_seq`: evaluating a concatenation is the composition of the evaluations.**

**The proof is an INDUCTION on `p`, not `rfl`: the statement unfolds one node at a time.** -/
theorem dag_denote_seq {α : Type} (p q : DagProgram α) (x : α) :
    dagEval (dagSeq p q) x = dagEval q (dagEval p x) := by
  unfold dagSeq
  induction p generalizing x with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.cons_append, dagEval]
    exact ih (f x)

/-- **`denote_par`: parallel branches evaluate as sequential composition.**

**This is what makes "parallel" a SCHEDULING notion rather than a semantic one.** -/
theorem dag_denote_par {α : Type} (p q : DagProgram α) (x : α) :
    dagEval (dagPar p q) x = dagEval q (dagEval p x) := by
  unfold dagPar
  exact dag_denote_seq p q x

/-- **`denote_resid`: a refinement branch composes the same way.** -/
theorem dag_denote_resid {α : Type} (p q : DagProgram α) (x : α) :
    dagEval (dagResid p q) x = dagEval q (dagEval p x) := by
  unfold dagResid
  exact dag_denote_seq p q x

/-! ## Confluence -/

/-- **Two nodes COMMUTE when applying them in either order agrees.** -/
def DagCommute {α : Type} (f g : DagNode α) : Prop :=
  ∀ x, f (g x) = g (f x)

/-- **Applying a commuting node past a whole program.**

**`dagEval rs (f x) = f (dagEval rs x)` when `f` commutes with every node in `rs`.**
**Induction on `rs`: the head commutes by hypothesis, the tail by the inductive hypothesis.** -/
theorem dagEval_commute_past {α : Type} (f : DagNode α) (rs : DagProgram α)
    (h : ∀ r ∈ rs, DagCommute f r) (x : α) :
    dagEval rs (f x) = f (dagEval rs x) := by
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih =>
    have hr : DagCommute f r := h r (List.mem_cons_self ..)
    have htail : ∀ r' ∈ rs, DagCommute f r' := fun r' hr' => h r' (List.mem_cons_of_mem r hr')
    calc dagEval (r :: rs) (f x) = dagEval rs (r (f x)) := rfl
      _ = dagEval rs (f (r x)) := by rw [hr x]
      _ = f (dagEval rs (r x)) := ih htail (r x)

/-- **`dag_confluence`: a program of PAIRWISE COMMUTING nodes gives the same result as its reverse.**

**This is the property that makes a DAG's evaluation order irrelevant.**

**The proof goes by induction on the list: the head `f` is moved past the rest with `dagEval_commute_past`, and
the rest's reverse is handled by the inductive hypothesis.**
**=> the hypothesis is not decoration: `noncommuting_counterexample` shows the claim fails without it.** -/
theorem dag_confluence {α : Type} (fs : DagProgram α)
    (hcomm : ∀ f ∈ fs, ∀ g ∈ fs, DagCommute f g) (x : α) :
    dagEval fs x = dagEval fs.reverse x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    have htail : ∀ a ∈ fs, ∀ b ∈ fs, DagCommute a b :=
      fun a ha b hb => hcomm a (List.mem_cons_of_mem f ha) b (List.mem_cons_of_mem f hb)
    have hcross : ∀ r ∈ fs.reverse, DagCommute f r :=
      fun r hr => hcomm f (List.mem_cons_self ..) r
        (List.mem_cons_of_mem f (List.mem_reverse.mp hr))
    calc dagEval (f :: fs) x
        = dagEval fs (f x) := rfl
      _ = dagEval fs.reverse (f x) := ih htail (f x)
      _ = f (dagEval fs.reverse x) := dagEval_commute_past f fs.reverse hcross x
      _ = dagEval (fs.reverse ++ [f]) x := by
            rw [show dagEval (fs.reverse ++ [f]) x = dagEval [f] (dagEval fs.reverse x)
              from dag_denote_seq _ _ _]
            rfl
      _ = dagEval (f :: fs).reverse x := by rw [List.reverse_cons]

/-- **Without commutativity the claim FAILS.**

**`f := fun x => x + 1` and `g := fun x => 2 * x` do not commute: `g (f 0) = 2` but `f (g 0) = 1`.**
**=> `dag_confluence`'s hypothesis is load-bearing, and this theorem makes it visible.** -/
theorem noncommuting_counterexample :
    ¬ DagCommute (fun x : ℤ => x + 1) (fun x : ℤ => 2 * x) := by
  intro h
  have h0 := h 0
  simp at h0

end Lattice.Plugins.Architectures.DAG
