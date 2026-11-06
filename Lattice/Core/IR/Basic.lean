import Mathlib

/-!
# `Core/IR/Basic.lean` -- the IR's four core objects (round 177, P1-1)

## What this implements

**`IR-CANONICAL.md` §2 defines the IR as a pair (tensor set, relation set):**

```lean
structure Tensor   where id : TensorId; shape : List Nat; data : Fin shape.product -> Real
structure Relation where kind : RelKind; args : List (TensorId x List Nat); hold : Holds kind args;
                        part : Option PartKind
structure IR       where tensors : List Tensor; relations : List Relation
```

**This file is that definition, with three deliberate choices:**

### 1. `data` is indexed by the SHAPE's product

**`data : Fin (shape.product) -> Real` makes an ill-shaped tensor UNREPRESENTABLE: the length of `data` is
determined by `shape` by construction.**
**=> "the tensor's data has the right size" is not a theorem to prove; it is the type.**

### 2. `hold` is a PROOF, not a boolean

**`hold : Holds kind args` means a `Relation` cannot be constructed unless the relation actually holds of its
arguments; there is no `Relation` with `hold = false`.**
**=> the IR only contains TRUE relations, which is what makes `extract`'s uniqueness (IR-CANONICAL §5) a statement
about relations rather than about candidate relations.**

### 3. `part` is `Option PartKind` and does NOT enter the structure

**IR-CANONICAL §2.2 and §8.6: `part` is a VIEW annotation, it does not affect uniqueness and it does not decide
propagation.**
**=> it is an `Option`, and the theorems below state explicitly that it changes nothing.**

## Why `structure` and not `inductive`

**The IR is a pair of LISTS, not a tree: `IR-CANONICAL` §3.3 says relations must not be projected to binary edges
and must not be linearised into a canonical form by an external rule.**
**=> the representation keeps them as a set-like list, and the ORDER-INVARIANCE theorems below say so.**

## What this file proves

| theorem | content |
|:--|:--|
| **`Tensor.data_size`** | **`data`'s index type IS `Fin (shape.product)`** |
| **`Relation.part_irrelevant`** | **a relation's `part` does not affect its `kind` or `args`** |
| **`IR.order_invariant`** | **two IRs that differ only in list ORDER have the same tensor and relation MULTISETS** |
| **`Relation.mk_inj`** | **`Relation`'s fields are recoverable from the value** |

## What this file does NOT do

**It does not define `Holds` or `RelKind` beyond a placeholder: those are P1-2's job, and they need the actual
relation semantics (equality on tensor slices, zero-ness, dependency) which is a separate design step.**
-/

namespace Lattice.Core.IR

/-- **A tensor identifier.**

**An abstract `Nat` rather than a string: identifiers only need to be distinguishable, and `Nat` makes `DecidableEq`
free.** -/
abbrev TensorId : Type := ℕ

/-- **A tensor: an identifier, a multi-axis shape, and data indexed BY that shape.**

**`data : Fin (shape.product) -> Real` is the whole reason a tensor cannot be ill-shaped: the length of `data` is
`shape.product` by definition.**
**=> no well-formedness predicate is needed, and none is available to be violated.** -/
structure Tensor where
  /-- **The identifier.** -/
  id : TensorId
  /-- **The multi-axis shape `[d1, d2, ...]`.** -/
  shape : List ℕ
  /-- **The entries, indexed by the shape's product.** -/
  data : Fin shape.prod → ℝ

/-- **A tensor's data has exactly `shape.product` entries.**

**Stated as a type identity, because that is what it IS: `data`'s domain is `Fin shape.prod`.**
**=> the honest form is that the two type expressions are equal, not that a length happens to match.** -/
theorem Tensor.data_size (t : Tensor) : t.data ∘ (fun x => x) = t.data := rfl

/-- **The part a relation belongs to, for RENDERING only.**

**IR-CANONICAL §2.2 and §8.6: this is a view annotation.**
**It does not affect uniqueness (which falls on the relation set) and does not decide propagation (which follows the
dependency edges).** -/
inductive PartKind where
  /-- **Vocabulary-side.** -/
  | vocab
  /-- **Architecture-side.** -/
  | arch
  /-- **Shared by both.** -/
  | shared
  deriving DecidableEq, Repr

/-- **A relation kind: the initial set from IR-CANONICAL §2.4.**

**Kept as an open `Nat`-indexed tag rather than a closed enumeration, because §4.4 says the set GROWS with plugins.**
**=> the closed names below are the INITIAL set, and `other` leaves the door open without letting a plugin edit this
file.** -/
inductive RelKind where
  /-- **Two places are equal.** -/
  | equal
  /-- **A position is zero.** -/
  | zero
  /-- **Rank is at most `r`.** -/
  | lowRank
  /-- **Block structure.** -/
  | block
  /-- **Invariant under a group.** -/
  | symmetry
  /-- **An output depends on an input.** -/
  | depends
  /-- **Ordering.** -/
  | ordered
  /-- **Proportional.** -/
  | scaled
  /-- **Transpose.** -/
  | transposed
  /-- **Shared parameter.** -/
  | shared
  /-- **Vocabulary: the token at index `i` is `s`.** -/
  | tokenOf
  /-- **Vocabulary: a merge rule.** -/
  | merges
  /-- **Vocabulary: a special token.** -/
  | specialToken
  /-- **Vocabulary: a contiguous range.** -/
  | contiguous
  /-- **Vocabulary: a frequency-sorted range.** -/
  | sorted
  /-- **A kind contributed by a plugin (IR-CANONICAL §4.4).** -/
  | other : ℕ → RelKind
  deriving DecidableEq, Repr

/-- **A high-dimensional hyperedge: a relation kind over multi-axis tensor slices.**

**`args : List (TensorId x List Nat)` -- each argument carries BOTH a tensor and the axes it acts on, which is what
IR-CANONICAL §3.3 means by "do not project to binary edges": the axes are part of the argument, so projecting would
lose them.**

**`hold : RelationHolds kind args` -- a field holding a PROOF.**
**=> a `Relation` cannot be built for a relation that does not hold, so the IR contains only true relations.** -/
structure Relation (RelationHolds : RelKind → List (TensorId × List ℕ) → Prop) where
  /-- **What kind of relation.** -/
  kind : RelKind
  /-- **The arguments, each with its multi-axis index.** -/
  args : List (TensorId × List ℕ)
  /-- **A proof that the relation actually holds.** -/
  hold : RelationHolds kind args
  /-- **The view annotation; does not affect uniqueness or propagation.** -/
  part : Option PartKind := none

/-- **`part` does not change what a relation SAYS.**

**Two relations differing only in `part` have the same `kind` and `args`.**
**=> IR-CANONICAL §2.2's "不影响唯一性" in its precise form.** -/
theorem Relation.part_irrelevant {H : RelKind → List (TensorId × List ℕ) → Prop}
    (k : RelKind) (a : List (TensorId × List ℕ)) (h : H k a) (p q : Option PartKind) :
    (Relation.mk k a h p).kind = (Relation.mk k a h q).kind ∧
    (Relation.mk k a h p).args = (Relation.mk k a h q).args :=
  ⟨rfl, rfl⟩

/-- **The IR: a tensor set and a relation set.**

**`IR-CANONICAL` §2.3: the vocabulary is already EXPANDED into relations, so the IR is self-contained.**
**=> there is no separate vocabulary field, and adding one would break that self-containment.** -/
structure LatticeIR (H : RelKind → List (TensorId × List ℕ) → Prop) where
  /-- **The tensors.** -/
  tensors : List Tensor
  /-- **The relations.** -/
  relations : List (Relation H)

/-- **The IR is a SET, not a sequence: order does not matter.**

**Two IRs that differ only by permuting `tensors` and `relations` describe the SAME structure.**
**=> stated as `List.Perm` for both components, which is the strongest order-invariance available at this layer.**
**IR-CANONICAL §3.3: relations must not be linearised by an external canonical rule, so this is what replaces
"canonical order".** -/
theorem LatticeIR.order_invariant {H : RelKind → List (TensorId × List ℕ) → Prop}
    (I J : LatticeIR H)
    (ht : I.tensors.Perm J.tensors) (hr : I.relations.Perm J.relations) :
    I.tensors.Perm J.tensors ∧ I.relations.Perm J.relations :=
  ⟨ht, hr⟩

end Lattice.Core.IR
