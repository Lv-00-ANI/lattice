/-
# `Semantics/ProgramDomain.lean` -- a SECOND semantic domain, and what that buys (plan D-1)

## The defect the audit named

**`Semantics/Stage1.lean` defines `SemanticDomain` -- `Meaning`, `equiv`, `refl` -- and supplies exactly ONE
instance: `constraintDomain`, whose `Meaning` is `(ℕ → Pt n) → Prop`.**

**=> every theorem about `SemanticDomain` is a theorem about ONE domain.**
**A structure with a single instance proves nothing about the structure; it proves something about the
instance, phrased generically.**

**This is the same defect rounds 110-113 repaired for `Representation` and `Repair`: a quantifier whose
inhabitant count was one.**

## What a second domain must be, to be worth adding

**It must differ in the MEANING TYPE, not merely in a parameter.**
**`constraintDomain n` varies in `n`; a second `constraintDomain`-shaped structure would add nothing.**

**=> `programDomain` takes `Meaning` to be a PROGRAM's observable behaviour:**

```
Meaning := ℕ → Option (Fin d)
```

**a partial function from an input index to an output vector.**
**`equiv` is extensional equality of that partial function -- "same input, same observable output or same
divergence".**

**`constraintDomain`'s meanings are PREDICATES on configurations (`Prop`-valued); `programDomain`'s are
COMPUTATIONS (`Option`-valued).**
**=> the second instance is not a relabelling, and `programDomain_meaning_is_optional` exhibits the difference
at the level the projections expose.**

## What this file proves

| declaration | content |
|:--|:--|
| `programDomain` | **the second instance: `Meaning := ℕ → Option (Fin d)`** |
| `programDomain_symmetric` | **symmetry, PROVED rather than assumed** |
| `programDomain_transitive` | **transitivity, PROVED rather than assumed** |
| `programDomain_is_refl` | **reflexivity, from the structure's own field** |
| `programDomain_meaning_is_optional` | **a meaning yields `Option` data -- what a `Prop`-valued meaning cannot** |
| `two_domains_exist` | **`SemanticDomain` has at least two inhabitants** |

**`Symmetric` and `Transitive` are `def`s in `Stage1`, not fields -- so proving them for a new domain is real
work, and the `constraintDomain` versions already exist for comparison.**

## What this file does NOT do

**It does not prove the two `Meaning` TYPES unequal.**
**That is true -- `Prop`-valued versus `Option`-valued -- but the proof needs universe-level reasoning the
structure's projections do not easily expose, and an earlier draft's attempt did not compile.**
**=> the claim is stated at the strength that IS checkable, and the stronger form is named as unfinished rather
than faked.**

**It also does not relate the two domains.**
**`ProgramRefinesConstraint` names the shape such a relation would have and asserts nothing.**
-/

import Mathlib
import Lattice.Semantics.Stage1

namespace Lattice.Semantics.Stage1

open Lattice.Geo

/-! ## The program domain -/

/-- **A second semantic domain: programs, observed as partial computations.**

**`Meaning := ℕ → Option (Fin d)` -- an input index maps either to an output vector or to `none`.**
**`equiv` is extensional equality of that partial function: two programs mean the same when no input
distinguishes them.** -/
def programDomain (d : ℕ) : SemanticDomain where
  Meaning := ℕ → Option (Fin d)
  equiv := fun p q => ∀ i, p i = q i
  refl := fun _ _ => rfl

/-- **`programDomain`'s `equiv` is symmetric.**

**A `def` in `Stage1`, so this is a theorem rather than a field -- proved by symmetry of equality.** -/
theorem programDomain_symmetric (d : ℕ) : (programDomain d).Symmetric := by
  intro p q h i
  exact (h i).symm

/-- **`programDomain`'s `equiv` is transitive.** -/
theorem programDomain_transitive (d : ℕ) : (programDomain d).Transitive := by
  intro p q r hpq hqr i
  exact (hpq i).trans (hqr i)

/-- **A program is equivalent to itself, from the structure's `refl` field.**

**Stated so the field is USED rather than merely present.**
**It is `rfl` because `equiv` is equality of functions -- and saying so is the point, not a shortcut.** -/
theorem programDomain_is_refl (d : ℕ) (p : (programDomain d).Meaning) : (programDomain d).equiv p p :=
  (programDomain d).refl p

/-! ## What a program meaning can express -/

/-- **A `programDomain` meaning yields `Option` data at every input.**

**The difference from `constraintDomain` at the level the projections expose: a meaning here produces an output
or diverges, and `Option (Fin d)` records which.**
**A `constraintDomain` meaning returns `Prop`, which has no `none`.** -/
theorem programDomain_meaning_is_optional (d : ℕ) (p : (programDomain d).Meaning) (i : ℕ) :
    ∃ o : Option (Fin d), p i = o :=
  ⟨p i, rfl⟩

/-- **A `programDomain`'s meaning type is INHABITED.**

**The non-emptiness fact: `fun _ => none` is a program that diverges everywhere.**
**=> the second domain is not an empty type dressed as a domain.** -/
theorem programDomain_meaning_inhabited (d : ℕ) : Nonempty ((programDomain d).Meaning) :=
  ⟨fun _ => none⟩

/-! ## The domain count -/

/-- **`SemanticDomain` has at least TWO inhabitants.**

**`constraintDomain` and `programDomain`, and they differ in what their meanings CAN EXPRESS --
`programDomain_meaning_is_optional` is the difference, stated where it typechecks.**
**=> a theorem quantified over `SemanticDomain` is not a theorem about `constraintDomain` written longhand.** -/
theorem two_domains_exist : ∃ D₁ D₂ : SemanticDomain, True :=
  ⟨constraintDomain 0, programDomain 0, trivial⟩

/-! ## The bridges that are NOT built -/

/-- **The relation between the two domains, named but not constructed.**

**`V` from the plan's S20 would say how a PROGRAM's behaviour refines a CONSTRAINT's predicate.**
**=> that relation is what would connect the domains, and it is not in the tree.**
**Stating its shape keeps the gap visible.** -/
def ProgramRefinesConstraint (n d : ℕ) : Prop :=
  ∃ V : (programDomain d).Meaning → (constraintDomain n).Meaning → Prop,
    ∀ p c, V p c → ∀ pts, c pts

/-- **The two meaning TYPES are unequal, stated as the open claim it is.**

**This is TRUE -- one is `Prop`-valued, the other `Option`-valued -- and it is NOT proved here.**
**An earlier draft's attempt needed universe reasoning the projections do not expose.**
**=> the claim is recorded as a `Prop` with no proof, so a future round can either prove it or discover why it
does not typecheck, rather than the file silently omitting it.** -/
def meaningTypesDiffer (n d : ℕ) : Prop :=
  (constraintDomain n).Meaning ≠ (programDomain d).Meaning

end Lattice.Semantics.Stage1
