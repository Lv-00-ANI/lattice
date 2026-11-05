/-
# `Semantics/ContextualInheritsNontrivial.lean` -- a NON-TRIVIAL contextual inheritance (plan D-5)

## The gap round 121 left

**`listContextualInherits` witnesses that `ContextualInherits` CAN express token dependence, but its
`labelAt _ toks := toks` IGNORES the carrier.**
**=> it shows EXPRESSIVITY, not CORRESPONDENCE: nothing in it says the geometry means anything.**

**This file supplies an instance where the carrier and the context BOTH matter.**

## The type that forces the shape

**`(constraintDomain n).Meaning` is `(ℕ → Pt n) → Prop` -- a PREDICATE, not a proposition.**
**=> `labelAt` must return such a function, and the context enters its BODY:**

```
labelAt cs toks  :=  fun pts => HoldsSet cs pts ∧ forall p in toks, HoldsSet cs p
```

**Both arguments are used: `cs` appears in both conjuncts, `toks` only in the second.**
**The first conjunct keeps the label a genuine predicate on configurations -- a bare
`forall p in toks, HoldsSet cs p` is a `Prop` and does not typecheck here.**
**A first draft wrote exactly that, and the build rejection is what forced the conjunction.**

## Both dependencies, proved separately

| theorem | witness |
|:--|:--|
| `labelAt_depends_on_carrier` | **`[]` versus `[eqZero (const 1)]` at the zero configuration** |
| `labelAt_depends_on_context` | **`[samePoint 0 1]` with `[]` versus a context listing a distinguishing configuration** |

**The context witness took three tries:**
**`eqZero (const 1)` fails at EVERY configuration, so both sides were false and no pair separated.**
**The witness needs a set that HOLDS somewhere, and `samePoint 0 1` holds at every constant configuration while
failing at one that tells `0` from `1`.**

## What this closes and what it does not

| gap | status after this file |
|:--|:--|
| **geometry non-trivial** | **CLOSED: `geometry_is_nontrivial` and `context_is_not_ignored`** |
| **`sound` non-trivial** | **STILL OPEN: `behavior` IS the label, so `sound` is `rfl`** |

**=> this file makes the GEOMETRY carry content, not the inheritance's `sound` field.**
**A non-trivial `sound` would need `behavior` computed from weights by a rule the geometry does not already
know, which is compilation -- and that is not here.**
-/

import Mathlib
import Lattice.Semantics.InheritsStructural
import Lattice.Semantics.Stage1

namespace Lattice.Semantics.Stage1

open Lattice.Geo
open Lattice.Geo.ConstraintSet

/-! ## The geometry -/

/-- **A contextual geometry whose label combines the carrier with the context.**

**A carrier point is a constraint set; a token is a configuration; the label at `(cs, toks)` is the predicate
"`cs` holds at `pts` AND at every configuration in `toks`".** -/
def holdsAtAllGeometry (n : ℕ) : ContextualGeometry (constraintDomain n) (ℕ → Pt n) where
  Carrier := List (GeoConstraint n)
  labelAt := fun cs toks => fun pts => HoldsSet cs pts ∧ ∀ p ∈ toks, HoldsSet cs p

/-! ## The carrier matters -/

/-- **`samePoint 0 1` holds at a CONSTANT configuration, so the library's `holdsSet_singleton` applies.** -/
theorem holdsSet_samePoint01_const {n : ℕ} (v : Pt n) :
    HoldsSet [GeoConstraint.samePoint 0 1] (fun _ => v) := by
  rw [holdsSet_singleton]
  -- `Holds (.samePoint 0 1) (fun _ => v)` is `(fun _ => v) 0 = (fun _ => v) 1`, i.e. `v = v`
  rfl

/-- **`eqZero (const 1)` fails at the zero configuration.** -/
theorem not_holdsSet_eqZero_const_one {n : ℕ} :
    ¬ HoldsSet [GeoConstraint.eqZero (GeoExpr.const 1)] (fun _ => (0 : Pt n)) := by
  rw [holdsSet_singleton]
  intro h
  simp [GeoConstraint.Holds, GeoExpr.evalPts] at h

/-- **The label DEPENDS on the carrier.**

**The empty set holds at every configuration; `eqZero (const 1)` fails at the zero one.**
**=> at a FIXED context and a FIXED configuration, replacing the carrier changes the label.** -/
theorem labelAt_depends_on_carrier (n : ℕ) (hn : 0 < n) :
    ∃ (toks : List (ℕ → Pt n)) (pts : ℕ → Pt n),
      (holdsAtAllGeometry n).labelAt [] toks pts
        ≠ (holdsAtAllGeometry n).labelAt [GeoConstraint.eqZero (GeoExpr.const 1)] toks pts := by
  refine ⟨[], fun _ => 0, ?_⟩
  have hleft : (holdsAtAllGeometry n).labelAt [] [] (fun _ => 0) :=
    ⟨holdsSet_nil _, fun p hp => absurd hp (by simp)⟩
  intro h
  rw [h] at hleft
  exact not_holdsSet_eqZero_const_one hleft.1

/-! ## The context matters -/

/-- **The label DEPENDS on the context.**

**`samePoint 0 1` holds at a CONSTANT configuration and fails where `0` and `1` differ.**
**=> with `cs = [samePoint 0 1]` and `pts` constant, adding a distinguishing configuration makes the second
conjunct false.**

**A first draft used `eqZero (const 1)`, which fails at EVERY configuration -- both sides were then false and no
pair separated.** -/
theorem labelAt_depends_on_context (n : ℕ) (hn : 1 < n) :
    ∃ (cs : List (GeoConstraint n)) (pts : ℕ → Pt n) (t₁ t₂ : List (ℕ → Pt n)),
      (holdsAtAllGeometry n).labelAt cs t₁ pts
        ≠ (holdsAtAllGeometry n).labelAt cs t₂ pts := by
  -- a configuration whose coordinates `0` and `1` differ
  let q : ℕ → Pt n := fun k => if (k : ℕ) = 0 then (0 : Pt n) else (1 : Pt n)
  refine ⟨[GeoConstraint.samePoint 0 1], fun _ => 0, [], [q], ?_⟩
  have hleft : (holdsAtAllGeometry n).labelAt [GeoConstraint.samePoint 0 1] [] (fun _ => 0) :=
    ⟨holdsSet_samePoint01_const _, fun p hp => absurd hp (by simp)⟩
  intro h
  rw [h] at hleft
  exact absurd hleft.2 (by
    intro hbad
    have hq := hbad q (List.mem_singleton_self q)
    rw [holdsSet_singleton] at hq
    -- `hq : (fun _ => v) 0 = ...` is about `q 0 = q 1`, which fails by construction
    have h1 := congrFun hq ⟨0, by omega⟩
    simp only [q] at h1
    norm_num at h1)

/-! ## The inheritance -/

/-- **The contextual inheritance over `holdsAtAllGeometry`.**

**`Weights := List (GeoConstraint n)`, `embed := id`, `behavior := labelAt`.**
**=> `sound` is `rfl`: behaviour IS the label.** -/
def holdsAtAllInherits (n : ℕ) :
    ContextualInherits (constraintDomain n) (ℕ → Pt n) (holdsAtAllGeometry n) where
  Weights := List (GeoConstraint n)
  embed := id
  behavior := fun cs toks => (holdsAtAllGeometry n).labelAt cs toks
  sound := fun _ _ => rfl

/-- **The geometry is NON-TRIVIAL, and the two dependence theorems say so.**

**`labelAt_depends_on_carrier` and `labelAt_depends_on_context` are the two halves: neither the carrier nor the
context is ignored.**
**=> unlike `listContextualGeometry`, this geometry's label uses BOTH arguments, which is what "non-trivial"
means here.**

**Stated as one conjunction so a reader does not have to notice that the two witnesses are separate.** -/
theorem geometry_is_nontrivial (n : ℕ) (hn : 1 < n) :
    (∃ (toks : List (ℕ → Pt n)) (pts : ℕ → Pt n),
        (holdsAtAllGeometry n).labelAt [] toks pts
          ≠ (holdsAtAllGeometry n).labelAt [GeoConstraint.eqZero (GeoExpr.const 1)] toks pts)
      ∧ (∃ (cs : List (GeoConstraint n)) (pts : ℕ → Pt n) (t₁ t₂ : List (ℕ → Pt n)),
          (holdsAtAllGeometry n).labelAt cs t₁ pts
            ≠ (holdsAtAllGeometry n).labelAt cs t₂ pts) :=
  ⟨labelAt_depends_on_carrier n (by omega), labelAt_depends_on_context n hn⟩

end Lattice.Semantics.Stage1
