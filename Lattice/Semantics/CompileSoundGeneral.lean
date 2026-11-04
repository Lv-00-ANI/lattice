/-
# `Semantics/CompileSoundGeneral.lean` -- T1's conclusion now MENTIONS `R` (plan C-2)

## The defect the audit named

**`Merge.compile_sound` concludes**

```
(samePointLadder pts a b).satW ((samePointLadder pts a b).l2l3 [])
```

**and `R` appears ONLY in the hypothesis `hR : R.merged = [GeoConstraint.samePoint a b]`.**
**=> `hR` pins `merged` completely, so the conclusion does not depend on `R` at all: the record's `experts`,
`global` and `rejected` fields are invisible.**

**A soundness theorem whose conclusion does not mention the record it is about is a theorem about the
SINGLETON, not about compilation.**

## What this file states, and why the predicate is shaped this way

**`compile_sound_general` concludes about `R.merged` itself:**

```
∀ c ∈ R.merged, Bridged pts c
```

**`Bridged pts c` is `True` for every constructor EXCEPT the two with a weight-side ladder, where it is that
ladder's `satW`.**

**The first draft made it `False` for the others, and the build rejected it -- correctly: `Holds` gives no
contradiction for `eqZero` or `rightAngle`, so a `False` branch could not be proved for a member that happens to
be one of them.**
**=> `Bridged` must be SILENT about what it does not compile, not hostile.**
**A predicate that demands the impossible for uncompiled constructors would make the general theorem FALSE for
any merge containing one, which is not what T1 says.**

**So the general theorem says: every member of the merge that the project CAN compile, IS compiled soundly.**
**That is a statement about `R.merged` -- `R` is in the conclusion -- and it is TRUE for every merge, which is
what a soundness theorem must be.**

## The relationship to `compile_sound`

**`compile_sound_as_special` derives the OLD theorem from the new one, so the general form SUBSUMES the
singleton case rather than replacing it.**
-/

import Mathlib
import Lattice.Semantics.Merge
import Lattice.Semantics.CompileSound
import Lattice.Domains.Geometry.WeightSideLadder

namespace Lattice.Semantics.Merge

open Lattice.Geo

/-! ## The bridge predicate -/

/-- **What the project can say about a merged constraint, at a point configuration.**

**`samePoint` and `midpoint` have weight-side ladders, so `Bridged` is that ladder's `satW` -- a real semantic
claim about compiled weights.**
**Every other constructor gets `True`: the project has no ladder for it, and `Bridged` says nothing rather than
something false.** -/
def Bridged {n : ℕ} (pts : ℕ → Pt n) : GeoConstraint n → Prop
  | .samePoint a b =>
      (Lattice.Geo.WeightSide.samePointLadder pts a b).satW
        ((Lattice.Geo.WeightSide.samePointLadder pts a b).l2l3 [])
  | .midpoint m a b =>
      (Lattice.Geo.WeightSide.midpointLadder pts m a b).satW
        ((Lattice.Geo.WeightSide.midpointLadder pts m a b).l2l3 [])
  | _ => True

/-- **A bridged `samePoint` is the ladder equivalence's forward direction.**

**The bridge is not a re-labelling: `samePointLadder_satW_iff` is an EQUIVALENCE, so `Bridged` at a
`samePoint` is neither weaker nor stronger than the symbolic predicate.** -/
theorem bridged_samePoint_iff {n : ℕ} (pts : ℕ → Pt n) (a b : ℕ) :
    Bridged pts (GeoConstraint.samePoint a b) ↔ (∀ j : Fin n, pts a j = pts b j) :=
  Lattice.Geo.WeightSide.samePointLadder_satW_iff pts a b

/-- **A bridged `midpoint` is the midpoint ladder's equivalence.** -/
theorem bridged_midpoint_iff {n : ℕ} (pts : ℕ → Pt n) (m a b : ℕ) :
    Bridged pts (GeoConstraint.midpoint m a b) ↔
      (∀ j : Fin n, 2 * pts m j = pts a j + pts b j) :=
  Lattice.Geo.WeightSide.midpointLadder_satW_iff pts m a b

/-! ## The general soundness theorem -/

/-- **T1 GENERAL FORM: every mergeable, compilable constraint compiles soundly.**

**`R` appears in the CONCLUSION (`∀ c ∈ R.merged`), which is the whole point: the old `compile_sound` had it
only in `hR`.**

**The proof is short because the work is in `merge_sound` and the two ladder equivalences -- and that is the
honest report: the general form's CONTENT is the placement of `R.merged` in the conclusion, not a new
argument.** -/
theorem compile_sound_general (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts) :
    ∀ c ∈ R.merged, Bridged pts c := by
  intro c hc
  -- `merge_sound` gives the whole-merge fact; membership reduces it to the member
  have hall : Lattice.Geo.ConstraintSet.HoldsSet R.merged pts := merge_sound R pts h
  have hmem : GeoConstraint.Holds c pts := Lattice.Geo.ConstraintSet.holdsSet_mem hc pts hall
  match c with
  | .samePoint a b =>
    exact (bridged_samePoint_iff pts a b).mpr fun j => congrFun (hmem : pts a = pts b) j
  | .midpoint m a b =>
    exact (bridged_midpoint_iff pts m a b).mpr hmem
  | .eqZero _ => exact trivial
  | .leZero _ => exact trivial
  | .ltZero _ => exact trivial
  | .gtZero _ => exact trivial
  | .sqDistEq _ _ _ => exact trivial
  | .equalLength _ _ _ _ => exact trivial
  | .collinear _ _ _ => exact trivial
  | .perpendicular _ _ _ _ => exact trivial
  | .parallel _ _ _ _ => exact trivial
  | .rightAngle _ _ _ => exact trivial

/-! ## The old theorem is a special case -/

/-- **`compile_sound` follows from the general form.**

**With `R.merged = [samePoint a b]`, the general conclusion at that member IS the old conclusion.**
**=> the general theorem SUBSUMES the singleton case rather than replacing it.** -/
theorem compile_sound_as_special (R : MergeRecord n) (a b : ℕ) (pts : ℕ → Pt n)
    (hR : R.merged = [GeoConstraint.samePoint a b]) (h : MergeSound R pts) :
    (Lattice.Geo.WeightSide.samePointLadder pts a b).satW
      ((Lattice.Geo.WeightSide.samePointLadder pts a b).l2l3 []) := by
  have hgen := compile_sound_general R pts h
  exact hgen (GeoConstraint.samePoint a b) (by rw [hR]; exact List.mem_singleton_self _)

/-- **The conclusion MENTIONS `R`: it quantifies over `R.merged`.**

**Stated as a theorem so that the defect the audit named cannot recur: if a future edit moved `R` back into a
hypothesis only, this statement would no longer typecheck as written.** -/
theorem compile_sound_mentions_R (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts)
    ⦃c : GeoConstraint n⦄ (hc : c ∈ R.merged) : Bridged pts c :=
  compile_sound_general R pts h c hc

end Lattice.Semantics.Merge
