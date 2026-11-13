import Mathlib
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Reference.Geometry.Geometry.Engine

/-!
# `Lattice.Geo.Loop` -- the verification loop, closed

## What the objective asks for

> 逆向把权重行为提取回符号，用于验证、修正、再注入；闭环就是验证回路

Until now each stage existed separately: extraction (`Lattice.Geo.Extract`), verification
(`Lattice.Geo.Engine`), and the repair framework (`Lattice.Core.Repair`) with a negative result about the
identity operator. Nothing said the loop *closes*.

This file closes it for the smallest constraint that admits a real repair operator, and in doing so
supplies what `Lattice.Geo.Repair.no_identity_repair` said was needed: an operator that moves.

## The operator

`samePoint a b` says two points coincide. Removing that violation is immediate -- copy `a`'s coordinates
onto `b` -- and it is a genuine state change rather than a bookkeeping trick, which is exactly what
`Repair.decreases` demands.

## Why the measure has only two values

The measure must fall strictly at every failing point and be zero exactly at satisfying ones. One repair
step suffices for `samePoint`, so a two-valued measure is the honest one: `decreases` asks for one step of
progress, and this operator delivers the whole of it. A finer measure would be theatre.

## What the loop theorem says

`loop_converges` is `Repair.progress` at this operator: from any configuration, some number of iterations
reaches a satisfying one -- here always at most one. `reinject_sound` is the "再注入" half: the repaired
configuration satisfies what was repaired for, so re-compiling produces a penalty that vanishes there.

## Scope

This closes the loop for `samePoint`, not for every geometric constraint. For `perpendicular` a step would
project an endpoint onto a plane, and constructing that operator with a provably falling measure is
separate work. What generalises is the *shape*: any `Repair` inhabitant gets `loop_converges` from
`Repair.progress` without restating the argument.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Copy one point's coordinates onto another.** The repair step for `samePoint a b`. -/
noncomputable def fixSamePoint (a b : ℕ) (pts : ℕ → Pt n) : ℕ → Pt n :=
  Function.update pts b (pts a)

/-- The repaired point reads back as `a`'s value -- by `update_same`, with no `if` to unfold. -/
@[simp] theorem fixSamePoint_self (a b : ℕ) (pts : ℕ → Pt n) :
    fixSamePoint a b pts b = pts a :=
  Function.update_same (β := fun _ => Pt n) b (pts a) pts

/-- Every other point is left where it was. -/
theorem fixSamePoint_other (a b : ℕ) (pts : ℕ → Pt n) {p : ℕ} (hp : p ≠ b) :
    fixSamePoint a b pts p = pts p :=
  Function.update_noteq (β := fun _ => Pt n) hp (pts a) pts

/-- **The fix establishes the constraint** in one step. -/
theorem fixSamePoint_holds (a b : ℕ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.samePoint a b) (fixSamePoint a b pts) := by
  show fixSamePoint a b pts a = fixSamePoint a b pts b
  by_cases hab : a = b
  · rw [hab]
  · rw [fixSamePoint_other a b pts hab, fixSamePoint_self]

/-- **The fix leaves a satisfying configuration alone.** -/
theorem fixSamePoint_absorbs (a b : ℕ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.samePoint a b) pts) :
    fixSamePoint a b pts = pts := by
  show Function.update pts b (pts a) = pts
  rw [show pts a = pts b from h]
  exact Function.update_eq_self b pts

/-- **The measure**: zero exactly where the points coincide.

`Holds` at `samePoint` is point equality, which is not decidable for real coordinates, so the definition
uses classical choice -- a property of the carrier rather than of the construction. Stating it on the
equation rather than on `Holds` lets `by_cases` and `simp` rewrite it. -/
noncomputable def samePointMeasure (a b : ℕ) (pts : ℕ → Pt n) : ℕ :=
  if pts a = pts b then 0 else 1

/-- The measure vanishes exactly where the points coincide. -/
theorem samePointMeasure_eq_zero_iff (a b : ℕ) (pts : ℕ → Pt n) :
    samePointMeasure a b pts = 0 ↔ pts a = pts b := by
  unfold samePointMeasure
  by_cases h : pts a = pts b <;> simp [h]

/-- **A genuine repair operator for `samePoint`.**

The inhabitant `Lattice.Geo.Repair.no_identity_repair` showed cannot be the identity: `fix` really moves the
configuration when the constraint fails, which is what makes `decreases` hold. -/
noncomputable def samePointRepair (a b : ℕ) : Lattice.Core.Repair (ℕ → Pt n) where
  Sat := fun pts => GeoConstraint.Holds (.samePoint a b) pts
  fix := fixSamePoint a b
  μ := samePointMeasure a b
  absorbs := fun pts h => fixSamePoint_absorbs a b pts h
  decreases := by
    intro pts h
    have hsat : GeoConstraint.Holds (.samePoint a b) (fixSamePoint a b pts) :=
      fixSamePoint_holds a b pts
    have hne : ¬(pts a = pts b) := by
      intro heq
      exact h heq
    have hpos : fixSamePoint a b pts a = fixSamePoint a b pts b := hsat
    show (if fixSamePoint a b pts a = fixSamePoint a b pts b then 0 else 1)
       < (if pts a = pts b then 0 else 1)
    rw [if_pos hpos, if_neg hne]
    norm_num

  atomic := by
    intro pts h
    exact (samePointMeasure_eq_zero_iff a b pts).mp h

/-- **The verification loop converges.** From any configuration, some number of repair iterations reaches
a satisfying one. -/
theorem loop_converges (a b : ℕ) (pts : ℕ → Pt n) :
    ∃ k : ℕ, (samePointRepair a b).Sat ((samePointRepair a b).iterate k pts) :=
  (samePointRepair a b).progress pts

/-- **The loop converges in at most one step**, sharper than `Repair.progress` promises. -/
theorem loop_converges_in_one (a b : ℕ) (pts : ℕ → Pt n) :
    (samePointRepair a b).Sat ((samePointRepair a b).iterate 1 pts) := by
  show GeoConstraint.Holds (.samePoint a b) (fixSamePoint a b pts)
  exact fixSamePoint_holds a b pts

/-- **Re-injection**: after the loop, the symbolic side holds what it was asked to hold, so re-compiling
produces a penalty that vanishes there. -/
theorem reinject_sound (a b : ℕ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.samePoint a b) ((samePointRepair a b).iterate 1 pts) :=
  loop_converges_in_one a b pts

/-- **The repaired state entails what it was repaired for**, in the engine's sense -- the loop and the
engine agree about success. -/
theorem reinject_entails (a b : ℕ) :
    EntailsGeo (n := n) [GeoConstraint.samePoint a b] (GeoConstraint.samePoint a b) :=
  entailsGeo_refl _

/-! ## The same repair over a finite index type

`samePointRepair` indexes points by `ℕ`, because the geometry layer's constraints do. `flattenRepresentation`
works on `Fin k → Pt n` instead, and `Lattice.Lift.loop_fixed_point` needs a `Repair` on the *same* type as the
`Representation` it is combined with. This section supplies it.

Nothing new is needed: the repair reads two points and writes one of them into the other's slot, and
`Function.update` works for any index type with decidable equality. The satisfying predicate is written directly as
`pts a = pts b` rather than through `GeoConstraint.Holds`, because `GeoConstraint` is indexed by `ℕ`; the two are
the same statement, since that is how `Holds` defines the `samePoint` case. -/

section FinIndex

variable {k : ℕ}

/-- **One repair step on a finite point set**: copy `a`'s position into `b`'s slot. -/
noncomputable def fixSamePointFin (a b : Fin k) (pts : Fin k → Pt n) : Fin k → Pt n :=
  Function.update pts b (pts a)

/-- **The measure**: `0` once the two points coincide, `1` while they do not. -/
noncomputable def samePointMeasureFin (a b : Fin k) (pts : Fin k → Pt n) : ℕ :=
  if pts a = pts b then 0 else 1

/-- **The repair leaves a satisfied configuration alone.** Same proof as the `ℕ` case; the index type plays no
part. -/
theorem fixSamePointFin_absorbs (a b : Fin k) (pts : Fin k → Pt n) (h : pts a = pts b) :
    fixSamePointFin a b pts = pts := by
  show Function.update pts b (pts a) = pts
  rw [h]
  exact Function.update_eq_self b pts

/-- **A failing configuration becomes satisfied** after one step: `b`'s slot receives `a`'s position. -/
theorem fixSamePointFin_holds (a b : Fin k) (pts : Fin k → Pt n) :
    fixSamePointFin a b pts a = fixSamePointFin a b pts b := by
  by_cases hab : a = b
  · rw [hab]
  · subst_vars
    simp [fixSamePointFin, Function.update, hab]

/-- **The finite-index `samePoint` repair.** All three obligations discharge with the same reasoning as the `ℕ`
version, which is the point: the repair never depended on the index type being `ℕ`. -/
noncomputable def samePointRepairFin (a b : Fin k) : Lattice.Core.Repair (Fin k → Pt n) where
  Sat := fun pts => pts a = pts b
  fix := fixSamePointFin a b
  μ := samePointMeasureFin a b
  absorbs := fun pts h => fixSamePointFin_absorbs a b pts h
  decreases := by
    intro pts h
    have hsat : fixSamePointFin a b pts a = fixSamePointFin a b pts b :=
      fixSamePointFin_holds a b pts
    show (if fixSamePointFin a b pts a = fixSamePointFin a b pts b then 0 else 1)
       < (if pts a = pts b then 0 else 1)
    rw [if_pos hsat, if_neg h]
    norm_num
  atomic := by
    intro pts h
    simp only [samePointMeasureFin] at h
    by_cases hab : pts a = pts b
    · exact hab
    · rw [if_neg hab] at h
      exact absurd h (by norm_num)

end FinIndex

end Lattice.Geo
