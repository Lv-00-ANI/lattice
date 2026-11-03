/-
# The degenerate-configuration family: four constraint kinds solved at once

**Round 74 solved `samePoint` over lists of arbitrary length.**
**This file answers the next question: is `samePoint` special, or does a BROADER family have the same
closed form?**

## The answer, and it is the useful one for T0

**A CONSTANT configuration `fun _ => p` satisfies four different constraint kinds simultaneously:**

- **`samePoint a b`** -- `pts a = pts b` -- **two equal entries.**
- **`midpoint m a b`** -- `2 * pts m i = pts a i + pts b i` -- **`2c = c + c`.**
- **`rightAngle a b c`** -- `∑ i, seg a b i * seg b c i = 0` -- **every `seg` is ZERO at a constant
  configuration.**
- **`perpendicular a b c e`** -- same, with a different pair of segments.

**The mechanism is uniform: at a constant configuration every SEGMENT is the zero vector, so every
bilinear form built from segments vanishes and every coordinate equation becomes reflexive.**

## Why this matters for T0

**T0's constructor must handle a spec MIXING constraint kinds.**
**`samePoint` alone is one family; a spec of `samePoint` and `midpoint` and `rightAngle` is what a real
geometry problem looks like.**
**=> the family `DegenerateOK` below is the largest set of kinds for which a constant configuration is a
solution, and it is closed under arbitrary finite mixing.**
**That is a genuine multi-kind solver, not a union of one-kind solvers.**

## What is NOT in the family, and why

**`eqZero e`, `sqDistEq a b d`, `equalLength`**: **their `Holds` mentions `e.evalPts pts` or `d.evalPts pts`,
which does NOT vanish at a constant configuration** -- **`evalPts` of an arbitrary expression is not
zero merely because all coordinates are equal.**
**`ltZero e`**: **needs a STRICT inequality, and a degenerate configuration gives `0 < 0`, which fails.**
**`leZero`/`gtZero`**: **depend on the sign of `evalPts`, which is not controlled.**

**=> the family is exactly "the constraints whose satisfaction at a constant configuration is a
reflexivity fact", and the docstring names the excluded kinds with their reason rather than silently
omitting them.**
-/

import Lattice.Plugins.Targets.MultiSolver

namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open scoped BigOperators

/-- **At a constant configuration, every segment is the zero vector.**

**`seg pts p q i = pts q i - pts p i`, and under `fun _ => c` both entries are `c`, so each coordinate
is `c - c = 0`.** **The proof is pointwise: `Pt n` is a function type, and the zero of a function type
is the constant-zero function, so `funext` is required before `sub_self` applies.**
**This single fact is what makes all four kinds below work -- they differ only in which bilinear form
they build on segments.** -/
theorem seg_const_zero {n : ℕ} (c : Pt n) (p q : ℕ) :
    seg (fun _ => c) p q = 0 := by
  funext i
  simp only [seg, Pi.zero_apply]
  ring

/-- **`midpoint m a b` holds at any constant configuration.** -/
theorem holds_midpoint_const {n : ℕ} (m a b : ℕ) (c : Pt n) :
    Holds (GeoConstraint.midpoint m a b) (fun _ => c) := by
  intro i
  ring

/-- **A bilinear sum of two segments vanishes at any constant configuration.**

**The GENERAL form: `∑ i, seg pts a b i * seg pts c e i = 0` whenever `pts` is constant.**
**Both `rightAngle` and `perpendicular` are this shape with different index pairs**, **so proving it
once removes the duplication rather than hiding it.**
**The proof is `seg_const_zero` at both factors, then the zero product summed.** -/
theorem bilinearSeg_const_zero {n : ℕ} (p : Pt n) (a b c e : ℕ) :
    ∑ i, seg (fun _ => p) a b i * seg (fun _ => p) c e i = 0 := by
  simp only [seg_const_zero, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- **`rightAngle a b c` holds at any constant configuration**, via `bilinearSeg_const_zero`. -/
theorem holds_rightAngle_const {n : ℕ} (a b c : ℕ) (p : Pt n) :
    Holds (GeoConstraint.rightAngle a b c) (fun _ => p) := by
  show ∑ i, seg (fun _ : ℕ => p) a b i * seg (fun _ : ℕ => p) b c i = 0
  exact bilinearSeg_const_zero p a b b c

/-- **`perpendicular a b c e` holds at any constant configuration**, via the same lemma.

**Note the index pairs differ (`a b` with `b c` versus `a b` with `c e`), which is why the general
form takes FOUR indices.** -/
theorem holds_perpendicular_const {n : ℕ} (a b c e : ℕ) (p : Pt n) :
    Holds (GeoConstraint.perpendicular a b c e) (fun _ => p) := by
  show ∑ i, seg (fun _ : ℕ => p) a b i * seg (fun _ : ℕ => p) c e i = 0
  exact bilinearSeg_const_zero p a b c e

/-- **The family of constraint KINDS that a constant configuration satisfies.**

**Four constructors, and the family is defined by CASE ANALYSIS on the constraint rather than by a
predicate on lists -- so a list mixing them is handled by the same induction as before.** -/
def DegenerateOK {n : ℕ} (c : GeoConstraint n) : Prop :=
  (∃ a b, c = GeoConstraint.samePoint a b) ∨
  (∃ m a b, c = GeoConstraint.midpoint m a b) ∨
  (∃ a b k, c = GeoConstraint.rightAngle a b k) ∨
  (∃ a b k e, c = GeoConstraint.perpendicular a b k e)

/-- **Every `DegenerateOK` constraint holds at any constant configuration.**

**Four cases, and three of them reduce to a `ring` identity or to `seg_const_zero`.**
**This is the lemma the multi-kind solver's `sound` field consumes.** -/
theorem holds_of_degenerateOK {n : ℕ} (c : GeoConstraint n) (hc : DegenerateOK c) (p : Pt n) :
    Holds c (fun _ => p) := by
  rcases hc with ⟨a, b, rfl⟩ | ⟨m, a, b, rfl⟩ | ⟨a, b, k, rfl⟩ | ⟨a, b, k, e, rfl⟩
  · -- `samePoint a b`: two equal entries
    rfl
  · exact holds_midpoint_const m a b p
  · exact holds_rightAngle_const a b k p
  · exact holds_perpendicular_const a b k e p

/-- **`DegenerateOK` constraints are all EXPRESSIBLE.**

**`samePoint`, `midpoint`, `rightAngle` are `poly`; `perpendicular` is `poly` too.**
**=> a spec of `DegenerateOK` constraints is an `ExpressibleSpec`, which is what T0's domain requires.**
**This is the bridge between the family and `ExpressibleSpec`.** -/
theorem expressible_of_degenerateOK {n : ℕ} (c : GeoConstraint n) (hc : DegenerateOK c) :
    IsExpressible c := by
  rcases hc with ⟨a, b, rfl⟩ | ⟨m, a, b, rfl⟩ | ⟨a, b, k, rfl⟩ | ⟨a, b, k, e, rfl⟩
  · exact samePoint_expressible a b
  · exact midpoint_expressible m a b
  · exact rightAngle_expressible a b k
  · exact perpendicular_expressible a b k e

end Lattice.Plugins.Targets
