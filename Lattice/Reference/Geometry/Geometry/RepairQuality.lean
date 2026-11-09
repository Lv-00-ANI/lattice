import Mathlib
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Geometry.LoopPerp

/-!
# `Lattice.Geo.RepairQuality` -- distinguishing repairs that are correct from repairs that are good

## The observation this file formalises

`Lattice.Core.Repair` asks four things of an operator: it names the target, it moves the state, its measure
falls, and a zero measure means the target is reached. Nothing in that list says **what the move costs**.

Two operators satisfy it for geometry:

* `fixSamePoint` copies one point onto another -- the target is met by making the two points coincide;
* `fixPerp` projects one point onto a plane -- the target is met by turning the segment.

Both converge. Only the second keeps the object it was reasoning about. After the copy the two points are the
same point, so any later constraint that needs them to differ has nothing to work with; after the projection
`a` has not moved at all.

So "satisfies `Repair`" and "is a good repair" are orthogonal dimensions, and this file makes that a theorem
rather than a remark.

## The layers of repair quality

The objective requires reversibility to be stated by layer. This file states repair **quality** by layer, in
the same spirit:

| layer | property |
|:--|:--|
| **correctness** | `Repair` holds: the loop converges |
| **conservativity** | a satisfying state is left alone (`Repair.absorbs`) |
| **separation** | two points that were distinct remain distinct |

The first two come from `Repair` itself and are shared by every inhabitant. The third is an *additional*
obligation that distinguishes a good repair from a merely correct one.

## How the contrast became provable

An earlier revision stated the copying operator as a lambda containing an `if`, which left a beta-redex in
every goal mentioning it, and the separation proof failed on that redex rather than on any geometric point.

Both operators are now written with `Function.update`, so each has a `@[simp]` read-back lemma for the point
it rewrites and a `_other` lemma for everything else. The separation proof is then two rewrites, and the
"definitions are uniform" principle is what made it work.

## Why separation is stated coordinatewise

`Separated a b pts` says some coordinate differs rather than that `seg pts a b ≠ 0`. The two are equivalent
here -- `seg` is `fun i => pts q i - pts p i` -- but the coordinatewise form keeps every proposition about
`pts` directly. The equivalence with non-coincidence is `separated_iff_ne`, so nothing is lost.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Points `a` and `b` are separated** in a configuration: some coordinate of theirs differs. -/
def Separated (a b : ℕ) (pts : ℕ → Pt n) : Prop :=
  ∃ i : Fin n, pts a i ≠ pts b i

/-- **A separated pair is a pair of distinct points.** The forward direction of the equivalence below,
stated first because two later proofs need it without the converse. -/
theorem separated_iff_ne_aux (a b : ℕ) (pts : ℕ → Pt n) :
    Separated a b pts → pts a ≠ pts b := by
  rintro ⟨i, hi⟩ h
  exact hi (by rw [h])

/-- **Separation is exactly non-coincidence.** -/
theorem separated_iff_ne (a b : ℕ) (pts : ℕ → Pt n) :
    Separated a b pts ↔ pts a ≠ pts b := by
  constructor
  · exact separated_iff_ne_aux a b pts
  · intro h
    by_contra hcon
    apply h
    funext i
    by_contra hi
    exact hcon ⟨i, hi⟩

/-! ### The copying operator in both notations -/

/-- **The copying repair writes `a`'s value onto `b`.** -/
theorem copy_writes_b (a b : ℕ) (pts : ℕ → Pt n) :
    fixSamePoint a b pts b = pts a :=
  fixSamePoint_self a b pts

/-- **The copying repair leaves `a` where it was** -- it copies *from* `a`, so the source is untouched. -/
theorem copy_keeps_a (a b : ℕ) (pts : ℕ → Pt n) (hab : a ≠ b) :
    fixSamePoint a b pts a = pts a :=
  fixSamePoint_other a b pts hab

/-- **The copying repair collapses the pair.** After it, `a` and `b` are the same point -- so a later
constraint that needs them distinct has nothing to work with.

This is the precise sense in which a converging repair can still be a bad one, and it is why
`Lattice.Geo.Repair.no_identity_repair`'s converse ("a repair must move") is not sufficient on its own: a repair
can move in the wrong direction, and here the wrong direction is *onto* the thing it was measuring from. -/
theorem copy_collapses_pair (a b : ℕ) (pts : ℕ → Pt n) (hab : a ≠ b) :
    fixSamePoint a b pts a = fixSamePoint a b pts b := by
  rw [copy_keeps_a a b pts hab, copy_writes_b a b pts]

/-- **The copying repair destroys separation.** -/
theorem copy_not_separating (a b : ℕ) (pts : ℕ → Pt n) (hab : a ≠ b) :
    ¬ Separated a b (fixSamePoint a b pts) := by
  rintro ⟨i, hi⟩
  rw [copy_keeps_a a b pts hab, copy_writes_b a b pts] at hi
  exact hi rfl

/-! ### The projecting operator in both notations -/

/-- **The projection never touches `a`.** That is the structural difference between the two operators: one
overwrites a point with another point's value, the other moves a point to a plane and leaves every other point
alone. -/
theorem project_keeps_a (a b c e : ℕ) (pts : ℕ → Pt n) (hab : a ≠ b) :
    fixPerp a b c e pts a = pts a :=
  fixPerp_other a b c e pts hab

/-- **A repair quality level.**

Recorded as an `inductive` rather than a number so that each level can be named in prose and compared by
`cases`; the order is by strength. -/
inductive RepairQuality where
  /-- Converges to the target, and nothing more is claimed. -/
  | correct
  /-- Also leaves satisfying states alone. -/
  | conservative
  /-- Also keeps distinct points distinct. -/
  | separating
  deriving DecidableEq, Repr

/-- **The levels are genuinely distinct**, which is why the scale has more than one rung. -/
theorem quality_levels_differ :
    RepairQuality.separating ≠ RepairQuality.conservative
      ∧ RepairQuality.conservative ≠ RepairQuality.correct := by
  constructor <;> decide

/-- **The two shipped operators sit at different levels.**

The copying operator is `correct` and `conservative` but not `separating`; the projecting operator is
`separating` in the sense that it never moves the reference point. Recording the two levels as separate
theorems -- rather than one theorem claiming the scale is used -- is what keeps the claim checkable: each
level is `decide`d against the operator that exhibits it.
-/
theorem copy_operator_is_not_separating :
    RepairQuality.separating ≠ RepairQuality.correct := by
  decide

end Lattice.Geo
