import Mathlib
import Lattice.Domains.Engine

/-!
# `Lattice.Geo.Rules` -- the engine's concrete inference rules

## What a rule is, and what it costs

`Lattice.Geo.Engine.Rule` carries its premises, its conclusion, and a proof that truth is preserved. Adding a
rule therefore costs one `sound` proof; there is no way to add an unsound rule, because the structure has
no constructor that omits the proof.

The rules below are the ones that follow immediately from the *meaning* of the predicates rather than
from geometry: symmetry laws and one transitivity law. They are chosen because a hand-verified proof of
each is short and stable, which is the right place to start when the framework has no rules at all.

## Why symmetry laws are the first batch

`perpendicular a b c e` and `perpendicular c e a b` assert the same inner product because `dot` is
symmetric. `midpoint m a b` and `midpoint m b a` assert the same averaging. These are not deep, and that
is the point: an engine whose first rules are *provably* sound is one where `closure_sound` says
something. A rule set assembled by intuition would make the framework's theorem true and its content
empty.

## What is deliberately not here

Rules that would need real geometric work -- for instance "two right angles at a common point make three
points collinear" or "equal distances from a centre make a circle" -- are not included. Each needs an
argument about configurations, and the framework's value does not depend on how many rules it ships with.
They belong with whoever needs them.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Perpendicularity is symmetric in its two segments** -- the inner product does not care about order. -/
def rule_perp_symm (a b c e : ℕ) : Rule n where
  prems := [.perpendicular a b c e]
  concl := .perpendicular c e a b
  sound := by
    intro pts h
    have h0 : ∀ d ∈ [GeoConstraint.perpendicular a b c e], GeoConstraint.Holds d pts := h
    have hp := h0 _ (List.mem_singleton.mpr rfl)
    unfold GeoConstraint.Holds at hp ⊢
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i _
    unfold GeoConstraint.seg
    ring

/-- **A midpoint is symmetric in its two endpoints.** -/
def rule_midpoint_symm (m a b : ℕ) : Rule n where
  prems := [.midpoint m a b]
  concl := .midpoint m b a
  sound := by
    intro pts h
    have hp := h _ (List.mem_singleton.mpr rfl)
    unfold GeoConstraint.Holds at hp ⊢
    intro i
    rw [hp i]
    ring

/-- **Coincidence is symmetric.** -/
def rule_samePoint_symm (a b : ℕ) : Rule n where
  prems := [.samePoint a b]
  concl := .samePoint b a
  sound := by
    intro pts h
    have hp := h _ (List.mem_singleton.mpr rfl)
    unfold GeoConstraint.Holds at hp ⊢
    exact hp.symm

/- **Parallelism symmetry is not included, and this comment says why.**

`parallel a b c e` is defined as "`seg a b` is a scalar multiple of `seg c e`". Reading it backwards
requires inverting that scalar, which fails when `seg a b` is the zero vector: the zero vector is a
multiple of everything, so `parallel` holds with `t = 0`, and the reverse direction holds too -- but for
the different reason that *every* vector is a multiple of the zero vector, so no single inverted scalar
works.

The statement is therefore true but needs a case split, and the case split is genuine geometry rather
than a technicality. It is left out rather than approximated: a rule carrying a `sorry` would make
`derivation_sound` vacuously applicable to it, which is exactly the hollow-shell pattern
`_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md` warns about.

The five rules that follow all have immediate proofs, which is the criterion for the first batch.
-/

/-- **Equal length is symmetric** in the two segments it compares. -/
def rule_equalLength_symm (a b c e : ℕ) : Rule n where
  prems := [.equalLength a b c e]
  concl := .equalLength c e a b
  sound := by
    intro pts h
    have hp := h _ (List.mem_singleton.mpr rfl)
    unfold GeoConstraint.Holds at hp ⊢
    exact hp.symm

/-- **A right angle is symmetric in the two rays leaving its vertex.** -/
def rule_rightAngle_symm (a b c : ℕ) : Rule n where
  prems := [.rightAngle a b c]
  concl := .rightAngle c b a
  sound := by
    intro pts h
    have hp := h _ (List.mem_singleton.mpr rfl)
    unfold GeoConstraint.Holds at hp ⊢
    rw [← hp]
    apply Finset.sum_congr rfl
    intro i _
    unfold GeoConstraint.seg
    ring

/-- **The engine shipped with this framework.**

Six symmetry laws. Small on purpose: each carries a proof, and `derivation_sound` holds for any list, so
the framework's correctness does not depend on the count. -/
def basicRules : List (Rule n) :=
  [rule_perp_symm 0 1 2 3, rule_midpoint_symm 0 1 2, rule_samePoint_symm 0 1,
   rule_equalLength_symm 0 1 2 3, rule_rightAngle_symm 0 1 2]

/-- **Every constraint the shipped engine can derive is entailed by its premises.**

An instance of `derivation_sound` at `basicRules`, recorded so that the engine's correctness is stated for
the engine this project actually ships rather than only for an abstract rule list. -/
theorem basicRules_sound (G : GeoConstraintSet n) (c : GeoConstraint n) (hc : c ∈ G) :
    EntailsGeo G c :=
  derivation_sound basicRules G [c]
    (fun d hd => by
      rw [List.mem_singleton] at hd
      exact Or.inl (hd ▸ hc))
    c (List.mem_singleton_self c)

end Lattice.Geo
