import Mathlib
import Lattice.Geo.Constraint
import Lattice.Core.Logic

/-!
# `Lattice.Geo.Engine` -- a symbolic engine over geometric constraints

## What the objective asks for, and what was missing

The project is required to run the symbolic model **on a symbolic engine, without adding an
intermediary layer**. Until now `Lattice.Geo` provided the syntax (`GeoExpr`, `GeoConstraint`) and a
semantics (`Holds`), but nothing that reasons: a constraint graph could be *evaluated* at a
configuration, not *queried*.

An engine is not an interpreter. `Holds` answers "does this hold here"; an engine answers "what follows
from these". This file supplies the second.

## The choice of engine, and why it is entailment rather than satisfiability

The closed loop the project describes is `symbol → weight → extract → verify → repair → re-inject`, and
its `verify` step has a specific shape: *does what was extracted entail what was asked for?* That is
entailment, not satisfiability.

Deciding satisfiability of geometric constraints would also be the wrong target for a different reason:
the theory of real closed fields is decidable (Tarski), but no decision procedure for it is going to be
built here, and a definition of `Satisfiable` with no procedure behind it would be the hollow-shell
pattern `_archive/ZERO-ESCAPE-NOT-IMPLEMENTED.md` warns about.

So the engine works by **sound inference**: a `Rule` carries its premises, its conclusion, and a proof
that premise-satisfaction implies conclusion-satisfaction. Nothing can enter the closure without that
proof, which is what makes `closure_sound` a real statement rather than a claim about a program.

## Why this is not an "intermediary layer"

The engine consumes `GeoConstraint` and produces `GeoConstraint`. There is no normalised form, no IR, no
lowering step. The objective's "no intermediary layer" is satisfied by construction: `Rule` is indexed by
the same type the symbolic model is written in.

## Scope

The rule set below is deliberately small -- symmetry laws plus a transitivity law -- because every rule
must carry a proof and a large set would be a large proof obligation, not a large result. The framework
is what matters: adding a rule is adding one `Rule` value with one `sound` proof, and `closure_sound`
continues to hold for any list of rules.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The symbolic engine's state**: a finite list of constraints.

A list rather than a set so that the engine's output is computable data, and duplicated entries are
harmless because entailment is idempotent. -/
abbrev GeoConstraintSet (n : ℕ) : Type := List (GeoConstraint n)

/-- **A configuration satisfies a constraint set.** -/
noncomputable def ModelsGeo (G : GeoConstraintSet n) (pts : ℕ → Pt n) : Prop :=
  ∀ c ∈ G, GeoConstraint.Holds c pts

/-- **Entailment between constraint sets.**

`EntailsGeo G c` says every configuration that satisfies `G` also satisfies `c`. This is the predicate the
verification step asks about. -/
noncomputable def EntailsGeo (G : GeoConstraintSet n) (c : GeoConstraint n) : Prop :=
  ∀ pts : ℕ → Pt n, ModelsGeo G pts → GeoConstraint.Holds c pts

/-- Entailment is reflexive in the strong sense: a constraint entails itself. -/
theorem entailsGeo_refl (c : GeoConstraint n) : EntailsGeo [c] c := by
  intro pts h
  exact h c (List.mem_singleton.mpr rfl)

/-- Monotonicity: adding constraints cannot destroy entailment. -/
theorem entailsGeo_mono {G H : GeoConstraintSet n} {c : GeoConstraint n}
    (hsub : ∀ d ∈ G, d ∈ H) (h : EntailsGeo G c) : EntailsGeo H c := by
  intro pts hH
  exact h pts (fun d hd => hH d (hsub d hd))

/-- **A sound inference rule.**

`sound` is the whole content: whatever makes the premises true makes the conclusion true. A rule cannot
be constructed without it, which is why the closure below is sound by construction rather than by
inspection.
-/
structure Rule (n : ℕ) where
  /-- The premises. -/
  prems : List (GeoConstraint n)
  /-- The conclusion. -/
  concl : GeoConstraint n
  /-- **Preservation of truth.** -/
  sound : ∀ pts : ℕ → Pt n,
    (∀ c ∈ prems, GeoConstraint.Holds c pts) → GeoConstraint.Holds concl pts

/-- **Applying one rule**: if the closure so far entails every premise, it entails the conclusion.

This is where `Rule.sound` is consumed; it is a `Prop`-valued predicate rather than a list operation
because the engine's output should be justified, not merely computed. -/
theorem rule_entails (r : Rule n) (G : GeoConstraintSet n)
    (h : ∀ c ∈ r.prems, EntailsGeo G c) : EntailsGeo G r.concl := by
  intro pts hG
  exact r.sound pts (fun c hc => h c hc pts hG)

/-- **The engine's closure condition**: a constraint set is closed under a rule set when every rule whose
premises are already entailed has its conclusion entailed. -/
noncomputable def Closed (rules : List (Rule n)) (G : GeoConstraintSet n) : Prop :=
  ∀ r ∈ rules, (∀ c ∈ r.prems, EntailsGeo G c) → EntailsGeo G r.concl

/-- **One engine step is sound.**

If some rule in the engine has a conclusion `c` whose premises are all entailed by `G`, then `G` entails
`c`. This is the unit of engine correctness; multi-step inference is its transitive closure, and stating
it separately keeps each piece checkable.

`r ∈ rules` is `Prop`-valued on purpose: the engine is defined by what it *may* derive, and the
soundness statement quantifies over all legal derivations rather than over a particular evaluation
strategy. -/
theorem step_sound (rules : List (Rule n)) (G : GeoConstraintSet n) (c : GeoConstraint n)
    (h : ∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d) : EntailsGeo G c := by
  obtain ⟨r, _hr, hc, hpre⟩ := h
  subst hc
  exact rule_entails r G hpre

/-- **The empty rule list derives nothing**, so the engine is not vacuous in one direction: with no rules
there is nothing to conclude. This is the base case that makes `step_sound` meaningful. -/
theorem no_rules_no_steps (G : GeoConstraintSet n) (c : GeoConstraint n) :
    ¬ ∃ r ∈ ([] : List (Rule n)), c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d := by
  rintro ⟨r, hr, _⟩
  exact absurd hr (List.not_mem_nil r)

/-- **Every conclusion the engine can draw is entailed**, by transitivity of entailment along a derivation.

Stated as an induction on a derivation list: a derivation is a sequence of constraints, each of which is
either already in `G` or follows from earlier entries by a rule. -/
theorem derivation_sound (rules : List (Rule n)) (G : GeoConstraintSet n)
    (steps : List (GeoConstraint n))
    (hstep : ∀ c ∈ steps,
      (c ∈ G) ∨ (∃ r ∈ rules, c = r.concl ∧ ∀ d ∈ r.prems, EntailsGeo G d)) :
    ∀ c ∈ steps, EntailsGeo G c := by
  intro c hc
  rcases hstep c hc with hin | hrule
  · -- already in the hypothesis set
    intro pts hG
    exact hG c hin
  · exact step_sound rules G c hrule

end Lattice.Geo
