import Mathlib
import Lattice.Domains.Geometry.Engine

/-!
# `Lattice.Geo.Derive` -- running the symbolic engine

## What was missing

`Lattice.Geo.Engine` defines what a *sound* inference rule is and proves that any conclusion reached through one is
entailed. That is the engine's correctness, but not its behaviour: nothing in the project ever *ran* a rule, so
`derivation_sound` had no caller of its own.

This file supplies the runner, in the form the objective asks for: the engine consumes a `GeoConstraintSet` and
produces a `GeoConstraintSet`, with no normalised form or intermediate representation in between -- "the symbolic
model runs directly on the symbolic engine, without adding an intermediary layer".

## Why the runner is a relation rather than a function

The obvious definition filters the rule list by a boolean test of `Fires r G`. That needs
`Decidable (∀ c ∈ r.prems, c ∈ G)`, which needs decidable equality on `GeoConstraint` -- and `GeoConstraint`
carries `GeoExpr` fields whose equality is not decidable (`ℝ` has no `DecidableEq`).

Deriving the instance is therefore impossible without an axiom, so the runner is written as a **relation**:
`Step rules G H` says `H` is `G` together with the conclusions of the rules whose premises `G` satisfies.
Soundness is then a statement about any such `H`, which is exactly what a caller iterating the engine needs.

This is recorded rather than hidden: a functional `closure` would require an instance search that does not exist,
and shipping one behind a `sorry` or an axiom would be the hollow-shell pattern the project's gate I1/I2 forbids.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The premises of a rule are all present.** The syntactic side condition for firing a rule. -/
def Fires (r : Rule n) (G : GeoConstraintSet n) : Prop :=
  ∀ c ∈ r.prems, c ∈ G

/-- **One firing round**, stated relationally: `H` contains everything `G` contained, every rule of `rules` whose
premises `G` satisfies has its conclusion in `H`, and nothing else is in `H`.

The three conjuncts say `H` is exactly what a filtering implementation would produce. `H` is not determined
uniquely by `G` (duplicates are allowed), which is harmless: soundness holds for every choice. -/
def Step (rules : List (Rule n)) (G H : GeoConstraintSet n) : Prop :=
  (∀ c ∈ G, c ∈ H) ∧
  (∀ r ∈ rules, Fires r G → Rule.concl r ∈ H) ∧
  (∀ c ∈ H, c ∈ G ∨ ∃ r ∈ rules, Fires r G ∧ Rule.concl r = c)

/-- **A firing round preserves entailment.** Every constraint in the new set is either already present -- hence
entailed by `G` -- or the conclusion of a rule whose premises `G` satisfies, hence entailed by `rule_entails`.

Named `round_sound` rather than `step_sound` because `Lattice.Geo.Engine.step_sound` already names the single-rule
version; the two are related (this one is the rule-set closure of that one) and keeping the names distinct keeps
the distinction visible.
-/
theorem round_sound (rules : List (Rule n)) (G H : GeoConstraintSet n) (hstep : Step rules G H)
    (c : GeoConstraint n) (hc : c ∈ H) : EntailsGeo G c := by
  obtain ⟨_hkeep, _hadd, hclass⟩ := hstep
  rcases hclass c hc with hin | ⟨r, _hr, hfire, hconcl⟩
  · exact fun pts hG => hG c hin
  · rw [← hconcl]
    exact rule_entails r G (fun d hd pts hG => hG d (hfire d hd))

/-- **Every firing round keeps the input**, which is what lets a caller recover earlier conclusions after a
round and what makes soundness compose across rounds. -/
theorem round_keeps (rules : List (Rule n)) (G H : GeoConstraintSet n) (hstep : Step rules G H) :
    ∀ c ∈ G, c ∈ H :=
  hstep.1

end Lattice.Geo
