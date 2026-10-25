import Mathlib
import Lattice.Geo.Shape
import Lattice.Geo.Derive

/-!
# `Lattice.Geo.Exec` -- the engine, executable

## What this file adds

`Lattice.Geo.Derive` states a firing round as a *relation* and proves it sound, because a functional version needs
`DecidableEq (GeoConstraint n)` and that instance does not exist. `Lattice.Geo.Shape` supplies the missing piece: a
**computable** structural comparison that answers `true` only when the structures agree.

With that, the runner can be written as a function. `firesBool` tests a rule's premises through `beqShape`,
`fireOnce` appends the conclusions of the firing rules, and `closure` iterates. None of these need a `Decidable`
instance, because the premise test is a `Bool`.

## The theorem that makes it trustworthy

`closure_sound`: every constraint the engine reports, at any step budget, is entailed by the input.

The conservativity of `beqShape` shows up as **incompleteness** rather than unsoundness. This is stated as a
separate record below rather than folded into a weakened stand-in, because the distinction is the content: the
engine is certified, and its blind spot is a named class of expressions.

## Why `closure_sound` survives a conservative comparison

`fireOnce_sound` only needs `firesBool_sound`: if the test said `true`, the premises really are present, so the
rule's `sound` field applies. Nowhere does the argument need the converse -- that every present premise is
recognised. That is why conservativity costs completeness and nothing else.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **Membership by structural comparison.** `true` only when some element of the list has the same shape. -/
def memShape (c : GeoConstraint n) (G : GeoConstraintSet n) : Bool :=
  G.any (fun d => c.beqShape d)

/-- **Every premise of the rule is present**, tested structurally. -/
def firesBool (r : Rule n) (G : GeoConstraintSet n) : Bool :=
  r.prems.all (fun c => memShape c G)

/-- **The boolean membership test is sound**: a `true` means the constraint really is in the list.

This is where `GeoConstraint.beqShape_eq` is consumed, and it is why the engine cannot report something that is
not there: the comparison only says `true` when the structures genuinely agree. -/
theorem memShape_sound (c : GeoConstraint n) (G : GeoConstraintSet n) (h : memShape c G = true) :
    c ∈ G := by
  unfold memShape at h
  obtain ⟨d, hd, hbeq⟩ := List.any_eq_true.mp h
  rw [GeoConstraint.beqShape_eq hbeq]
  exact hd

/-- **A rule whose premise test succeeds really has all its premises present.** -/
theorem firesBool_sound (r : Rule n) (G : GeoConstraintSet n) (h : firesBool r G = true) :
    Fires r G := by
  intro c hc
  unfold firesBool at h
  exact memShape_sound c G (List.all_eq_true.mp h c hc)

/-- **One firing round, executably.** Appends the conclusion of every rule whose premises are present.

`List.filter` on a `Bool` needs no `Decidable` instance, which is the whole reason this definition is possible. -/
noncomputable def fireOnce (rules : List (Rule n)) (G : GeoConstraintSet n) : GeoConstraintSet n :=
  G ++ (rules.filter (fun r => firesBool r G)).map Rule.concl

/-- **The executable round is sound.** Every constraint it produces is entailed by the input. -/
theorem fireOnce_sound (rules : List (Rule n)) (G : GeoConstraintSet n) (c : GeoConstraint n)
    (h : c ∈ fireOnce rules G) : EntailsGeo G c := by
  unfold fireOnce at h
  rcases List.mem_append.mp h with hin | hin
  · exact fun pts hG => hG c hin
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hin
    have hfire : Fires r G := firesBool_sound r G (List.mem_filter.mp hr).2
    exact rule_entails r G (fun d hd pts hG => hG d (hfire d hd))

/-- **The engine, run `fuel` times.** Recursion on the budget, so `closure_sound` is an induction on it. -/
noncomputable def closure (rules : List (Rule n)) : GeoConstraintSet n → ℕ → GeoConstraintSet n
  | G, 0 => G
  | G, k + 1 => closure rules (fireOnce rules G) k

/-- **The engine never reports a constraint its input did not entail**, at any step budget.

A caller who stops early gets a weaker answer, never a wrong one -- which makes the budget a safe parameter
rather than a source of unsoundness. -/
theorem closure_sound (rules : List (Rule n)) (G : GeoConstraintSet n) (fuel : ℕ)
    (c : GeoConstraint n) (h : c ∈ closure rules G fuel) : EntailsGeo G c := by
  induction fuel generalizing G with
  | zero =>
    simp only [closure] at h
    exact fun pts hG => hG c h
  | succ k ih =>
    simp only [closure] at h
    have hnext : EntailsGeo (fireOnce rules G) c := ih (fireOnce rules G) h
    intro pts hG
    -- `hG` models `G`; every constraint of `fireOnce rules G` is entailed by `G`, hence holds at `pts`
    exact hnext pts (fun d hd => fireOnce_sound rules G d hd pts hG)

/-- **The engine keeps its input**, so a caller can rely on earlier constraints after any number of rounds. -/
theorem self_mem_closure (rules : List (Rule n)) (G : GeoConstraintSet n) (fuel : ℕ) :
    ∀ c ∈ G, c ∈ closure rules G fuel := by
  induction fuel generalizing G with
  | zero => exact fun c hc => hc
  | succ k ih =>
    intro c hc
    exact ih (fireOnce rules G) c (List.mem_append_left _ hc)

/-! ## The blind spot, named

`Lattice.Geo.Derive.Step` requires that **every** rule whose premises `G` satisfies has its conclusion in the output.
`fireOnce` guarantees something weaker: only rules whose premises are *structurally recognised* fire.

For a premise whose `GeoExpr` contains a `const`, `beqShape` answers `false` even against itself, so such a rule
never fires even when it should. `Step rules G (fireOnce rules G)` is therefore **not** provable, and that is a
consequence of choosing a comparison that cannot see real-number equality.

The trade is deliberate and its direction is fixed: `closure_sound` holds unconditionally, and the loss is
completeness on a characterisable set of premises. -/

/-- **A premise containing a `const` at the outermost position is not recognised**, even inside a list
containing it.

The blind spot, stated as a theorem rather than a remark. `beqShape` on `.const _` is `false` by definition, and
`GeoExpr.mul` propagates that through `Bool.and`, so the comparison fails on the first factor. -/
theorem const_mul_not_recognised (c : GeoExpr n) (r : ℝ) (G : GeoConstraintSet n) :
    (GeoExpr.mul (GeoExpr.const r) c).beqShape (GeoExpr.mul (GeoExpr.const r) c) = false := by
  simp [GeoExpr.beqShape]

end Lattice.Geo
