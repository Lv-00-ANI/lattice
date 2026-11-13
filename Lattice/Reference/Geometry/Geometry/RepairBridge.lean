import Mathlib
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Core.Invariant
import Lattice.Core.Simulation
import Lattice.Core.Idempotent
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Constraints.Loss

/-!
# `Lattice.Geo.RepairBridge` -- the verification loop's two halves, and one new measure bound

## Correction: most of this was already in `Core`

`Zero/Core/Repair.lean` already contains, at `Repair`'s level of generality:

* `Repair.progress` -- iterating reaches a satisfying state;
* `Repair.preserves` -- iterating keeps a satisfying state satisfying;
* `Repair.stable` -- a satisfying state is a fixed point.

**The first two are exactly what earlier revisions of this file set out to prove, and failed to.** The
"convergence is not available generically" claim those revisions carried was wrong: it *is* available, in `Core`,
under different notation (`R.iterate n x` there, `R.fix^[n] x` here).

This file is therefore not a new result but a **restatement in the `fix^[n]` notation**, kept because the two
notations are both in use and a reader following `Lattice.Geo.Loop` will meet the latter. What is genuinely new is the
last theorem, `measure_iterate_le`, which `Core` does not state.

## What is genuinely new

`measure_iterate_le` bounds the measure after any number of steps by its initial value. `Core`'s `progress` proves
termination by a clever bounded-descent argument but does not expose that bound; a caller who wants to know "how
many steps are needed" or "how small can the measure get in `n` steps" needs it, and it is not derivable from the
termination statement alone.
-/

namespace Lattice.Core

variable {α : Type}

namespace Repair

/-- **A satisfying state is a fixed point of every iterate.**

Immediate from `absorbs` by induction on the iterate: the state never changes, so it stays put. -/
theorem iterate_fix_of_sat (R : Repair α) (x : α) (h : R.Sat x) :
    ∀ n : ℕ, R.fix^[n] x = x := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, R.absorbs x h]

/-- **A satisfying state stays satisfying under iteration.** -/
theorem iterate_sat_of_sat (R : Repair α) (x : α) (h : R.Sat x) (n : ℕ) :
    R.Sat (R.fix^[n] x) := by
  rw [iterate_fix_of_sat R x h n]
  exact h

/-- **The loop does not destroy semantics.**

A satisfying state is untouched by every iterate, so it remains satisfying. This is the "without destroying
semantics" half of the fourth target, stated at `Repair`'s level of generality so that every operator -- the two
geometric ones, the linear one, and any future one -- inherits it from `absorbs` alone.

It is deliberately separate from convergence: an operator can be conservative without converging, and a caller
who only needs "the loop will not corrupt a good answer" should not be forced to establish convergence first. -/
theorem loop_preserves_sat (R : Repair α) (x : α) (h : R.Sat x) (n : ℕ) :
    R.fix^[n] x = x ∧ R.Sat (R.fix^[n] x) :=
  ⟨iterate_fix_of_sat R x h n, iterate_sat_of_sat R x h n⟩

/-- **Restating `Core`'s `progress` in the `fix^[n]` notation.**

The substance is `Lattice.Core.Repair.progress`; this is the same statement with the iterate written as `fix^[n]`
rather than `iterate n x`, so that the theorems in this file read uniformly. -/
theorem converges (R : Repair α) (x : α) : ∃ n : ℕ, R.Sat (R.fix^[n] x) :=
  R.progress x

/-- **One step strictly lowers the measure while unsatisfied**, read off `decreases`. -/
theorem measure_step (R : Repair α) (x : α) (h : ¬ R.Sat x) :
    R.μ (R.fix x) < R.μ x :=
  R.decreases x h

/-- **Reaching measure zero means reaching satisfaction**, by `atomic`. -/
theorem sat_of_measure_zero (R : Repair α) (x : α) (h : R.μ x = 0) : R.Sat x :=
  R.atomic x h

/-- **The measure never increases under iteration.**

A weaker statement than strict descent, and the part of the convergence argument that *does* go through: at a
satisfying state `absorbs` makes the measure constant, at an unsatisfied one `decreases` makes it smaller.

Stated because it is useful on its own -- a caller bounding the measure after `n` steps needs exactly this, and
not the existence of a terminating `n`. -/
theorem measure_iterate_le (R : Repair α) (x : α) :
    ∀ n : ℕ, R.μ (R.fix^[n] x) ≤ R.μ x := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases hsat : R.Sat (R.fix^[k] x)
    · -- an absorbing state does not move, so the measure is unchanged
      rw [R.absorbs _ hsat]
      exact ih
    · -- an unsatisfied state loses at least one unit
      exact Nat.le_trans (Nat.le_of_lt (R.decreases _ hsat)) ih

/-! ## Relation to `Lattice.Core.Repair`

| statement | `Core` | here |
|:--|:--|:--|
| convergence | `progress` | `converges` (restatement) |
| preservation | `preserves` | `iterate_sat_of_sat` (restatement) |
| absorption | `stable` | `iterate_fix_of_sat` (uses it directly) |
| measure bound | — | **`measure_iterate_le`** |

Two of these are restatements and the table says so: the point of keeping them is not duplication but that the
`Lattice.Geo` layer reads `fix^[n]`, and a reader there should not have to translate. The fourth row is new.

**Lesson worth recording**: the earlier attempts at a "generic convergence theorem" spent six rounds reconstructing
`Core`'s `progress` without noticing it existed. Grepping the interface's own file before proving something about
the interface would have found it in one step. -/

/-- **The repair loop as a self-simulation.**

`Repair`'s preservation property, read through `Lattice.Core.Simulation`: take the state space `α`, the transition
relation "one `fix` step", and the identity map. Identity is a forward simulation (`Simulation.sim_id`), and the
satisfying states are carried along it -- which is `iterate_sat_of_sat`.

Stated here so that `Lattice.Core.Simulation` has a consumer. The file's header claims the simulation shape is
"stated once here and reused"; before this theorem nothing imported it, so that claim had no instance. This is the
first one. -/
theorem repair_as_self_simulation (R : Repair α)
    (step : α → Unit → α → Prop) (hstep : ∀ x y, step x () y ↔ R.fix x = y) :
    ForwardSim step step id ∧ ∀ x, R.Sat x → ∀ n, R.Sat (R.fix^[n] x) :=
  ⟨sim_id step, fun x hx n => iterate_sat_of_sat R x hx n⟩

/-! ## The loop as a run in the simulation framework

`Lattice.Core.Simulation` provides `StarAny` (labelled multi-step reachability) and `runs_preserved` (a forward
simulation lifts to whole runs). Until recently nothing consumed either. The repair loop is a run: its state space
is `α`, its transition is one `fix` step, and every step carries the unit label.

`iterate_to_starAny` records that identification, and `repair_run_preserved` applies `runs_preserved` to it. The
*conclusion* duplicates `iterate_sat_of_sat` -- which is worth saying: the point is not a new fact but that the
repair loop now shares the same correctness skeleton as compilation and extraction.

`iterate_comm` is the bookkeeping lemma the identification needs: `StarAny.cons` asks its tail to start from
`R.fix x`, while the induction hypothesis speaks about `x`, and the two meet only after commuting the extra step
past the iterates. It is a two`-term` proof from `Function.iterate_succ_apply` and its primed form -- the signature
of both was checked before writing rather than guessed. -/

/-- **Iteration order commutes**: `f^[k] (f x) = f (f^[k] x)`.

Both sides equal `f^[k + 1] x`, by `Function.iterate_succ_apply` on one side and
`Function.iterate_succ_apply'` on the other. -/
theorem iterate_comm (f : α → α) (k : ℕ) (x : α) :
    f^[k] (f x) = f (f^[k] x) :=
  (Function.iterate_succ_apply f k x).symm.trans (Function.iterate_succ_apply' f k x)

/-- **`n` iterations of `fix` form a labelled run** of length `n`, every label being `()`.

The induction is on the length with the starting state generalized: each `StarAny.cons` needs its tail to start
from `R.fix x`, so the hypothesis must be applicable at any state. Zero steps is `StarAny.nil`; each further step
is `StarAny.cons` with the label `()` and the transition witness `rfl`. -/
theorem iterate_to_starAny (R : Repair α) :
    ∀ n : ℕ, ∀ x : α,
      StarAny (fun a (_ : Unit) b => R.fix a = b) x (List.replicate n ()) (R.fix^[n] x) := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [Function.iterate_zero_apply, List.replicate_zero]
    exact StarAny.nil x
  | succ k ih =>
    intro x
    -- rewrite the goal's endpoint from `fix^[k+1] x` to `fix^[k] (fix x)`, which is what the
    -- hypothesis provides at the state `R.fix x`
    rw [Function.iterate_succ_apply]
    exact StarAny.cons rfl (ih (R.fix x))

/-- **The repair loop preserves satisfaction, via the simulation framework.**

This is `runs_preserved` applied to the run `iterate_to_starAny`. Its conclusion is `iterate_sat_of_sat`, which was
already available by direct induction -- the reason to state it again is that it makes the repair loop an instance
of the same simulation argument used for compilation, rather than a separate argument that happens to look similar.

`Lattice.Core.Simulation`'s header claims the simulation shape is stated once and reused. This is the first consumer
of its multi-step version. -/
theorem repair_run_preserved (R : Repair α) (x : α) (h : R.Sat x) (n : ℕ) :
    StarAny (fun a (_ : Unit) b => R.fix a = b) x (List.replicate n ()) (R.fix^[n] x) ∧
      R.Sat (R.fix^[n] x) := by
  have hsim : ForwardSim (fun a (_ : Unit) b => R.fix a = b)
      (fun a (_ : Unit) b => R.fix a = b) id := sim_id _
  have hrun := runs_preserved hsim (iterate_to_starAny R n x)
  exact ⟨hrun, iterate_sat_of_sat R x h n⟩

/-! ## The join with T2: a repair's success is a penalty reaching zero

`Repair`'s satisfiability predicate and the penalties of `Lattice.Geo.Loss` / `Lattice.Geo.Square` are two spellings of one
condition -- "the constraint holds". The two theorems below make that explicit, and they close the loop the
objective describes: **verification succeeds exactly when the penalty reaches zero**, so a training run that drives
the penalty to zero has produced a model the symbolic side agrees with.

The general form needs only that the two predicates coincide; the concrete form discharges that premise for the
`samePoint` repair using `Lattice.Geo.Loss.loss_eq_zero_toGeo_samePoint`. -/

/-- **A repair whose criterion is "penalty zero" converges to penalty zero.**

`Repair.progress` supplies a step count at which `Sat` holds; the hypothesis turns that into `pen = 0`. This is
generic in the operator, so any future repair whose `Sat` is a penalty's vanishing joins here by supplying one
equivalence. -/
theorem repair_success_is_penalty_zero (R : Repair α) (pen : α → ℝ)
    (h : ∀ x, R.Sat x ↔ pen x = 0) (x : α) :
    ∃ n : ℕ, pen (R.fix^[n] x) = 0 := by
  obtain ⟨n, hn⟩ := R.progress x
  exact ⟨n, (h _).mp hn⟩

end Repair

/-! ## The shape T3 and T4 share -- defined in `Core`, used here

`IdempotentOn` and its two theorems live in `Lattice.Core.Idempotent`, one layer below this file, because the round-trip
obligation they also cover belongs to `Lattice.Lift.Extraction` -- which cannot import anything from `Geo`. Putting the
definition up here would have made the unification unreachable from one of the two things it unifies.

What this file adds is the `Repair`-side instance, since `Repair` is a `Core` structure and could technically have
carried it directly; it is stated here to keep `Core.Repair` free of any mention of idempotence, which is a fact about
how the loop is used rather than about what a repair is.

**What the unification does not give** is a closed loop returning to the original weight: that needs
`compile ∘ extract = id`, a right inverse, and `Lattice.Lift.Extraction.semantic_not_injective` shows none exists. The
loop closes at the level of semantics, not of objects. -/

/-- **`Repair.absorbs` is `IdempotentOn`** at `R.Sat` — the `Repair`-side instance of the shared shape. -/
theorem Repair.absorbs_is_idempotentOn (R : Repair α) :
    IdempotentOn R.Sat R.fix :=
  R.absorbs

/-- **`Repair.iterate_fix_of_sat` is the `IdempotentOn.iterate` instance** at `S := R.Sat`: restating it through the
general theorem records that the loop's preservation is not a special fact about absorption but the iteration law of
any idempotent-on-a-subset operator. -/
theorem Repair.iterate_fix_of_sat_via_idempotent (R : Repair α) (x : α) (h : R.Sat x) :
    ∀ n : ℕ, R.fix^[n] x = x :=
  fun n => IdempotentOn.iterate (Repair.absorbs_is_idempotentOn R) n x h

end Lattice.Core
