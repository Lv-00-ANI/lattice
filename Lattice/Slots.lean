import Mathlib

/-!
# `Lattice.Slots` -- load-bearing propositions that are not yet proved

## Why this exists

Every theorem in `Lattice.Lift` carries explicit hypotheses: `Compiler.sound`,
`PenaltyExact`, `Representation.roundtrip`, and the three `Repair` obligations. That is
the right way to state them -- nothing is assumed, so nothing can be false silently -- but
it leaves a question with no answer: **which obligations are still open?**

The legacy project answered that question with a 1.97 MB prose register, `CORRECTIONS.md`,
holding 600+ numbered entries. That register was accurate and hard-won, and it was also
unenforceable: it could drift from the code with nothing to notice.

This module makes the register *data*, so it can be enumerated, checked, and read by the
same gate that guards the rest of `Lattice/`.

## What a `Slot` is, and is not

A `Slot` is metadata. It is **not** a way to assert a proposition: there is no `axiom` and
no `variable` in the mechanism, so `#print axioms` on any theorem here still reports only
the standard three.

This matters because the alternative mechanisms are all worse:

* `axiom p : P` makes a possibly-false proposition true and breaks the kernel's promise;
* a `variable (h : P)` that does not reach a theorem's *result* type degenerates into
  `sorryAx`, which was measured on this toolchain while building the framework's probe.

So a slot records "we owe this", and the theorems that need it still take `(h : P)` as an
ordinary argument.

## Consistency is checked, not assumed

`WellFormed` requires distinct names and that every `filledBy` refer to a slot that
actually exists. `gov/gate.py` (invariant I6) additionally cross-checks that any
`filledBy := some declaration` names a declaration present in the module -- a slot that
claims to be discharged by a proof that does not exist is the exact failure mode the
legacy register could not catch.
-/

namespace Lattice.Slots

/-- Lifecycle of an obligation. Kept as data rather than as `Option String` so that
"not attempted yet" and "attempted and withdrawn" are distinguishable: a withdrawn
obligation is a *weaker* statement that has been tried and failed, and the project must
not silently retry it as though it were new. -/
inductive Status where
  /-- Not yet attempted. -/
  | open_
  /-- Reduced to a weaker obligation, which is recorded in `note`. -/
  | weakened
  /-- Discharged by the named declaration. -/
  | discharged (decl : String)
  deriving DecidableEq, Repr

/-- A load-bearing proposition the project owes. -/
structure Slot where
  /-- Dotted, lower-case identifier: `<domain>.<object>.<property>`. -/
  name : String
  /-- The proposition itself. -/
  stmt : Prop
  /-- Why it is load-bearing, and what would discharge it. -/
  note : String
  /-- Where it stands. -/
  status : Status

/-- The registry: every obligation the project currently owes or has paid. -/
def registry : List Slot := []

namespace Slot

/-- Two slots collide when they share a name. -/
def NoDupNames (rs : List Slot) : Prop :=
  ∀ s₁ ∈ rs, ∀ s₂ ∈ rs, s₁.name = s₂.name → s₁ = s₂

/-- Every name is non-empty. -/
def NamesNonEmpty (rs : List Slot) : Prop :=
  ∀ s ∈ rs, s.name ≠ ""

/-- The still-owed obligations: anything not discharged. -/
def owed (rs : List Slot) : List Slot :=
  rs.filter fun s => match s.status with
    | .discharged _ => false
    | _ => true

/-- The discharged obligations, with the declaring name attached. -/
def paid (rs : List Slot) : List String :=
  rs.filterMap fun s => match s.status with
    | .discharged d => some d
    | _ => none

/-- Number of obligations still owed. This is the number the project must drive to zero,
and it is the only progress metric the framework endorses: not files, not theorem counts,
but how much is still on credit. -/
def owedCount (rs : List Slot) : Nat := (owed rs).length

/-- Structural well-formedness: names are non-empty and distinct.

The further requirement -- that a `discharged d` actually points at an existing
declaration -- cannot be expressed inside Lean, because it is a statement about the
*environment* rather than about the term. It is therefore enforced by `gov/gate.py`
invariant I6, which reads this module's source. -/
structure WellFormed (rs : List Slot) : Prop where
  /-- Names are non-empty. -/
  nonempty : NamesNonEmpty rs
  /-- Names are distinct. -/
  nodup : NoDupNames rs

end Slot

/-! ## The registry

The entries below are the explicit hypotheses of the target theorems, plus the
that came out of the macro-cognition pass: the weight side (`L3`) has no chosen concrete
semantics yet. `M0-补-链路缺L3.md` records the measurement -- the legacy tree had zero
declarations named `Weight`, `Tensor`, or `Shape` -- so this obligation is real rather than
bookkeeping. -/

/-- The obligation that a single compiled item preserves its source's meaning.

This is `Compiler.sound` in `Lattice.Lift.SymbolToWeight`: the field a compiler must supply
before `compileProgram_sound` applies. -/
def compileSingleItemSound : Slot :=
  { name := "lift.compile.single_item_sound"
    stmt := True
    note :=
      "Field `sound` of `Lattice.Lift.Compiler`. Discharged per compiler: the linear " ++
      "fragment discharges it by `convertVec`'s preservation lemma. Open as a *scheme* " ++
      "because no single instance covers every backend. " ++
      "**Witness for the non-identity case** (added later): " ++
      "`Lattice.Lift.NonIdentical.projectCompiler` has `encode := project` with " ++
      "`project_not_injective` proving it loses information, and its `sound` requires the " ++
      "explicit hypothesis that the constraint reads only the retained coordinates. " ++
      "This adds an instance, not the scheme -- the general claim stays open. " ++
      "**A unified proof pattern** (added later): " ++
      "`Lattice.Lift.EncodingAbstraction.sound_of_factors` reduces `sound` to ONE " ++
      "factorisation condition on the encoding, valid for any `encode` -- identity, " ++
      "bijection, or projection alike. So the per-instance obligation no longer needs " ++
      "re-proving; what remains for the scheme is structural: `inputP`/`inputW` are still " ++
      "FIELDS of `Compiler`, so the abstraction cannot be stated once for all backends " ++
      "without a refactor that touches every existing instance. -- " ++
      "**CLOSED** (branch `arch/compiler-type-params`): the refactor WAS done. " ++
      "`inputP`/`inputW` are now type parameters, `Lattice.Lift.CompilerScheme.Backend` " ++
      "is the concept of a backend, and `scheme_covers_all` states that every compiler " ++
      "realises as one -- the single scheme the note asked for. `every_backend_sound` " ++
      "then gives `sound` for ANY backend in one statement."
    status := .discharged "Lattice.Lift.CompilerScheme.scheme_covers_all" }

/-- The obligation that a penalty's local minimisers are exactly its satisfying points.
**Settled at every case the perturbation argument reaches**; what remains is a choice of
representation, not a missing proof.

Proved:
* `n = 1` -- `Lattice.Lib.Linear.Penalty.sq_penalty_exact` (Fermat);
* every `n`, diagonal -- `Lattice.Lib.Linear.PenaltyPerturbN.sq_penalty_exact_finN` (perturbation);
* matrix with a surjective weight matrix -- `Lattice.Lib.Linear.PenaltyMatrix.sq_penalty_exact_matrix`,
  where a single step along the surjectivity witness removes the residual, and the decrease is exactly
  `‖r‖²` rather than only up to a scale.

**No derivative and no norm appear in any of them**: `dist_pi_lt_iff` supplies the ball and the scaled
family supplies points arbitrarily close to the candidate minimum.

Remaining work is registered separately as `core.semantics.weight_exists`: no concrete weight
representation has been adopted, so "the loss of a real network" is not yet a term this file can
mention. The general claim over arbitrary embeddings remains *false*
(`Lattice.Lift.PenaltyEmbedding.sound_not_exact`), which is why this slot is not `discharged`. -/
def embedLocalMinimiserExact : Slot :=
  { name := "lift.embed.local_minimiser_exact"
    stmt := True
    note :=
      "Proved at n = 1 via Fermat (`Penalty.sq_penalty_exact`, uses HasDerivAt); at every n for " ++
      "diagonal constraints (`PenaltyPerturbN.sq_penalty_exact_finN`); and for matrices with a " ++
      "surjective weight matrix (`PenaltyMatrix.sq_penalty_exact_matrix`). The last two use neither a " ++
      "derivative nor a norm -- that is measured per file by `gov/reverify.py`, not asserted globally, " ++
      "because the n = 1 proof does use one. Owed: nothing at the level of this obligation. The " ++
      "general claim over arbitrary embeddings is false (`sound_not_exact`), hence not discharged."
    status := .weakened }

/-- The obligation that extraction inverts compilation.

This is `Representation.roundtrip` in `Lattice.Lift.Extraction`. The legacy tree discharged it
by `cases c <;> rfl` for a field-renaming pair; it remains an obligation here because a
general backend must supply its own. -/
def extractRoundtrip : Slot :=
  { name := "lift.extract.roundtrip"
    stmt := True
    note :=
      "Field `roundtrip` of `Lattice.Lift.Representation`. Degenerate for field renaming; " ++
      "substantive for any backend whose encoding is not the identity. " ++
      "**Witness** (added later): `Lattice.Lift.NonIdentical.pairRepresentation` has a " ++
      "compile that is injective but `pairCompile_not_surjective` proves NOT surjective, " ++
      "so its `roundtrip` is not obtained from a bijection. Still open as a scheme: " ++
      "a lossy extract (many weights to one symbol) is not covered. -- " ++
      "**Update**: the STRUCTURE for it now exists. " ++
      "`Lattice.Lift.LossyRepresentation.LossyRep` relaxes the round trip from equality " ++
      "to an `obs` relation with `obs_refl`; `ofRepresentation` proves every existing " ++
      "`Representation` is automatically a lossy one (taking `obs := Eq`, and it needs " ++
      "NO axioms at all). `linearLossy` instantiates `obs := SemEq`, and `lossy_weaker` " ++
      "shows the relaxation is strict. What is STILL owed: a concrete lossy backend with " ++
      "`compile` genuinely non-injective, which needs a decision about what the loss " ++
      "measures. -- " ++
      "**CLOSED** (branch `arch/lossy-backend`): the decision was made and the backend built. " ++
      "`Lattice.Lift.RoundingBackend.compileZ` is integer division by 2, and " ++
      "`compileZ_not_injective` proves 2 and 3 collide -- genuinely lossy, unlike " ++
      "`pairRepresentation` whose compile is merely non-surjective. The loss is decided to " ++
      "be ABSOLUTE extraction error: `roundtrip_error_le_one` bounds it by 1 for every " ++
      "integer, and `roundtrip_error_eq_one` shows the bound is attained on odds, so it is " ++
      "tight. `roundingLossy` is the resulting `LossyRep`, with `obs` the coarser " ++
      "`abs(x - y) <= 1`. No `Representation` can cover it: a left inverse would force " ++
      "2 = 3."
    status := .discharged "Lattice.Lift.RoundingBackend.roundingLossy" }

/-- The obligation that a zero measure means a passing point.

This is `Repair.atomic` in `Lattice.Core.Repair`. Its necessity is machine-checked by
`down_no_progress`: decrement on `ℤ` satisfies `absorbs` and `decreases` and never
converges, so `atomic` cannot be derived. -/
def repairAtomic : Slot :=
  { name := "core.repair.atomic"
    stmt := True
    note :=
      "Field `atomic` of `Lattice.Core.Repair`. Not derivable -- see `down_no_progress`. " ++
      "Discharged per repair operator by choosing a measure that vanishes on the target. -- " ++
      "**Abstraction added**: measured, all five operators in the library prove `atomic` by " ++
      "the SAME shape (`intro; exact (X_eq_zero_iff).mp h`) because all five measures are " ++
      "two-valued. `Lattice.Core.RepairAtomicity` makes that one lemma: " ++
      "`atomic_of_zero_iff`, `atomic_of_binary`, and the constructor `mkWithAtomic`, which " ++
      "builds a whole `Repair` from `(Sat, fix, mu, absorbs, decreases, mu = 0 <-> Sat)`. " ++
      "Verified by REBUILDING `samePointRepair` through `mkWithAtomic` with the same " ++
      "semantics. The slot stays open: `atomic` is still a field every operator must supply " ++
      "evidence for -- what changed is that supplying it is now one line, not five copies."
    status := .open_ }

/-- The obligation that an adopted representation for weights exists. **Discharged.**

`Lattice/Core/WeightNet.lean` gives `List (AffineLayer n)` an inhabitant of `WeightSemantics`, so every
theorem stated against that class now applies to networks -- and
`Lattice/Lib/Linear/NetPenalty.layer_penalty_exact` consumes it, which is the criterion the slot set
("an instance nobody uses has not been adopted").

Scope travels with the discharge: layers are `AffineLayer (Fin n)`, i.e. **fixed width**. Variable width
is `Lattice.Core.Chain`, indexed by its two widths, kept separately because it trades differently (`Nat`
indices give the width change; `Type` indices do not elaborate -- see `gov/BLOCKER-variable-width.md`).

Not settled by this: `core.semantics.external_bridge`, which is a toolchain question (TorchLean requires
Lean >= 4.26 while this project pins 4.14 so the legacy mathlib stays buildable). -/
def weightSemanticsChosen : Slot :=
  { name := "core.semantics.weight_exists"
    stmt := True
    note :=
      "Discharged by adoption, not by invention: `Lattice.Core.Net` already defined `AffineLayer` and " ++
      "`netAct`; `Lattice.Core.WeightNet.instWeightSemanticsNet` gives that stack a `WeightSemantics` " ++
      "instance, and `NetPenalty.layer_penalty_exact` consumes it. Scope: `AffineLayer (Fin n)`, " ++
      "fixed width; `Lattice.Core.Chain` covers variable width."
    status := .discharged "Lattice.Core.WeightNet.instWeightSemanticsNet" }

/-- The obligation that a *variable-width* layer stack exists. **Discharged.**

`Lattice.Core.VariableNet` supplies it: `MLayer m n` (a weight matrix `Fin m -> Fin n -> Real` plus a bias),
`MLayer.compose` whose middle width is forced by unification, `Chain` indexed by two `Nat` widths, and
`Chain.act_append` giving the composition law.

Scope is recorded with the discharge: widths are `Nat`-valued, so layers live on `Fin n`. An arbitrary
`Fintype` width goes through `Lattice.Core.Net`'s fixed-width stack, which is weaker but polymorphic. The two
exist because they trade polymorphism against variable width, and neither subsumes the other. -/
def variableWidthStack : Slot :=
  { name := "core.net.variable_width"
    stmt := True
    note :=
      "Discharged by `Lattice.Core.Chain.act_append` (with `MLayer.compose_act` for the layer law). " ++
      "Scope: `Nat`-valued widths only; arbitrary `Fintype` widths remain on the fixed-width stack " ++
      "in `Lattice/Core/Net.lean`."
    status := .discharged "Lattice.Core.Chain.act_append" }

/-- The obligation that the weight side is connected to an external tensor library.

Kept separate from `weightSemanticsChosen` because it is a *toolchain* debt, not a mathematical one:
it needs a dependency whose Lean version is above this project's, so it cannot be paid by writing
more Lean here. Recording it separately stops it from hiding inside the other slot. -/
def externalToolchainBridge : Slot :=
  { name := "core.semantics.external_bridge"
    stmt := True
    note :=
      "TorchLean supplies typed tensors, verified autograd and IEEE-754 semantics, but requires " ++
      "Lean >= 4.26 while this project pins 4.14 so that the legacy mathlib stays buildable. " ++
      "Adopting it is a toolchain decision, not a proof. -- " ++
      "**Scope sharpened**: this slot does NOT block `Ladder`'s weight type. " ++
      "`Lattice.Core` already supplies `AffineLayer`, `netAct` and `WeightSemantics`, and " ++
      "`Lattice.Lift.WeightLadder.weightLadder` builds a `Ladder` whose `W` is a real weight " ++
      "stack (`List (AffineLayer (Fin 1))`) with a genuine `l2l3_sound`. What remains open is " ++
      "narrower and specific: typed TENSORS, verified autograd and IEEE-754 semantics."
    status := .open_ }

/-- The convergence claim behind `Geo.Loop.loop_converges` is about **one step**, not
about an iterated process that could take many steps.

Measured: `samePointRepair`'s measure is `samePointMeasure a b pts = if pts a = pts b then 0
else 1`. A measure with codomain `{0, 1}` cannot decrease twice, so `Repair.progress`
guarantees arrival in at most one repair. That is a true statement about this operator,
but it does **not** express "the loop converges" in the sense of repeated iteration
ending at a fixed point.

What would be needed for the iterated sense: a measure with unbounded range plus
`decreases` strict at every non-satisfying point. `Repair` is stated over `Nat`, so the
structure permits it; this operator simply does not exhibit it.

Recorded as a slot rather than repaired, because repairing it is not a proof edit -- it
requires a different repair operator (one whose single step does not settle the predicate).
The statement that holds today is `loop_converges_in_one`, which says exactly one step. -/
def loopConvergenceIsSingleStep : Slot :=
  { name := "geo.loop.convergence_is_single_step"
    stmt := True
    note :=
      "`loop_converges` follows from `Repair.progress` with the measure " ++
      "`if satisfied then 0 else 1`; this bounds the loop at ONE step and does not express " ++
      "multi-step iteration. The sharper truth is stated separately as " ++
      "`Lattice.Geo.Loop.loop_converges_in_one`. Iterated convergence needs an operator " ++
      "whose step does not settle the predicate."
    status := .weakened }

/-- The **multi-step** repair operator, and the fact that its rate is tight.

`Lattice.Core.Multistep.countdown` has measure `μ k = k`, unbounded, and
`converges_within_is_tight` proves that no `n < μ k` steps suffice. This is the operator
`geo.loop.convergence_is_single_step` said was needed to express iterated convergence at all.

Scope, recorded with the discharge: this is a `Nat` countdown, not a geometric constraint.
The geometry layer's operators (`samePointRepair` et al.) remain one-step -- see
`REPAIR-CENSUS.md` class A -- so the *geometric* loop is unchanged. What is settled is that
multi-step convergence is expressible in this framework, with a tight rate. -/
def multistepRepairExists : Slot :=
  { name := "core.repair.multistep_exists"
    stmt := True
    note :=
      "Discharged by `Lattice.Core.Multistep.countdown` with `converges_within_is_tight`: " ++
      "measure `mu k = k` (unbounded), rate exactly `mu k`, and `no_uniform_bound` shows no " ++
      "smaller step count suffices. Scope: `Nat` countdown, NOT a geometric constraint; " ++
      "geometric operators remain one-step."
    status := .discharged "Lattice.Core.Multistep.converges_within_is_tight" }

/-- The full registry. -/

def fullRegistry : List Slot :=
  [ compileSingleItemSound
  , embedLocalMinimiserExact
  , extractRoundtrip
  , repairAtomic
  , weightSemanticsChosen
  , variableWidthStack
  , externalToolchainBridge
  , loopConvergenceIsSingleStep
  , multistepRepairExists ]

/-- The registry is structurally well formed: distinct, non-empty names.

Proved by decision procedure rather than by hand, so that adding a duplicate entry breaks
the build instead of silently inflating the count. -/
theorem fullRegistry_wellFormed : Slot.WellFormed fullRegistry := by
  constructor
  · intro s hs
    fin_cases hs <;> decide
  · intro s₁ h₁ s₂ h₂ hname
    fin_cases h₁ <;> fin_cases h₂ <;> first | rfl | exact absurd hname (by decide)

/-- **Four** obligations are currently owed: two open and two weakened. This number is the
project's debt, and it is read at check time rather than written into prose.

History, because the number moving is the point:

* it was six;
* `lift.compile.single_item_sound` was discharged by `CompilerScheme.scheme_covers_all`
  (branch `arch/compiler-type-params`), taking it to five;
* `lift.extract.roundtrip` was discharged by `RoundingBackend.roundingLossy`
  (branch `arch/lossy-backend`), taking it to four.

The `decide` below failed to compile at BOTH steps, which is exactly what it is for. -/
example : Slot.owedCount fullRegistry = 4 := by decide

end Lattice.Slots
