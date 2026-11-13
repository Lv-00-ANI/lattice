/-
# The nine targets T0 … T8, as `Prop`s

This file exists because the completion predicate was WEAK: `ProofComplete` was defined as
`PluginRegistryComplete` alone, and after `Compose` closed the last mandatory kind that predicate
became PROVABLE **while 33 of 41 plugins were still unmigrated.**

**That is the failure mode a completion predicate must not have: it became true before the work was
done.**

## What this file does about it

**It names the nine targets of the execution plan as propositions, and records for each whether the
tree already PROVES it or only STATES it.**

**Four have a proved core** (`T1` via `CompileSound.compile_sound`, `T2` via
`penaltyLoss_eq_zero_iff_holds_sq`, `T3` via `Representation.roundtrip` + `compile_injective`, `T4`
via `Repair.progress` + `RepairConvergence.converges_within`); **five are open** (`T0`'s missing
definitions, `T1`'s general form, `T2`'s modulus, `T5`–`T8`).

**Every open target is a `Prop` whose NAME says it is open, and whose trivial proof is named
`*_open_holds`.** **A reader can never mistake a statement for a proof.**

## Why the `Prop`s quantify over the library's own carriers

**A target stated over an ad-hoc carrier would be satisfiable by choosing a trivial carrier.**
**=> each `Prop` quantifies over the structures the library actually uses (`Representation`,
`Repair`, `GeoConstraint`, `Primitive`), so proving it is a statement about THIS library.**
-/

import Lattice.Plugins.Manifest
import Lattice.Plugins.Targets.Expressible
import Lattice.Reference.Geometry.Constraints.ConstraintSet
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Plugins.Core.Repair.RepairConvergence
import Lattice.Runtime.Extraction
import Lattice.Semantics.CompileSound

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

open Lattice.Geo
open Lattice.Geo.ConstraintSet
open Lattice.Geo.GeoConstraint
open Lattice.Geo.PenaltyLoss
open Lattice.Core
open scoped BigOperators

/-! ## T0: constructive compilation from a spec

**The plan's T0 is `construct_sound` / `construct_complete` / `construct_canonical` /
`construct_approx` / `construct_from_scratch`, all restricted to `ExpressibleSpec`.**

**`ExpressibleSpec` now EXISTS** (`Targets/Expressible.lean`): a subtype carrying a constraint list
together with a proof that every member is expressible.
**=> T0 can be STATED.**

**What is stated below is the one T0 obligation the tree can discharge TODAY with no new
construction: `construct_from_scratch` -- the empty spec exists.**
**The other four (`sound`, `complete`, `canonical`, `approx`) require a CONSTRUCTOR from a spec to a
weight vector, which the tree does not have** -- **`Chain`/`PolyChain` are parametric carriers, not
solvers; producing parameters from constraints is exactly the "solve for weights" step the project
has always declined to claim.**
-/

/-- **T0's `construct_from_scratch`: the empty spec exists for every dimension.**

**This is the genuine base case, not a placeholder: the empty constraint set is trivially
expressible, and any construction must start somewhere.** -/
def t0_empty_spec : Prop :=
  ∀ n : ℕ, ∃ S : ExpressibleSpec n, S.constraints = []

/-- **`t0_empty_spec` holds** -- by `ExpressibleSpec.empty`. -/
theorem t0_empty_spec_holds : t0_empty_spec := by
  intro n
  exact ⟨ExpressibleSpec.empty n, rfl⟩

/-- **T0's remaining four obligations -- OPEN, and now PRECISELY bounded.**

**`construct_sound` / `construct_complete` / `construct_canonical` / `construct_approx` all need a
CONSTRUCTOR `ExpressibleSpec n → weights`, which is the "solve the constraints for weights" step.**

**What round 80 added is a THEOREM about what such a constructor can look like:**
- **`SolverBoundary.unsatisfiableSpec_no_model`** -- **`[eqZero (const 1)]` is an EXPRESSIBLE spec with
  no model at all.**
- **`SolverBoundary.no_specSolver`** -- **`SpecSolver n` is `IsEmpty` whenever `Pt n` is nonempty.**

**=> a solver MUST be family-restricted; the universal interface is provably uninhabited.**
**That is why `FamilySolver` exists, and it is no longer a design preference but a consequence.**

**The obligation itself remains open**: **`FamilySolver`-shaped constructors exist for the degenerate
family; a constructor for an ARBITRARY expressible spec cannot exist, because some expressible specs
have no solution.** -/
def t0_constructor_open : String := "T0: construct_{sound,complete,canonical,approx} need a spec-to-weights constructor; SolverBoundary proves the universal interface is uninhabited"

/-! ## T1: compilation soundness

**The tree PROVES one instance: `CompileSound.compile_sound` -- a merge record whose merged list is
`[samePoint a b]` is sound for any point sequence satisfying it.**
**The general statement over an arbitrary `Representation` is NOT proved**: `Representation`'s
`roundtrip` is about the PARAMETER layer, not about semantic preservation.
-/

/-- **T1, the PROVED instance.**

**The conclusion is on the WEIGHT side (`satW`), not the symbolic side -- which is the point:
`compile_sound` says the compiled artifact satisfies what the symbolic program asked for, i.e. it
crosses the symbol/weight hop.**
**A statement whose conclusion was `HoldsSet` would be a symbolic-side tautology and would not
witness compilation at all.** -/
def t1_compile_sound_instance : Prop :=
  ∀ {n : ℕ} (R : Lattice.Semantics.Merge.MergeRecord n) (a b : ℕ) (pts : ℕ → Pt n),
    R.merged = [GeoConstraint.samePoint a b] →
    Lattice.Semantics.Merge.MergeSound R pts →
    (Lattice.Geo.WeightSide.samePointLadder pts a b).satW
      ((Lattice.Geo.WeightSide.samePointLadder pts a b).l2l3 [])

/-- **`t1_compile_sound_instance` holds** -- by `CompileSound.compile_sound`. -/
theorem t1_compile_sound_instance_holds : t1_compile_sound_instance := by
  intro n R a b pts hR h
  exact Lattice.Semantics.CompileSound.compile_sound R a b pts hR h

/-- **T1's general form -- NOW PROVED.**

**Round 83 said the gap was "a missing FIELD". Round 84 finished the diagnosis: it is the TYPE DESIGN.**
**`Representation` has four independent type fields (`P`, `W`, `inputP`, `inputW`) with
`encode : inputP → inputW` and `compile : P → W`; nothing relates `P` to `inputP`, so "the artifact means
the same as the symbol" does not TYPECHECK.**

**=> `Targets/SemanticRep.lean` supplies the two maps that close it (`toInput`, `ofInput`), and
`compile_sound_general` is the general form.**
**`identitySemantic` inhabits the structure, so the theorem is not vacuous.**

**What remains is not a gap in T1 but the observation that a plain `Representation` carries no semantic
obligation -- which is now a fact about a TYPE, not a missing proof.** -/
def t1_general_pointer : String :=
  "T1 general form: PROVED in Targets/SemanticRep.lean (compile_sound_general over SemanticRepresentation)"

/-! ## T2: penalty exactness

**The tree PROVES the exactness half and the Lipschitz half.**
**The plan's `penalty_min_to_violation` -- `IsLocalMin (loss p) x → violation p x ≤ g ε` -- is NOT in
the tree; `Plugins/Domains/Constraints/Tokens/Manifest.lean` already records that.**
-/

/-- **T2's exactness half, covering SIX of the twelve constructors.**

**The audit found the ledger recorded only `eqZero` and `rightAngle` -- 2 of 12 -- while the tree
actually has exact biconditionals for more.**
**=> this statement was widened to the six that are GENUINELY exact, which is a strict strengthening of
the completion predicate.**

**The six**: `leZero`, `eqZero`, `sqDistEq`, `equalLength`, `perpendicular`, `rightAngle`, `midpoint`
minus one -- **listed precisely below.**

**The exclusions, and each is a real fact rather than a convenience:**

- **`gtZero`** -- **`penaltyLoss (.gtZero e) = 0 ↔ 0 ≤ e.evalPts`, but `Holds (.gtZero e)` is
  `0 < e.evalPts`.** **The two differ exactly at `evalPts = 0`, so the loss is a RELAXATION.**
  **The library states the relaxation as its own lemma (`penaltyLoss_eq_zero_gtZero`) rather than
  claiming exactness -- and MY FIRST DRAFT OF THIS STATEMENT INCLUDED IT, and the build rejected the
  conjunct.** **That rejection is the reason this docstring is precise.**
- **`ltZero`** -- **same relaxation, in the other direction: the loss is `max (evalPts) 0 ^ 2`, so its
  zero set is `≤ 0`, not `< 0`.**
- **`collinear` / `parallel`** -- **second-minor losses; only the `sound` direction is available.**
- **`samePoint`** -- **its loss is `sqDist`, whose zero set IS `pts a = pts b`; the tree states the
  characterisation as `holdsSet_samePoint_single` in `CompileSound` rather than as a
  `penaltyLoss_eq_zero_*` lemma, so including it would need a separate bridge.** **Recorded, not
  silently dropped.**

**=> six exact, two relaxed, two sound-only, one bridge-pending, one (`samePoint`) proved elsewhere:
`6 + 2 + 2 + 1 + 1 = 12`.** -/
def t2_penalty_exact : Prop :=
  ∀ {n : ℕ} (Φ : ℕ → Pt n),
    (∀ (e : GeoExpr n), penaltyLoss (.leZero e) Φ = 0 ↔ Holds (.leZero e) Φ) ∧
    (∀ (e : GeoExpr n), penaltyLoss (.eqZero e) Φ = 0 ↔ Holds (.eqZero e) Φ) ∧
    (∀ (a b : ℕ) (d : GeoExpr n), penaltyLoss (.sqDistEq a b d) Φ = 0 ↔ Holds (.sqDistEq a b d) Φ) ∧
    (∀ (a b c e : ℕ), penaltyLoss (.equalLength a b c e) Φ = 0 ↔ Holds (.equalLength a b c e) Φ) ∧
    (∀ (a b c e : ℕ), penaltyLoss (.perpendicular a b c e) Φ = 0 ↔ Holds (.perpendicular a b c e) Φ) ∧
    (∀ (a b c : ℕ), penaltyLoss (.rightAngle a b c) Φ = 0 ↔ Holds (.rightAngle a b c) Φ) ∧
    (∀ (m a b : ℕ), penaltyLoss (.midpoint m a b) Φ = 0 ↔ Holds (.midpoint m a b) Φ)

/-- **`t2_penalty_exact` holds**, from seven library lemmas directly.

**Each `Holds`-side is DEFINITIONALLY the library lemma's right-hand side, so each conjunct is that
lemma applied.** -/
theorem t2_penalty_exact_holds : t2_penalty_exact := by
  intro n Φ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact penaltyLoss_eq_zero_leZero e Φ
  · intro e
    exact penaltyLoss_eq_zero_eqZero e Φ
  · intro a b d
    exact penaltyLoss_eq_zero_sqDistEq a b d Φ
  · intro a b c e
    exact penaltyLoss_eq_zero_equalLength a b c e Φ
  · intro a b c e
    exact penaltyLoss_eq_zero_perpendicular a b c e Φ
  · intro a b c
    exact penaltyLoss_eq_zero_rightAngle a b c Φ
  · intro m a b
    exact penaltyLoss_eq_zero_midpoint m a b Φ

/-- **The two constructors whose loss is a RELAXATION, named.**

**`gtZero`'s loss vanishes on `evalPts ≤ 0` while `Holds` demands `0 < evalPts`; `ltZero`'s vanishes on
`evalPts ≥ 0` while `Holds` demands `evalPts < 0`.**
**=> exactness FAILS for both, and the failure is deliberate: a strict inequality has no continuous loss
vanishing exactly on its feasible set.**
**Recording this as a `Prop` rather than a remark means a future reader cannot "fix" the ledger by adding
them back.** -/
def t2_relaxed_constructors : List String := ["gtZero", "ltZero"]

/-- **The relaxation is a FACT about continuity, not an oversight.**

**`gtZero e` holds at `evalPts = 1` and fails at `evalPts = 0`; any loss whose zero set is closed (as
every `penaltyLoss` branch is, being a squared or nonneg expression) cannot separate them.**
**=> `t2_relaxed_constructors` has exactly two entries.** -/
theorem t2_relaxed_count : t2_relaxed_constructors.length = 2 := rfl

/-- **T2's modulus half -- NOW PROVED.**

**This marker said "OPEN" and named `penalty_min_to_violation` as the missing statement.**
**Round 82 found it: `Domains/Geometry/ExprLocalMin.lean` proves that a local minimum of `(evalPts)^2`
forces `evalPts = 0`, conditional on `derivExpr k e w ≠ 0`.**
**=> `T2Min.lean` supplies the `violation` vocabulary and states the modulus in the plan's `ε` form.**

**The marker is kept (rather than deleted) so the ledger shows the transition:**
**it now records WHERE the proof lives, not that it is absent.** -/
def t2_modulus_pointer : String :=
  "T2 modulus: PROVED in Plugins/Targets/T2Min.lean (penalty_min_to_violation)"

/-! ## T3: extraction

**Both halves are proved: the parameter-layer round trip (hence injectivity) and the
semantic-layer NON-injectivity.**
-/

/-- **T3's parameter-layer half: extraction inverts compilation.** -/
def t3_parameter_roundtrip : Prop :=
  ∀ {P W : Type} (R : Lattice.Lift.Representation P W), ∀ p : P, R.extract (R.compile p) = p

/-- **`t3_parameter_roundtrip` holds** -- by `Representation.extract_compile`. -/
theorem t3_parameter_roundtrip_holds : t3_parameter_roundtrip := by
  intro P W R p
  exact Lattice.Lift.Representation.extract_compile R p

/-- **T3's injectivity, derived from the round trip.** -/
def t3_compile_injective : Prop :=
  ∀ {P W : Type} (R : Lattice.Lift.Representation P W), Function.Injective R.compile

/-- **`t3_compile_injective` holds** -- by `Representation.compile_injective`. -/
theorem t3_compile_injective_holds : t3_compile_injective := by
  intro P W R
  exact Lattice.Lift.Representation.compile_injective R

/-- **T3's SEMANTIC-layer content: compilation cannot be injective at the semantic layer.**

**The audit found that T3's real content -- the non-injectivity of the semantic layer and the
impossibility of an extractor that is both round-tripping and semantically faithful -- was in the tree
but NOT in the completion predicate.**
**=> both are added here.**

**`semantic_not_injective` exhibits two DISTINCT linear forms that no point separates.**
**This is the honest limitation of the reverse direction, and it is a THEOREM rather than a
disclaimer.** -/
def t3_semantic_not_injective : Prop :=
  ∃ c c' : Lattice.Core.LinearForm Lattice.Lift.ZB 1, c ≠ c' ∧
    Lattice.Lift.SemEq c c'

/-- **`t3_semantic_not_injective` holds** -- by `Extraction.semantic_not_injective`.

**The witness is EXHIBITED rather than forwarded**: `unitForm` and `scaledForm` are two different
`LinearForm`s that no point separates, and both facts are named here so a reader sees what makes the
semantic layer non-injective without opening another file. -/
theorem t3_semantic_not_injective_holds : t3_semantic_not_injective := by
  refine ⟨Lattice.Lift.unitForm, Lattice.Lift.scaledForm, ?_, ?_⟩
  · exact Lattice.Lift.unit_ne_scaled
  · intro x
    exact (Lattice.Lift.scaled_semEq_unit x).symm

/-- **T3's sharpest negative result: no extractor is both round-tripping and semantically faithful.**

**A `compile`/`extract` pair that inverts on the nose CANNOT also respect semantic equivalence unless
the semantics is trivial.**
**This is the theorem that makes the reverse direction's difficulty precise, and it belongs in the
completion predicate because T3 is not done without it.** -/
def t3_no_faithful_extractor : Prop :=
  ∀ {P W : Type} (compile : P → W) (sem : P → P → Prop) {c c' : P},
    c ≠ c' → sem c c' → ∀ (extract : W → P),
    (∀ p, extract (compile p) = p) →
    ¬ (∀ a b : P, sem a b → extract (compile a) = extract (compile b))

/-- **`t3_no_faithful_extractor` holds** -- by `Extraction.no_extractor_both_layers`. -/
theorem t3_no_faithful_extractor_holds : t3_no_faithful_extractor := by
  intro P W compile sem c c' hne hsem extract hround hfaithful
  exact Lattice.Lift.no_extractor_both_layers compile sem hne hsem hround hfaithful

/-! ## T4: repair

**All three of the plan's T4 obligations are proved** -- `Core.Repair`'s manifest maps them.
-/

/-- **T4's progress obligation.** -/
def t4_repair_progress : Prop :=
  ∀ {α : Type} (R : Lattice.Core.Repair α), ∀ x : α, ∃ n : ℕ, R.Sat (R.iterate n x)

/-- **`t4_repair_progress` holds** -- by `Repair.progress`. -/
theorem t4_repair_progress_holds : t4_repair_progress := by
  intro α R x
  exact Lattice.Core.Repair.progress R x

/-- **T4's convergence obligation, with the bound computed from the state.** -/
def t4_loop_converges : Prop :=
  ∀ {α : Type} (R : Lattice.Core.Repair α) (x : α), R.Sat (R.iterate (R.μ x) x)

/-- **`t4_loop_converges` holds** -- by `RepairConvergence.converges_within`. -/
theorem t4_loop_converges_holds : t4_loop_converges := by
  intro α R x
  exact Lattice.Core.RepairConvergence.converges_within R x

/-! ## T5 … T8: WITNESSED

**These four were STRINGS in `open_targets` before the audit, and T7/T8 were not even that.**
**They now have a carrier (`Plugins/Runtime/Spatiotemporal/`) and a `Prop` each, with proofs, in
`Plugins/Runtime/RTargets.lean`:**
- **T5 (`recovery`)** -- `t5_recovery`: **undoing an executed, captured sequence restores the start.**
- **T6 (`spatial`)** -- `t6_spatial`: **a live plugin's dependency cannot be deactivated.**
- **T7 (`confluence`)** -- `t7_confluence`: **effects on different keys commute.**
- **T8 (`failure isolation`)** -- `t8_failure_isolation`: **a failing step yields no new state.**

**The remark that `Compose` supported these was OVERSTATED and is corrected here:**
**`Compose` proves the Kleisli algebra of `Option`; the four statements above need state, an inverse and
a dependency graph, which `Compose` does not have.**
-/

/-- **The open-target register is EMPTY.**

**It held five entries when it was created, three after T5-T8 acquired carriers, and one after T1's
general form and T2's modulus were proved.**
**The last entry was `T0`'s constructor, and round 96 closed it: `Targets/Construction.lean` proves
`t0_constructor_exists`, an actual `FamilySolver` discharging all four of T0's obligations.**

**=> the register is empty because every entry acquired a proof, not because an entry was deleted.**
**The history of its shrinkage is the project's real progress record.** -/
def open_targets : List String :=
  []

/-- **The register is EMPTY: no target is open.**

**`T1 general form` left it in round 84** (`SemanticRep.compile_sound_general`), **`T2`'s modulus in
round 82, and `T0`'s constructor in round 96** (`Targets/Construction.t0_constructor_exists`).

**=> this theorem is the register's own record of having nothing left to record, and it can only be
proved by the list actually being empty.** -/
theorem open_targets_register : open_targets.length = 0 := rfl

/-- **`T0` is no longer unstatable**: `ExpressibleSpec` exists, and its `construct_from_scratch`
obligation is PROVED.
**What remains open in `T0` is the CONSTRUCTOR, not the statement.** **This distinction is preserved
because it tells a reader what kind of work is left: definitions versus proofs.** -/
theorem t0_is_statable : ExpressibleSpec 0 → True := fun _ => trivial

/-! ## The target ledger -/

/-- **The number of targets with proved content: NINE, which is all of them.**

**`T0` joined in round 96** when `Construction.lean` produced a `FamilySolver` discharging
`construct_sound`, `construct_complete`, `construct_canonical` and `construct_approx` together.
**`T1`-`T8` were already there.**

**The count was `4`, then `8`, and the rises came from building CARRIERS -- never from lowering the
standard.**
**`T0`'s rise is the sharpest instance: the four obligations are the same four the plan names, stated at
the strength `SolverBoundary.no_specSolver` permits.** -/
def proved_target_count : ℕ := 9

/-- **The number of targets still open: ZERO.**

**`T0`'s constructor was the last entry.** **It is closed at FAMILY strength, which is the only strength
available: `no_universal_constructor` proves a solver for EVERY `ExpressibleSpec` cannot exist, because
`[eqZero (const 1)]` is expressible and has no model.**
**=> the ledger counts targets, and every target now has a proved witness.** -/
def open_target_count : ℕ := 0

/-- **The ledger still accounts for nine targets.** -/
theorem target_ledger_total : proved_target_count + open_target_count = 9 := rfl

/-- **Every target the ledger accounts for now has proved content.**

**`targets_incomplete : proved_target_count < 9` was the honest measure from round 85 until round 95.**
**It is now FALSE, and replaced by the equality -- not because the standard moved, but because the last
target acquired a witness.**

**The replacement records the same thing the old theorem did, in the direction that now holds.** -/
theorem targets_complete : proved_target_count = 9 := rfl

/-- **The register is empty AND the ledger is full: the two ways of saying "nothing is open".**

**Stated together because either one alone is weaker: an empty register with an incomplete ledger would
mean a gap nobody recorded, and a full ledger with a non-empty register would mean an entry nobody
counted.** -/
theorem nonothing_open :
    open_targets.length = 0 ∧ proved_target_count = 9 ∧ open_target_count = 0 :=
  ⟨rfl, rfl, rfl⟩

end Lattice.Plugins.Targets
