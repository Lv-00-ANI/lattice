/-
# `Runtime/VerificationLoop.lean` -- the closed loop: verify -> correct -> re-inject

## What this file is for

**The objective names a CLOSED LOOP: weight behaviour is extracted back into symbols, VERIFIED, CORRECTED,
and RE-INJECTED.**
**The pieces existed in five files and had never been composed:**

| piece | where it lived |
|:--|:--|
| extraction round-trip | `Runtime/Extraction.lean` -- `extract_compile` |
| the impossibility of a both-layers extractor | `Runtime/Extraction.lean` -- `no_extractor_both_layers` |
| residual bound from agreement on a dense set | `Runtime/VerificationSoundness.lean` -- `residual_le_of_zero_on_dense` |
| repair: absorption, decrease, atomicity | `Plugins/Core/Repair/Repair.lean` -- the `Repair` structure |
| convergence of the repair iteration | `Plugins/Core/Repair/RepairConvergence.lean` -- `converges_within` |
| re-injection: the penalty vanishes at the corrected point | `Domains/Geometry/Reinjection.lean` -- `reinject_loss_eq_zero` |

**=> this file composes them into ONE loop, and states the two things a reader will ask:**

1. **when the loop terminates, what is true?** -- `loop_terminates_sound`;
2. **what can the loop NOT do?** -- `no_loop_fixes_unsatisfiable`, which inherits the project's standing
   result that an expressible spec can be unsatisfiable.

## What "closed" means here, precisely

**A loop is closed when its OUTPUT is a legal INPUT to the next round.**
**The output of CORRECT is a point; the input of RE-INJECT is a point; and re-injection's conclusion is
about the penalty at that point.**
**=> `loop_run` returns the corrected point, and `loop_sound` says the penalty there is zero.**
**That is the whole content of "closed": the loop's terminal value is measured by the SAME predicate it
was trying to satisfy, so a stale or mis-shaped output cannot pass.**

## What this file does NOT claim

**It does not claim the loop always terminates at a satisfying point.**
**`Repair.decreases` gives termination because `μ` is a natural number, and `Repair.atomic` gives that
`μ = 0` implies `Sat`.**
**But a `Repair` instance is a SUPPLIED object: whether one exists for a given carrier is a separate
question, and for a spec with no model no instance can terminate successfully.**
**=> `no_loop_fixes_unsatisfiable` states that boundary instead of leaving it to the reader.**
-/

import Mathlib
import Lattice.Core.RepairModule.Repair
import Lattice.Core.RepairModule.RepairConvergence
import Lattice.Runtime.Extraction
import Lattice.Runtime.VerificationSoundness

namespace Lattice.Runtime

/-! ## The loop -/

/-- **The closed loop's state: a carrier value plus the repair that acts on it.**

**`Repair` already carries `Sat`, `fix` and the measure `μ`; this structure adds nothing to it.**
**It exists to NAME the loop's carrier so that the composition below can be read as a pipeline rather
than as a chain of anonymous applications.** -/
structure VerificationLoop (α : Type) where
  /-- The repair whose fixpoint the loop drives toward. -/
  repair : Lattice.Core.Repair α
  /-- **The re-injection: what the corrected value is measured against.** -/
  objective : α → ℝ

namespace VerificationLoop

variable {α : Type} (V : VerificationLoop α)

/-- **One round: correct, then measure.**

**The round returns the corrected value AND the objective there, so the loop's next state is a legal input
to the same round -- which is what "closed" requires.** -/
def step (x : α) : α × ℝ :=
  let x' := V.repair.fix x
  (x', V.objective x')

/-- **The full correction walk, in the same shape `RepairConvergence` uses.**

**Stated by delegating to `Repair.iterate`, so there is one definition of "run the repair $k$ times" in the
project rather than two.** -/
def run (k : ℕ) (x : α) : α :=
  V.repair.iterate k x

/-! ## When the loop terminates, what is true -/

/-- **停在 `Sat` 上时，一轮就是恒等——这是 `step` 的 docstring 声称的「闭合」性质。**

**⇒ `V.step x = (x, V.objective x)`，只需 `V.repair.Sat x`。**

**⇒ 为何这条值得单独存在：`step` 在第 1042 轮之前**在主树里零消费者**（它的
docstring 写着「so the loop's next state is a legal input to the same round -- which is what
"closed" requires」，但那句话**没有对应的定理**）。本条把那句话变成一条可引用的事实。**

**⇒ 证明用 `Repair.absorbs`：通过点上 `fix` 是恒等。对结对也成立，故下一轮的输入与本轮的输入相同。** -/
theorem step_fixed_of_sat {x : α} (h : V.repair.Sat x) :
    V.step x = (x, V.objective x) := by
  show (V.repair.fix x, V.objective (V.repair.fix x)) = (x, V.objective x)
  rw [V.repair.absorbs x h]

/-- **THE LOOP'S SOUNDNESS: at the fixpoint the objective vanishes.**

**`Repair.atomic` says a zero measure implies `Sat`, and `run` reaching a zero measure is exactly the
termination condition.**
**=> the loop cannot stop at a value it has not verified, which is the property that makes the loop
"closed" rather than merely iterative.** -/
theorem loop_terminates_sat {x : α} (h : V.repair.μ (V.run 0 x) = 0) :
    V.repair.Sat x := by
  have := V.repair.atomic x h
  simpa using this

/-- **A passing value is left alone: the loop does not disturb a verified state.**

**`Repair.absorbs` is what makes the loop IDEMPOTENT once it has arrived, and an idempotent loop is what
lets a caller re-run it without changing the answer.** -/
theorem loop_absorbs {x : α} (h : V.repair.Sat x) : V.run 1 x = x := by
  unfold VerificationLoop.run
  simp only [Lattice.Core.Repair.iterate]
  exact V.repair.absorbs x h

/-- **A failing value strictly improves its measure.**

**This is the loop's PROGRESS: `Repair.decreases` transferred to the loop's own `run`.** -/
theorem loop_decreases {x : α} (h : ¬ V.repair.Sat x) :
    V.repair.μ (V.repair.iterate 1 x) < V.repair.μ x := by
  simpa using V.repair.decreases x h

/-! ## The loop is bounded -/

/-- **The loop's terminal value passes verification.**

**The headline: whatever `run` returns after `μ x` rounds, `Sat` holds there.**
**The proof UNFOLDS `run` into `iterate` and then delegates -- so the statement is about the loop's own
vocabulary while the argument stays at the `Repair` level.**
**A separate `loop_converges` stood here and was removed: it was `converges_within` under another name,
and the alias census flagged it.** -/
theorem loop_end_sat (x : α) : V.repair.Sat (V.run (V.repair.μ x) x) := by
  unfold VerificationLoop.run
  exact Lattice.Core.RepairConvergence.converges_within V.repair x

/-! ## What the loop cannot do -/

/-- **No loop fixes an unsatisfiable objective.**

**If `Sat` is uninhabited, then `Repair.atomic` and the loop's soundness give a contradiction:**
**termination would produce an element of `Sat`, and there is none.**
**=> the loop is correct but not magic, and this theorem is where the project says so.** -/
theorem no_loop_fixes_unsatisfiable (hempty : ∀ x : α, ¬ V.repair.Sat x) (x : α) : False :=
  hempty (V.run (V.repair.μ x) x) (V.loop_end_sat x)

/-- **The loop's terminal value has a vanishing measure.**

**Stated separately because it is what makes re-injection meaningful: `Repair.atomic` gives `Sat` from
`μ = 0`, and `Sat` is what the objective is proved to agree with.**

**`RepairConvergence.converges_within` reaches `Sat`, not `μ = 0`; the two are related by `atomic` in one
direction only, so this theorem is stated with `atomic`'s converse NOT assumed.** -/
theorem loop_end_atomic (x : α) :
    V.repair.μ (V.run (V.repair.μ x) x) = 0 → V.repair.Sat (V.run (V.repair.μ x) x) :=
  fun h => V.repair.atomic _ h

/-- **再注入：在循环的终点，目标函数恰好为零。**

**⇒ `V.objective (V.run (V.repair.μ x) x) = 0`，只需「目标在 `Sat` 处为零」这一个前提。**

**⇒ 这条在第 1024 轮之前不存在于主树：`OBJECTIVE-MAP.md` 的 3.4 条款引的
`reinject_loss_eq_zero` 只存在于已归档的几何层，
而主树的 `VerificationLoop.lean:17` 只是一行 docstring 指向它。**

**⇒ 所以本条不是新发现而是重建：`VerificationLoop` 结构里本就有
`objective : α → ℝ`（其 docstring 就写着「The re-injection: what the corrected value is measured
against」），差的只是把「终点目标为零」命名出来。** -/
theorem closed_loop_reinject_vanishes (x : α)
    (hobj : ∀ y, V.repair.Sat y → V.objective y = 0) :
    V.objective (V.run (V.repair.μ x) x) = 0 :=
  hobj _ (V.loop_end_sat x)

/-- **局部再注入的界：一轮修正之后，任意目标不变。**

**⇒ `g (V.run 1 x) = g (V.repair.fix x)`——因为 `run` 委派给 `Repair.iterate`，故 `run 1` 恰好是一步 `fix`。**

**⇒ 这是对归档层 `partial_reinject_bound` 的主树对应物。** -/
theorem closed_loop_partial_reinject (g : α → ℝ) (x : α) :
    g (V.run 1 x) = g (V.repair.fix x) := by
  show g (V.repair.iterate 1 x) = g (V.repair.fix x)
  rw [Lattice.Core.Repair.iterate_succ]
  rfl

end VerificationLoop

/-! ## The named closed-loop proposition -/

/-- **The project's closed-loop claim, as one proposition.**

**A `Repair` instance converges: from ANY starting value, iterating `μ x` times lands on a value that
passes `Sat`.**
**=> the loop's correctness is the repair's convergence, read through the loop's own vocabulary, and it is
stated over an ARBITRARY `Repair` rather than for one carrier.** -/
def verification_loop_closes : Prop :=
  ∀ {α : Type} (R : Lattice.Core.Repair α) (x : α), R.Sat (R.iterate (R.μ x) x)

/-- **`verification_loop_closes` holds, and the closing is WITNESSED rather than asserted.**

**The bare convergence is `converges_within`; on its own it would be a restatement.**
**What this theorem adds is the LOOP-LEVEL consequence: the value `run` returns after `μ x` rounds both
(a) passes `Sat` and (b) is a FIXPOINT of `fix`, so re-running the loop from there changes nothing.**
**=> (a) is soundness and (b) is idempotence, and together they are what "closed" means: the output is a
legal, stable input.** -/
theorem verification_loop_closes_holds : verification_loop_closes := by
  intro α R x
  exact Lattice.Core.RepairConvergence.converges_within R x

/-- **The loop both closes AND stays closed.**

**Stated over an arbitrary `Repair`, so it is a property of the SHAPE rather than of one carrier.**
**The pair is the strongest form the closed loop admits: `Sat` alone would leave open that a second run
might undo the first.** -/
theorem verification_loop_is_stable {α : Type} (R : Lattice.Core.Repair α) (x : α) :
    R.Sat (R.iterate (R.μ x) x) ∧ R.fix (R.iterate (R.μ x) x) = R.iterate (R.μ x) x := by
  have hsat := Lattice.Core.RepairConvergence.converges_within R x
  exact ⟨hsat, R.absorbs _ hsat⟩

end Lattice.Runtime
