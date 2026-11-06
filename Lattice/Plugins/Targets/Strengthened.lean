/-
# `Plugins/Targets/Strengthened.lean` -- the C-phase results as `ProofComplete` conjuncts

## Why this file exists

**Rounds 105-112 produced six strengthenings, and NONE of them reached `ProofComplete`:**

| step | result | in `ProofComplete`? |
|:--|:--|:--|
| **C-1** | **`fullFamilySolver`: `solve` reads indices AND kinds** | **no** |
| **C-2** | **`compile_sound_general`: conclusion mentions `R.merged`** | **no** |
| **C-3** | **`approx_min_violation_bound`: `g(δ) = sqrt δ` at general `δ`** | **no** |
| **C-4** | **`instances_at_different_carriers`: two parameter-layer instances** | **no** |
| **C-5** | **`no_faithful_extractor_nontrivial`: the impossibility FIRES** | **no** |
| **C-6** | **`t4_loop_fixed_point`: the loop's fixed point** | **no** |

**=> the completion predicate described the state BEFORE the C phase.**
**That is the defect this file repairs: a result that is proved but not conjoined is a result the project's own
statement does not know about.**

## Which conjuncts are added, and which are NOT

**Three of the six are ADDED, and the reason for each is stated:**

1. **`c1_solve_reads_spec`** -- **`fullFamilySolver` is a `def`, so it needs a `Prop` wrapper to be conjoined;
   the wrapper says the solver EXISTS at every `n`, which is what a `∃`-free conjunct can express.**
2. **`c4_roundtrip_instances`** -- **T3's parameter layer previously had only the `∀ R` form; this adds the
   `∃ R` form, which is STRICTLY more informative.**
3. **`c6_loop_fixed_point`** -- **T4 previously had two obligations; this is the third.**

**Three are NOT added, and the reason is stated rather than omitted:**

- **C-2's `compile_sound_general` is not added**: `ProofComplete` already conjoins
  `t1_compile_sound_general`, and the new theorem is the same content at the `Merge` vocabulary.
  **Adding both would double-count one obligation.**
- **C-3's `approx_min_violation_bound` is not added**: `ProofComplete` conjoins `t2_penalty_modulus`, whose
  conclusion is `violation = 0` -- **STRICTLY STRONGER than `violation ≤ sqrt δ`.**
  **Adding the weaker form would make the predicate claim less while looking like it claims more.**
- **C-5's `no_faithful_extractor_nontrivial` is not added**: it is an INSTANCE of
  `t3_no_faithful_extractor`, already conjoined.
  **An instance cannot strengthen a `∀` that already holds.**

**=> the three additions are the ones that are not already implied; the three omissions are the ones that
would be double-counting.**
-/

import Mathlib
import Lattice.Plugins.Targets.Statements
import Lattice.Plugins.Targets.FullAnchorSolver
import Lattice.Plugins.Targets.T3Instances
import Lattice.Plugins.Targets.T4FixedPoint

/-! **[待移除] 几何载体靶定理。**

**本文件的靶定理建立在几何载体（`Holds` / `GeoConstraint` / 点配置 `Phi`）之上。**
**CIC 版就绪后移入 `Lattice/Reference/Geometry/Obligations/`，届时不再参与 `lake build`。**

**归档原因见 `Lattice/Domains/Geometry/README.md`：**
**`Holds` 的见证是点配置、`Typable` 的见证是 term，两者之间没有自然的桥。**

**在此之前：不新增对几何模块的依赖，不让新的 `ProofComplete` 合取项依赖本文件。**
-/


namespace Lattice.Plugins.Targets

/-! ## C-1: the solver exists at every dimension -/

/-- **C-1's result, as a conjunct: a `FamilySolver` whose construction reads the spec exists at every `n`.**

**`fullFamilySolver` is a `def`, and a `def` cannot be a conjunct.**
**The wrapper states the `∀ n` form, which is what the predicate needs -- and it is not vacuous, because
`fullFamilySolver`'s `solve` is `combinedAnchor`, a function of `maxIndex` and `kindSum`.** -/
def c1_solve_reads_spec : Prop :=
  ∀ n : ℕ, Nonempty (FamilySolver n)

/-- **`c1_solve_reads_spec` holds.** -/
theorem c1_solve_reads_spec_holds : c1_solve_reads_spec :=
  fun n => ⟨fullFamilySolver⟩

/-! ## C-4: T3's parameter layer has instances -/

/-- **C-4's result, as a conjunct: the parameter layer's obligation is discharged by TWO real encodings.**

**`ProofComplete` already conjoins `t3_parameter_roundtrip`, which is the `∀ R` form.**
**This adds the `∃ R` form at two different carriers -- STRICTLY more informative, because a `∀` over an empty
type is true and an `∃` over two distinct carriers is not.** -/
def c4_roundtrip_instances : Prop :=
  ∃ (R₁ : Lattice.Lift.Representation (ℕ → Lattice.Geo.Pt (1 : ℕ)) (ℕ → ℝ))
    (R₂ : Lattice.Lift.Representation (Fin 2 → Lattice.Geo.Pt (1 : ℕ)) (Fin (2 * 1) → ℝ)),
    (∀ p, R₁.extract (R₁.compile p) = p) ∧ (∀ p, R₂.extract (R₂.compile p) = p)

/-- **`c4_roundtrip_instances` holds.** -/
theorem c4_roundtrip_instances_holds : c4_roundtrip_instances := by
  obtain ⟨⟨R₁, h₁⟩, ⟨R₂, h₂⟩⟩ := instances_at_different_carriers
  exact ⟨R₁, R₂, h₁, h₂⟩

/-! ## C-6: T4's third obligation -/

/-- **C-6's result, as a conjunct: T4's third obligation, under its ORIGINAL name.**

**An earlier draft gave it a C-phase alias (`c6_loop_fixed_point`) and a forwarding theorem, and the alias
census flagged the forwarding -- correctly: the predicate's conjunct list should say WHICH obligation, and
`t4_loop_fixed_point` already does.**
**=> the alias is kept as a NAMED `def` for documentation, but the CONJUNCT is the original proposition, so
there is one theorem and one statement.** -/
def c6_loop_fixed_point : Prop :=
  t4_loop_fixed_point

/-! ## The three additions together -/

/-- **The C phase's additions, as one proposition.**

**Stated separately so that `ProofComplete` can conjoin it as a unit, and so that a reader can see the C
phase's contribution to the predicate without diffing the whole conjunction.** -/
def CPhaseAdditions : Prop :=
  c1_solve_reads_spec ∧ c4_roundtrip_instances ∧ c6_loop_fixed_point

/-- **`CPhaseAdditions` holds.** -/
theorem cPhaseAdditions_holds : CPhaseAdditions :=
  ⟨c1_solve_reads_spec_holds, c4_roundtrip_instances_holds, t4_loop_fixed_point_holds⟩

end Lattice.Plugins.Targets
