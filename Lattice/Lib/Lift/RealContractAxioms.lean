/-
LATTICE: axiom-dependency assertions for the doc/03 implementation contract.

WHY THIS FILE EXISTS
--------------------
`doc/03-实现契约.md` rests on the principle "Lean proofs are the verification
basis; the C implementation is the executable edition of the proof". That claim
is only worth something if the named theorems (a) exist and (b) are proved
without extra axioms. R6 (`doc/research/R6-formalization-precedents.md` §2)
recommends turning the project's "0 axiom" *declaration* into a *reproducible
machine check*, aligned with the mathlib official criterion
<https://leanprover-community.github.io/did_you_prove_it.html>:

    #print axioms my_proof   must return a subset of
    [propext, Classical.choice, Quot.sound]

This file is that check. It emits `#print axioms` for every main-line
`*Correctness`-family theorem backing the contract's 19 invariants.

IMPORTANT PROPERTIES OF THIS FILE
---------------------------------
1. `#print axioms` writes an **info** message. It produces no error, so this
   file still builds cleanly; and being info-only it does NOT alter the
   compiled artifact, so adding it cannot invalidate other modules' oleans.
   The assertions are read by `scripts/check-axioms.ps1`, which parses the
   output and fails if any theorem depends on anything outside the three
   standard axioms.
2. This file is **read-only with respect to the proofs**. It imports the
   contract modules and only *queries* them; it defines no new mathematics.
3. Names are fully qualified as `Lattice.<name>` because every contract module
   (except `ConstraintEmbeddingSoundness`) is inside `namespace Lattice`, and
   this query file deliberately sits at the root namespace to avoid ambiguity.
4. Every symbol below was verified to exist, with the exact printed form, by
   `scripts/audit-contract.ps1` and `scripts/enumerate-contract-decls.ps1`.

NAMING-COLLISION CONSTRAINT (why this is split into TWO files)
-------------------------------------------------------------
`scripts/verify.ps1` §4b enforces `scripts/collision-pairs.txt`: certain module
pairs declare the SAME top-level names inside `namespace Lattice` and therefore
can never be imported together. For the contract modules the collisions are:

    ConvertLinear + VerifyLoopConvergence   -> EvenSat
    ConvertLinear + ComboN                  -> EvenSat, EvenOut
    VerifyLoopConvergence + ComboN          -> EvenSat
    Combinators + RealCombinators           -> andC, orC, dist_preserves, ...

CRUCIALLY these must be evaluated over the TRANSITIVE import closure, not the
direct imports. `VerifyLoopProgress` imports `ConvertLinear`, and
`Combinators` / `Disjunction` / `Inequality` reach it through `TotalLoss`, so
importing any of them drags in `Lattice.EvenSat`. The first version of this
probe got that wrong and Lean rejected it with:

    _probe_ax_group_c.lean:28:0: error: import VerifyLoopConvergence failed,
    environment already contains 'Lattice.EvenSat' from ConvertLinear

`scripts/plan-axiom-probe-groups.ps1` computes the closure and the minimum
partition: **3 groups**. Two suffice for the queries themselves, because
`ComboN` shares no queried name with `VerifyLoopConvergence` and both are
collision-free against this file's set:

    RealContractAxioms.lean   group A: everything except the two below
    _probe_ax_group_b.lean    group B: VerifyLoopConvergence + ComboN + RealCombinators

`scripts/check-axioms.ps1` runs both and merges the results.
-/

import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lift.ConstraintEmbeddingSoundness
import Lattice.Lift.TotalLoss
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Compiler.Disjunction
import Lattice.Lib.Compiler.Combinators
import Lattice.Lib.Chain.Geometry
import Lattice.Lib.Compiler.Inequality
import Lattice.Lift.LayerComposition
import Lattice.Lib.Compiler.ModConstraint
import Lattice.Runtime.RealLinear
import Lattice.Runtime.RealTotalLoss
import Lattice.Lib.Architectures.RealLayerPropagation
import Lattice.Lib.Chain.RealGeometry
import Lattice.Runtime.RealNonlinear
import Lattice.Lib.Architectures.RealReLULayer
open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## C1 标量线性约束 — 见 _probe_ax_group_b（`ConvertLinear` 与 `ComboN` 冲突） -/

/-! ## C2 向量约束 → 线性层 -/
#print axioms convertVec_preserves_semantics
#print axioms scaleVec_preserves
#print axioms convertVec_preserves_solution_set

/-! ## C3 编译（约束集 → 网络）— 主线定理 -/
#print axioms symbolToWeight_correct
#print axioms symbolToWeight_verify
#print axioms symbolToWeight_empty

/-! ## C4 平方损失嵌入 -/
#print axioms embedding_soundness
#print axioms embedding_no_false_solutions
#print axioms embedding_no_missing_solutions

/-! ## C5 总损失 -/
#print axioms totalLoss_eq_zero_iff_allSatisfied
#print axioms totalLoss_verify

/-! ## C6 提取往返恒等 -/
#print axioms roundtrip_extract
#print axioms roundtrip_extractVec
#print axioms roundtrip_behavior
#print axioms extract_is_valid

/-! ## C7a 验证回路（保持语义） — `VerifyLoopProgress` 经 ConvertLinear 引入 EvenSat，
    与 C7b/C8 冲突，故其查询放在 group B。 -/

/-! ## C9 析取组合 -/
#print axioms disjN_preserves
#print axioms disj_embedding

/-! ## C10 组合子代数（Int） -/
#print axioms andC_eq_zero_iff
#print axioms orC_eq_zero_iff
#print axioms and_comm_preserves
#print axioms or_comm_preserves
#print axioms dist_preserves
#print axioms and_assoc_preserves
#print axioms or_assoc_preserves

/-! ## C11 几何（Int 共线） -/
#print axioms collinear_preserves
#print axioms collinear_translate
#print axioms collinear_cyclic
#print axioms collinear_swap
#print axioms collinear_degenerate

/-! ## C12 不等式约束 -/
#print axioms le_ge_iff_sq_zero
#print axioms le_preserves
#print axioms le_and_ge_iff_eq
#print axioms bound_embedding_chain

/-! ## C13 多层传播 -/
#print axioms constraint_satisfaction_propagates
#print axioms layerFwd_allzero
#print axioms layerSeq_three

/-! ## C14 同余约束 -/
#print axioms congruent_trans
#print axioms congruent_refl
#print axioms congruent_symm
#print axioms congruent_add
#print axioms congruent_mod_zero
#print axioms congruent_mod_one
#print axioms congruent_mod_neg_one
#print axioms mod_preserves

/-! ## C15 ℝ 线性 -/
#print axioms convertReal_preserves
#print axioms convertRealVec_preserves
#print axioms realVec_scale_preserves
#print axioms realLoss_soundness
#print axioms real_sq_sum_zero_iff
#print axioms real_scale_preserves

/-! ## C16 ℝ 总损失 -/
#print axioms realTotalLoss_soundness
#print axioms realTotalLoss_zero_iff_all_outputs
#print axioms realTotalLoss_verify
#print axioms realTotalLoss_pos_of_unsatisfied

/-! ## C17 ℝ 层传播 -/
#print axioms realConstraint_satisfaction_propagates
#print axioms realLayer_allSatisfied_iff_zero_output

/-! ## C18 ℝ 几何 -/
#print axioms orthogonalR_symm
#print axioms distSqR_eq_zero_iff
#print axioms collinearR_preserves
#print axioms collinearR_translate
#print axioms collinearR_cyclic
#print axioms collinearR_scale
#print axioms distSqR_translate

/-! ## C19 ReLU / sign 编码 -/
#print axioms relu_preserves
#print axioms sign_preserves
#print axioms relu_eq_zero_iff
#print axioms relu_nonneg
#print axioms sumRelu_all_constraints
#print axioms sumRelu_pos_of_unsatisfied

/-! ## C21 ReLU 层传播 -/
#print axioms relu_propagation
#print axioms ReLUSum_zero_iff_all
#print axioms ReLUSum_iff_all_constraints
#print axioms reluLayer_out_nonneg
#print axioms reluLayer_zero_input

end Lattice
