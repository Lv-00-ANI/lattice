import Mathlib
import Lattice.Lib.Chain.RealLv00AxiomDischargeClosure

/-!
# `RealLv00AxiomDischargePerPackage.lean` 的 `A` 部分

由原文件按语义分节拆分而来；节标题与内容未改动。
-/

/-! # RealLv00AxiomDischargePerPackage

拆分自 `RealLv00AxiomDischarge.lean`（第 879–1303 行），2026-10-14。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00AxiomDischarge` 仍有效。

本模块重新声明了原文件的三项模块级设置（缺一不可）：
`noncomputable section`（:64）、`set_option maxHeartbeats 1000000`（:66）、
`namespace Lattice.Lv00.AxiomDischarge`（:68）。
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Lattice.Lv00.AxiomDischarge


/-! ## 5. 12 tiao axiom de zhu tiao qingsuan

Dui mei ge bao <X>:

- `not_<X>_orig` : **yuan weici wei jia** (ji shangyou na tiao axiom duanyan de shi jia mingti).
- `<X>_closed`   : **xiufu weici wei zhen**, extra = gai bao de kua yinyong ming ji.
- `<X>_false_but_repairable` : dui zhao + extra fei kong.

Lu jing: xian zai **Bool he xin** shang suan chu jie guo, zai jing `*_iff` qiao jie hui Prop.
**Bu yong `native_decide`.** -/

/-! ### computabilityTheory (computability_theory) -- kua yinyong 3 ge ming, 13 tiao bian -/

/-- computability_theory de kua yinyong ming ji (ji extra). -/
def computabilityTheoryExtra : List String :=
  [ "halting_problem", "post_correspondence_problem", "rice_theorem_undecidability" ]

theorem computabilityTheory_extra_length : computabilityTheoryExtra.length = 3 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem computabilityTheory_validB_eq_false : packageDependenciesValidB computabilityTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem computabilityTheory_closedB_eq_true : packageDependenciesClosedB computabilityTheoryPackage computabilityTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `computabilityTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_computabilityTheory_orig : ¬ (PackageDependenciesValid computabilityTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [computabilityTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem computabilityTheory_closed : PackageDependenciesClosed computabilityTheoryPackage computabilityTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact computabilityTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem computabilityTheory_false_but_repairable :
    (¬ (PackageDependenciesValid computabilityTheoryPackage)) ∧
      PackageDependenciesClosed computabilityTheoryPackage computabilityTheoryExtra ∧
      computabilityTheoryExtra.length = 3 := by
  exact ⟨not_computabilityTheory_orig, computabilityTheory_closed, computabilityTheory_extra_length⟩

/-! ### modalLogic (modal_logic) -- kua yinyong 5 ge ming, 7 tiao bian -/

/-- modal_logic de kua yinyong ming ji (ji extra). -/
def modalLogicExtra : List String :=
  [ "classical_propositional_logic", "modal_logic", "modal_satisfiability_K",
    "modal_satisfiability_S4", "second_order_logic" ]

theorem modalLogic_extra_length : modalLogicExtra.length = 5 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem modalLogic_validB_eq_false : packageDependenciesValidB modalLogicPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem modalLogic_closedB_eq_true : packageDependenciesClosedB modalLogicPackage modalLogicExtra = true := rfl

/-- **Qingsuan**: shangyou `modalLogicPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_modalLogic_orig : ¬ (PackageDependenciesValid modalLogicPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [modalLogic_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem modalLogic_closed : PackageDependenciesClosed modalLogicPackage modalLogicExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact modalLogic_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem modalLogic_false_but_repairable :
    (¬ (PackageDependenciesValid modalLogicPackage)) ∧
      PackageDependenciesClosed modalLogicPackage modalLogicExtra ∧
      modalLogicExtra.length = 5 := by
  exact ⟨not_modalLogic_orig, modalLogic_closed, modalLogic_extra_length⟩
