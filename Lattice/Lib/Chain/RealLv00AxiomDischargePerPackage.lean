import Mathlib
import Lattice.Lib.Chain.RealLv00AxiomDischargeClosure
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


/-! ### zfcSetTheory (zfc_set_theory) -- kua yinyong 1 ge ming, 2 tiao bian -/

/-- zfc_set_theory de kua yinyong ming ji (ji extra). -/
def zfcSetTheoryExtra : List String :=
  [ "continuum_hypothesis" ]

theorem zfcSetTheory_extra_length : zfcSetTheoryExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem zfcSetTheory_validB_eq_false : packageDependenciesValidB zfcSetTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem zfcSetTheory_closedB_eq_true : packageDependenciesClosedB zfcSetTheoryPackage zfcSetTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `zfcSetTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_zfcSetTheory_orig : ¬ (PackageDependenciesValid zfcSetTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [zfcSetTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem zfcSetTheory_closed : PackageDependenciesClosed zfcSetTheoryPackage zfcSetTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact zfcSetTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem zfcSetTheory_false_but_repairable :
    (¬ (PackageDependenciesValid zfcSetTheoryPackage)) ∧
      PackageDependenciesClosed zfcSetTheoryPackage zfcSetTheoryExtra ∧
      zfcSetTheoryExtra.length = 1 := by
  exact ⟨not_zfcSetTheory_orig, zfcSetTheory_closed, zfcSetTheory_extra_length⟩


/-! ### graphTheory (graph_theory) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- graph_theory de kua yinyong ming ji (ji extra). -/
def graphTheoryExtra : List String :=
  [ "three_colorability" ]

theorem graphTheory_extra_length : graphTheoryExtra.length = 1 := rfl

/-! 注意 **EXEC-Y1 语义变更（必读）**

`graph_theory` 是 **唯一** 一个「补 30 外名」后其**原谓词即变真**的包：
其唯一缺失依赖 `three_colorability` 已由 EXEC-Y1 补进本包模板表，
且该包的其余依赖**全部**本来就在本包表内（无跨包依赖）。

⟹ 本文件原先的三条定理（`graphTheory_validB_eq_false` /
`not_graphTheory_orig` / `graphTheory_false_but_repairable`）
断言「原谓词为假」，**在补数据后即为假命题**，故本轮**同步改判**：

- `graphTheory_validB_eq_false` → **`graphTheory_validB_eq_true`**（原谓词变真）
- `not_graphTheory_orig` → **`graphTheory_orig_true`**（正面命题，不再是否定式）
- `graphTheory_false_but_repairable` → **`graphTheory_repaired`**（乙单独即闭合的见证）

要点 这条**不是**「为了通过而放宽」：它是「乙」方案对 `graph_theory` 的**真实效果**，
且使 `graph_theory` 成为**「乙」单独闭合率的直接见证（1/6）**。 -/

/-- Bool he xin pan ju: yuan weici **wei zhen**（EXEC-Y1 补 30 外名后变真）。 -/
theorem graphTheory_validB_eq_true : packageDependenciesValidB graphTheoryPackage = true := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem graphTheory_closedB_eq_true : packageDependenciesClosedB graphTheoryPackage graphTheoryExtra = true := rfl

/-- **Qingsuan（改判）**: EXEC-Y1 补 30 外名后，原谓词**为真**。 -/
theorem graphTheory_orig_true : PackageDependenciesValid graphTheoryPackage := by
  rw [<- packageDependenciesValidB_iff]
  exact graphTheory_validB_eq_true

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem graphTheory_closed : PackageDependenciesClosed graphTheoryPackage graphTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact graphTheory_closedB_eq_true

/-- Dui zhao: EXEC-Y1 后原谓词**已为真**，且并集闭包亦为真，extra 非空。
    要点 这是「乙」方案**单独**（不靠甲）即闭合一个包的见证。 -/
theorem graphTheory_repaired :
    PackageDependenciesValid graphTheoryPackage ∧
      PackageDependenciesClosed graphTheoryPackage graphTheoryExtra ∧
      graphTheoryExtra.length = 1 := by
  exact ⟨graphTheory_orig_true, graphTheory_closed, graphTheory_extra_length⟩


/-! ### measureTheory (measure_theory) -- kua yinyong 2 ge ming, 7 tiao bian -/

/-- measure_theory de kua yinyong ming ji (ji extra). -/
def measureTheoryExtra : List String :=
  [ "computability_theory", "zfc_set_theory" ]

theorem measureTheory_extra_length : measureTheoryExtra.length = 2 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem measureTheory_validB_eq_false : packageDependenciesValidB measureTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem measureTheory_closedB_eq_true : packageDependenciesClosedB measureTheoryPackage measureTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `measureTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_measureTheory_orig : ¬ (PackageDependenciesValid measureTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [measureTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem measureTheory_closed : PackageDependenciesClosed measureTheoryPackage measureTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact measureTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem measureTheory_false_but_repairable :
    (¬ (PackageDependenciesValid measureTheoryPackage)) ∧
      PackageDependenciesClosed measureTheoryPackage measureTheoryExtra ∧
      measureTheoryExtra.length = 2 := by
  exact ⟨not_measureTheory_orig, measureTheory_closed, measureTheory_extra_length⟩


/-! ### functionalAnalysis (functional_analysis) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- functional_analysis de kua yinyong ming ji (ji extra). -/
def functionalAnalysisExtra : List String :=
  [ "lp_space" ]

theorem functionalAnalysis_extra_length : functionalAnalysisExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem functionalAnalysis_validB_eq_false : packageDependenciesValidB functionalAnalysisPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem functionalAnalysis_closedB_eq_true : packageDependenciesClosedB functionalAnalysisPackage functionalAnalysisExtra = true := rfl

/-- **Qingsuan**: shangyou `functionalAnalysisPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_functionalAnalysis_orig : ¬ (PackageDependenciesValid functionalAnalysisPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [functionalAnalysis_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem functionalAnalysis_closed : PackageDependenciesClosed functionalAnalysisPackage functionalAnalysisExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact functionalAnalysis_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem functionalAnalysis_false_but_repairable :
    (¬ (PackageDependenciesValid functionalAnalysisPackage)) ∧
      PackageDependenciesClosed functionalAnalysisPackage functionalAnalysisExtra ∧
      functionalAnalysisExtra.length = 1 := by
  exact ⟨not_functionalAnalysis_orig, functionalAnalysis_closed, functionalAnalysis_extra_length⟩


/-! ### probabilityTheory (probability_theory) -- kua yinyong 4 ge ming, 7 tiao bian -/

/-- probability_theory de kua yinyong ming ji (ji extra). -/
def probabilityTheoryExtra : List String :=
  [ "axiom_of_choice", "computational_complexity_theory", "measure_theory",
    "zfc_set_theory" ]

theorem probabilityTheory_extra_length : probabilityTheoryExtra.length = 4 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem probabilityTheory_validB_eq_false : packageDependenciesValidB probabilityTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem probabilityTheory_closedB_eq_true : packageDependenciesClosedB probabilityTheoryPackage probabilityTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `probabilityTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_probabilityTheory_orig : ¬ (PackageDependenciesValid probabilityTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [probabilityTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem probabilityTheory_closed : PackageDependenciesClosed probabilityTheoryPackage probabilityTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact probabilityTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem probabilityTheory_false_but_repairable :
    (¬ (PackageDependenciesValid probabilityTheoryPackage)) ∧
      PackageDependenciesClosed probabilityTheoryPackage probabilityTheoryExtra ∧
      probabilityTheoryExtra.length = 4 := by
  exact ⟨not_probabilityTheory_orig, probabilityTheory_closed, probabilityTheory_extra_length⟩


/-! ### informationTheory (information_theory) -- kua yinyong 12 ge ming, 13 tiao bian -/

/-- information_theory de kua yinyong ming ji (ji extra). -/
def informationTheoryExtra : List String :=
  [ "adversary_model", "channel_model", "channel_model_specification",
    "channel_models", "cryptographic_protocol", "distortion_measure",
    "network_topology", "program_termination", "received_signal",
    "source_distribution", "turing_machine_universality", "universal_turing_machine" ]

theorem informationTheory_extra_length : informationTheoryExtra.length = 12 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem informationTheory_validB_eq_false : packageDependenciesValidB informationTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem informationTheory_closedB_eq_true : packageDependenciesClosedB informationTheoryPackage informationTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `informationTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_informationTheory_orig : ¬ (PackageDependenciesValid informationTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [informationTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem informationTheory_closed : PackageDependenciesClosed informationTheoryPackage informationTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact informationTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem informationTheory_false_but_repairable :
    (¬ (PackageDependenciesValid informationTheoryPackage)) ∧
      PackageDependenciesClosed informationTheoryPackage informationTheoryExtra ∧
      informationTheoryExtra.length = 12 := by
  exact ⟨not_informationTheory_orig, informationTheory_closed, informationTheory_extra_length⟩


/-! ### linearAlgebra (linear_algebra) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- linear_algebra de kua yinyong ming ji (ji extra). -/
def linearAlgebraExtra : List String :=
  [ "matrix_mortality_problem" ]

theorem linearAlgebra_extra_length : linearAlgebraExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem linearAlgebra_validB_eq_false : packageDependenciesValidB linearAlgebraPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem linearAlgebra_closedB_eq_true : packageDependenciesClosedB linearAlgebraPackage linearAlgebraExtra = true := rfl

/-- **Qingsuan**: shangyou `linearAlgebraPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_linearAlgebra_orig : ¬ (PackageDependenciesValid linearAlgebraPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [linearAlgebra_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem linearAlgebra_closed : PackageDependenciesClosed linearAlgebraPackage linearAlgebraExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact linearAlgebra_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem linearAlgebra_false_but_repairable :
    (¬ (PackageDependenciesValid linearAlgebraPackage)) ∧
      PackageDependenciesClosed linearAlgebraPackage linearAlgebraExtra ∧
      linearAlgebraExtra.length = 1 := by
  exact ⟨not_linearAlgebra_orig, linearAlgebra_closed, linearAlgebra_extra_length⟩


/-! ### projectiveGeometry (projective_geometry) -- kua yinyong 11 ge ming, 12 tiao bian -/

/-- projective_geometry de kua yinyong ming ji (ji extra). -/
def projectiveGeometryExtra : List String :=
  [ "alternative_division_ring", "bruck_ryser_chowla_theorem", "combinatorial_design_theory",
    "computational_search", "coordinate_field_construction", "desargues_theorem_failure",
    "field_theory", "finite_field_theory", "non_desarguesian_plane_construction",
    "projective_to_euclidean_specialization", "translation_plane_theory" ]

theorem projectiveGeometry_extra_length : projectiveGeometryExtra.length = 11 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem projectiveGeometry_validB_eq_false : packageDependenciesValidB projectiveGeometryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem projectiveGeometry_closedB_eq_true : packageDependenciesClosedB projectiveGeometryPackage projectiveGeometryExtra = true := rfl

/-- **Qingsuan**: shangyou `projectiveGeometryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_projectiveGeometry_orig : ¬ (PackageDependenciesValid projectiveGeometryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [projectiveGeometry_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem projectiveGeometry_closed : PackageDependenciesClosed projectiveGeometryPackage projectiveGeometryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact projectiveGeometry_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem projectiveGeometry_false_but_repairable :
    (¬ (PackageDependenciesValid projectiveGeometryPackage)) ∧
      PackageDependenciesClosed projectiveGeometryPackage projectiveGeometryExtra ∧
      projectiveGeometryExtra.length = 11 := by
  exact ⟨not_projectiveGeometry_orig, projectiveGeometry_closed, projectiveGeometry_extra_length⟩


/-! ### orderTheory (order_theory) -- kua yinyong 9 ge ming, 16 tiao bian -/

/-- order_theory de kua yinyong ming ji (ji extra). -/
def orderTheoryExtra : List String :=
  [ "convex_geometry", "dilworth_theorem", "graph_isomorphism",
    "group_theory", "partial_order", "poset_dimension",
    "realizer", "topological_sort", "zfc_set_theory" ]

theorem orderTheory_extra_length : orderTheoryExtra.length = 9 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem orderTheory_validB_eq_false : packageDependenciesValidB orderTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem orderTheory_closedB_eq_true : packageDependenciesClosedB orderTheoryPackage orderTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `orderTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_orderTheory_orig : ¬ (PackageDependenciesValid orderTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [orderTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem orderTheory_closed : PackageDependenciesClosed orderTheoryPackage orderTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact orderTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem orderTheory_false_but_repairable :
    (¬ (PackageDependenciesValid orderTheoryPackage)) ∧
      PackageDependenciesClosed orderTheoryPackage orderTheoryExtra ∧
      orderTheoryExtra.length = 9 := by
  exact ⟨not_orderTheory_orig, orderTheory_closed, orderTheory_extra_length⟩


/-! ### affineGeometry (affine_geometry) -- kua yinyong 4 ge ming, 15 tiao bian -/

/-- affine_geometry de kua yinyong ming ji (ji extra). -/
def affineGeometryExtra : List String :=
  [ "affine_geometry", "combinatorics", "euclidean_plane",
    "projective_geometry" ]

theorem affineGeometry_extra_length : affineGeometryExtra.length = 4 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem affineGeometry_validB_eq_false : packageDependenciesValidB affineGeometryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem affineGeometry_closedB_eq_true : packageDependenciesClosedB affineGeometryPackage affineGeometryExtra = true := rfl

/-- **Qingsuan**: shangyou `affineGeometryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_affineGeometry_orig : ¬ (PackageDependenciesValid affineGeometryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [affineGeometry_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem affineGeometry_closed : PackageDependenciesClosed affineGeometryPackage affineGeometryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact affineGeometry_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem affineGeometry_false_but_repairable :
    (¬ (PackageDependenciesValid affineGeometryPackage)) ∧
      PackageDependenciesClosed affineGeometryPackage affineGeometryExtra ∧
      affineGeometryExtra.length = 4 := by
  exact ⟨not_affineGeometry_orig, affineGeometry_closed, affineGeometry_extra_length⟩



end Lattice.Lv00.AxiomDischarge
