import Mathlib
import Lattice.Lib.Chain.RealLv00AxiomDischargeClosure
import Lattice.Lib.Chain.RealLv00AxiomDischargePerPackage_parts.A

/-!
# `RealLv00AxiomDischargePerPackage.lean` 的 `B` 部分

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
