import Mathlib
import Lattice.Lib.Compiler.ReversibilityCriterion
import Lattice.Lib.Compiler.ReluLemmas
import Lattice.Lib.Compiler.ReversibilityLimit
import Lattice.Lib.Compiler.NoIntermediateLayer
import Lattice.Runtime.ConvertVectorLinear

/-!
# 把两个特例归约到判据（阶段 C，P6）

## 上一轮的成果与本轮的缺口

**第 942 轮证明了判据：**

```lean
theorem reversibility_criterion (compile : S → W) [Inhabited S] :
    Function.Injective compile ↔ ∃ extract : W → S, ∀ s, extract (compile s) = s
```

**=> 但当时它**还没有接上任何实例**。本文件接上两个，证明判据不是空转。**

## 为什么必须接上

**一个判据若无实例，等于没有判据。**
**而项目已有的两个结论——`linearReversible`（可逆）与 `relu_not_reversible`（不可逆）——**
**此前是**两条独立的证明**。本文件证明它们是**同一个判据的两个实例**。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`linear_injective`** | **⭐⭐ `convertVec` 单射（线性编译不丢信息）** |
| **`linear_reversible_by_criterion`** | **⭐⭐ 线性可逆 ← 判据** |
| **`relu_not_injective`** | **⭐⭐ `reluCompile` 非单射（折叠负值）** |
| **`relu_irreversible_by_criterion`** | **⭐⭐ ReLU 不可逆 ← 判据** |
| **`one_criterion_two_outcomes`** | **⭐⭐⭐ 同一判据同时给出可逆与不可逆** |

**=> 最后一条是本轮的交付：判据**解释**了分野，而不只是描述它。** -/

namespace Lattice.Lib.Compiler.ReversibilityInstances

open Lattice

/-- **⭐⭐ `convertVec` 单射：线性编译不丢信息。**

**=> 由既有的 `convertVec_bijective` 取单射分量。**

**=> 这是判据的第一个前提，直接来自「线性载体是双射」。** -/
theorem linear_injective : Function.Injective convertVec :=
  Lattice.Lib.Compiler.NoIntermediateLayer.convertVec_bijective.injective

/-- **⭐⭐ 线性可逆：由判据得到。**

**=> `∃ extract, ∀ c, extract (convertVec c) = c` 由 `reversibility_criterion` 与
`linear_injective` 直接给出。**

**=> 与 `CarrierInstantiation.linearReversible` **同一结论**，但走的是**一般判据**。** -/
theorem linear_reversible_by_criterion :
    ∃ extract : LinearLayer → VectorConstraint, ∀ c, extract (convertVec c) = c :=
  -- the criterion needs an `Inhabited` fallback for weights OUTSIDE the image;
  -- supply it locally so the tree does not gain a global instance for a proof-only need
  @Lattice.Lib.Compiler.ReversibilityCriterion.reversibility_criterion
    VectorConstraint LinearLayer ⟨⟨[], 0⟩⟩ convertVec |>.mp linear_injective

/-- **⭐⭐ `reluCompile` 非单射。**

**=> 由 `reluCompile_collapses_ne`：存在两个不同的输入给出同一输出。**

**=> 这是判据的第二个前提，来源是「ReLU 把负值折成零」。** -/
theorem relu_not_injective :
    ¬ Function.Injective (fun s : ℝ × ℝ × ℝ => reluCompile s.1 s.2.1 s.2.2) := by
  intro hinj
  obtain ⟨heq, hne⟩ := Lattice.Lib.Compiler.ReluLemmas.reluCompile_collapses_ne
  exact hne (hinj heq)

/-- **⭐⭐ ReLU 不可逆：由判据得到。**

**=> 这是 `ReversibilityLimit.relu_not_reversible` 的**判据版**：
同一结论，但理由是「非单射」，而不是逐个反例排除。** -/
theorem relu_irreversible_by_criterion :
    ¬ ∃ extract : ℝ → ℝ × ℝ × ℝ, ∀ s : ℝ × ℝ × ℝ, extract (reluCompile s.1 s.2.1 s.2.2) = s :=
  Lattice.Lib.Compiler.ReversibilityCriterion.not_injective_gives_no_extract _ relu_not_injective

/-- **⭐⭐⭐ 同一判据同时给出可逆与不可逆。**

**=> 陈述：两条结论——线性可逆、ReLU 不可逆——**都是由同一条判据推出的**，
且两条的成立理由分别是单射与非单射。**

**=> 这是本轮的交付：分野由**编译映射是否单射**决定，而不是由载体种类枚举决定。** -/
theorem one_criterion_two_outcomes :
    (∃ extract : LinearLayer → VectorConstraint, ∀ c, extract (convertVec c) = c) ∧
      (¬ ∃ extract : ℝ → ℝ × ℝ × ℝ, ∀ s : ℝ × ℝ × ℝ, extract (reluCompile s.1 s.2.1 s.2.2) = s) :=
  ⟨linear_reversible_by_criterion, relu_irreversible_by_criterion⟩

end Lattice.Lib.Compiler.ReversibilityInstances
