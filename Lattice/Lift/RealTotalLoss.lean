import Mathlib
import Lattice.Runtime.RealLinear
/-!
# LATTICE: ℝ 总损失 —— Σ (out_i)² = 0 ⟺ 全部约束满足

ℝ 版 TotalLoss（对应 TotalLoss.lean 的 ℝ 版）：
符号程序（有限约束序列）编译为 ℝ 网络后，**总平方损失为零 ⟺ 全部约束满足**。

Mathlib 提供 Finset 求和与 sum_eq_zero_iff_of_nonneg，证明比 Int 手工版（`int_sq_nonneg` 等）简洁：
  训练中总损失降到 0 的点恰好满足全部符号约束（连续域训练语义）。

注意 **订正 B400**：此处原写「对应纯 Std TotalLoss.lean」、
「证明比纯 Std 简洁」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾；
且被对照的 `TotalLoss.lean` 自身第 1 行同样是 `import Mathlib`
（其文件头亦已就此作出同名订正，见 RealLinear 的文件头「订正 B400」）。
真实情况是：**只有上述那个 Int 离散域的手工版证明才只用 Std 层的东西**
（`Int` 及其引理，如 `int_sq_nonneg`）；
**本文件的表示层构造基于 Std 类型** —— `compileFin`/`RealTotalLoss` 都只是
`Fin n` 上的普通 `def`，但其中的 `ℝ` 类型本身来自 Mathlib，
证明手段（`Finset.sum_eq_zero_iff_of_nonneg`、`sq_nonneg`、`sq_eq_zero_iff`）亦由 Mathlib 提供，
并非 Lean core 内置，且**文件整体 import 了 Mathlib**。
⇒ 原措辞把「被对比的那个手工版」误写成了「本文件」，并把「表示层的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice

/-! ## 网络：Fin n 索引的 ℝ 神经元（每约束一个） -/

def compileFin {n : Nat} (cs : Fin n → RealConstraint) : Fin n → RealNeuron :=
  fun i => convertReal (cs i)

/-! ## 总平方损失 -/

def RealTotalLoss {n : Nat} (ls : Fin n → RealNeuron) (x : ℝ) : ℝ :=
  ∑ i : Fin n, (RealNeuronOut (ls i) x) ^ 2

/-! ## 定理一：总损失零化 ⟺ 每个输出为零
ℝ 平方非负（sq_nonneg）+ Mathlib sum_eq_zero_iff_of_nonneg。-/

theorem realTotalLoss_zero_iff_all_outputs {n : Nat} (ls : Fin n → RealNeuron) (x : ℝ) :
    RealTotalLoss ls x = 0 ↔ ∀ i : Fin n, RealNeuronOut (ls i) x = 0 := by
  unfold RealTotalLoss
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h i
      exact sq_eq_zero_iff.mp (h i (Finset.mem_univ i))
    · intro h i hi
      exact sq_eq_zero_iff.mpr (h i)
  · intro i hi
    exact sq_nonneg (RealNeuronOut (ls i) x)

/-! ## 定理二：总损失零化 ⟺ 全部约束满足
（编译保语义 + 逐元素转换）——训练损失降到 0 ⟺ 符号约束全部成立。-/

theorem realTotalLoss_soundness {n : Nat} (cs : Fin n → RealConstraint) (x : ℝ) :
    RealTotalLoss (compileFin cs) x = 0 ↔ ∀ i : Fin n, RealConstraintSat (cs i) x := by
  rw [realTotalLoss_zero_iff_all_outputs]
  constructor
  · intro h i
    exact (convertReal_preserves (cs i) x).mp (h i)
  · intro h i
    exact (convertReal_preserves (cs i) x).mpr (h i)

/-! ## 推论：训练验证信号
总损失为零 ⟹ 全部约束满足（训练完成后可用损失判满足）。-/

theorem realTotalLoss_verify {n : Nat} (cs : Fin n → RealConstraint) (x : ℝ)
    (h : RealTotalLoss (compileFin cs) x = 0) : ∀ i : Fin n, RealConstraintSat (cs i) x :=
  (realTotalLoss_soundness cs x).mp h

/-! ## 定理三：损失严格性 —— 约束不满足则损失为正
存在未满足约束 ⟹ 总损失 > 0（训练可观测失败信号）。-/

theorem realTotalLoss_pos_of_unsatisfied {n : Nat} (ls : Fin n → RealNeuron) (x : ℝ)
    (i : Fin n) (h : RealNeuronOut (ls i) x ≠ 0) : 0 < RealTotalLoss ls x := by
  unfold RealTotalLoss
  -- 总损失 ≥ (out_i)² > 0
  have hsq : 0 < (RealNeuronOut (ls i) x) ^ 2 := by
    have hsq0 : (RealNeuronOut (ls i) x) ^ 2 ≠ 0 := by
      intro hs
      exact h (sq_eq_zero_iff.mp hs)
    exact lt_of_le_of_ne (sq_nonneg (RealNeuronOut (ls i) x)) (Ne.symm hsq0)
  have hsum_ge : (RealNeuronOut (ls i) x) ^ 2 ≤ ∑ j : Fin n, (RealNeuronOut (ls j) x) ^ 2 := by
    -- 单项 ≤ 总和（其余项非负，single_le_sum）
    exact Finset.single_le_sum
      (fun j hj => sq_nonneg (RealNeuronOut (ls j) x)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hsq hsum_ge

end Lattice
