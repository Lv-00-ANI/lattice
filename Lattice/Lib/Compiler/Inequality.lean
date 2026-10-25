import Mathlib
import Lattice.Lift.TotalLoss
/-!
# LATTICE: 不等式约束 —— 上下界夹逼 ⟺ 等式 ⟺ 平方损失

不等式约束的嵌入与规范化：
  1. 单边不等式 x ≤ a → 神经元输出 x - a，激活 = 输出 ≤ 0（比较器）；
  2. 上下界夹逼 x ≤ a ∧ a ≤ x ⟺ x = a（Int 线性序）；
  3. 夹逼 ⟺ 平方损失零化 (x-a)² = 0 —— 从不等式对到等式损失的桥，
     对应"软约束规范化"（上下界收紧为精确值）。

**注意** **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层只用到 `Int` 等核心类型**
（约束、输出、比较器皆以 `Int` 表达，不依赖 mathlib 的专用结构），
但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
另：`omega` 并非 Lean core 内置，而是 **Mathlib 提供的 tactic**（本文件的 `omega` 用法来自文件整体 import 的 Mathlib）。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice

/-! ## 单边不等式约束（符号侧） -/

def ConstraintLe (x a : Int) : Prop := x ≤ a

/-! ## 比较器神经元（权重侧输出：差值） -/

def LeOut (x a : Int) : Int := x - a

/-! ## 定理一：单边不等式保语义
x ≤ a ⟺ 输出 (x-a) ≤ 0。-/

theorem le_preserves (x a : Int) : ConstraintLe x a ↔ LeOut x a ≤ 0 := by
  unfold ConstraintLe LeOut
  constructor <;> omega

/-! ## 定理二：上下界夹逼 ⟺ 等式
x ≤ a ∧ a ≤ x ⟺ x = a（Int 反对称）。-/

theorem le_and_ge_iff_eq (x a : Int) : x ≤ a ∧ a ≤ x ↔ x = a := by
  constructor
  · intro h; omega
  · intro h; omega

/-! ## 定理三：夹逼 ⟺ 平方损失零化
(x-a ≤ 0 ∧ a-x ≤ 0) ⟺ (x-a)² = 0。
上下界夹逼（软约束对）收紧为精确等式，等价于平方损失降到零。-/

theorem le_ge_iff_sq_zero (x a : Int) :
    (LeOut x a ≤ 0 ∧ LeOut a x ≤ 0) ↔ (LeOut x a) ^ 2 = 0 := by
  unfold LeOut
  constructor
  · intro h
    have heq : x = a := by omega
    simp [heq]
  · intro h
    have hz : x - a = 0 := (int_sq_eq_zero_iff (x - a)).mp h
    constructor <;> omega

/-! ## 推论：不等式夹逼在嵌入下的完整链
符号侧夹逼 ⟺ 等式 ⟺ 平方损失零化（可作训练损失）。-/

theorem bound_embedding_chain (x a : Int) :
    (ConstraintLe x a ∧ ConstraintLe a x) ↔ (LeOut x a) ^ 2 = 0 := by
  -- 左 = 夹逼 = 等式 = 平方损失零
  rw [le_preserves, le_preserves]
  exact le_ge_iff_sq_zero x a

/-! ## 非退化：非零差值的平方损失为正
x ≠ a ⟹ (x-a)² > 0（损失严格区分不满足）。-/

theorem sq_pos_of_ne (x a : Int) (h : x ≠ a) : 0 < (x - a) ^ 2 := by
  have hz : x - a ≠ 0 := by omega
  have hsq : (x - a) ^ 2 ≠ 0 := by
    intro hs
    exact hz ((int_sq_eq_zero_iff (x - a)).mp hs)
  -- Int 平方非负且非零 → 正
  have hn : 0 ≤ (x - a) ^ 2 := int_sq_nonneg (x - a)
  omega

end Lattice
