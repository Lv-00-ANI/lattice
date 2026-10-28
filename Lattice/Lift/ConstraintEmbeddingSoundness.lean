import Mathlib
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
/-!
# LATTICE: ConstraintEmbeddingSoundness（最小版本）—— 约束嵌入平方损失

doc/02 §4.3 的 `ConstraintEmbeddingSoundness` 的最小实例：
把符号约束嵌入为**平方损失** L(x) = (out x)²，证明：

  损失零化 ⟺ 约束满足（L(x) = 0 ⟺ ConstraintSat c x）

这是 doc/01「硬约束的解嵌入软约束的零损失点」的代数核心：
训练中损失降到零的点，恰好就是符号约束被满足的点——
嵌入不引入虚假解、也不丢失真解。

**注意** **订正 B400**：此处原写「纯 Std（无 mathlib）」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层构造基于 Std 类型**（损失 L(x) = (out x)²、约束与神经元皆以 `Int` 表达，
平方零化用 `Int.mul_eq_zero` 这一核心引理，不依赖 mathlib 的专用结构），
但**文件整体 import 了 Mathlib**（本文件所 import 的 `ConvertLinear`、`ConvertVectorLinear`、
`SymbolToWeightCorrectness` 亦然）。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。**以本段为准。**
-/


open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 平方损失：约束嵌入 -/

def loss (c : LinearConstraint) (x : Int) : Int :=
  (NeuronOut (convert c) x) ^ 2

/-! ## 引理：整数平方为零 ⟺ 底数为零
(Int.mul_eq_zero：无零因子，a*a = 0 → a = 0)-/

lemma int_sq_eq_zero_iff (a : Int) : a ^ 2 = 0 ↔ a = 0 := by
  constructor
  · intro h
    have : a * a = 0 := by simpa [pow_two] using h
    exact Int.mul_eq_zero.mp this |>.elim id id
  · intro h
    simp [h]

/-! ## 定理：ConstraintEmbeddingSoundness（最小版本）
损失零化 ⟺ 约束满足。-/

theorem embedding_soundness (c : LinearConstraint) (x : Int) :
    loss c x = 0 ↔ ConstraintSat c x := by
  unfold loss
  rw [int_sq_eq_zero_iff]
  exact convert_preserves_semantics c x

/-! ## 推论一：嵌入不引入虚假解
损失为零的点必满足约束（训练降到零损失 = 约束被满足）。-/

theorem embedding_no_false_solutions (c : LinearConstraint) (x : Int)
    (h : loss c x = 0) : ConstraintSat c x :=
  (embedding_soundness c x).mp h

/-! ## 推论二：嵌入不丢失真解
约束被满足的点损失必为零（可作训练中的验证信号）。-/

theorem embedding_no_missing_solutions (c : LinearConstraint) (x : Int)
    (h : ConstraintSat c x) : loss c x = 0 :=
  (embedding_soundness c x).mpr h

/-! ## 与组合的联系：单层网络逐神经元损失
符号程序（约束集合）编译为网络后，逐神经元损失全零 ⟺ 全部约束满足。

注：原稿的 「embedding_all_neurons」 陈述类型错误无法成立——
`loss` 作用于标量约束 `LinearConstraint`（`a : Int`），而编译层的
神经元是 `LinearLayer`（`w : List Int`），`loss { a := l.w, b := l.b } x`
把 `List Int` 当作 `Int` 使用（且 `x : List Int` 传给期望 `Int` 的 `loss`），
类型不匹配，无法构成合法的定理陈述。该组合性质的正确版本即
`SymbolToWeightCorrectness.symbolToWeight_correct`
（`LayerOut` 全零 ⟺ 全部约束满足）。
-/

end Lattice
