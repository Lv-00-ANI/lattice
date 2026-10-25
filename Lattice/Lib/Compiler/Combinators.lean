import Mathlib
import Lattice.Lift.TotalLoss
/-!
# LATTICE: 组合子代数健全性 —— AND/OR 嵌入保持交换律与分配律

doc/01 组合律架桥（难点 4）的代数健全性证明：
符号侧的 AND（∧）、OR（∨）组合律，在权重侧的嵌入组合子
（平方和、乘积）下**结构保持**：

  AND 组合子  andC a b := a² + b²        （=0 ⟺ a=0 ∧ b=0）
  OR  组合子  orC  a b := a · b          （=0 ⟺ a=0 ∨ b=0）

证明：
  1. 交换律保持：andC a b = 0 ↔ andC b a = 0；orC 同理；
  2. 分配律保持：a ∧ (b ∨ c) 的嵌入 = 0 ⟺ (a ∧ b) ∨ (a ∧ c) 的嵌入 = 0
     —— 符号逻辑分配律在网络侧成立（结构同态）。

这保证：符号规则的逻辑变换（交换/分配）可以安全地在权重侧进行，
不会改变满足语义。

  **注意** **订正 B400**：此处原写「纯 Std」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
  真实情况是：**本文件的表示层与数学内容确实只用 Std 层的东西** —— 组合子
  `andC`/`orC` 及其全部引理、定理都建立在 Lean core 的 `Int` 上，证明只用到
  `omega`、`tauto`、`simp` 等 core/Std 级手段，并复用 `TotalLoss.int_sq_nonneg`，
  **不依赖 mathlib 的专用结构**；
  但**文件整体 import 了 Mathlib**。⇒ 原措辞把「内容的选型」误写成了「依赖的选型」。
  订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice

/-! ## 嵌入组合子 -/

def andC (a b : Int) : Int := a ^ 2 + b ^ 2

def orC (a b : Int) : Int := a * b

/-! ## 引理一：AND 组合子零化 ⟺ 两项为零 -/

lemma andC_eq_zero_iff (a b : Int) : andC a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hsum : a ^ 2 + b ^ 2 = 0 := by simpa [andC] using h
    have ha_nonneg : 0 ≤ a ^ 2 := int_sq_nonneg a
    have hb_nonneg : 0 ≤ b ^ 2 := int_sq_nonneg b
    have ha2 : a ^ 2 = 0 := by
      apply le_antisymm
      · omega
      · exact ha_nonneg
    have hb2 : b ^ 2 = 0 := by
      apply le_antisymm
      · omega
      · exact hb_nonneg
    exact ⟨(int_sq_eq_zero_iff a).mp ha2, (int_sq_eq_zero_iff b).mp hb2⟩
  · intro h
    rcases h with ⟨ha, hb⟩
    simp [andC, ha, hb]

/-! ## 引理二：OR 组合子零化 ⟺ 任一项为零 -/

lemma orC_eq_zero_iff (a b : Int) : orC a b = 0 ↔ a = 0 ∨ b = 0 := by
  unfold orC
  exact Int.mul_eq_zero

/-! ## 定理一：AND 交换律保持 -/

theorem and_comm_preserves (a b : Int) : andC a b = 0 ↔ andC b a = 0 := by
  rw [andC_eq_zero_iff, andC_eq_zero_iff]
  constructor
  · intro h; exact ⟨h.2, h.1⟩
  · intro h; exact ⟨h.2, h.1⟩

/-! ## 定理二：OR 交换律保持 -/

theorem or_comm_preserves (a b : Int) : orC a b = 0 ↔ orC b a = 0 := by
  simp only [orC_eq_zero_iff]
  tauto

/-! ## 定理三：分配律保持（符号逻辑分配律在网络侧成立）
a ∧ (b ∨ c) ⟺ (a ∧ b) ∨ (a ∧ c)-/

theorem dist_preserves (a b c : Int) :
    andC a (orC b c) = 0 ↔ orC (andC a b) (andC a c) = 0 := by
  simp only [andC_eq_zero_iff, orC_eq_zero_iff]
  tauto

/-! ## 定理四：结合律保持
(a ∧ b) ∧ c ⟺ a ∧ (b ∧ c)-/

theorem and_assoc_preserves (a b c : Int) :
    andC (andC a b) c = 0 ↔ andC a (andC b c) = 0 := by
  simp only [andC_eq_zero_iff]
  tauto

/-! ## 定理五：OR 结合律保持 -/

theorem or_assoc_preserves (a b c : Int) :
    orC (orC a b) c = 0 ↔ orC a (orC b c) = 0 := by
  simp only [orC_eq_zero_iff]
  tauto

end Lattice
