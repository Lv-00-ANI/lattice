import Mathlib
import Lattice.Lib.Attention.RealMaskFamily

/-!
# **掩码代数：`True` 是单位、合取可交换、合取幂等**（阶段 AA）

## 为什么需要这个文件

**第 997 轮排空 `Attention` 三槽后，剩下 `recovery` / `confluence` / `idempotence` 三槽仍是 `True`。**

**⇒ 本轮先判定它们属于哪种情形：库里有没有现成命题？答案是没有。**
**⇒ 但这不是「无法填」，而是「要先把它证出来」——因为这三条正是掩码作为**组合机制**的代数性质：**

| 槽 | 含义 | 对应事实 |
|:--|:--|:--|
| **`recovery`** | 时间可组合性 | **宽松阶段是单位**：`True ∧ m = m`——加上一个不加限制的阶段，原行为被**恢复** |
| **`confluence`** | 独立效应合流 | **合取可交换**：`m₁ ∧ m₂ = m₂ ∧ m₁`——两个独立掩码谁先谁后都一样 |
| **`idempotence`** | 幂等 | **合取幂等**：`m ∧ m = m`——重复施加同一限制是惰性的 |

**⇒ 三者合起来说明：掩码在 `(∧, True)` 下构成一个**交换幂等幺半群**。
这不是三个孤立的巧合，而是同一个结构的三条定律。**

## 一个刻意的取舍：先在**掩码层**陈述

**也可以把这三条直接写成 `maskedSoftmax` 的等式。但 `maskedSoftmax` 带 `[DecidableRel mask]` 实例参数，
改写掩码时实例也要跟着变，证明会退化为处理实例无关性。**

**⇒ 本文件先在**掩码层**陈述（纯 `Prop` 等式，无实例），
再额外给出 `idempotence` 的**输出层**推论作为示范——
说明掩码层的等式确实能传下去，而不只是关于布尔函数的空话。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`mask_and_true`** | **`True ∧ m = m`（单位律）** |
| **`mask_and_comm`** | **`m₁ ∧ m₂ = m₂ ∧ m₁`（交换律）** |
| **`mask_and_self`** | **`m ∧ m = m`（幂等律）** |
| **`mask_and_assoc`** | **`(m₁ ∧ m₂) ∧ m₃ = m₁ ∧ (m₂ ∧ m₃)`（结合律，用于说明它是半群）** |
| **`maskedSoftmax_and_self`** | **⭐⭐ 输出层推论：`maskedSoftmax (m ∧ m) s i = maskedSoftmax m s i`** | -/

namespace Lattice

/-- **⭐⭐ 单位律：`True` 与任何掩码合取还是那个掩码。**

**⇒ 这就是 `recovery`：一个**不加限制**的阶段被加上之后，原行为被恢复。** -/
theorem mask_and_true {n : ℕ} (m : Fin n → Fin n → Prop) :
    (fun i j => True ∧ m i j) = m := by
  funext i j
  exact propext ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- **⭐⭐ 交换律：两个独立掩码的合取与顺序无关。**

**⇒ 这就是 `confluence`：两处独立效应无论以什么次序施加，结果相同。** -/
theorem mask_and_comm {n : ℕ} (m₁ m₂ : Fin n → Fin n → Prop) :
    (fun i j => m₁ i j ∧ m₂ i j) = (fun i j => m₂ i j ∧ m₁ i j) := by
  funext i j
  exact propext ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **⭐⭐ 幂等律：把同一掩码合取两次等于一次。**

**⇒ 这就是 `idempotence`：重复施加同一限制不产生任何新效果。** -/
theorem mask_and_self {n : ℕ} (m : Fin n → Fin n → Prop) :
    (fun i j => m i j ∧ m i j) = m := by
  funext i j
  exact propext ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

/-- **结合律：合取可以任意加括号。**

**⇒ 加上交换律与单位律，掩码在 `(∧, True)` 下是**交换幂等幺半群**。** -/
theorem mask_and_assoc {n : ℕ} (m₁ m₂ m₃ : Fin n → Fin n → Prop) :
    (fun i j => (m₁ i j ∧ m₂ i j) ∧ m₃ i j)
      = (fun i j => m₁ i j ∧ (m₂ i j ∧ m₃ i j)) := by
  funext i j
  exact propext ⟨fun h => ⟨h.1.1, ⟨h.1.2, h.2⟩⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- **⭐⭐ 输出层推论：掩码层等式确实能传到 `maskedSoftmax` 上。**

**=> 这条是本节最要紧的一条：它排除「上面四条只是关于布尔函数的空话」这一可能。
取幂等律为例，`maskedSoftmax` 在 `m ∧ m` 与 `m` 上逐项相同，故结果作为函数相等。** -/
theorem maskedSoftmax_and_self {n : ℕ} (m : Fin n → Fin n → Prop) [DecidableRel m]
    (s : Fin n → ℝ) (i : Fin n) :
    maskedSoftmax (fun a b => m a b ∧ m a b) s i = maskedSoftmax m s i := by
  funext j
  simp only [maskedSoftmax, maskedDenom, and_self]

end Lattice
