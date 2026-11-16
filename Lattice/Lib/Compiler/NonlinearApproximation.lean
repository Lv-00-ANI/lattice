import Mathlib
import Lattice.Lib.Compiler.CarrierApproximation
import Lattice.Lib.Compiler.ReluLemmas

/-!
# 非线性的误差机制：**`x²` 与割线的偏差由二阶差分决定**（阶段 C，P8）

## 第 947 轮留下的唯一出路

**`two_walls` 证明了两道墙：**

1. **离散载体上 `ε < 1` 强制相等；**
**2. 嵌入 `ℝ` 后，线性族对 `x²` 有 `1/8` 的地板。**

**=> 本轮要证明第二道墙对**分段线性**族不存在。**

## 本文件实际交付了什么，以及**没有**交付什么

**交付：`x²` 与任意割线的偏差**恰为** `|(x-a)(x-(a+h))|`，**
**它在 `[a, a+h]` 上由 `h²/4` 控制。**

**=> 这就是「分段线性可以任意逼近」的**全部数学内容**：
取 `n` 等分，每片 `h = 1/n`，误差 `≤ 1/(4n²)`。**

**=> ⚠ 本文件**没有**把最后那一步「`1/(4n²)` 可任意小」证出来。
那是一个纯 `ℝ` 的 Archimedes 推理，我这一轮在它的
`div_le_iff₀` 形态上反复失败；与其塞进一个不完整的写法，
不如把它记成明确的下一步。**

**=> 因此本文件的定理是**有限**的但**确凿**的：二阶差分恒等式与 `h²/4` 界。
它们已经足够说明「线性族每片误差是**平方**下降，而线性族的整体地板是常数」。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`relu_is_max`** | **⭐ `Lattice.relu t = max t 0`** |
| **`chord_deviation`** | **⭐⭐ `x² - 割线 = (x-a)(x-(a+h))`（二阶差分）** |
| **`chord_error_bound`** | **⭐⭐ 该偏差 `≤ h²/4`** |
| **`linear_floor_vs_chord_scaling`** | **⭐⭐ 线性地板恒定 vs 割线误差随 `h` 平方缩小** | -/

namespace Lattice.Lib.Compiler.NonlinearApproximation

/-- **⭐ `Lattice.relu t = max t 0`（定义相等）。** -/
theorem relu_is_max (t : ℝ) : Lattice.relu t = max t 0 := rfl

/-- **⭐⭐ 割线偏差的精确形式（二阶差分）。**

**=> `x² - (过 `a` 与 `a+h` 的割线) = (x - a) * (x - (a + h))`。**

**=> 线性族在 `[0,1]` 上的误差是**常数** `1/8`；
而割线误差随片长 `h` **平方**缩小。**

**=> 这就是「非线性严格更强」的机制，而它不依赖任何 LATTICE 类型。** -/
theorem chord_deviation (a h x : ℝ) :
    x ^ 2 - (a * x + (a + h) * x - a * (a + h)) = (x - a) * (x - (a + h)) := by
  ring

/-- **⭐⭐ 割线偏差的绝对值由 `h²/4` 控制。**

**=> 在中点 `a + h/2` 取等号。**

**=> 于是 `n` 等分（`h = 1/n`）时每片误差 `≤ 1/(4n²)`。** -/
theorem chord_error_bound (a h x : ℝ) (hh : 0 ≤ h) (hx : x ∈ Set.Icc a (a + h)) :
    |x ^ 2 - (a * x + (a + h) * x - a * (a + h))| ≤ h ^ 2 / 4 := by
  rw [chord_deviation]
  obtain ⟨hxa, hxb⟩ := hx
  have hneg : (x - a) * (x - (a + h)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have habs : |(x - a) * (x - (a + h))| = -((x - a) * (x - (a + h))) := abs_of_nonpos hneg
  rw [habs]
  have hexp : -((x - a) * (x - (a + h))) = (h / 2) ^ 2 - (x - (a + h / 2)) ^ 2 := by ring
  have hsq : (0 : ℝ) ≤ (x - (a + h / 2)) ^ 2 := sq_nonneg _
  have hmain : -((x - a) * (x - (a + h))) ≤ h ^ 2 / 4 := by
    rw [hexp]
    nlinarith [hsq]
  exact hmain

/-- **⭐⭐ 两条曲线：线性地板恒定，割线误差随 `h` 平方缩小。**

**=> 陈述（并列）：**

1. **线性族对 `x²` 的误差下界 `1/8`（与任何参数无关）；**
2. **割线在片长 `h` 上的误差 `≤ h²/4`（随 `h` 平方缩小）。**

**=> 这是「非线性严格更强」在**误差数量级**层面的精确对照，
而不是一个完整的逼近定理（那是下一步）。** -/
theorem linear_floor_vs_chord_scaling :
    (∀ a b : ℝ, ∃ x ∈ Set.Icc (0 : ℝ) 1, 1 / 8 ≤ |x ^ 2 - (a * x + b)|) ∧
      (∀ a h x : ℝ, 0 ≤ h → x ∈ Set.Icc a (a + h) →
        |x ^ 2 - (a * x + (a + h) * x - a * (a + h))| ≤ h ^ 2 / 4) :=
  ⟨Lattice.Lib.Compiler.LowerBound.target_not_attainable, chord_error_bound⟩

end Lattice.Lib.Compiler.NonlinearApproximation
