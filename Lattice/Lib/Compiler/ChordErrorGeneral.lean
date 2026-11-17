import Mathlib
import Lattice.Lib.Compiler.ChordGeneral

/-!
# **一般弦的误差界**：从 `x²` 泛化到满足帐篷界的一切函数（阶段 F，P8 边界 3）

## 泛化的是什么

**第 948 轮的**专用弦误差界**（在 `NonlinearApproximation`）只对 `f = ·²` 成立：**

```lean
theorem <专用版本> (a h x : ℝ) (hh : 0 ≤ h) (hx : x ∈ Icc a (a+h)) :
    |x^2 - (a*x + (a+h)*x - a*(a+h))| ≤ h^2 / 4
```

**它依赖一个**仅对二次函数成立**的因式分解：`x² - 割线 = (x-a)(x-b)`。**

**=> 对一般 `f`，这个因式分解没有对应物。**

**本文件的解法：把那个因式分解**当成假设**。**
**=> 若 `f` 的弦误差被**帐篷函数** `M·(x-a)(b-x)` 控制，则误差界 `M·(b-a)²/4` 成立。**

**=> 这不是把定理变弱，而是把它**分离**成：**

1. **一条**纯代数**的引理（帐篷下的面积 ≤ `(b-a)²/4`，即 AM–GM）；**
2. **一条**假设驱动**的一般定理（任何满足帐篷界的 `f` 都继承该界）。**

**=> 而二次函数**实例化**该假设（`M = 1`），故旧结果被**重新推出**（`chord_error_sq_rederived`）。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`tent_le_quarter`** | **⭐⭐ `M·(x-a)(b-x) ≤ M·(b-a)²/4`（AM–GM）** |
| **`chord_error_of_tent_bound`** | **⭐⭐⭐ 任何满足帐篷界的 `f` 都有 `M·(b-a)²/4` 的弦误差界** |
| **`sq_chord_error_eq_tent`** | **⭐⭐ `x²` 的弦误差**恰等于**帐篷（`M = 1`）** |
| **`chord_error_sq_rederived`** | **⭐⭐⭐ 从一般定理**重新推出**旧的专用界** |

## 为什么第 4 条是关键的诚实性检查

**若泛化后的定理推不出旧定理，则它就不是泛化，而是**另起一套**。**
**=> `chord_error_sq_rederived` 证明：旧结果是新定理在 `M = 1, f = x²` 时的**实例**。**

**=> 于是第 948 轮的 `1/(4n²)`、第 949 轮的 `quarter_inv_sq_tends_to_zero`、
第 959 轮的一致逼近，全部**原样成立**，且现在有了对**一般 `f`** 的推广。** -/

namespace Lattice.Lib.Compiler.ChordErrorGeneral

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.ChordGeneral

/-- **⭐⭐ 帐篷下的「面积」不超过 `(b-a)²/4`。**

**=> 这是 AM–GM：设 `u = x-a`、`v = b-x`，则 `u + v = b-a`，
而 `((u+v)/2)² - u·v = (u-v)²/4 ≥ 0`。**

**=> 纯代数，无导数、无中值定理。** -/
theorem tent_le_quarter (a b x M : ℝ) (hab : a ≤ b) (hx : x ∈ Icc a b) (hM : 0 ≤ M) :
    M * ((x - a) * (b - x)) ≤ M * ((b - a) ^ 2 / 4) := by
  have hkey : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    have hsq : (0 : ℝ) ≤ ((a + b) - 2 * x) ^ 2 := sq_nonneg _
    nlinarith [hsq]
  exact mul_le_mul_of_nonneg_left hkey hM

/-- **⭐⭐⭐ 一般弦误差界：若 `f` 的弦误差被帐篷 `M·(x-a)(b-x)` 控制，
则它被 `M·(b-a)²/4` 控制。**

**=> 这条定理**对任意 `f` 成立**，不依赖 `f` 的具体形式、不需要可微性。**

**=> 它把「二阶曲率」的作用**完全封装**进那个帐篷假设里。** -/
theorem chord_error_of_tent_bound (f : ℝ → ℝ) (a b M : ℝ) (hab : a < b) (hM : 0 ≤ M)
    (htent : ∀ x, x ∈ Icc a b →
      |f x - (chordOf f a b).eval x| ≤ M * ((x - a) * (b - x))) :
    ∀ x ∈ Icc a b, |f x - (chordOf f a b).eval x| ≤ M * ((b - a) ^ 2 / 4) := by
  intro x hx
  exact le_trans (htent x hx) (tent_le_quarter a b x M (le_of_lt hab) hx hM)

/-- **⭐⭐ `x²` 的弦误差**恰等于**帐篷（`M = 1`）。**

**=> `x² - 割线 = (x-a)(x-b)`，而在 `[a,b]` 上它 `≤ 0`，
故绝对值 `= -((x-a)(x-b)) = (x-a)(b-x)`。**

**=> 这就是第 948 轮那个因式分解的**精确定位**：它是「帐篷界在 `M = 1` 时取等」。** -/
theorem sq_chord_error_eq_tent (a b x : ℝ) (hab : a < b) (hx : x ∈ Icc a b) :
    |x ^ 2 - (chordOf (fun t : ℝ => t ^ 2) a b).eval x| = (x - a) * (b - x) := by
  have hne : a ≠ b := ne_of_lt hab
  rw [chordOf_sq a b hne, chordSegment_eval]
  have hfac : x ^ 2 - (a * x + b * x - a * b) = (x - a) * (x - b) := by ring
  rw [hfac]
  have hxa : (0 : ℝ) ≤ x - a := by linarith [hx.1]
  have hxb : x - b ≤ 0 := by linarith [hx.2]
  have hprod : (x - a) * (x - b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hxa hxb
  rw [abs_of_nonpos hprod]
  ring

/-- **⭐⭐⭐ 旧结果是新定理的**实例**：从 `chord_error_of_tent_bound` 重新推出 `(b-a)²/4` 界。**

**=> 取 `f = ·²`、`M = 1`。帐篷假设由 `sq_chord_error_eq_tent` 提供（此时取等）。**

**=> 这条定理是对本轮泛化的**诚实性检查**：
**泛化必须能推出旧结果，否则它只是另起一套。**
**=> 而它证明了这一点：第 948 轮的界原样回来。** -/
theorem chord_error_sq_rederived (a b x : ℝ) (hab : a < b) (hx : x ∈ Icc a b) :
    |x ^ 2 - (chordOf (fun t : ℝ => t ^ 2) a b).eval x| ≤ (b - a) ^ 2 / 4 := by
  have htent : ∀ y ∈ Icc a b,
      |(fun t : ℝ => t ^ 2) y - (chordOf (fun t : ℝ => t ^ 2) a b).eval y|
        ≤ 1 * ((y - a) * (b - y)) := by
    intro y hy
    rw [sq_chord_error_eq_tent a b y hab hy]
    ring_nf
    exact le_refl _
  have h := chord_error_of_tent_bound (fun t : ℝ => t ^ 2) a b 1 hab zero_le_one htent x hx
  simpa using h

end Lattice.Lib.Compiler.ChordErrorGeneral
