import Mathlib
import Lattice.Lib.Compiler.ChordErrorGeneral

/-!
# **凸性 ⟹ 帐篷界**：从半凸/半凹对推出弦误差（阶段 G，P8 边界 3 最后一步）

## 本文件补的是哪一环

**第 961 轮的 `chord_error_of_tent_bound` 把「帐篷假设」当作**输入**，
并明确记下：从 `|f''| ≤ M` 推出该假设**仍开放**。**

**本文件把那一步拆成**两层**，并完成**第一层**：**

| 层 | 内容 | 状态 |
|:--|:--|:--|
| **1** | **半凸/半凹**对** ⟹ 帐篷界** | **本文件，已证** |
| **2** | `|f''| ≤ M` ⟹ 半凸/半凹对 | 需 `convexOn_of_deriv2_nonneg` + 迭代导数计算，见 §5 |

**=> 于是「开放」从「一整步分析」缩小为「一层导数计算」。**

## 路线（为什么用凸性而不是 Rolle）

**教科书路线是 Rolle 定理连用两次（`φ(t) = f t - p t - K(t-a)(t-b)` 有三个零点）。
那需要构造 Lagrange 余项，形式化成本高。**

**本文件用**等价的半凸性**路线，它只需 Mathlib 已有的一个引理：**

**`ConvexOn.slope_mono_adjacent`：凸函数上 `slope(a,x) ≤ slope(x,b)`。**
**=> 交叉相乘即得「凸函数图像在弦下」（`convex_le_chord`）。**

**对 `F t = f t + (M/2)·t²` 与 `G t = -f t + (M/2)·t²` 各用一次，就得到**双侧**帐篷界。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`chord_eval_eq_div`** | **⭐ 弦值的分式形式** |
| **`convex_le_chord`** | **⭐⭐⭐ 凸 ⟹ 图像在弦下（本项目的通用引理）** |
| **`tent_of_semiconvex`** | **⭐⭐⭐ 半凸/半凹对 ⟹ 帐篷界 `(M/2)(x-a)(b-x)`** |
| **`chord_error_of_semiconvex`** | **⭐⭐⭐ 合成为经典结论 `M(b-a)²/8`** | -/

namespace Lattice.Lib.Compiler.ConvexityChord

open Set
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.ChordErrorGeneral

/-- **⭐ 弦值的分式形式：`(g b·(x-a) + g a·(b-x)) / (b-a)`。**

**=> 这个形式把弦关于 `g` 的关系**显式化**，使「加上一个二次项」可以直接展开。** -/
theorem chord_eval_eq_div (g : ℝ → ℝ) (a b x : ℝ) (hab : a < b) :
    (chordOf g a b).eval x = (g b * (x - a) + g a * (b - x)) / (b - a) := by
  unfold chordOf Segment.eval chordSlope
  have hba : b - a ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **⭐⭐⭐ 凸函数图像在弦下。**

**=> 由 `ConvexOn.slope_mono_adjacent`（`slope(a,x) ≤ slope(x,b)`）交叉相乘得到。**

**=> 这是本项目的**通用引理**：它把「凸性」与「弦」直接连起来，
而不经过任何 LagTangre 余项构造。** -/
theorem convex_le_chord (f : ℝ → ℝ) (a b x : ℝ) (hab : a < b)
    (hconv : ConvexOn ℝ (Icc a b) f) (hx : x ∈ Icc a b) :
    f x ≤ (chordOf f a b).eval x := by
  have ha : a ∈ Icc a b := ⟨le_refl a, le_of_lt hab⟩
  have hb : b ∈ Icc a b := ⟨le_of_lt hab, le_refl b⟩
  rcases eq_or_lt_of_le hx.1 with hxa | hax
  · rw [← hxa, chordOf_eval_left]
  · rcases eq_or_lt_of_le hx.2 with hxb | hxb
    · rw [hxb]
      exact le_of_eq (chordOf_eval_right f a b (ne_of_lt hab)).symm
    · have hs := hconv.slope_mono_adjacent ha hb hax hxb
      have hxa' : (0 : ℝ) < x - a := by linarith
      have hbx' : (0 : ℝ) < b - x := by linarith
      have hba : (0 : ℝ) < b - a := by linarith
      have hcross : (f x - f a) * (b - x) ≤ (f b - f x) * (x - a) :=
        (div_le_div_iff hxa' hbx').mp hs
      have hkey : f x * (b - a) ≤ f b * (x - a) + f a * (b - x) := by linarith [hcross]
      rw [chord_eval_eq_div f a b x hab, le_div_iff₀ hba]
      linarith [hkey]

/-- **⭐ 二次函数的弦恰是 `(a+b)·x - a·b`。**

**=> 这是 `chordSegment` 的求值，用分式形式写出以便与二次项合并。** -/
theorem sq_chord_div (a b x : ℝ) (hab : a < b) :
    (b ^ 2 * (x - a) + a ^ 2 * (b - x)) / (b - a) = (a + b) * x - a * b := by
  have hba : b - a ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **⭐⭐⭐ 半凸/半凹对 ⟹ **帐篷界**。**

**=> 陈述：若 `F t = f t + (M/2)t²` 与 `G t = -f t + (M/2)t²` 都在 `[a,b]` 上凸，
则 `|f x - 弦(x)| ≤ (M/2)·(x-a)(b-x)`。**

**=> 这是**双侧**估计：`F` 的凸性给上界，`G` 的凸性给下界。** -/
theorem tent_of_semiconvex (f : ℝ → ℝ) (a b M x : ℝ) (hab : a < b) (hM : 0 ≤ M)
    (h1 : ConvexOn ℝ (Icc a b) (fun t => f t + (M / 2) * t ^ 2))
    (h2 : ConvexOn ℝ (Icc a b) (fun t => -(f t) + (M / 2) * t ^ 2))
    (hx : x ∈ Icc a b) :
    |f x - (chordOf f a b).eval x| ≤ (M / 2) * ((x - a) * (b - x)) := by
  have hba : b - a ≠ 0 := ne_of_gt (by linarith)
  -- upper bound, from convexity of F
  have hF := convex_le_chord (fun t => f t + (M / 2) * t ^ 2) a b x hab h1 hx
  rw [chord_eval_eq_div (fun t => f t + (M / 2) * t ^ 2) a b x hab] at hF
  have hFsplit : ((f b + (M / 2) * b ^ 2) * (x - a) + (f a + (M / 2) * a ^ 2) * (b - x)) / (b - a)
      = (f b * (x - a) + f a * (b - x)) / (b - a) + (M / 2) * ((a + b) * x - a * b) := by
    rw [← sq_chord_div a b x hab]
    field_simp
    ring
  rw [hFsplit, ← chord_eval_eq_div f a b x hab] at hF
  have hupper : f x - (chordOf f a b).eval x ≤ (M / 2) * ((x - a) * (b - x)) := by
    have expand : (M / 2) * ((a + b) * x - a * b) - (M / 2) * x ^ 2
        = (M / 2) * ((x - a) * (b - x)) := by ring
    linarith [hF, expand]
  -- lower bound, from convexity of G
  have hG := convex_le_chord (fun t => -(f t) + (M / 2) * t ^ 2) a b x hab h2 hx
  rw [chord_eval_eq_div (fun t => -(f t) + (M / 2) * t ^ 2) a b x hab] at hG
  have hGsplit : ((-(f b) + (M / 2) * b ^ 2) * (x - a) + (-(f a) + (M / 2) * a ^ 2) * (b - x)) / (b - a)
      = -((f b * (x - a) + f a * (b - x)) / (b - a)) + (M / 2) * ((a + b) * x - a * b) := by
    rw [← sq_chord_div a b x hab]
    field_simp
    ring
  rw [hGsplit, ← chord_eval_eq_div f a b x hab] at hG
  have hlower : -((M / 2) * ((x - a) * (b - x))) ≤ f x - (chordOf f a b).eval x := by
    have expand : (M / 2) * ((a + b) * x - a * b) - (M / 2) * x ^ 2
        = (M / 2) * ((x - a) * (b - x)) := by ring
    linarith [hG, expand]
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- **⭐⭐⭐ 经典结论：`M(b-a)²/8`。**

**=> 把 `tent_of_semiconvex` 交给第 961 轮的 `chord_error_of_tent_bound`，
帐篷常数取 `M/2`，于是 `(M/2)·(b-a)²/4 = M(b-a)²/8`。**

**=> 这正是教科书与文献中的线性插值误差界 `(x₁-x₀)²/8 · max|f''|`。**

**=> 于是第 961 轮记下的「帐篷假设从何而来」有了答案：
它来自**半凸性**，而半凸性来自二阶导数下界（见 §5 的剩余一层）。** -/
theorem chord_error_of_semiconvex (f : ℝ → ℝ) (a b M x : ℝ) (hab : a < b) (hM : 0 ≤ M)
    (h1 : ConvexOn ℝ (Icc a b) (fun t => f t + (M / 2) * t ^ 2))
    (h2 : ConvexOn ℝ (Icc a b) (fun t => -(f t) + (M / 2) * t ^ 2))
    (hx : x ∈ Icc a b) :
    |f x - (chordOf f a b).eval x| ≤ M * (b - a) ^ 2 / 8 := by
  have htent : ∀ y ∈ Icc a b,
      |f y - (chordOf f a b).eval y| ≤ (M / 2) * ((y - a) * (b - y)) :=
    fun y hy => tent_of_semiconvex f a b M y hab hM h1 h2 hy
  have h := chord_error_of_tent_bound f a b (M / 2) hab (by linarith) htent x hx
  have heq : (M / 2) * ((b - a) ^ 2 / 4) = M * (b - a) ^ 2 / 8 := by ring
  linarith [h, heq.le, heq.ge]

/-! ## 5. 剩下的**一层**：从 `|f''| ≤ M` 到半凸对

**本文件把第 961 轮记下的「帐篷假设从何而来」缩小为一层导数计算。**
**=> 剩余工作**不是**开放式缺口，而是**一个已知配方**：**

**Mathlib 已有**
`Analysis/Convex/Deriv.lean:212` 的
`convexOn_of_deriv2_nonneg`：**

```
(hD : Convex ℝ D) (hf : ContinuousOn f D)
(hf' : DifferentiableOn ℝ f (interior D))
(hf'' : DifferentiableOn ℝ (deriv f) (interior D))
(hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f
```

**于是第 2 层的形状是：**

1. **对 `F t = f t + (M/2)·t²` 用 `convexOn_of_deriv2_nonneg`，**
   **需要 `deriv^[2] F x = deriv^[2] f x + M ≥ 0`（由 `|f''| ≤ M`）；**
2. **对 `G t = -f t + (M/2)·t²` 同样，需要 `deriv^[2] G x = -deriv^[2] f x + M ≥ 0`；**
3. **两者合起来给出 `h1` 与 `h2`，再交给 `chord_error_of_semiconvex`。**

**=> 唯一未做的技术点是第 1、2 条的**迭代导数计算**
`deriv^[2] (fun t => f t + c·t²) = deriv^[2] f + 2c`
（`deriv_add`、`deriv_const_mul`、`deriv_pow` 的组合，属机械工作）。**

**=> 因此本文件与第 961 轮的合取给出：**
**「`|f''| ≤ M` ⟹ 弦误差 `≤ M(b-a)²/8`」只差那条导数恒等式。** -/

end Lattice.Lib.Compiler.ConvexityChord
