import Mathlib
import Lattice.Lib.Compiler.ConvexityChord

/-!
# **二阶导数界**：`|f''| ≤ M ⟹ 弦误差 ≤ M(b−a)²/8`（阶段 H，P8 边界 3 最后一步）

## 本文件闭合第 962 轮记下的「剩下的一层」

**第 962 轮的 `chord_error_of_semiconvex` 需要一对半凸性假设 `h1`、`h2`。
本文件用 Mathlib 的 `convexOn_of_deriv2_nonneg` 从二阶导数界**产出**它们。**

**=> 整条链因此闭合：**

```
|f''| ≤ M  ──(convexOn_of_deriv2_nonneg)──▶  平移后的凸性
           ──(tent_of_semiconvex)──▶  帐篷界 (M/2)(x-a)(b-x)
           ──(chord_error_of_tent_bound)──▶  M(b-a)²/8
```

## 三个技术障碍及其解法

| 障碍 | 解法 |
|:--|:--|
| **`rw` 无法穿透 `deriv^[2]` 展开后的 lambda** | **先用 `funext` 把一阶导数写成**显式函数**，再取二阶** |
| **`deriv^[2]` 是 `iteratedDeriv` 记号，`simp` 展不开** | **用 `show` 把目标强制写成 `deriv (deriv _) _`** |
| **半凹分支若逐条重做会冗长** | **抽象成 `convex_shift_of_lower`，用 `g` 与 `-f` 各调一次** |

**★ 签名陷阱：`deriv_const_mul (c : 𝔸) (hd : DifferentiableAt 𝕜 d x)` ——
`c` 在**前面**，不是证明在前的常见形状。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`deriv_shift_eq`** | **⭐ 一阶导数显式形式** |
| **`iter_deriv_shift_eq`** | **⭐⭐ `deriv^[2]` 平移恒等式** |
| **`deriv_neg_eq`** / **`iter_deriv_neg_eq`** | **⭐⭐ 取负的对应形式** |
| **`convex_shift_of_lower`** | **⭐⭐⭐ 核心：`-M ≤ g''` ⟹ `g + (M/2)t²` 凸** |
| **`chord_error_of_second_deriv_bound`** | **⭐⭐⭐ **主定理**：`M(b−a)²/8`** | -/

namespace Lattice.Lib.Compiler.SecondDerivBound

open Set
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.ConvexityChord

/-- **⭐ 一阶导数的显式形式：`deriv (f + c·t²) = deriv f + 2c·t`。** -/
theorem deriv_shift_eq (f : ℝ → ℝ) (c : ℝ) (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => f t + c * t ^ 2) = fun y => deriv f y + 2 * c * y := by
  funext y
  rw [deriv_add (hf.differentiableAt) (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => c * t ^ 2) y)]
  congr 1
  rw [deriv_const_mul c (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => t ^ 2) y)]
  rw [deriv_pow]
  norm_num
  ring

/-- **⭐⭐ `deriv^[2]` 的平移恒等式：`(f + c·t²)'' = f'' + 2c`。** -/
theorem iter_deriv_shift_eq (f : ℝ → ℝ) (c x : ℝ) (hf : Differentiable ℝ f)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    deriv^[2] (fun t : ℝ => f t + c * t ^ 2) x = deriv^[2] f x + 2 * c := by
  have h1 := deriv_shift_eq f c hf
  show deriv (deriv (fun t : ℝ => f t + c * t ^ 2)) x = deriv (deriv f) x + 2 * c
  rw [h1]
  rw [deriv_add hf' (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => 2 * c * y) x)]
  congr 1
  rw [deriv_const_mul (2 * c) (by fun_prop : DifferentiableAt ℝ (fun y : ℝ => y) x)]
  simp

/-- **⭐⭐ 取负的一阶导数：`deriv (-f) = -(deriv f)`。** -/
theorem deriv_neg_eq (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => -(f t)) = fun y => -(deriv f y) := by
  funext y
  exact (hf.differentiableAt.hasDerivAt.neg).deriv

/-- **⭐⭐ `deriv^[2]` 的取负恒等式：`(-f)'' = -f''`。** -/
theorem iter_deriv_neg_eq (f : ℝ → ℝ) (x : ℝ) (hf : Differentiable ℝ f)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    deriv^[2] (fun t : ℝ => -(f t)) x = -(deriv^[2] f x) := by
  have h1 := deriv_neg_eq f hf
  show deriv (deriv (fun t : ℝ => -(f t))) x = -(deriv (deriv f) x)
  rw [h1]
  exact (hf'.hasDerivAt.neg).deriv

/-- **⭐⭐⭐ 核心辅助：若 `g'' ≥ -M`（在开区间上），则 `g t + (M/2)·t²` 在 `[a,b]` 上凸。**

**=> 由 `convexOn_of_deriv2_nonneg`：只需
`deriv^[2] (g + (M/2)t²) = deriv^[2] g + M ≥ 0`。**

**=> 半凸（上界）与半凹（下界）各用它一次：前者取 `g = f`，后者取 `g = -f`。** -/
theorem convex_shift_of_lower (a b M : ℝ) (hab : a < b) (hM : 0 ≤ M)
    (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (hg' : DifferentiableOn ℝ (deriv g) (interior (Icc a b)))
    (hge : ∀ x ∈ interior (Icc a b), -M ≤ deriv^[2] g x) :
    ConvexOn ℝ (Icc a b) (fun t => g t + (M / 2) * t ^ 2) := by
  refine convexOn_of_deriv2_nonneg (convex_Icc a b) ?_ ?_ ?_ ?_
  · exact hg.continuous.continuousOn.add (by fun_prop)
  · exact hg.differentiableOn.add (by fun_prop)
  · have hshift : deriv (fun t : ℝ => g t + (M / 2) * t ^ 2) = fun y => deriv g y + M * y := by
      rw [deriv_shift_eq g (M / 2) hg]
      funext y
      ring
    rw [hshift]
    exact hg'.add (by fun_prop)
  · intro x hx
    have hx' : x ∈ Ioo a b := by rw [← interior_Icc]; exact hx
    have hfin : DifferentiableAt ℝ (deriv g) x := by
      refine hg'.differentiableAt ?_
      rw [interior_Icc]
      exact IsOpen.mem_nhds isOpen_Ioo hx'
    rw [iter_deriv_shift_eq g (M / 2) x hg hfin]
    have h := hge x hx
    linarith

/-- **⭐⭐⭐ 主定理：`|f''| ≤ M` 在开区间上 ⟹ 弦误差 `≤ M(b−a)²/8`。**

**=> 这是线性插值误差的**经典界** `(x₁−x₀)²/8 · max|f''|`。**

**=> 至此 P8「一般误差界」链条闭合：不再有未证的一层。** -/
theorem chord_error_of_second_deriv_bound (f : ℝ → ℝ) (a b M : ℝ) (hab : a < b) (hM : 0 ≤ M)
    (hf : Differentiable ℝ f)
    (hf' : DifferentiableOn ℝ (deriv f) (interior (Icc a b)))
    (hM2 : ∀ x ∈ interior (Icc a b), |deriv^[2] f x| ≤ M) :
    ∀ x ∈ Icc a b, |f x - (chordOf f a b).eval x| ≤ M * (b - a) ^ 2 / 8 := by
  intro x hx
  -- upper side: `f'' ≥ -M` gives convexity of `f + (M/2)t²`
  have h1 : ConvexOn ℝ (Icc a b) (fun t => f t + (M / 2) * t ^ 2) :=
    convex_shift_of_lower a b M hab hM f hf hf'
      (fun y hy => (abs_le.mp (hM2 y hy)).1)
  -- lower side: `(-f)'' = -f'' ≥ -M` gives convexity of `-f + (M/2)t²`
  have h2 : ConvexOn ℝ (Icc a b) (fun t => -(f t) + (M / 2) * t ^ 2) := by
    have hneg' : DifferentiableOn ℝ (deriv (fun t : ℝ => -(f t))) (interior (Icc a b)) := by
      rw [deriv_neg_eq f hf]
      exact hf'.neg
    refine convex_shift_of_lower a b M hab hM (fun t => -(f t)) hf.neg hneg' ?_
    intro y hy
    have hy' : y ∈ Ioo a b := by rw [← interior_Icc]; exact hy
    have hfin : DifferentiableAt ℝ (deriv f) y := by
      refine hf'.differentiableAt ?_
      rw [interior_Icc]
      exact IsOpen.mem_nhds isOpen_Ioo hy'
    rw [iter_deriv_neg_eq f y hf hfin]
    have hle : deriv^[2] f y ≤ M := (abs_le.mp (hM2 y hy)).2
    linarith
  exact chord_error_of_semiconvex f a b M x hab hM h1 h2 hx

end Lattice.Lib.Compiler.SecondDerivBound
