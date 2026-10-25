import Mathlib

/-!
# LATTICE: 多项式插值（Lagrange 基的 cardinal 性质）

神经网络里"插值"无处不在：位置编码的线性插值、核方法的 Nyström 重构、激活函数的
多项式逼近、以及优化里用**弦**近似凸函数。本文件把最基础、最不含分析成分的那部分
形式化：**Lagrange 基的 cardinal 性质**——

    lagrange x i t = ∏_{j ≠ i} (t - x j) / (x i - x j)

则（节点互异时）

    lagrange x i (x j) = if i = j then 1 else 0        （cardinal）
    ∑ i, f (x i) · lagrange x i (x k) = f (x k)        （节点处精确重构）

第二条是**任意** `f : n → ℝ`（不要求 `f` 是多项式）在节点上的插值恒等式，
即"插值算子在节点上等于恒等"。另外给出 `n = 2` 的显式两点线性插值公式及其
端点正确性（`linInterp_left` / `linInterp_right`）。

**诚实边界**：
- 本文件**只做节点处的 cardinal 性质**；`∑ i, lagrange x i t = 1` 对所有 `t`
  的恒等式（"单位分解"）需要多项式环上的恒等论证，标为 **未做**；
- 插值误差界（Lebesgue 常数、等距节点的 Runge 现象、凸函数的弦误差 `O(h²)`）
  **未做**，那需要中值定理与凸性工具；
- 唯一性（次数 ≤ n-1 且在两两互异节点上取同值的多项式相等）**未做**（需要
  `Polynomial` 的根计数引理）；
- 节点互异是本文件全部结论的**必要假设**（否则分母为零）。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

open Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Lagrange 基函数：`lagrange x i t = ∏_{j ≠ i} (t - x j)/(x i - x j)`。 -/
def lagrange (x : n → ℝ) (i : n) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (t - x j) / (x i - x j)

/-- 节点互异时，`lagrange x i` 在自身节点处取 1。 -/
theorem lagrange_at_self {x : n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j) (i : n) :
    lagrange x i (x i) = 1 := by
  unfold lagrange
  refine Finset.prod_eq_one ?_
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hne : x i - x j ≠ 0 := sub_ne_zero.mpr (Ne.symm (hx j i hji))
  exact div_self hne

/-- 节点互异时，`lagrange x i` 在其它节点处取 0（其实只需 `i ≠ j`：分子含零因子）。 -/
theorem lagrange_at_other {x : n → ℝ} {i j : n} (hij : i ≠ j) :
    lagrange x i (x j) = 0 := by
  unfold lagrange
  have hmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  exact Finset.prod_eq_zero hmem (by simp)

/-- Cardinal 性质：`lagrange x i (x j) = if i = j then 1 else 0`。 -/
theorem lagrange_cardinal {x : n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j) (i j : n) :
    lagrange x i (x j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [lagrange_at_self hx i]
  · simp [h, lagrange_at_other h]

/-- **主定理**：插值算子在节点上等于恒等——任意 `f` 在节点处被精确重构。 -/
theorem lagrange_interpolates {x : n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (f : n → ℝ) (k : n) :
    ∑ i, f i * lagrange x i (x k) = f k := by
  have hkey : ∀ i, f i * lagrange x i (x k) = if i = k then f k else 0 := by
    intro i
    by_cases hi : i = k
    · rw [hi, lagrange_at_self hx k, mul_one, if_pos rfl]
    · rw [lagrange_at_other hi, mul_zero, if_neg hi]
  calc ∑ i, f i * lagrange x i (x k)
      = ∑ i, if i = k then f k else 0 := Finset.sum_congr rfl (fun i _ => hkey i)
    _ = f k := by simp

/-- 单位分解的节点版本（由主定理取 `f ≡ 1`）。 -/
theorem lagrange_sum_at_node {x : n → ℝ} (hx : ∀ i j, i ≠ j → x i ≠ x j) (k : n) :
    ∑ i, lagrange x i (x k) = 1 := by
  have h := lagrange_interpolates hx (fun _ => (1 : ℝ)) k
  simpa using h

/-! ## 两点线性插值的显式公式 -/

/-- 两点线性插值：过 `(x0, y0)` 与 `(x1, y1)` 的直线在 `t` 处的值。 -/
def linInterp (x0 x1 y0 y1 t : ℝ) : ℝ :=
  y0 * (t - x1) / (x0 - x1) + y1 * (t - x0) / (x1 - x0)

/-- 左端点正确性。 -/
theorem linInterp_left {x0 x1 y0 y1 : ℝ} (h : x0 ≠ x1) :
    linInterp x0 x1 y0 y1 x0 = y0 := by
  unfold linInterp
  have h1 : x0 - x1 ≠ 0 := sub_ne_zero.mpr h
  have h2 : x1 - x0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp

/-- 右端点正确性。 -/
theorem linInterp_right {x0 x1 y0 y1 : ℝ} (h : x0 ≠ x1) :
    linInterp x0 x1 y0 y1 x1 = y1 := by
  unfold linInterp
  have h1 : x0 - x1 ≠ 0 := sub_ne_zero.mpr h
  have h2 : x1 - x0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp

/-- 斜截式改写：`linInterp = y0 + (y1 - y0)·(t - x0)/(x1 - x0)`。 -/
theorem linInterp_slope_form {x0 x1 y0 y1 t : ℝ} (h : x0 ≠ x1) :
    linInterp x0 x1 y0 y1 t = y0 + (y1 - y0) * (t - x0) / (x1 - x0) := by
  unfold linInterp
  have h1 : x0 - x1 ≠ 0 := sub_ne_zero.mpr h
  have h2 : x1 - x0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- 重心（凸组合）形式：`linInterp = ((x1-t)·y0 + (t-x0)·y1)/(x1-x0)`。 -/
theorem linInterp_convex_form {x0 x1 y0 y1 t : ℝ} (h : x0 ≠ x1) :
    linInterp x0 x1 y0 y1 t = ((x1 - t) * y0 + (t - x0) * y1) / (x1 - x0) := by
  unfold linInterp
  have h1 : x0 - x1 ≠ 0 := sub_ne_zero.mpr h
  have h2 : x1 - x0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  field_simp
  ring

/-- 凸组合形式的意义：`t ∈ [x0,x1]`（`x0 < x1`）时插值值是两端点的凸组合，
故落在两端点值之间。这是"弦夹在函数值与端点之间"类论证的代数内核。 -/
theorem linInterp_between {x0 x1 y0 y1 t : ℝ} (h : x0 < x1)
    (ht0 : x0 ≤ t) (ht1 : t ≤ x1) :
    min y0 y1 ≤ linInterp x0 x1 y0 y1 t ∧ linInterp x0 x1 y0 y1 t ≤ max y0 y1 := by
  rw [linInterp_convex_form (ne_of_lt h)]
  have hden : 0 < x1 - x0 := by linarith
  have hw0 : 0 ≤ (x1 - t) / (x1 - x0) := div_nonneg (by linarith) (le_of_lt hden)
  have hw1 : 0 ≤ (t - x0) / (x1 - x0) := div_nonneg (by linarith) (le_of_lt hden)
  have hsum : (x1 - t) / (x1 - x0) + (t - x0) / (x1 - x0) = 1 := by
    field_simp
  have hrewrite : ((x1 - t) * y0 + (t - x0) * y1) / (x1 - x0)
      = ((x1 - t) / (x1 - x0)) * y0 + ((t - x0) / (x1 - x0)) * y1 := by
    field_simp
  rw [hrewrite]
  constructor
  · calc min y0 y1
        = ((x1 - t) / (x1 - x0)) * min y0 y1 + ((t - x0) / (x1 - x0)) * min y0 y1 := by
          rw [← add_mul, hsum, one_mul]
      _ ≤ ((x1 - t) / (x1 - x0)) * y0 + ((t - x0) / (x1 - x0)) * y1 :=
          add_le_add (mul_le_mul_of_nonneg_left (min_le_left y0 y1) hw0)
            (mul_le_mul_of_nonneg_left (min_le_right y0 y1) hw1)
  · calc ((x1 - t) / (x1 - x0)) * y0 + ((t - x0) / (x1 - x0)) * y1
        ≤ ((x1 - t) / (x1 - x0)) * max y0 y1 + ((t - x0) / (x1 - x0)) * max y0 y1 :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left y0 y1) hw0)
            (mul_le_mul_of_nonneg_left (le_max_right y0 y1) hw1)
      _ = max y0 y1 := by
          rw [← add_mul, hsum, one_mul]

end Lattice
