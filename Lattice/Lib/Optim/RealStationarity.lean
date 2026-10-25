import Mathlib

/-!
# LATTICE: P0 标量驻点定理 —— 平方损失驻点 ⟺ 满足点

调研（research/embedding/README.md §4 P0）的最小版本：
一致标量线性系统 a·x = b（a ≠ 0），平方损失 L(y) = (a·y - b)²，

  驻点（导数为零）⟺ 满足点（a·x = b）。

证明：
  1. 导数计算：L'(x) = 2a·(a·x - b)（HasDerivAt 链式法则）；
  2. 2a ≠ 0（a ≠ 0，实数零因子）⟹ L'(x) = 0 ⟺ a·x - b = 0 ⟺ a·x = b。

这是「硬约束解嵌入软约束驻点」的连续域形式化种子：
训练中梯度为零的点恰是约束被满足的点（一致系统）。法方程向量版为长线。
-/

noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! ## 引理：平方线性损失的导数
d/dy [(a·y - b)²] = 2a·(a·x - b)（在 x 处）。-/

lemma deriv_sq_linear (a b x : ℝ) :
    deriv (fun y => (a * y - b) ^ 2) x = 2 * a * (a * x - b) := by
  -- 内层：d(a·y - b) = a
  have hlin : HasDerivAt (fun y : ℝ => a * y - b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).sub (hasDerivAt_const x b)
  -- 外层：平方，导数 = 2·(a·x-b)·a
  have hpow : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * (a * x - b) * a) x := by
    simpa using hlin.pow 2
  -- 归一：2·(a·x-b)·a = 2a·(a·x-b)
  have hpow' : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * a * (a * x - b)) x := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpow
  exact hpow'.deriv

/-! ## 引理：a ≠ 0 ⟹ 2a ≠ 0（实数无零因子） -/

lemma two_mul_ne_zero {a : ℝ} (ha : a ≠ 0) : 2 * a ≠ 0 := by
  intro hz
  apply ha
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num : (2 : ℝ) ≠ 0)

/-! ## 定理：P0 标量驻点 ⟺ 满足
一致线性系统 a·x = b（a ≠ 0）下，平方损失导数为零 ⟺ 约束满足。-/

theorem P0_scalar_stationarity (a b x : ℝ) (ha : a ≠ 0) :
    deriv (fun y => (a * y - b) ^ 2) x = 0 ↔ a * x = b := by
  rw [deriv_sq_linear a b x]
  constructor
  · intro h
    -- 2a·(a·x-b) = 0 → a·x-b = 0（2a ≠ 0）
    have hz : a * x - b = 0 := (mul_eq_zero.mp h).resolve_left (two_mul_ne_zero ha)
    linarith
  · intro h
    rw [h]
    ring

/-! ## 推论：驻点即满足（含解的唯一性）
a ≠ 0 时驻点唯一，就是精确解 b/a。-/

theorem P0_scalar_unique_solution (a b : ℝ) (ha : a ≠ 0) :
    ∀ x : ℝ, deriv (fun y => (a * y - b) ^ 2) x = 0 → x = b / a := by
  intro x h
  have hsat : a * x = b := (P0_scalar_stationarity a b x ha).mp h
  -- a·x = b → x = b/a
  calc
    x = (a * x) / a := by
      rw [mul_div_cancel_left₀ x ha]
    _ = b / a := by rw [hsat]

/-! ## 推论：非一致系统（a = 0, b ≠ 0）无满足驻点
a = 0 且 b ≠ 0 时损失恒为 b²（导数恒 0），但无满足点——驻点集 ≠ 满足集。
这界定了 P0 的适用范围（一致系统）。-/

theorem P0_inconsistent_no_solution (b x : ℝ) (hb : b ≠ 0) :
    deriv (fun y => (0 * y - b) ^ 2) x = 0 ∧ ¬(0 * x = b) := by
  constructor
  · rw [deriv_sq_linear 0 b x]
    ring
  · intro h
    exact hb (by simpa using h.symm)

end Lattice
