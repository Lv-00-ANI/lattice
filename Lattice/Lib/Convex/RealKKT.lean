import Mathlib
import Lattice.Lib.Optim.RealStationarity
/-!
# LATTICE: P4 增广拉格朗日驻点 —— 乘子视角的驻点 ⟺ 满足

调研（research/embedding/README.md §4 P4）的最小版本：
等式约束 a·x = b（a ≠ 0）的增广拉格朗日

  L_aug(x, λ) = (a·x - b)² + λ·(a·x - b)

的两个偏导（∂/∂x、∂/∂λ）同时为零，⟺ 约束满足且乘子归零：

  ∂/∂x = 2a(ax-b) + λa = 0
  ∂/∂λ = (ax-b) = 0
  ⟹ ax = b（满足）且 λ = 0（乘子归零，因约束被精确满足）。

这是 KKT 风格"约束驻点"的连续域形式化：满足点即增广拉格朗日驻点，
乘子编码约束违背（违背时 λ ≠ 0）。向量版/不等式版（KKT 一般形式）为长线。
-/


noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! ## 偏导一：∂L/∂x（对 x 求导）
d/dy [(a·y-b)² + λ·(a·y-b)] = 2a(ax-b) + λa。-/

lemma deriv_aug_x (a b lam x : ℝ) :
    deriv (fun y => (a * y - b) ^ 2 + lam * (a * y - b)) x = 2 * a * (a * x - b) + lam * a := by
  -- 第一项：平方损失导数（复用 deriv_sq_linear 的 HasDerivAt 证明方式）
  have h₁ : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * a * (a * x - b)) x := by
    have hlin : HasDerivAt (fun y : ℝ => a * y - b) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).sub (hasDerivAt_const x b)
    have hpow : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * (a * x - b) * a) x := by
      simpa using hlin.pow 2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpow
  -- 第二项：lam·(a·y-b) 线性导数 = lam·a
  have h₂ : HasDerivAt (fun y : ℝ => lam * (a * y - b)) (lam * a) x := by
    have hinner : HasDerivAt (fun y : ℝ => a * y - b) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).sub (hasDerivAt_const x b)
    simpa using hinner.const_mul lam
  -- 和的可导性 + deriv_add
  have hadd : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2 + lam * (a * y - b))
      ((2 * a * (a * x - b)) + lam * a) x := h₁.add h₂
  exact hadd.deriv

/-! ## 偏导二：∂L/∂λ（对 λ 求导）
d/dλ' [(a·x-b)² + λ'·(a·x-b)] = a·x - b（在任意点 pt 处成立，
因为被积函数对 λ' 是仿射的）。-/

lemma deriv_aug_lam (a b x : ℝ) (pt : ℝ) :
    deriv (fun t => (a * x - b) ^ 2 + t * (a * x - b)) pt = a * x - b := by
  -- 常数项（相对 t）导数 0；线性项 t·(ax-b) 导数 = ax-b
  have hconst : HasDerivAt (fun t : ℝ => (a * x - b) ^ 2) 0 pt := hasDerivAt_const pt _
  have hlin : HasDerivAt (fun t : ℝ => t * (a * x - b)) (a * x - b) pt := by
    simpa using (hasDerivAt_id pt).mul_const (a * x - b)
  have hadd : HasDerivAt (fun t : ℝ => (a * x - b) ^ 2 + t * (a * x - b))
      (0 + (a * x - b)) pt := hconst.add hlin
  simpa using hadd.deriv

/-! ## 定理：P4 增广拉格朗日驻点 ⟺ 约束满足 ∧ 乘子归零 -/

theorem P4_augmented_stationarity (a b x lam : ℝ) (ha : a ≠ 0) :
    (deriv (fun y => (a * y - b) ^ 2 + lam * (a * y - b)) x = 0 ∧
     deriv (fun t => (a * x - b) ^ 2 + t * (a * x - b)) lam = 0) ↔
    a * x = b ∧ lam = 0 := by
  rw [deriv_aug_x a b lam x, deriv_aug_lam a b x lam]
  constructor
  · intro h
    -- ∂/∂λ = 0 ⟹ 约束满足
    have hsat : a * x - b = 0 := h.2
    have hx : a * x = b := by linarith
    -- ∂/∂x = 0 且 ax-b = 0 ⟹ lam·a = 0 ⟹ lam = 0
    have hlam : lam = 0 := by
      have hfirst : 2 * a * (a * x - b) + lam * a = 0 := h.1
      have hzero : lam * a = 0 := by
        rw [hsat] at hfirst
        simpa using hfirst
      exact (mul_eq_zero.mp hzero).resolve_right ha
    exact ⟨hx, hlam⟩
  · intro h
    rcases h with ⟨hx, hlam⟩
    constructor
    · rw [hx, hlam]
      ring
    · rw [hx]
      ring

/-! ## 推论：乘子编码约束违背
约束不满足时乘子非零（∂/∂x = 0 给出 2a(ax-b) + λa = 0，除以 a 后
λ = -2(ax-b)；注意原稿中的 `/a` 是笔误——-2a(ax-b)/a 的 a 已被约去）。
-/

theorem P4_multiplier_encodes_violation (a b x lam : ℝ) (ha : a ≠ 0)
    (h : deriv (fun y => (a * y - b) ^ 2 + lam * (a * y - b)) x = 0) :
    lam = -2 * (a * x - b) := by
  rw [deriv_aug_x a b lam x] at h
  -- 2a(ax-b) + lam·a = 0 → lam·a = -2a(ax-b) → lam = -2(ax-b)（除以 a，a≠0）
  have hmain : lam * a = -2 * a * (a * x - b) := by
    calc
      lam * a = -(2 * a * (a * x - b)) := by linarith
      _ = -2 * a * (a * x - b) := by ring
  calc
    lam = (lam * a) / a := by rw [mul_div_cancel_right₀ lam ha]
    _ = (-2 * a * (a * x - b)) / a := by rw [hmain]
    _ = -2 * (a * x - b) := by
      -- (-2a·d)/a = -2d（a≠0）：-2a·d = (-2d)·a，代入后消去 a
      rw [show -2 * a * (a * x - b) = (-2 * (a * x - b)) * a by ring]
      rw [mul_div_cancel_right₀ (-2 * (a * x - b)) ha]

end Lattice
