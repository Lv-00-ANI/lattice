import Mathlib
import Lattice.Lib.Optim.RealStationarity
/-!
# LATTICE: P-Mix —— 组合损失（L_CE + 约束）的驻点⟺满足

对齐约束注入调研（research/real-world/alignment-constraint-math.md §4.3 目标 B 正定理）：
增广拉格朗日

  L_aug(x, μ) = L_CE(x) + (a·x − b)² + μ·(a·x − b)

的关键性质：
  1. 联合驻点（∂/∂x = 0 ∧ ∂/∂μ = 0）⟹ a·x = b —— **无条件**（对任意
     可微 L_CE 成立：∂/∂μ 只依赖约束项，与 L_CE 无关）；
  2. 满足点处乘子 μ* = −L_CE'(x)/a 使 ∂/∂x = 0 —— 乘子从"违背编码"
     推广为「违背 + LM 梯度编码」。

对比：纯惩罚 L_CE + λ(ax−b)² 有限 λ 下驻点不⟹满足（P-Mix 反例）；
增广拉格朗日则无条件成立（∂/∂μ 强制约束满足）。
-/


noncomputable section

open Filter
open scoped Topology

namespace Lattice

/-! ## 增广拉格朗日（等式约束 ax = b，LM 项 + 惩罚项） -/

def AugLagrangian (L_CE : ℝ → ℝ) (a b : ℝ) (x μ : ℝ) : ℝ :=
  L_CE x + (a * x - b) ^ 2 + μ * (a * x - b)

/-! ## 引理一：∂L/∂μ（对 μ 求导）
∂/∂μ = a·x − b（L_CE 与惩罚项不含 μ）。-/

lemma auglag_mu_derivative (L_CE : ℝ → ℝ) (a b x p : ℝ) :
    deriv (fun μ : ℝ => AugLagrangian L_CE a b x μ) p = a * x - b := by
  unfold AugLagrangian
  -- 常数项（相对 μ'）：L_CE x + (ax-b)²，导数 0
  have hconst : HasDerivAt (fun μ : ℝ => L_CE x + (a * x - b) ^ 2) 0 p :=
    hasDerivAt_const p _
  -- 线性项：μ'·(ax-b)，导数 ax-b
  have hlin : HasDerivAt (fun μ : ℝ => μ * (a * x - b)) (a * x - b) p := by
    simpa using (hasDerivAt_id p).mul_const (a * x - b)
  have hadd : HasDerivAt (fun μ : ℝ => L_CE x + (a * x - b) ^ 2 + μ * (a * x - b))
      (0 + (a * x - b)) p := hconst.add hlin
  simpa using hadd.deriv

/-! ## 定理一：联合驻点 ⟹ 约束满足（无条件）
∂L/∂μ = 0 ⟹ a·x = b——对任意 L_CE（无需可导假设）。-/

theorem PMix_stationarity_implies_satisfied (L_CE : ℝ → ℝ) (a b x : ℝ) :
    deriv (fun μ : ℝ => AugLagrangian L_CE a b x μ) x = 0 → a * x = b := by
  intro h
  rw [auglag_mu_derivative L_CE a b x x] at h
  linarith

/-! ## 引理二：∂L/∂x（对 x 求导，μ 固定）
∂/∂x = L_CE'(x) + 2a(ax−b) + μ·a（L_CE 可导时）。-/

lemma auglag_x_derivative (L_CE : ℝ → ℝ) (a b x μ : ℝ)
    (hd : DifferentiableAt ℝ L_CE x) :
    deriv (fun y : ℝ => AugLagrangian L_CE a b y μ) x =
      deriv L_CE x + 2 * a * (a * x - b) + μ * a := by
  unfold AugLagrangian
  -- 三项分别：L_CE（deriv）、惩罚（deriv_sq_linear）、μ·(ay-b)（线性）
  have h₁ : HasDerivAt (fun y : ℝ => L_CE y) (deriv L_CE x) x := hd.hasDerivAt
  have h₂ : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * a * (a * x - b)) x := by
    have hlin : HasDerivAt (fun y : ℝ => a * y - b) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).sub (hasDerivAt_const x b)
    have hpow : HasDerivAt (fun y : ℝ => (a * y - b) ^ 2) (2 * (a * x - b) * a) x := by
      simpa using hlin.pow 2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpow
  have h₃ : HasDerivAt (fun y : ℝ => μ * (a * y - b)) (μ * a) x := by
    have hinner : HasDerivAt (fun y : ℝ => a * y - b) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).sub (hasDerivAt_const x b)
    simpa using hinner.const_mul μ
  -- 逐项相加
  have h₁₂ : HasDerivAt (fun y : ℝ => L_CE y + (a * y - b) ^ 2)
      (deriv L_CE x + 2 * a * (a * x - b)) x := h₁.add h₂
  have h₀ : HasDerivAt (fun y : ℝ => L_CE y + (a * y - b) ^ 2 + μ * (a * y - b))
      (deriv L_CE x + 2 * a * (a * x - b) + μ * a) x := h₁₂.add h₃
  exact h₀.deriv

/-! ## 定理二：满足点处乘子使驻点（乘子编码违背+LM 梯度）
若 a·x = b 且 L_CE 可导，则 μ* = −L_CE'(x)/a 使 ∂L/∂x = 0。 -/

theorem PMix_multiplier_makes_stationary (L_CE : ℝ → ℝ) (a b x : ℝ) (ha : a ≠ 0)
    (hx : a * x = b) (hd : DifferentiableAt ℝ L_CE x) :
    deriv (fun y : ℝ => AugLagrangian L_CE a b y (-deriv L_CE x / a)) x = 0 := by
  -- ∂/∂x = L_CE'(x) + 2a(ax-b) + μa；ax=b → 2a·0 = 0；μa = -L_CE'(x)
  rw [auglag_x_derivative L_CE a b x (-deriv L_CE x / a) hd]
  have hterm : 2 * a * (a * x - b) = 0 := by
    rw [hx]
    ring
  have hmu : (-deriv L_CE x / a) * a = -deriv L_CE x := by
    field_simp [ha]
  rw [hterm, hmu]
  ring

/-! ## 推论：驻点等价（联合）
联合驻点 ⟺ 约束满足 ∧ 乘子 = −L_CE'(x)/a（在可导假设下）。
这是「驻点⟺满足」在 RL 目标下的精确刻画。 -/

theorem PMix_stationarity_characterization (L_CE : ℝ → ℝ) (a b x μ : ℝ) (ha : a ≠ 0)
    (hd : DifferentiableAt ℝ L_CE x) :
    (deriv (fun y : ℝ => AugLagrangian L_CE a b y μ) x = 0 ∧
     deriv (fun μ' : ℝ => AugLagrangian L_CE a b x μ') μ = 0) ↔
    a * x = b ∧ μ = -deriv L_CE x / a := by
  constructor
  · intro h
    rcases h with ⟨hx, hμ⟩
    -- 联合驻点：∂/∂μ = 0 ⟹ 满足；∂/∂x = 0 且满足 ⟹ μ = -L_CE'/a
    have hsat : a * x = b := PMix_stationarity_implies_satisfied L_CE a b x (by
      -- ∂/∂μ ≡ ax-b，在 μ 处为 0 与在 x 处为 0 等价
      rw [auglag_mu_derivative L_CE a b x x]
      rw [← auglag_mu_derivative L_CE a b x μ]
      exact hμ)
    have hxder : deriv L_CE x + 2 * a * (a * x - b) + μ * a = 0 := by
      rwa [auglag_x_derivative L_CE a b x μ hd] at hx
    have hmu : μ = -deriv L_CE x / a := by
      have hterm : 2 * a * (a * x - b) = 0 := by
        rw [hsat]
        ring
      have : μ * a = -deriv L_CE x := by
        rw [hterm] at hxder
        linarith
      calc
        μ = (μ * a) / a := by rw [mul_div_cancel_right₀ μ ha]
        _ = (-deriv L_CE x) / a := by rw [this]
        _ = -deriv L_CE x / a := by ring
    exact ⟨hsat, hmu⟩
  · intro h
    rcases h with ⟨hsat, hmu⟩
    constructor
    · -- ∂/∂x = 0（用乘子定理）
      rw [hmu]
      exact PMix_multiplier_makes_stationary L_CE a b x ha hsat hd
    · -- ∂/∂μ = 0（满足 ⟹ ax-b = 0）
      rw [auglag_mu_derivative L_CE a b x μ]
      linarith

end Lattice
