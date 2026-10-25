import Mathlib

/-!
# LATTICE: 策略梯度 —— RL 策略半边的收敛目标（有限版）

RL 完整目标（RealValueIteration 已给价值半边）的**策略半边**：
有限动作空间（Fin m）上的策略 π_θ(a)，期望回报

    J(θ) = Σ_a π_θ(a)·Q(a)     （Q 由价值迭代给出）

策略梯度定理（∇π = π·∇log π 的 log 导数恒等式）：

    ∇J(θ) = Σ_a π_θ(a)·(∇log π_θ(a))·Q(a)

  1. log 导数恒等式：π > 0 可导 ⟹ deriv π = π·deriv(log∘π)
     （链式法则 + Real.log 导数 1/x，mathlib hasDerivAt_log）；
  2. 策略梯度（有限版）：deriv[Σ π_a·Q_a] = Σ π_a·(deriv log π_a)·Q_a
     （deriv_sum + 乘积法则 + log 导数恒等式）。

闭环：价值迭代（Q*）⟹ 策略梯度（∇J 方向）⟹ 策略提升——
RL 完整目标的两个半边齐备（有限 MDP；连续版需测度，标注）。

模型无关：任意动作数 m、任意策略参数化（θ 标量版；
hlog 是「log 导数恒等式」的抽象，可由引理一验证）。
-/

noncomputable section

namespace Lattice

/-! ## 定理一：log 导数恒等式（策略梯度的核心前提）
π > 0 且 π 可导 ⟹ deriv π = π·deriv(log∘π)（(log π)' = π'/π）。-/

theorem log_derivative_identity (π : ℝ → ℝ) (θ : ℝ) (hpos : 0 < π θ) (hd : DifferentiableAt ℝ π θ) :
    deriv π θ = π θ * deriv (fun t => Real.log (π t)) θ := by
  -- 链式：deriv (log∘π) θ = (π θ)⁻¹ · deriv π θ
  have hlogat : HasDerivAt Real.log (π θ)⁻¹ (π θ) := Real.hasDerivAt_log (ne_of_gt hpos)
  have hcomp : HasDerivAt (fun t => Real.log (π t)) ((π θ)⁻¹ * deriv π θ) θ :=
    HasDerivAt.comp θ hlogat hd.hasDerivAt
  have hderiv_log : deriv (fun t => Real.log (π t)) θ = (π θ)⁻¹ * deriv π θ := hcomp.deriv
  rw [hderiv_log]
  field_simp [ne_of_gt hpos]

/-! ## 定理二：策略梯度（有限版）
deriv[Σ_a π_a·Q_a] = Σ_a π_a·(deriv log π_a)·Q_a（∇π = π·∇logπ）。-/

theorem policy_gradient_scalar {m : ℕ} (θ : ℝ) (π : ℝ → Fin m → ℝ) (Q : Fin m → ℝ)
    (hd : ∀ a : Fin m, DifferentiableAt ℝ (fun t => π t a) θ)
    (hlog : ∀ a : Fin m, deriv (fun t => π t a) θ
      = π θ a * deriv (fun t => Real.log (π t a)) θ) :
    deriv (fun t => ∑ a : Fin m, π t a * Q a) θ
      = ∑ a : Fin m, π θ a * (deriv (fun t => Real.log (π t a)) θ) * Q a := by
  -- deriv_sum：和的可导性
  have hsum : deriv (fun t : ℝ => ∑ a : Fin m, π t a * Q a) θ
      = ∑ a : Fin m, deriv (fun t : ℝ => π t a * Q a) θ := by
    exact deriv_sum (u := Finset.univ) (A := fun a t => π t a * Q a) (by
      intro a ha
      exact (hd a).mul_const (Q a))
  -- 逐项：deriv (π_a·Q_a) = deriv π_a · Q_a = (π_a·∇log π_a)·Q_a
  have hitem : ∀ a : Fin m, deriv (fun t : ℝ => π t a * Q a) θ
      = π θ a * (deriv (fun t : ℝ => Real.log (π t a)) θ) * Q a := by
    intro a
    rw [deriv_mul_const (hd a) (Q a)]
    rw [hlog a]
  calc
    deriv (fun t : ℝ => ∑ a : Fin m, π t a * Q a) θ
        = ∑ a : Fin m, deriv (fun t : ℝ => π t a * Q a) θ := hsum
    _ = ∑ a : Fin m, π θ a * (deriv (fun t : ℝ => Real.log (π t a)) θ) * Q a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hitem a

/-! ## 注：RL 完整目标收官
  价值半边（RealValueIteration：Bellman 收缩 ⟹ Q*）⟹
  策略半边（本文件：∇J = Σπ·∇logπ·Q，策略梯度方向）⟹
  策略提升（沿 ∇J 更新 θ）——有限 MDP 的 RL 完整目标齐备。
  hlog 假设由引理一验证（π > 0 时）；连续状态/动作的测度版
  （期望积分）标注为扩展（需 ProbabilityTheory 测度积分）。-/

end Lattice
