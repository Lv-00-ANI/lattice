import Mathlib

/-!
# LATTICE: 策略梯度 —— 连续/测度版（抽象线性泛函路线 + 测度实例化）

RealPolicyGradient（有限动作 Σ_a π_a·Q_a）与 RealPolicyGradientVector（fderiv
参数空间）之后，本文件把策略梯度从**有限动作**提升到**连续动作空间**：

    J(θ) = ∫ a, π_θ a · Q a ∂μ

其中 μ 是动作空间 α 上的概率测度，π : α → ℝ 为策略密度（π ≥ 0、∫π dμ = 1），
Q : α → ℝ 为回报（Bochner 积分）。策略梯度定理（score function 形式）：

    dJ/dθ = ∫ a, (dπ/dθ a) · Q a ∂μ = ∫ a, π a · (d log π/dθ a) · Q a ∂μ

## 证明路线（诚实选择）

**抽象线性泛函路线（主路线，定理一~四）**：把「积分」抽象为任意连续线性泛函
`I : (α → ℝ) →L[ℝ] ℝ`，则积分的一切线性性质（可加、齐次、零元）都是纯代数 +
泛函线性，与测度无关，因此**无条件可证**（不依赖 μ 的任何可测性/可积性）。

「导数与积分可交换」（Leibniz 法则 / 控制收敛定理 DominatedConvergence）
**不作为已证定理**：本文件把它写成**显式假设** `DerivIntegralExchange`
（即：J 沿 θ 方向的导数 = 把逐点方向导数 dπ 送进积分泛函 I 的结果）。
在测度实例中该假设由控制收敛定理保证，标注为后续工作。

**测度实例化（定理五~七）**：取 I = ∫ · ∂μ，把抽象定理落到 Bochner 积分，
在可积性假设下给出可加性、score 恒等式与零回报，**不涉及导数与积分的交换**。

模型无关：任意动作空间 α、任意测度 μ、任意策略密度与回报。
-/

noncomputable section

open MeasureTheory

namespace Lattice

variable {α : Type*}

/-! ## 抽象策略值：J = I(π · Q)
I 是「积分」的抽象（连续线性泛函），π 为策略密度，Q 为回报。
（测度实例 I = ∫ · ∂μ 见定理五~七。） -/

def PolicyValueL (I : (α → ℝ) →L[ℝ] ℝ) (π Q : α → ℝ) : ℝ :=
  I (fun a => π a * Q a)

/-! ## 概率密度（诚实设定）
π ≥ 0（μ-a.e.）且 ∫π dμ = 1 —— 策略密度归一。 -/

def IsPolicyDensity [MeasurableSpace α] (μ : Measure α) (π : α → ℝ) : Prop :=
  (0 ≤ᵐ[μ] π) ∧ ∫ a, π a ∂μ = 1

/-! ## 定理一：J 对回报的线性性（抽象版）
I(π·(Q₁+Q₂)) = I(π·Q₁) + I(π·Q₂)（逐点分配律 + 泛函可加性）。 -/

theorem pg_integral_linear (I : (α → ℝ) →L[ℝ] ℝ) (π Q₁ Q₂ : α → ℝ) :
    I (fun a => π a * (Q₁ a + Q₂ a)) = I (fun a => π a * Q₁ a) + I (fun a => π a * Q₂ a) := by
  have h : (fun a => π a * (Q₁ a + Q₂ a)) = (fun a => π a * Q₁ a) + (fun a => π a * Q₂ a) := by
    funext a
    rw [Pi.add_apply]
    ring
  rw [h, map_add]

/-! ## 定理一′：J 对回报的齐次性（抽象版）
I(π·(c·Q)) = c·I(π·Q)（逐点结合律 + 泛函齐次性）。 -/

theorem pg_integral_smul (I : (α → ℝ) →L[ℝ] ℝ) (π Q : α → ℝ) (c : ℝ) :
    I (fun a => π a * (c * Q a)) = c * I (fun a => π a * Q a) := by
  have h : (fun a => π a * (c * Q a)) = c • (fun a => π a * Q a) := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, ContinuousLinearMap.map_smul]
  simp

/-! ## 导数与积分可交换 —— 显式假设（诚实处理）

`DerivIntegralExchange I dJ dπ Q` 断言：回报 J（关于参数 θ 的）导数 dJ
等于把**逐点导数** dπ 与回报 Q 相乘后送进积分泛函 I。

这是「导数与积分交换」（Leibniz 法则）的抽象形式化：它**不是**本文件的定理，
而是主定理的显式前提。测度实例中它由控制收敛定理（DominConvergence /
hasFDerivAt_integral_of_dominated_convergence）保证，标注为后续工作。 -/

def DerivIntegralExchange (I : (α → ℝ) →L[ℝ] ℝ) (dJ : ℝ) (dπ Q : α → ℝ) : Prop :=
  dJ = I (fun a => dπ a * Q a)

/-! ## 定理二（核心）：log 导数恒等式的积分版（score function 形式）

在交换假设 hswap 之下，逐点 log 导数恒等式 `dπ a = π a · s a`
（s = d log π/dθ 即 score）给出

    dJ = ∫ (dπ)·Q = ∫ π·s·Q

—— 连续策略梯度定理：把有限版 Σ_a π_a·∇log π_a·Q_a 的 Σ 换成积分。 -/

theorem pg_log_derivative_identity_integral (I : (α → ℝ) →L[ℝ] ℝ) (dJ : ℝ)
    (π dπ s Q : α → ℝ) (hswap : DerivIntegralExchange I dJ dπ Q)
    (hscore : ∀ a, dπ a = π a * s a) :
    dJ = I (fun a => π a * s a * Q a) := by
  rw [hswap]
  have hfun : (fun a => dπ a * Q a) = (fun a => π a * s a * Q a) := by
    funext a
    rw [hscore a]
  rw [hfun]

/-! ## 定理三：score function 形式（有限动作空间，Σ 实例）
若 dπ = π·s 逐点成立，则 Σ_a (dπ_a)·Q_a = Σ_a π_a·s_a·Q_a
（与 RealPolicyGradient 的有限版一致；score 形式的和式表述）。 -/

theorem pg_score_function_form {m : ℕ} (π dπ s Q : Fin m → ℝ)
    (hscore : ∀ a, dπ a = π a * s a) :
    ∑ a : Fin m, dπ a * Q a = ∑ a : Fin m, π a * s a * Q a := by
  apply Finset.sum_congr rfl
  intro a _
  rw [hscore a]

/-! ## 定理四：零回报验证
Q = 0 ⟹ J = 0；且梯度 = 0（在交换假设下，dπ·Q 恒为 0）。 -/

theorem pg_zero_reward (I : (α → ℝ) →L[ℝ] ℝ) (π : α → ℝ) :
    PolicyValueL I π (fun _ => (0 : ℝ)) = 0 := by
  unfold PolicyValueL
  have h : (fun a => π a * (0 : ℝ)) = (0 : α → ℝ) := by
    funext a
    simp
  rw [h, map_zero]

theorem pg_zero_reward_gradient (I : (α → ℝ) →L[ℝ] ℝ) (dJ : ℝ) (Q : α → ℝ)
    (hswap : DerivIntegralExchange I dJ (fun _ => (0 : ℝ)) Q) : dJ = 0 := by
  rw [hswap]
  have h : (fun a => (0 : ℝ) * Q a) = (0 : α → ℝ) := by
    funext a
    simp
  rw [h, map_zero]

/-! ## 定理五：测度实例化 —— J 的可加性（Bochner 积分）
可积性假设下 ∫ (π·(Q₁+Q₂)) = ∫(π·Q₁) + ∫(π·Q₂)（I = ∫·∂μ 的实例）。 -/

theorem pg_integral_linear_measure [MeasurableSpace α] (μ : Measure α)
    (π Q₁ Q₂ : α → ℝ) (h1 : Integrable (fun a => π a * Q₁ a) μ)
    (h2 : Integrable (fun a => π a * Q₂ a) μ) :
    ∫ a, π a * (Q₁ a + Q₂ a) ∂μ = (∫ a, π a * Q₁ a ∂μ) + ∫ a, π a * Q₂ a ∂μ := by
  have h : (fun a => π a * (Q₁ a + Q₂ a)) = (fun a => π a * Q₁ a + π a * Q₂ a) := by
    funext a
    ring
  rw [h]
  exact integral_add h1 h2

/-! ## 定理六：测度实例化 —— score 恒等式（积分版）
逐点 log 导数恒等式 ⟹ 积分恒等 ⟹ ∫ (dπ)·Q = ∫ π·s·Q（无需可积性，
积分对 a.e. 相等的被积函数相同）。 -/

theorem pg_log_derivative_identity_measure [MeasurableSpace α] (μ : Measure α)
    (π dπ s Q : α → ℝ) (hscore : ∀ a, dπ a = π a * s a) :
    ∫ a, dπ a * Q a ∂μ = ∫ a, π a * s a * Q a ∂μ := by
  apply integral_congr_ae
  filter_upwards with a
  rw [hscore a]

/-! ## 定理七：测度实例化 —— 零回报
∫ a, π a · 0 ∂μ = 0（Q = 0 ⟹ J = 0 的积分形式）。 -/

theorem pg_zero_reward_measure [MeasurableSpace α] (μ : Measure α) (π : α → ℝ) :
    ∫ a, π a * (0 : ℝ) ∂μ = 0 := by
  simp

/-! ## 注：连续策略梯度闭环
  抽象线性泛函路线（定理一~四）给出**无条件**的线性性与 score 形式，
  其「积分」的实质由测度实例化（定理五~七）落实为 Bochner 积分；
  唯一的诚实前提是 `DerivIntegralExchange`（导数与积分交换 =
  控制收敛定理），它是主定理二的显式假设而非隐藏公理。
  与 RealPolicyGradient（有限 Σ）/ RealPolicyGradientVector（fderiv 参数空间）
  合起来：策略梯度的有限、参数空间、连续测度三版齐备。 -/

end Lattice
