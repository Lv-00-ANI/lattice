import Lattice.Lib.Optim.RealGradDescent
import Lattice.Runtime.RealRandomVerify
import Mathlib

/-!
# LATTICE: 训练-验证闭环协议 —— GD 收敛 ⟹ 采样验证概率保证

把训练线（RealGradDescent 收敛）与验证线（RealRandomVerify 概率
保证）组装成端到端协议：

  训练（GD）：谱界 ‖1−2η·AA†‖ ≤ c < 1 ⟹ ∃t，‖Ax_t − b‖² < ε²
    （GD_converges，误差平方 ε-终止）
  ⟹ 验证（采样）：固定训练输出 x_t 的损失为常数 f = ‖Ax_t−b‖²，
    其期望 ∫f = ‖Ax_t−b‖² ≤ ε²（概率测度）
    ⟹ 违背概率 μ{ε ≤ f} ≤ ε（verify_probability_guarantee，马尔可夫）
    ——验证 pass 概率 ≥ 1−ε。

闭环：训练收敛（ε-终止）⟹ 验证概率保证（pass ≥ 1−ε）⟹
「训练 → 验证」的完整协议；训练线、验证线、收敛线（RealConvergence）
三线汇合。

模型无关：任意 RCLike 域、任意概率测度（IsProbabilityMeasure）、
任意谱界（训练收敛条件）。
-/

noncomputable section

namespace Lattice

open MeasureTheory

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-! ## 定理：训练-验证闭环协议
GD 收敛（谱界 c < 1）⟹ ∃t，对任意概率测度 μ：
采样验证（阈值 ε）的违背概率 ≤ ε（pass 概率 ≥ 1−ε）。-/

theorem train_verify_protocol (A : E →L[𝕜] F) (b : F) (η : ℝ) (x₀ : E) (c ε : ℝ)
    (hε : 0 < ε) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ∀ x : E, ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ∃ t : ℕ, ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ],
      (μ { x : α | ε ≤ ‖A (GDIterate A b η t x₀) - b‖ ^ 2 }).toReal ≤ ε := by
  -- 训练收敛：∃t，误差平方 < ε²（GD_converges）
  rcases (GD_converges A b η x₀ c hc0 hc1 hspec (ε ^ 2) (by positivity : 0 < ε ^ 2))
    with ⟨t, ht⟩
  -- ht : GDError A b η x₀ t < ε²；展开 GDError 为范数形式（linarith 不解定义）
  have ht' : ‖A (GDIterate A b η t x₀) - b‖ ^ 2 < ε ^ 2 := by
    simpa [GDError] using ht
  refine ⟨t, ?_⟩
  intro α hms μ hprob
  haveI := hprob
  -- 验证：损失 f = 常数（固定训练输出），期望 ≤ ε²（概率测度）
  have hfn : 0 ≤ᵐ[μ] fun _ : α => ‖A (GDIterate A b η t x₀) - b‖ ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hfi : Integrable (fun _ : α => ‖A (GDIterate A b η t x₀) - b‖ ^ 2) μ := integrable_const _
  have hE : (∫ x : α, ‖A (GDIterate A b η t x₀) - b‖ ^ 2 ∂μ) ≤ ε ^ 2 := by
    -- ∫ 常数 = 常数·μ.univ = 常数（概率测度）
    rw [integral_const]
    simp [measure_univ]
    linarith [ht']
  -- 马尔可夫验证保证：违背概率 ≤ ε
  exact verify_probability_guarantee hfn hfi hε hE

/-! ## 注：三线汇合
  训练线（GD 谱界收缩，RealGradDescent）⟹ 收敛线（ε-终止，
  RealConvergence）⟹ 验证线（马尔可夫概率保证，RealRandomVerify）
  ⟹ 训练-验证闭环协议（本定理）：训练到 ε 内 ⟹ 采样验证
  pass 概率 ≥ 1−ε——完整训练-验证联合语义；与修复循环
  （VerifyLoopProgress：失败则修复再验证）衔接构成完整回路。-/

end Lattice
