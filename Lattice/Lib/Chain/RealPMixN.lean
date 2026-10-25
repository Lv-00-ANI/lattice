import Mathlib
import Lattice.Lib.Optim.RealStationarity
/-!
# LATTICE: P-Mix 多约束（泛化）—— n 约束增广拉格朗日

RealPMix（单约束）的 **n 约束泛化**：多个等式约束 {aᵢx = bᵢ}ᵢ 的增广拉格朗日

    L_aug(x, μ) = L_CE(x) + Σᵢ (aᵢx − bᵢ)² + Σᵢ μᵢ·(aᵢx − bᵢ)

关键性质（对任意可微 L_CE 无条件成立）：

    ∂L/∂μᵢ = aᵢx − bᵢ（第 i 个乘子的导数只依赖第 i 个约束项）
    ⟹ 联合驻点（∀i，∂/∂μᵢ = 0）⟹ ∀i，aᵢx = bᵢ（各约束满足）

这正是「增广拉格朗日乘子强制约束满足」的多约束版——RL 对齐
（多安全约束注入）的驻点基础；单约束（RealPMix）是 n=1 特例。

模型无关：任意约束数 n；联合驻点定理（PMixN_stationarity_implies_satisfied）与
∂/∂μᵢ 公式（auglagN_mu_derivative）对任意 L_CE 成立（连可微都不需要，
L_CE x 在 ∂/∂μᵢ 中只作常数项）；仅 ∂/∂x 公式（auglagN_x_derivative）
额外要求 L_CE 在 x 处可微（DifferentiableAt ℝ L_CE x）。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## n 约束增广拉格朗日（LM 项 + 惩罚项，逐约束） -/

def AugLagrangianN (L_CE : ℝ → ℝ) (a b : Fin n → ℝ) (μ : Fin n → ℝ) (x : ℝ) : ℝ :=
  L_CE x + (∑ i : Fin n, (a i * x - b i) ^ 2) + (∑ i : Fin n, μ i * (a i * x - b i))

/-! ## 引理：∂L/∂μᵢ（第 i 个乘子求导）
∂/∂μᵢ = aᵢx − bᵢ（L_CE 与惩罚项、其他乘子项不含 μᵢ）。-/

lemma auglagN_mu_derivative (L_CE : ℝ → ℝ) (a b : Fin n → ℝ) (μ : Fin n → ℝ) (x : ℝ) (i : Fin n) :
    deriv (fun m : ℝ => AugLagrangianN L_CE a b (Function.update μ i m) x) (μ i) = a i * x - b i := by
  -- 线性项和：Σⱼ (update μ i m)ⱼ·(aⱼx−bⱼ)，只有 j=i 依赖 m
  have hd : ∀ j : Fin n, DifferentiableAt ℝ
      (fun m : ℝ => (Function.update μ i m) j * (a j * x - b j)) (μ i) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa using ((differentiableAt_id (𝕜 := ℝ) (x := μ i)).mul_const (a i * x - b i))
    · have hf : (fun m : ℝ => (Function.update μ i m) j * (a j * x - b j))
          = fun _ : ℝ => μ j * (a j * x - b j) := by
        funext m
        rw [Function.update_noteq hj]
      rw [hf]
      exact differentiableAt_const _
  have hlin : deriv (fun m : ℝ => ∑ j : Fin n, (Function.update μ i m) j * (a j * x - b j)) (μ i)
      = a i * x - b i := by
    rw [deriv_sum (u := Finset.univ) (A := fun j m => (Function.update μ i m) j * (a j * x - b j)) (x := μ i) (fun j hj => hd j)]
    calc
      (∑ j : Fin n, deriv (fun m : ℝ => (Function.update μ i m) j * (a j * x - b j)) (μ i))
          = deriv (fun m : ℝ => (Function.update μ i m) i * (a i * x - b i)) (μ i) := by
            apply Finset.sum_eq_single i
            · intro j hj hji
              have hf : (fun m : ℝ => (Function.update μ i m) j * (a j * x - b j))
                  = fun _ : ℝ => μ j * (a j * x - b j) := by
                funext m
                rw [Function.update_noteq hji]
              rw [hf, deriv_const]
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
      _ = a i * x - b i := by
            have hf : (fun m : ℝ => (Function.update μ i m) i * (a i * x - b i))
                = fun m : ℝ => m * (a i * x - b i) := by
              funext m
              simp
            rw [hf]
            simpa using ((hasDerivAt_id (μ i)).mul_const (a i * x - b i)).deriv
  -- 常数项（L_CE + 惩罚和）导数 0；HasDerivAt 加法组合
  have hc : HasDerivAt (fun m : ℝ => L_CE x + (∑ j : Fin n, (a j * x - b j) ^ 2)) 0 (μ i) := by
    simpa using hasDerivAt_const (μ i) (L_CE x + (∑ j : Fin n, (a j * x - b j) ^ 2))
  have hdiffs : DifferentiableAt ℝ
      (fun m : ℝ => ∑ j : Fin n, (Function.update μ i m) j * (a j * x - b j)) (μ i) := by
    exact DifferentiableAt.sum (u := Finset.univ) (A := fun j m => (Function.update μ i m) j * (a j * x - b j)) (fun j hj => hd j)
  have hf : HasDerivAt
      (fun m : ℝ => ∑ j : Fin n, (Function.update μ i m) j * (a j * x - b j)) (a i * x - b i) (μ i) := by
    simpa [hlin] using hdiffs.hasDerivAt
  -- 整体 = 常数(0) + 线性(cᵢ)
  have hadd := hc.add hf
  -- 目标函数展开：L_CE x + Σ惩罚 + Σ线性 = 常数项 + 线性项
  have hfun : (fun m : ℝ => AugLagrangianN L_CE a b (Function.update μ i m) x)
      = fun m : ℝ => (L_CE x + (∑ j : Fin n, (a j * x - b j) ^ 2))
          + (∑ j : Fin n, (Function.update μ i m) j * (a j * x - b j)) := by
    funext m
    unfold AugLagrangianN
    ring
  calc
    deriv (fun m : ℝ => AugLagrangianN L_CE a b (Function.update μ i m) x) (μ i)
        = deriv (fun m : ℝ => (L_CE x + (∑ j : Fin n, (a j * x - b j) ^ 2))
            + (∑ j : Fin n, (Function.update μ i m) j * (a j * x - b j))) (μ i) := by
          rw [hfun]
    _ = a i * x - b i := by
          simpa using hadd.deriv

/-! ## 定理：多约束联合驻点 ⟹ 各约束满足（无条件）
∀i，∂L/∂μᵢ = 0 ⟹ ∀i，aᵢx = bᵢ——对任意 L_CE（无需可导假设）。-/

theorem PMixN_stationarity_implies_satisfied (L_CE : ℝ → ℝ) (a b : Fin n → ℝ)
    (μ : Fin n → ℝ) (x : ℝ) :
    (∀ i : Fin n, deriv (fun m : ℝ => AugLagrangianN L_CE a b (Function.update μ i m) x) (μ i) = 0)
      → ∀ i : Fin n, a i * x = b i := by
  intro h i
  have hderiv := auglagN_mu_derivative L_CE a b μ x i
  have hi : deriv (fun m : ℝ => AugLagrangianN L_CE a b (Function.update μ i m) x) (μ i) = 0 := h i
  rw [hderiv] at hi
  linarith

/-! ## 引理：∂L/∂x（对 x 求导，μ 固定，n 版）
∂/∂x = L_CE'(x) + Σᵢ 2aᵢ(aᵢx−bᵢ) + Σᵢ μᵢ·aᵢ（L_CE 可导时）。-/

lemma auglagN_x_derivative (L_CE : ℝ → ℝ) (a b : Fin n → ℝ) (μ : Fin n → ℝ) (x : ℝ)
    (hd : DifferentiableAt ℝ L_CE x) :
    deriv (fun y : ℝ => AugLagrangianN L_CE a b μ y) x =
      deriv L_CE x + (∑ i : Fin n, 2 * a i * (a i * x - b i)) + (∑ i : Fin n, μ i * a i) := by
  -- 惩罚项逐项：deriv (aᵢy−bᵢ)² = 2aᵢ(aᵢx−bᵢ)
  have hps_i : ∀ i : Fin n, HasDerivAt (fun y : ℝ => (a i * y - b i) ^ 2)
      (2 * a i * (a i * x - b i)) x := by
    intro i
    have hdsq_i : DifferentiableAt ℝ (fun y : ℝ => (a i * y - b i) ^ 2) x := by
      have hlin_i : DifferentiableAt ℝ (fun y : ℝ => a i * y - b i) x := by
        simpa using ((differentiableAt_id (𝕜 := ℝ) (x := x)).const_mul (a i)).sub (differentiableAt_const (b i))
      exact hlin_i.pow 2
    rw [← deriv_sq_linear (a i) (b i) x]
    exact hdsq_i.hasDerivAt
  -- 线性乘子项逐项：deriv μᵢ(aᵢy−bᵢ) = μᵢaᵢ
  have hlin_i : ∀ i : Fin n, HasDerivAt (fun y : ℝ => μ i * (a i * y - b i)) (μ i * a i) x := by
    intro i
    have hinner : HasDerivAt (fun y : ℝ => a i * y - b i) (a i) x := by
      simpa using ((hasDerivAt_id x).const_mul (a i)).sub (hasDerivAt_const x (b i))
    simpa using hinner.const_mul (μ i)
  -- 求和
  have hps : HasDerivAt (fun y : ℝ => ∑ i : Fin n, (a i * y - b i) ^ 2)
      (∑ i : Fin n, 2 * a i * (a i * x - b i)) x := by
    simpa using (HasDerivAt.sum (u := Finset.univ) (fun i hi => hps_i i))
  have hls : HasDerivAt (fun y : ℝ => ∑ i : Fin n, μ i * (a i * y - b i))
      (∑ i : Fin n, μ i * a i) x := by
    simpa using (HasDerivAt.sum (u := Finset.univ) (fun i hi => hlin_i i))
  have hce : HasDerivAt L_CE (deriv L_CE x) x := hd.hasDerivAt
  -- 整体相加
  have hsum := hce.add hps
  have hsum2 := hsum.add hls
  simpa [AugLagrangianN] using hsum2.deriv

/-! ## 注：RL 对齐语义
  多安全约束 {aᵢx ≤/= bᵢ} 注入：增广拉格朗日乘子 μᵢ 逐约束
  强制满足——联合驻点 ⟹ 每个约束成立（无条件，无需 L_CE 可导）；
  ∂/∂x = L_CE' + Σ(惩罚梯度 + 乘子梯度)（auglagN_x_derivative）给出
  满足点处乘子对 L_CE 梯度的编码；单约束（RealPMix，n=1）是本文件
  特例；约束为不等式时以 relu 惩罚替换平方项（P2a 系列）。-/

end Lattice
