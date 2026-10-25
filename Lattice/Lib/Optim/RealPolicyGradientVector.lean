import Mathlib

/-!
# LATTICE: 策略梯度 —— 参数空间版（标量 θ : ℝ → 向量 θ : E，fderiv 表述）

RealPolicyGradient（标量版，deriv）把策略梯度定理限制在标量参数 θ : ℝ。
本文件把同一结果**泛化到任意参数空间 E**（EuclideanSpace ℝ (Fin d) 或任意
NormedAddCommGroup + NormedSpace ℝ），用 fderiv（Fréchet 导数）表述：

  J(θ) = Σ_a π θ a · Q a，θ : E（E 为参数空间，π θ a = 动作 a 的概率，Q 固定回报）

策略梯度定理（参数空间版，对任意方向 v : E）：

  fderiv J θ v = Σ_a π θ a · (fderiv (fun θ => Real.log (π θ a)) θ v) · Q a

即 ∇J(θ)·v = Σ_a π_a(θ)·(∇log π_a(θ)·v)·Q_a —— 标量版 ∇J = Σπ·∇logπ·Q 的
fderiv（对偶）推广；v 是任意方向，定理在 v 中线性（policy_gradient_vector_clm
给出整映射版，policy_gradient_vector_directional 给出沿直线方向导数版）。

证明结构（对应标量版 log_derivative_identity / policy_gradient_scalar）：
  1. fderiv_log_derivative_identity：fderiv 版 log 导数恒等式
     fderiv (log∘π_a) θ v = (π θ a)⁻¹ · fderiv π_a θ v
     （HasFDerivAt.log = log 在 π θ a ≠ 0 的导数 + 链式法则）；
  2. policy_gradient_vector：fderiv_sum + 乘积法则（fderiv_mul_const）+
     代入引理一（反解：π θ a > 0 ⟹ fderiv π_a = π θ a · fderiv (log∘π_a)）；
  3. policy_gradient_vector_clm / policy_gradient_vector_directional：
     整映射版与方向导数版（fderiv 应用 = 沿直线导数，RealNormalEquation 的桥）。

模型无关：任意动作数 m、任意参数空间 E、任意策略参数化 π（只要逐动作可导且
π θ a > 0——log 的定义域）。softmax 策略满足这些假设的检查（π > 0、Σπ = 1）
附于文末；softmax 的显式 fderiv 展开（score = ∇s − Σπ·∇s）标注为后续工作。
-/

noncomputable section

open Filter
open scoped Topology

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 期望回报（参数空间版）
J(θ) = Σ_a π θ a · Q a，θ : E。-/

def PolicyValue {m : ℕ} (π : E → Fin m → ℝ) (Q : Fin m → ℝ) (θ : E) : ℝ :=
  ∑ a : Fin m, π θ a * Q a

/-! ## 引理一：log 导数恒等式（fderiv 版）
π θ a > 0 且 π(·, a) 在 θ 可导 ⟹
fderiv (fun θ => Real.log (π θ a)) θ v = (π θ a)⁻¹ · fderiv (fun θ => π θ a) θ v
（标量版 log_derivative_identity 的 fderiv 泛化；HasFDerivAt.log 即链式法则）。-/

lemma fderiv_log_derivative_identity {m : ℕ} (π : E → Fin m → ℝ) (θ : E) (v : E) (a : Fin m)
    (hpos : 0 < π θ a) (hd : DifferentiableAt ℝ (fun x : E => π x a) θ) :
    fderiv ℝ (fun x : E => Real.log (π x a)) θ v
      = (π θ a)⁻¹ * fderiv ℝ (fun x : E => π x a) θ v := by
  -- 链式（HasFDerivAt.log：log 在 π θ a ≠ 0 的导数 1/x，复合 π(·,a) 的 fderiv）
  have hlog : HasFDerivAt (fun x : E => Real.log (π x a))
      ((π θ a)⁻¹ • fderiv ℝ (fun x : E => π x a) θ) θ := by
    exact (hd.hasFDerivAt).log (ne_of_gt hpos)
  calc
    fderiv ℝ (fun x : E => Real.log (π x a)) θ v
        = ((π θ a)⁻¹ • fderiv ℝ (fun x : E => π x a) θ) v := by rw [hlog.fderiv]
    _ = (π θ a)⁻¹ * fderiv ℝ (fun x : E => π x a) θ v := by
          simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ## 引理二：期望回报可导
π(·, a) 逐动作在 θ 可导 ⟹ J 在 θ 可导（fderiv_sum + mul_const）。-/

lemma policy_value_differentiable {m : ℕ} (π : E → Fin m → ℝ) (Q : Fin m → ℝ) (θ : E)
    (hd : ∀ a : Fin m, DifferentiableAt ℝ (fun x : E => π x a) θ) :
    DifferentiableAt ℝ (fun x : E => PolicyValue π Q x) θ := by
  unfold PolicyValue
  exact DifferentiableAt.sum (u := Finset.univ) (A := fun a x => π x a * Q a) (x := θ) (by
    intro a ha
    exact (hd a).mul_const (Q a))

/-! ## 定理一：策略梯度（参数空间版，核心）
fderiv J θ v = Σ_a π θ a · (fderiv (fun θ => Real.log (π θ a)) θ v) · Q a
（∇J·v = Σ π·(∇logπ)·Q·v；fderiv_sum + 乘积法则 + 代入引理一）。-/

theorem policy_gradient_vector {m : ℕ} (θ : E) (v : E) (π : E → Fin m → ℝ) (Q : Fin m → ℝ)
    (hpos : ∀ a : Fin m, 0 < π θ a)
    (hd : ∀ a : Fin m, DifferentiableAt ℝ (fun x : E => π x a) θ) :
    fderiv ℝ (fun x : E => PolicyValue π Q x) θ v
      = ∑ a : Fin m, π θ a * (fderiv ℝ (fun x : E => Real.log (π x a)) θ v) * Q a := by
  -- 引理一：每个动作的 log 导数恒等式（代入用）
  have hlog : ∀ a : Fin m, fderiv ℝ (fun x : E => Real.log (π x a)) θ v
      = (π θ a)⁻¹ * fderiv ℝ (fun x : E => π x a) θ v := fun a =>
    fderiv_log_derivative_identity π θ v a (hpos a) (hd a)
  -- fderiv_sum：和的可导性（显式 (u := Finset.univ) (A := ...) (x := θ)）
  have hsum : fderiv ℝ (fun x : E => PolicyValue π Q x) θ
      = ∑ a : Fin m, fderiv ℝ (fun x : E => π x a * Q a) θ := by
    simpa [PolicyValue] using
      (fderiv_sum (u := Finset.univ) (A := fun a x => π x a * Q a) (x := θ) (by
        intro a ha
        exact (hd a).mul_const (Q a)))
  -- 逐项：fderiv (π_a·Q_a) θ v = π θ a · (fderiv (log∘π_a) θ v) · Q a
  have hitem : ∀ a : Fin m,
      fderiv ℝ (fun x : E => π x a * Q a) θ v
        = π θ a * (fderiv ℝ (fun x : E => Real.log (π x a)) θ v) * Q a := by
    intro a
    -- 乘积法则（常数因子）：fderiv (π_a·Q_a) θ v = Q a · fderiv π_a θ v
    have hfc : fderiv ℝ (fun x : E => π x a * Q a) θ v
        = Q a * fderiv ℝ (fun x : E => π x a) θ v := by
      have hd' : fderiv ℝ (fun x : E => π x a * Q a) θ = Q a • fderiv ℝ (fun x : E => π x a) θ :=
        fderiv_mul_const (hd a) (Q a)
      calc
        fderiv ℝ (fun x : E => π x a * Q a) θ v
            = (Q a • fderiv ℝ (fun x : E => π x a) θ) v := by rw [hd']
        _ = Q a * fderiv ℝ (fun x : E => π x a) θ v := by
              simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
    -- 反解引理一（π θ a > 0 ⟹ 可消）：fderiv π_a θ v = π θ a · fderiv (log∘π_a) θ v
    have hπ : fderiv ℝ (fun x : E => π x a) θ v
        = π θ a * fderiv ℝ (fun x : E => Real.log (π x a)) θ v := by
      calc
        fderiv ℝ (fun x : E => π x a) θ v
            = π θ a * ((π θ a)⁻¹ * fderiv ℝ (fun x : E => π x a) θ v) := by
              rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hpos a)), one_mul]
        _ = π θ a * fderiv ℝ (fun x : E => Real.log (π x a)) θ v := by rw [hlog a]
    rw [hfc, hπ]
    ring
  -- 组合
  calc
    fderiv ℝ (fun x : E => PolicyValue π Q x) θ v
        = (∑ a : Fin m, fderiv ℝ (fun x : E => π x a * Q a) θ) v := by rw [hsum]
    _ = ∑ a : Fin m, fderiv ℝ (fun x : E => π x a * Q a) θ v := by
          simp
    _ = ∑ a : Fin m, π θ a * (fderiv ℝ (fun x : E => Real.log (π x a)) θ v) * Q a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hitem a

/-! ## 引理三：方向导数 = fderiv 作用（桥）
fderiv f x v = deriv (fun t => f (x + t·v)) 0（RealNormalEquation 同款桥，
用于方向导数版定理）。-/

lemma fderiv_apply_direction_vector {f : E → ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x v = deriv (fun t : ℝ => f (x + t • v)) 0 := by
  -- 直线 t ↦ x + t·v 在 0 处导数为 v，复合 HasFDerivAt.comp_hasDerivAt
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    have hx : x + (0 : ℝ) • v = x := by simp
    rw [hx]
    exact hf.hasFDerivAt
  exact (hf'.comp_hasDerivAt 0 hg).deriv.symm

/-! ## 定理二：方向导数形式（∇J·v = Σ π·(∇logπ)·Q·v 的直线表述）
deriv (fun t => J (θ + t·v)) 0 = Σ_a π θ a · (fderiv (log∘π_a) θ v) · Q a
（fderiv 应用 = 沿直线导数：桥 + 定理一）。-/

theorem policy_gradient_vector_directional {m : ℕ} (θ : E) (v : E) (π : E → Fin m → ℝ)
    (Q : Fin m → ℝ) (hpos : ∀ a : Fin m, 0 < π θ a)
    (hd : ∀ a : Fin m, DifferentiableAt ℝ (fun x : E => π x a) θ) :
    deriv (fun t : ℝ => PolicyValue π Q (θ + t • v)) 0
      = ∑ a : Fin m, π θ a * (fderiv ℝ (fun x : E => Real.log (π x a)) θ v) * Q a := by
  -- 桥：方向导数 = fderiv 作用
  have hdir : fderiv ℝ (fun x : E => PolicyValue π Q x) θ v
      = deriv (fun t : ℝ => PolicyValue π Q (θ + t • v)) 0 := by
    exact fderiv_apply_direction_vector (policy_value_differentiable π Q θ hd)
  rw [← hdir]
  exact policy_gradient_vector θ v π Q hpos hd

/-! ## 定理三：整映射版（∇J 作为连续线性映射）
fderiv J θ = Σ_a (Q a · π θ a) • fderiv (log∘π_a) θ
（对任意方向 v 应用即定理一；v 线性出现的组合形式）。-/

theorem policy_gradient_vector_clm {m : ℕ} (π : E → Fin m → ℝ) (Q : Fin m → ℝ) (θ : E)
    (hpos : ∀ a : Fin m, 0 < π θ a)
    (hd : ∀ a : Fin m, DifferentiableAt ℝ (fun x : E => π x a) θ) :
    fderiv ℝ (fun x : E => PolicyValue π Q x) θ
      = ∑ a : Fin m, ((Q a * π θ a) • fderiv ℝ (fun x : E => Real.log (π x a)) θ) := by
  -- 逐方向与定理一一致（ext v）
  ext v
  calc
    fderiv ℝ (fun x : E => PolicyValue π Q x) θ v
        = ∑ a : Fin m, π θ a * (fderiv ℝ (fun x : E => Real.log (π x a)) θ v) * Q a :=
          policy_gradient_vector θ v π Q hpos hd
    _ = (∑ a : Fin m, ((Q a * π θ a) • fderiv ℝ (fun x : E => Real.log (π x a)) θ)) v := by
          simp [ContinuousLinearMap.smul_apply, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-! ## softmax 策略（特例）：满足主定理的诚实假设
π θ a = exp(s θ a) / Σ_b exp(s θ b)（s : E → Fin m → ℝ 任意得分）。
  1. softmax_policy_pos：0 < π θ a（log 定义域——主定理的假设）；
  2. softmax_policy_pmf：Σ_a π θ a = 1（概率分布归一）。
softmax 的显式 fderiv 展开（score = ∇s − Σ_b π_b·∇s_b，即
fderiv (log∘softmax_a) = fderiv s_a − Σ_b π_b · fderiv s_b）需要
HasFDerivAt.exp + 商的 fderiv 簿记，标注为后续工作。
（本小节只用到 E : Type*，重新声明变量避免携带范数类型类参数。）-/

section Softmax

variable {E : Type*}

def SoftmaxPolicy {m : ℕ} (s : E → Fin m → ℝ) (θ : E) (a : Fin m) : ℝ :=
  Real.exp (s θ a) / ∑ b : Fin m, Real.exp (s θ b)

lemma softmax_policy_pos {m : ℕ} (s : E → Fin m → ℝ) (θ : E) (a : Fin m) :
    0 < SoftmaxPolicy s θ a := by
  unfold SoftmaxPolicy
  have hnum : 0 < Real.exp (s θ a) := Real.exp_pos (s θ a)
  have hden : 0 < ∑ b : Fin m, Real.exp (s θ b) := by
    exact Finset.sum_pos (fun b _ => Real.exp_pos (s θ b)) ⟨a, Finset.mem_univ a⟩
  exact div_pos hnum hden

lemma softmax_policy_pmf {m : ℕ} [NeZero m] (s : E → Fin m → ℝ) (θ : E) :
    ∑ a : Fin m, SoftmaxPolicy s θ a = 1 := by
  unfold SoftmaxPolicy
  have hden : (∑ b : Fin m, Real.exp (s θ b)) ≠ 0 := by
    have hn : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.1 hn
    exact ne_of_gt (Finset.sum_pos (fun b _ => Real.exp_pos (s θ b)) Finset.univ_nonempty)
  calc
    ∑ a : Fin m, (Real.exp (s θ a) / ∑ b : Fin m, Real.exp (s θ b))
        = (∑ a : Fin m, Real.exp (s θ a)) / ∑ b : Fin m, Real.exp (s θ b) := by
          rw [← Finset.sum_div]
    _ = 1 := by
          exact div_self hden

end Softmax

end Lattice
