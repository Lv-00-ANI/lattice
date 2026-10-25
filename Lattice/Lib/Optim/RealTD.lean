import Mathlib
import Lattice.Lib.LinearAlgebra.RealBanach
/-!
# LATTICE: 时序差分 —— TD(0) 的收缩与收敛

RealValueIteration（Bellman 收缩 ⟹ 价值迭代收敛）与 RealBanach（Banach 不动点）
处理「模型已知」的价值迭代。本文件给**模型无关**的时序差分 TD(0)：只需单步
采样转移 (next s, r s) 的更新

    V'(s) = V(s) + α·(r(s) + γ·V(next s) − V(s))

其中 next : Fin n → Fin n 为采样后继、r : Fin n → ℝ 为奖励、α ∈ (0,1] 步长、
γ ∈ [0,1) 折扣。

关键观察：TD(0) 是 Bellman 备份 T V (s) = r(s) + γ·V(next s) 的**仿射插值**

    V' = V + α·(T V − V) = (1−α)·V + α·T V

其差只含 (1−α)(V−W) + αγ·(V∘next − W∘next)，故 ∞-范数下是收缩：

    ‖V' − W'‖_∞ ≤ (1 − α + αγ)·‖V − W‖_∞,     c := 1 − α + αγ

α ∈ (0,1]、γ < 1 ⟹ c = 1 − α·(1−γ) ∈ [0,1)（0 ≤ c 且 c < 1）。

定理：
  1. td_target（def TDV）/ td_update（def TDUpdate）：TD(0) 目标与更新；
  2. td_operator_affine：TD 更新 = 仿射插值 V + α(T V − V) = (1−α)V + α T V；
  3. td_contraction_norm：∞-范数收缩（‖·‖ 形式，系数 c = 1−α+αγ）；
  4. td_contraction：同上的 LinfNorm（sSup）形式（接 RealValueIteration 风格）；
  5. td_converges：收缩 ⟹ 任意两初值的 TD 迭代差 ε-收敛
     （接 RealConvergence 的 contraction_converges）；
  6. td_contracting / td_fixed_point_exists：ContractingWith 形式 ⟹
     TD 不动点 V* 存在（Banach 闭合，接 RealBanach 的 exists_fixedPoint）；
  7. td_fixed_point_is_value / td_fixed_point_eq_bellman：TD 不动点满足
     Bellman 方程 r s + γ·V(next s) = V s（即 V = T V）——TD 收敛到的正是价值函数。

模型无关：任意状态数 n、任意确定性采样后继、任意奖励、α ∈ (0,1]、γ ∈ [0,1)。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## TD(0) 目标：单步 Bellman 备份
T V (s) = r s + γ·V(next s)。 -/

def TDV (next : Fin n → Fin n) (r : Fin n → ℝ) (γ : ℝ) (V : Fin n → ℝ) : Fin n → ℝ :=
  fun s => r s + γ * V (next s)

/-! ## TD(0) 更新
V' s = V s + α·(r s + γ·V(next s) − V s)（步长 α 的 Bellman 备份插值）。 -/

def TDUpdate (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ) (V : Fin n → ℝ) : Fin n → ℝ :=
  fun s => V s + α * (r s + γ * V (next s) - V s)

/-! ## 定理一：TD(0) 更新是仿射插值
V + α(T V − V) = (1−α)·V + α·T V（逐点代数恒等式）。 -/

theorem td_operator_affine (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (V : Fin n → ℝ) :
    TDUpdate next r γ α V
      = fun s => (1 - α) * V s + α * (r s + γ * V (next s)) := by
  funext s
  unfold TDUpdate
  ring

/-! ## 定理二（核心）：TD(0) 是 ∞-范数收缩（‖·‖ 形式）
‖TD(V) − TD(W)‖ ≤ (1−α+αγ)·‖V − W‖（α ∈ (0,1]、γ ≥ 0）。 -/

theorem td_contraction_norm (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hγ0 : 0 ≤ γ) (_hγ1 : γ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (V W : Fin n → ℝ) :
    ‖TDUpdate next r γ α V - TDUpdate next r γ α W‖
      ≤ (1 - α + α * γ) * ‖V - W‖ := by
  have hc0 : 0 ≤ 1 - α + α * γ := by nlinarith [hα1, hγ0, hα0.le]
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc0 (norm_nonneg (V - W)))).2 ?_
  intro s
  -- 逐点差：奖励 r 抵消，只剩 (1−α)(V−W) + αγ·(V∘next − W∘next)
  have hD : (TDUpdate next r γ α V - TDUpdate next r γ α W) s
      = (1 - α) * (V s - W s) + (α * γ) * (V (next s) - W (next s)) := by
    show TDUpdate next r γ α V s - TDUpdate next r γ α W s = _
    unfold TDUpdate
    ring
  rw [Real.norm_eq_abs, hD]
  -- 分量 ≤ ∞-范数（Pi sup 范数）
  have h1 : |V s - W s| ≤ ‖V - W‖ := by
    have h := norm_le_pi_norm (V - W) s
    rwa [Real.norm_eq_abs] at h
  have h2 : |V (next s) - W (next s)| ≤ ‖V - W‖ := by
    have h := norm_le_pi_norm (V - W) (next s)
    rwa [Real.norm_eq_abs] at h
  calc
    |(1 - α) * (V s - W s) + (α * γ) * (V (next s) - W (next s))|
        ≤ |(1 - α) * (V s - W s)| + |(α * γ) * (V (next s) - W (next s))| := abs_add _ _
    _ = (1 - α) * |V s - W s| + (α * γ) * |V (next s) - W (next s)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - α),
            abs_of_nonneg (mul_nonneg hα0.le hγ0)]
    _ ≤ (1 - α) * ‖V - W‖ + (α * γ) * ‖V - W‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left h1 (by linarith))
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg hα0.le hγ0))
    _ = (1 - α + α * γ) * ‖V - W‖ := by ring

/-! ## 定理三：TD(0) 收缩（LinfNorm / sSup 形式）
LinfNorm(T(V) − T(W)) ≤ c·LinfNorm(V − W)（接 RealValueIteration 的 ∞-范数）。 -/

theorem td_contraction (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (V W : Fin n → ℝ) :
    LinfNorm (fun s => TDUpdate next r γ α V s - TDUpdate next r γ α W s)
      ≤ (1 - α + α * γ) * LinfNorm (fun s => V s - W s) := by
  -- 桥：LinfNorm = Pi sup 范数（RealBanach.linfNorm_eq_norm）
  rw [linfNorm_eq_norm, linfNorm_eq_norm]
  simpa using td_contraction_norm next r γ α hγ0 hγ1 hα0 hα1 V W

/-! ## 定理四（核心）：TD(0) 迭代 ε-收敛
c = 1−α+αγ < 1 ⟹ 任意两初值的 TD 迭代差最终任意小
（接 RealConvergence.contraction_converges）。 -/

theorem td_converges (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (V₀ V₁ : Fin n → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℕ,
      LinfNorm (fun s => ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₁ s
        - ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₀ s) < ε := by
  have hc0 : 0 ≤ 1 - α + α * γ := by nlinarith [hα1, hγ0, hα0.le]
  have hc1 : 1 - α + α * γ < 1 := by nlinarith [hα0, hγ1]
  let e : ℕ → ℝ := fun t => LinfNorm (fun s => ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₁ s
      - ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₀ s)
  have hnonneg : ∀ t : ℕ, 0 ≤ e t := by intro t; dsimp only [e]; exact linfNorm_nonneg _
  have hstep : ∀ t : ℕ, e (t + 1) ≤ (1 - α + α * γ) * e t := by
    intro t
    -- 单步：e(t+1) = LinfNorm(TD(V_t) − TD(W_t)) ≤ c·e(t)
    have h := td_contraction next r γ α hγ0 hγ1 hα0 hα1
      (ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₁)
      (ChainFwd (fun _ : ℕ => TDUpdate next r γ α) t V₀)
    dsimp only [e]
    simpa [ChainFwd] using h
  intro ε hε
  obtain ⟨t, ht⟩ := contraction_converges (1 - α + α * γ) hc0 hc1 hstep hnonneg ε hε
  exact ⟨t, ht⟩

/-! ## 定理五：TD(0) 是 ContractingWith（Banach 收缩条件）
α ∈ (0,1]、γ < 1 ⟹ TDUpdate 是 c = 1−α+αγ < 1 的收缩映射。 -/

theorem td_contracting (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContractingWith ⟨1 - α + α * γ, by nlinarith [hα1, hγ0, hα0.le]⟩
      (TDUpdate next r γ α) := by
  have hc0 : 0 ≤ 1 - α + α * γ := by nlinarith [hα1, hγ0, hα0.le]
  have hc1 : 1 - α + α * γ < 1 := by nlinarith [hα0, hγ1]
  constructor
  · simpa using hc1
  · rw [LipschitzWith]
    intro V W
    rw [edist_dist, edist_dist]
    rw [ENNReal.coe_nnreal_eq (⟨1 - α + α * γ, hc0⟩ : NNReal)]
    simp
    rw [← ENNReal.ofReal_mul hc0]
    exact ENNReal.ofReal_le_ofReal (td_contraction_norm next r γ α hγ0 hγ1 hα0 hα1 V W)

/-! ## 定理六：TD 不动点存在（Banach 闭合）
c < 1 ⟹ 存在 V* 使 TDUpdate V* = V*（接 exists_fixedPoint）。 -/

theorem td_fixed_point_exists (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hα0 : 0 < α) (hα1 : α ≤ 1) (V₀ : Fin n → ℝ) :
    ∃ Vstar : Fin n → ℝ, TDUpdate next r γ α Vstar = Vstar := by
  have hc := td_contracting next r γ α hγ0 hγ1 hα0 hα1
  have hfinite : edist V₀ (TDUpdate next r γ α V₀) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  rcases (ContractingWith.exists_fixedPoint hc V₀ hfinite) with ⟨Vstar, hfix, _, _⟩
  exact ⟨Vstar, hfix⟩

/-! ## 定理七：TD 不动点满足 Bellman 方程
α ≠ 0 且 TDUpdate V = V ⟹ r s + γ·V(next s) = V s（逐状态 Bellman 方程）。 -/

theorem td_fixed_point_is_value (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hα : α ≠ 0) (V : Fin n → ℝ) (hfix : TDUpdate next r γ α V = V) (s : Fin n) :
    r s + γ * V (next s) = V s := by
  have h := congr_fun hfix s
  have hzero : α * (r s + γ * V (next s) - V s) = 0 := by
    unfold TDUpdate at h
    linarith
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact absurd h1 hα
  · linarith

/-! ## 定理八：TD 不动点 = Bellman 备份不动点
TDUpdate V = V ⟹ T V = V（函数等式形式，T = TDV）。 -/

theorem td_fixed_point_eq_bellman (next : Fin n → Fin n) (r : Fin n → ℝ) (γ α : ℝ)
    (hα : α ≠ 0) (V : Fin n → ℝ) (hfix : TDUpdate next r γ α V = V) :
    TDV next r γ V = V := by
  funext s
  exact td_fixed_point_is_value next r γ α hα V hfix s

/-! ## 注：TD(0) 闭环
  仿射插值（定理一）⟹ ∞-范数收缩（定理二/三）⟹ 迭代差 ε-收敛（定理四）
  与 Banach 不动点存在（定理五/六）；不动点满足 Bellman 方程（定理七/八）
  —— TD(0) 收敛到的正是价值函数 V* = T(V*)，与 RealValueIteration 的
  「模型已知」价值迭代殊途同归：两者都是 Bellman 算子的收缩迭代，
  差别只在 T 用全期望（行随机 P）还是单样本后继 next。
  收缩系数 c = 1 − α·(1−γ) < 1 是 α ∈ (0,1]、γ < 1 的直接推论。 -/

end Lattice
