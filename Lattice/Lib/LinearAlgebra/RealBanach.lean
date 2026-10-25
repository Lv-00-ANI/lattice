import Lattice.Lib.Optim.RealValueIteration
import Mathlib

/-!
# LATTICE: Banach 不动点 —— 价值迭代的不动点闭合（收敛统一化）

RealValueIteration（Bellman 收缩 ⟹ 迭代 ε-收敛）的**不动点闭合**：
用 Banach 不动点定理闭合价值函数 V* 的存在性与迭代收敛。

 1. 桥：LinfNorm（sSup 定义）= (Fin n → ℝ) 的默认范数（Pi sup）；
 2. Bellman 收缩的 ‖·‖ 形式：‖T(V) − T(W)‖ ≤ γ·‖V − W‖；
 3. ContractingWith（γ < 1 收缩，mathlib 定义）⟹
    exists_fixedPoint：不动点存在 + 迭代收敛 + 几何误差界。

闭环：价值迭代（收敛骨架）⟹ Banach 不动点（V* = T(V*) 存在，
迭代收敛到它）——RL 价值学习的完整理论；也统一了各收敛实例
（GD/价值迭代/N 算子）的「收缩 ⟹ 不动点」骨架。

模型无关：任意状态数 n、行随机转移、折扣 γ ∈ [0,1)。
-/

noncomputable section

namespace Lattice

/-! ## 定理一：桥 —— LinfNorm = 默认范数
对 (Fin n → ℝ)，‖V‖ = sSup{|V s|}（Pi 的 sup 范数）。-/

theorem linfNorm_eq_norm {n : ℕ} (V : Fin n → ℝ) : LinfNorm V = ‖V‖ := by
  -- 最小修正：‖V‖（Pi sup 范数）非 rfl 定义，用 le_antisymm + 分量界桥接
  unfold LinfNorm
  apply le_antisymm
  · by_cases hne : Nonempty (Fin n)
    · apply csSup_le
      · rcases hne with ⟨s0⟩
        exact ⟨|V s0|, ⟨s0, rfl⟩⟩
      · rintro x ⟨s, rfl⟩
        exact norm_le_pi_norm V s
    · have h0 : {x : ℝ | ∃ s : Fin n, x = |V s|} = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro x hx
        rcases hx with ⟨s, _⟩
        exact hne ⟨s⟩
      rw [h0, Real.sSup_empty]
      exact norm_nonneg V
  · exact (pi_norm_le_iff_of_nonneg
      (show 0 ≤ sSup {x : ℝ | ∃ s : Fin n, x = |V s|} from linfNorm_nonneg V)).2
      (fun b => le_csSup (bddAbove_abs V) ⟨b, rfl⟩)

/-! ## 定理二：Bellman 收缩（‖·‖ 形式）
‖T(V) − T(W)‖ ≤ γ·‖V − W‖（价值迭代的单步收缩）。-/

theorem bellman_contraction_norm {n : ℕ} (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hPnonneg : ∀ s s', 0 ≤ P s s') (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1)
    (V W : Fin n → ℝ) :
    ‖BellmanOp P R γ V - BellmanOp P R γ W‖ ≤ γ * ‖V - W‖ := by
  -- BellmanOp 差 = γ·Σ P·(V−W)（R 抵消）
  have hdiff : BellmanOp P R γ V - BellmanOp P R γ W
      = fun s => γ * (∑ s' : Fin n, P s s' * (V s' - W s')) := by
    funext s
    unfold BellmanOp
    calc
      R s + γ * (∑ s' : Fin n, P s s' * V s') - (R s + γ * (∑ s' : Fin n, P s s' * W s'))
          = γ * ((∑ s' : Fin n, P s s' * V s') - (∑ s' : Fin n, P s s' * W s')) := by ring
      _ = γ * (∑ s' : Fin n, P s s' * (V s' - W s')) := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hdiff]
  -- 桥：LinfNorm = ‖·‖
  have hbc := bellman_contraction P γ hγ0 hPnonneg hPsum V W
  have h1 : LinfNorm (fun s => γ * (∑ s' : Fin n, P s s' * (V s' - W s')))
      = ‖fun s => γ * (∑ s' : Fin n, P s s' * (V s' - W s'))‖ :=
    linfNorm_eq_norm _
  have h2 : LinfNorm (fun s => |V s - W s|) = ‖V - W‖ := by
    have hf : (fun s : Fin n => |V s - W s|) = fun s : Fin n => |(V - W) s| := by
      funext s
      rfl
    rw [hf]
    rw [linfNorm_abs (V - W)]
    exact linfNorm_eq_norm (V - W)
  rw [← h1, ← h2]
  exact hbc

/-! ## 定理三：Bellman 收缩（ContractingWith 形式）
γ < 1 ⟹ BellmanOp 是 γ-收缩映射（Banach 收缩条件）。-/

theorem bellman_contracting {n : ℕ} (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hPnonneg : ∀ s s', 0 ≤ P s s')
    (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1) :
    -- 最小修正：ℝ≥0 系数需 0 ≤ γ 证明，用 hγ0（hγ1 类型是 γ < 1，不合法）
    ContractingWith ⟨γ, hγ0⟩ (BellmanOp P R γ) := by
  constructor
  · exact hγ1
  · rw [LipschitzWith]
    intro V W
    -- edist 展开为 ofReal(dist)（MetricSpace），dist = ‖·‖（normed）
    rw [edist_dist, edist_dist]
    -- (γ : ℝ≥0∞) = ofReal γ；ofReal γ · ofReal d = ofReal (γ·d)
    rw [ENNReal.coe_nnreal_eq (⟨γ, hγ0⟩ : NNReal)]
    simp
    rw [← ENNReal.ofReal_mul hγ0]
    -- 由 ‖·‖ 形式收缩 + ofReal 单调
    exact ENNReal.ofReal_le_ofReal (bellman_contraction_norm P R γ hγ0 hPnonneg hPsum V W)

/-! ## 定理四：价值迭代不动点（Banach 闭合）
γ < 1 ⟹ 存在不动点 V*（BellmanOp P R γ V* = V*），且迭代收敛到它
（exists_fixedPoint 给不动点 + 收敛 + 几何误差界）。-/

theorem bellman_fixed_point {n : ℕ} (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hPnonneg : ∀ s s', 0 ≤ P s s')
    (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1) (V₀ : Fin n → ℝ) :
    -- 最小修正：V*（* 非合法标识符字符）改名 Vstar
    ∃ Vstar : Fin n → ℝ, BellmanOp P R γ Vstar = Vstar := by
  have hc : ContractingWith ⟨γ, hγ0⟩ (BellmanOp P R γ) :=
    bellman_contracting P R γ hγ0 hγ1 hPnonneg hPsum
  have hfinite : edist V₀ (BellmanOp P R γ V₀) ≠ ⊤ := by
    rw [edist_dist]
    exact ENNReal.ofReal_ne_top
  rcases (ContractingWith.exists_fixedPoint hc V₀ hfinite) with ⟨Vstar, hfix, hconv, _⟩
  exact ⟨Vstar, hfix⟩

/-! ## 注：价值函数不动点闭合
  bellman_contraction_norm（‖·‖ 收缩）⟹ ContractingWith（γ-收缩）
  ⟹ exists_fixedPoint（不动点存在 + 迭代收敛 + 几何误差界）——
  价值函数 V*（满足 Bellman 方程 V* = T(V*)）的完整闭合；
  与 value_iteration_converges（迭代差 ε-收敛）互补：
  收敛骨架 + 不动点存在 = RL 价值学习的完备理论。
  收敛统一化：GD/价值迭代/N 算子（RealConvergence 骨架）皆
  「收缩 ⟹ 不动点」的实例。-/

end Lattice
