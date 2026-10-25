import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: RL 价值函数 —— Bellman 算子收缩 ⟹ 价值迭代收敛

RL 完整目标（VERIFICATION 剩余项）的价值函数部分：
有限状态 MDP（状态 Fin n），折扣 γ（0 ≤ γ < 1），转移 P（行随机），
Bellman 算子

    T(V)(s) = R(s) + γ·Σ_{s'} P(s,s')·V(s')

满足收缩性质（∞ 范数）：

    ‖T(V) − T(V')‖_∞ ≤ γ·‖V − V'‖_∞

（回报 R 抵消；|γ·Σ P·d| ≤ γ·(ΣP)·max|d| = γ·max|d|，行随机 ΣP = 1）

⟹ 价值迭代 V_{t+1} = T(V_t) 的迭代差几何收缩：

    ‖T^t(V₁) − T^t(V₀)‖_∞ ≤ γ^t·‖V₁ − V₀‖_∞

且 γ < 1 ⟹ 迭代差最终任意小（ε-收敛，衔接 RealConvergence
的等比序列终止）。

价值迭代收敛（V_t → V*，不动点 V* = T(V*)）是 RL 价值学习的
理论基础；本文件给收敛的收缩骨架（不动点存在性即 Banach，
标注为依赖）。

模型无关：任意状态数 n、任意行随机转移、任意折扣 γ ∈ [0,1)。
-/

noncomputable section

namespace Lattice

variable {n : ℕ}

/-! ## ∞ 范数（sSup 定义，Fin n 上） -/

def LinfNorm (V : Fin n → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ s : Fin n, x = |V s|}

/-! 辅助：有限值域集合有上界（ℝ 为 ConditionallyComplete，非 CompleteLattice，
故用 le_csSup/csSup_le 而非 le_sSup/sSup_le；空集时 sSup ∅ = 0）。 -/

lemma bddAbove_abs (V : Fin n → ℝ) : BddAbove {x : ℝ | ∃ s : Fin n, x = |V s|} := by
  convert (Set.Finite.bddAbove (Set.finite_range (fun s : Fin n => |V s|)) :
      BddAbove (Set.range (fun s : Fin n => |V s|))) using 1
  ext x
  constructor <;> rintro ⟨s, rfl⟩ <;> exact ⟨s, rfl⟩

lemma linfNorm_abs (V : Fin n → ℝ) : LinfNorm (fun s => |V s|) = LinfNorm V := by
  unfold LinfNorm
  congr 1
  ext x
  constructor <;> rintro ⟨s, rfl⟩ <;> exact ⟨s, by rw [abs_abs]⟩

lemma linfNorm_nonneg (V : Fin n → ℝ) : 0 ≤ LinfNorm V := by
  unfold LinfNorm
  by_cases h : Nonempty (Fin n)
  · rcases h with ⟨s⟩
    exact le_trans (abs_nonneg (V s)) (le_csSup (bddAbove_abs V) (by exact ⟨s, rfl⟩))
  · have h0 : {x : ℝ | ∃ s : Fin n, x = |V s|} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      rcases hx with ⟨s, _⟩
      exact h ⟨s⟩
    rw [h0, Real.sSup_empty]

/-! ## Bellman 算子（策略评估/价值迭代） -/

def BellmanOp (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ) (V : Fin n → ℝ) (s : Fin n) : ℝ :=
  R s + γ * (∑ s' : Fin n, P s s' * V s')

/-! ## 定理一：Bellman 算子收缩（∞ 范数）
‖T(V) − T(V')‖_∞ ≤ γ·‖V − V'‖_∞（回报抵消，行随机 ΣP = 1）。-/

theorem bellman_contraction (P : Fin n → Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hPnonneg : ∀ s s', 0 ≤ P s s')
    (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1)
    (V V' : Fin n → ℝ) :
    LinfNorm (fun s => γ * (∑ s' : Fin n, P s s' * (V s' - V' s')))
      ≤ γ * LinfNorm (fun s => |V s - V' s|) := by
  -- LinfNorm (|V - V'|) = LinfNorm (V - V')（abs_abs），统一值域集合
  rw [linfNorm_abs (fun s => V s - V' s)]
  unfold LinfNorm
  by_cases hne : Nonempty (Fin n)
  · -- 非空：csSup_le（ℝ 是 ConditionallyComplete，非 CompleteLattice）
    apply csSup_le
    · rcases hne with ⟨s0⟩
      exact ⟨|γ * (∑ s' : Fin n, P s0 s' * (V s' - V' s'))|, ⟨s0, rfl⟩⟩
    · intro x hx
      rcases hx with ⟨s, rfl⟩
      calc
        |γ * (∑ s' : Fin n, P s s' * (V s' - V' s'))|
            = γ * |∑ s' : Fin n, P s s' * (V s' - V' s')| := by
              rw [abs_mul, abs_of_nonneg hγ0]
        _ ≤ γ * (∑ s' : Fin n, |P s s' * (V s' - V' s')|) := by
              exact mul_le_mul_of_nonneg_left
                (Finset.abs_sum_le_sum_abs (fun s' => P s s' * (V s' - V' s')) Finset.univ) hγ0
        _ ≤ γ * (∑ s' : Fin n, P s s' * sSup {x : ℝ | ∃ s, x = |V s - V' s|}) := by
              have hstep : ∀ s' : Fin n, s' ∈ Finset.univ →
                  |P s s' * (V s' - V' s')| ≤ P s s' * sSup {x : ℝ | ∃ s, x = |V s - V' s|} := by
                intro s' hs'
                calc
                  |P s s' * (V s' - V' s')| ≤ P s s' * |V s' - V' s'| := by
                        rw [abs_mul, abs_of_nonneg (hPnonneg s s')]
                  _ ≤ P s s' * sSup {x : ℝ | ∃ s, x = |V s - V' s|} := by
                        exact mul_le_mul_of_nonneg_left
                          (le_csSup (bddAbove_abs (fun s => V s - V' s)) (by exact ⟨s', rfl⟩))
                          (hPnonneg s s')
              exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hγ0
        _ = γ * sSup {x : ℝ | ∃ s, x = |V s - V' s|} := by
              rw [← Finset.sum_mul]
              rw [hPsum s]
              simp
  · -- 空（Fin n 无元素）：两边 sSup ∅ = 0
    have hL : {x : ℝ | ∃ s : Fin n, x = |γ * (∑ s' : Fin n, P s s' * (V s' - V' s'))|} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      rcases hx with ⟨s, _⟩
      exact hne ⟨s⟩
    have hR : {x : ℝ | ∃ s : Fin n, x = |V s - V' s|} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      rcases hx with ⟨s, _⟩
      exact hne ⟨s⟩
    simp [hL, hR, Real.sSup_empty]

/-! ## 定理二：价值迭代几何收缩
‖T^t(V₁) − T^t(V₀)‖_∞ ≤ γ^t·‖V₁ − V₀‖_∞（迭代差指数衰减）。-/

theorem value_iteration_contraction (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (_hγ1 : γ < 1) (hPnonneg : ∀ s s', 0 ≤ P s s')
    (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1) (V₀ V₁ : Fin n → ℝ) :
    ∀ t : ℕ, LinfNorm (fun s => ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁ s
        - ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀ s)
      ≤ γ ^ t * LinfNorm (fun s => V₁ s - V₀ s) := by
  intro t
  induction t with
  | zero =>
      simp [ChainFwd]
  | succ t ih =>
      calc
        LinfNorm (fun s => ChainFwd (fun _ : ℕ => BellmanOp P R γ) (t + 1) V₁ s
            - ChainFwd (fun _ : ℕ => BellmanOp P R γ) (t + 1) V₀ s)
            = LinfNorm (fun s => BellmanOp P R γ (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁) s
                - BellmanOp P R γ (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀) s) := by
              simp [ChainFwd]
        _ ≤ γ * LinfNorm (fun s => |ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁ s
            - ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀ s|) := by
              -- Bellman 算子差（R 抵消）：T(V₁') - T(V₀') = γ·ΣP·(V₁'-V₀')
              -- 注意 ChainFwd 层的 BellmanOp 差正是定理一的形状
              have hdiff : ∀ s : Fin n,
                  BellmanOp P R γ (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁) s
                  - BellmanOp P R γ (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀) s
                  = γ * (∑ s' : Fin n, P s s' * (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁ s'
                      - ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀ s')) := by
                intro s
                unfold BellmanOp
                -- R(s) 抵消；γ·ΣP·V₁ - γ·ΣP·V₀ = γ·ΣP·(V₁-V₀)
                simp [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
              have hb := bellman_contraction P γ hγ0 hPnonneg hPsum
                (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁) (ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀)
              -- hb : LinfNorm (fun s => γ·ΣP·(V₁' - V₀')) ≤ γ·LinfNorm (|V₁' - V₀'|)
              -- 目标：LinfNorm (fun s => T(V₁')s - T(V₀')s) ≤ γ·LinfNorm (|V₁' - V₀'|)
              -- 由 hdiff 逐点替换
              simpa [hdiff] using hb
        _ = γ * LinfNorm (fun s => ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁ s
            - ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀ s) := by
              -- |a - b| 的 LinfNorm 与 (a - b) 的相同（linfNorm_abs）
              rw [linfNorm_abs]
        _ ≤ γ * (γ ^ t * LinfNorm (fun s => V₁ s - V₀ s)) := by
              exact mul_le_mul_of_nonneg_left ih hγ0
        _ = γ ^ (t + 1) * LinfNorm (fun s => V₁ s - V₀ s) := by
              rw [pow_succ]
              ring

/-! ## 定理三：价值迭代 ε-收敛
γ < 1 ⟹ 迭代差最终任意小（衔接 RealConvergence 等比终止）。-/

theorem value_iteration_converges (P : Fin n → Fin n → ℝ) (R : Fin n → ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hPnonneg : ∀ s s', 0 ≤ P s s')
    (hPsum : ∀ s, (∑ s' : Fin n, P s s') = 1) (V₀ V₁ : Fin n → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℕ,
      LinfNorm (fun s => ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₁ s
        - ChainFwd (fun _ : ℕ => BellmanOp P R γ) t V₀ s) < ε := by
  intro ε hε
  have hM0 : 0 ≤ LinfNorm (fun s => V₁ s - V₀ s) := linfNorm_nonneg _
  -- γ^t·M 最终 < ε（γ < 1，等比终止）
  rcases (geom_contraction_eventually γ (LinfNorm (fun s => V₁ s - V₀ s)) hγ0 hγ1 hM0 ε hε)
    with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  exact lt_of_le_of_lt (value_iteration_contraction P R γ hγ0 hγ1 hPnonneg hPsum V₀ V₁ t) ht

/-! ## 注：RL 语义
  Bellman 算子收缩（定理一）⟹ 价值迭代收敛（定理二/三）：
  V_t → V*（不动点，Banach 依赖标注）；V* 满足 Bellman 方程
  V* = T(V*)。策略评估/价值迭代的收敛骨架完成——RL 完整目标
  的「价值」半边（策略半边 = 策略梯度，需概率测度，另文）。
  模型无关：行随机转移 + 折扣 [0,1) 是唯一假设。-/

end Lattice
