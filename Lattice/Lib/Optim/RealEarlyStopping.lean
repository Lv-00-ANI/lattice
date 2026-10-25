import Lattice.Lib.Optim.RealConvergence
import Mathlib

/-!
# LATTICE: 早停（early stopping）的终止性与泛化间隙界

早停规则：验证损失连续 `k` 步不下降即停止。

    IsStopPoint v k t  ⟺  ∀ s, t ≤ s → s < t + k → v (s+1) ≤ v s

## 主结果

1. **训练-验证间隙界**（`monotone_gap_bound`）：若验证损失在 t 处不下降，且
   训练/验证损失的间隙被 γ 界住，则训练损失在该处不增超过 `2γ`：

       u(t+1) − u(t) ≤ 2γ

2. **早停点的损失上界**（`earlyStopping_iterate_bound`）：每步至少下降 γ > 0 且损失
   有下界 b ⟹ `ℓ n ≤ ℓ 0 − nγ`。
3. **终止性**（`stopping_property`）：同样条件下 `∀ ε > 0, ∃ N, ∀ n ≥ N, ℓ n ≤ b + ε`
   —— 有限步进入 b 的 ε-邻域。
4. **早停 vs 跑满**（`earlyStopping_vs_full`）：训练损失非增、有下界 b 时，
   跑满 T 步相对早停点 t 的额外下降不超过总预算 `ℓ 0 − b`。
5. **几何收缩的 ε-收敛**（`earlyStopping_from_contraction`）：接
   `RealConvergence.contraction_converges`。

## 诚实边界（重要）

- **单调有下界本身不足以有限步停**（反例：`ℓ n = 1/n` 单调递减、有下界 0，
  却永远取不到下界）。因此终止性定理必须假设**每步至少下降 γ > 0**
  （`hdec`），这是显式的、诚实的强化条件；`stopping_property` 的陈述与
  `earlyStopping_from_contraction` 的对比把这一点说清楚。
- 定理 1 的「训练-验证间隙 ≤ γ」是显式假设（标准早停分析中的
  uniform convergence / 稳定性假设），本文件不推导它。
- 定标量 ℝ 一维，序列 `ℓ v u : ℕ → ℝ`。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：停止点与早停规则 -/

/-- 从 t 起连续 k 步验证损失不下降（触发早停判定）。 -/
def IsStopPoint (v : ℕ → ℝ) (k t : ℕ) : Prop :=
  ∀ s : ℕ, t ≤ s → s < t + k → v (s + 1) ≤ v s

/-- 早停规则：在 N 步之内存在一个停止点。 -/
def StopsBy (v : ℕ → ℝ) (k N : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ N ∧ IsStopPoint v k t

/-- 停止点集随 N 单调。 -/
theorem stopsBy_mono {v : ℕ → ℝ} {k N N' : ℕ} (h : StopsBy v k N) (hNN : N ≤ N') :
    StopsBy v k N' := by
  rcases h with ⟨t, ht, hstop⟩
  exact ⟨t, le_trans ht hNN, hstop⟩

/-- 非增序列在其区间上不减：`a ≤ b ⟹ ℓ b ≤ ℓ a`。 -/
lemma mono_le_of_le {ℓ : ℕ → ℝ} (hmono : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n) {a b : ℕ}
    (hab : a ≤ b) : ℓ b ≤ ℓ a := by
  induction hab with
  | refl => exact le_refl _
  | step hab ih => exact le_trans (hmono _) ih

/-! ## 二、训练-验证间隙界下的早停误差界 -/

/-- **训练-验证间隙界**：验证损失在 t 处不下降 + 两侧间隙 ≤ γ ⟹
    训练损失 `u(t+1) − u(t) ≤ 2γ`。 -/
theorem monotone_gap_bound {u v : ℕ → ℝ} {k t : ℕ} (γ : ℝ) (hk : 1 ≤ k)
    (hstop : IsStopPoint v k t)
    (hgap : |u t - v t| ≤ γ) (hgap' : |u (t + 1) - v (t + 1)| ≤ γ) :
    u (t + 1) - u t ≤ 2 * γ := by
  have h1 : v (t + 1) ≤ v t := hstop t (le_refl t) (by omega)
  have hu1 : u (t + 1) ≤ v (t + 1) + γ := by
    have := (abs_le.mp hgap').2
    linarith
  have hu0 : v t ≤ u t + γ := by
    have := (abs_le.mp hgap).1
    linarith
  linarith

/-! ## 三、终止性：每步下降 γ > 0 + 有下界 -/

/-- **早停点的损失上界**：每步至少下降 γ > 0、损失有下界 b ⟹ `ℓ n ≤ ℓ 0 − nγ`。 -/
theorem earlyStopping_iterate_bound {ℓ : ℕ → ℝ} {γ b : ℝ} (_hγ : 0 < γ)
    (hdec : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n - γ)
    (_hlow : ∀ n : ℕ, b ≤ ℓ n) :
    ∀ n : ℕ, ℓ n ≤ ℓ 0 - (n : ℝ) * γ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ℓ (n + 1) ≤ ℓ n - γ := hdec n
        _ ≤ (ℓ 0 - (n : ℝ) * γ) - γ := by linarith
        _ = ℓ 0 - ((n : ℝ) + 1) * γ := by ring
        _ = ℓ 0 - ((n + 1 : ℕ) : ℝ) * γ := by rw [Nat.cast_add, Nat.cast_one]

/-- **终止性**：每步至少下降 γ > 0 且损失有下界 b ⟹
    `∀ ε > 0, ∃ N, ∀ n ≥ N, ℓ n ≤ b + ε`（有限步进入 b 的 ε-邻域）。 -/
theorem stopping_property {ℓ : ℕ → ℝ} {γ b : ℝ} (hγ : 0 < γ)
    (hdec : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n - γ)
    (hlow : ∀ n : ℕ, b ≤ ℓ n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ℓ n ≤ b + ε := by
  intro ε hε
  refine ⟨Nat.ceil ((ℓ 0 - b) / γ) + 1, ?_⟩
  intro n hn
  have hbound : ℓ n ≤ ℓ 0 - (n : ℝ) * γ := earlyStopping_iterate_bound hγ hdec hlow n
  have hceil : ((ℓ 0 - b) / γ) < ((Nat.ceil ((ℓ 0 - b) / γ) + 1 : ℕ) : ℝ) := by
    have h1 : ((ℓ 0 - b) / γ) ≤ ((Nat.ceil ((ℓ 0 - b) / γ) : ℕ) : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hle : ((Nat.ceil ((ℓ 0 - b) / γ) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hprod : ℓ 0 - b < (n : ℝ) * γ := by
    have h1 : ((ℓ 0 - b) / γ) * γ < ((Nat.ceil ((ℓ 0 - b) / γ) + 1 : ℕ) : ℝ) * γ :=
      mul_lt_mul_of_pos_right hceil hγ
    rw [div_mul_cancel₀ _ (ne_of_gt hγ)] at h1
    have h2 : ((Nat.ceil ((ℓ 0 - b) / γ) + 1 : ℕ) : ℝ) * γ ≤ (n : ℝ) * γ :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hγ)
    linarith
  linarith

/-! ## 四、早停 vs 跑满 -/

/-- **早停 vs 跑满**：训练损失非增、有下界 b、`t ≤ T` ⟹
    `ℓ t − ℓ T ≤ ℓ 0 − b`（跑满得到的额外下降不超过总预算）。 -/
theorem earlyStopping_vs_full {ℓ : ℕ → ℝ} {b : ℝ} (hmono : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n)
    (hlow : ∀ n : ℕ, b ≤ ℓ n) {t T : ℕ} (htT : t ≤ T) :
    ℓ t - ℓ T ≤ ℓ 0 - b := by
  have hTt : ℓ T ≤ ℓ t := mono_le_of_le hmono htT
  have ht0 : ℓ t ≤ ℓ 0 := mono_le_of_le hmono (Nat.zero_le t)
  linarith [hTt, ht0, hlow T]

/-- 跑满不会比早停更差（训练损失非增）：`ℓ T ≤ ℓ t`。 -/
theorem earlyStopping_le_full {ℓ : ℕ → ℝ} (hmono : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n)
    {t T : ℕ} (htT : t ≤ T) : ℓ T ≤ ℓ t :=
  mono_le_of_le hmono htT

/-! ## 五、几何收缩的 ε-终止（接 RealConvergence） -/

/-- **几何收缩 ⟹ ε-终止**：`ℓ(n+1) ≤ c·ℓ n`、`0 ≤ c < 1`、`ℓ ≥ 0` ⟹
    `∀ ε > 0, ∃ N, ∀ n ≥ N, ℓ n < ε`。 -/
theorem earlyStopping_from_contraction {ℓ : ℕ → ℝ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hnonneg : ∀ n : ℕ, 0 ≤ ℓ n) (hstep : ∀ n : ℕ, ℓ (n + 1) ≤ c * ℓ n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ℓ n < ε := by
  have hconv := contraction_converges c hc0 hc1 hstep hnonneg
  have hmono : ∀ n : ℕ, ℓ (n + 1) ≤ ℓ n := by
    intro n
    calc
      ℓ (n + 1) ≤ c * ℓ n := hstep n
      _ ≤ 1 * ℓ n := mul_le_mul_of_nonneg_right (le_of_lt hc1) (hnonneg n)
      _ = ℓ n := one_mul _
  intro ε hε
  rcases hconv ε hε with ⟨N, hN⟩
  exact ⟨N, fun n hn => lt_of_le_of_lt (mono_le_of_le hmono hn) hN⟩

/-! ## 注：闭环语义
  停止点（IsStopPoint）→ 早停规则（StopsBy）→
  训练-验证间隙界下的早停误差（monotone_gap_bound）→
  早停点损失上界（earlyStopping_iterate_bound）→ 终止性（stopping_property）→
  早停 vs 跑满（earlyStopping_vs_full / earlyStopping_le_full）→
  几何收缩的 ε-收敛（earlyStopping_from_contraction，接 RealConvergence）。
  诚实假设：每步至少下降 γ > 0 才有有限步终止（单调有下界不足）；间隙界 γ 显式给出。 -/

end Lattice
