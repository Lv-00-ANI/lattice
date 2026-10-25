import Lattice.Lib.Convex.RealSubgradientDescent
import Lattice.Lib.Optim.RealConvergence
import Mathlib

/-!
# LATTICE: 持续学习的灾难性遗忘界（EWC 与回放）

持续学习中，学习新任务会改变参数 θ，从而**抬高旧任务的损失**（灾难性遗忘）。
本文件把遗忘量化为「参数漂移 × 损失 Lipschitz 常数」，并给出两条正则化路线的界：

- **EWC（弹性权重巩固）**：Fisher 加权二次惩罚 `(F/2)(θ − θ_old)²`；
- **回放（replay）**：限制每步漂移，从而限制累积漂移。

## 主结果

1. **遗忘界**（`forgetting_bound`）：损失 `L_i` 以常数 Λ 是 Lipschitz 的 ⟹

       |L_i(θ_after) − L_i(θ_before)| ≤ Λ·|θ_after − θ_before|

2. **EWC 漂移界**（`ewc_drift_bound`）：`F > 0`、惩罚 ≤ λ ⟹

       |θ − θ_old| ≤ √(2λ/F)

3. **EWC 遗忘界**（`ewc_forgetting_bound`）：合并 1、2 得

       |遗忘| ≤ Λ·√(2λ/F)     —— **与训练步数 T 无关**

4. **回放漂移与遗忘界**（`drift_bound_of_step` / `replay_bound`）：每步漂移 ≤ ηG ⟹

       |θ_T − θ_0| ≤ T·η·G,    |遗忘| ≤ Λ·T·η·G     —— **随 T 线性增长**

5. **对照**（`replay_forgetting_unbounded`）：无正则时遗忘界随 T 无界（`∀ B, ∃ T, B < ΛT`），
   这正是「灾难性遗忘」的量化表述。

## 诚实边界

- 损失 Lipschitz 常数 Λ（`IsLip`）与 EWC 惩罚预算 λ 是**显式假设**；
  本文件不构造 Fisher 信息矩阵，也不从二次损失推出 Lipschitz 常数。
- EWC 的漂移界来自「惩罚项 ≤ λ」这一预算假设，不来自 EWC 优化过程的收敛分析。
- 一维参数 θ : ℝ（与项目其它 Real* 文件同口径）。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：任务损失、遗忘、EWC 惩罚、Lipschitz 常数 -/

/-- 多任务损失：任务 `i` 在参数 θ 处的损失。 -/
def taskLoss {ι : Type*} (L : ι → ℝ → ℝ) (θ : ℝ) (i : ι) : ℝ := L i θ

/-- 任务 `i` 的遗忘量：参数变化后与变化前的损失差。 -/
def forgetting {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (θafter θbefore : ℝ) : ℝ :=
  L i θafter - L i θbefore

/-- 任务 `i` 的损失以常数 Λ 是 Lipschitz 的。 -/
def IsLip {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (Λ : ℝ) : Prop :=
  ∀ a b : ℝ, |L i a - L i b| ≤ Λ * |a - b|

/-- EWC 的 Fisher 加权二次惩罚：`(F/2)(θ − θ_old)²`。 -/
def ewcPenalty (F θ θold : ℝ) : ℝ := (F / 2) * (θ - θold) ^ 2

/-- 回放的梯度预算：`T·η·G`。 -/
def replayGradientBudget (η G : ℝ) (T : ℕ) : ℝ := (T : ℝ) * η * G

/-! ## 二、遗忘界：漂移 × Lipschitz 常数 -/

/-- **遗忘界**：`|L_i(θ_after) − L_i(θ_before)| ≤ Λ·|θ_after − θ_before|`。 -/
theorem forgetting_bound {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (Λ θafter θbefore : ℝ)
    (hLip : IsLip L i Λ) :
    |forgetting L i θafter θbefore| ≤ Λ * |θafter - θbefore| :=
  hLip θafter θbefore

/-- 无漂移 ⟹ 无遗忘。 -/
theorem forgetting_self {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (θ : ℝ) :
    forgetting L i θ θ = 0 := by
  simp [forgetting]

/-- 漂移被 d 界住 ⟹ 遗忘被 Λ·d 界住。 -/
theorem forgetting_bound_of_drift {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (Λ θafter θbefore d : ℝ)
    (hΛ : 0 ≤ Λ) (hLip : IsLip L i Λ) (hdrift : |θafter - θbefore| ≤ d) :
    |forgetting L i θafter θbefore| ≤ Λ * d := by
  calc
    |forgetting L i θafter θbefore| ≤ Λ * |θafter - θbefore| := forgetting_bound L i Λ _ _ hLip
    _ ≤ Λ * d := mul_le_mul_of_nonneg_left hdrift hΛ

/-! ## 三、EWC：惩罚预算 ⟹ 漂移界 ⟹ 遗忘界 -/

/-- EWC 惩罚非负（`F ≥ 0`）。 -/
theorem ewcPenalty_nonneg (F θ θold : ℝ) (hF : 0 ≤ F) : 0 ≤ ewcPenalty F θ θold := by
  unfold ewcPenalty
  exact mul_nonneg (div_nonneg hF (by norm_num)) (sq_nonneg _)

/-- **EWC 漂移界**：`F > 0`、`(F/2)(θ − θ_old)² ≤ λ` ⟹ `|θ − θ_old| ≤ √(2λ/F)`。 -/
theorem ewc_drift_bound (F θ θold lam : ℝ) (hF : 0 < F)
    (hpen : ewcPenalty F θ θold ≤ lam) :
    |θ - θold| ≤ Real.sqrt (2 * lam / F) := by
  have hsq : (θ - θold) ^ 2 ≤ 2 * lam / F := by
    have hmul : (F / 2) * (θ - θold) ^ 2 * 2 ≤ lam * 2 :=
      mul_le_mul_of_nonneg_right hpen (by norm_num)
    have hkey : F * (θ - θold) ^ 2 ≤ 2 * lam := by
      unfold ewcPenalty at hmul
      linarith
    rw [le_div_iff₀ hF]
    nlinarith [hkey]
  calc
    |θ - θold| = Real.sqrt ((θ - θold) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (2 * lam / F) := Real.sqrt_le_sqrt hsq

/-- **EWC 遗忘界**：Lipschitz Λ + 惩罚预算 λ ⟹ `|遗忘| ≤ Λ·√(2λ/F)`（与 T 无关）。 -/
theorem ewc_forgetting_bound {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (Λ F θ θold lam : ℝ)
    (hΛ : 0 ≤ Λ) (hF : 0 < F) (hLip : IsLip L i Λ)
    (hpen : ewcPenalty F θ θold ≤ lam) :
    |forgetting L i θ θold| ≤ Λ * Real.sqrt (2 * lam / F) := by
  calc
    |forgetting L i θ θold| ≤ Λ * |θ - θold| := forgetting_bound L i Λ _ _ hLip
    _ ≤ Λ * Real.sqrt (2 * lam / F) :=
      mul_le_mul_of_nonneg_left (ewc_drift_bound F θ θold lam hF hpen) hΛ

/-! ## 四、回放：每步漂移有界 ⟹ 累积漂移线性增长 -/

/-- **累积漂移界**：每步 `|θ_{t+1} − θ_t| ≤ D` ⟹ `|θ_T − θ_0| ≤ T·D`。 -/
theorem drift_bound_of_step {θ : ℕ → ℝ} (D : ℝ)
    (hstep : ∀ t : ℕ, |θ (t + 1) - θ t| ≤ D) :
    ∀ T : ℕ, |θ T - θ 0| ≤ (T : ℝ) * D := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        |θ (T + 1) - θ 0| = |(θ (T + 1) - θ T) + (θ T - θ 0)| := by
          congr 1
          ring
        _ ≤ |θ (T + 1) - θ T| + |θ T - θ 0| := abs_add _ _
        _ ≤ D + (T : ℝ) * D := add_le_add (hstep T) ih
        _ = ((T : ℝ) + 1) * D := by ring
        _ = ((T + 1 : ℕ) : ℝ) * D := by rw [Nat.cast_add, Nat.cast_one]

/-- **回放遗忘界**：每步漂移 ≤ ηG ⟹ `|遗忘| ≤ Λ·T·η·G`（随 T 线性增长）。 -/
theorem replay_bound {ι : Type*} (L : ι → ℝ → ℝ) (i : ι) (Λ η G : ℝ) (T : ℕ)
    (θ : ℕ → ℝ) (hΛ : 0 ≤ Λ) (hLip : IsLip L i Λ)
    (hstep : ∀ t : ℕ, |θ (t + 1) - θ t| ≤ η * G) :
    |forgetting L i (θ T) (θ 0)| ≤ Λ * ((T : ℝ) * η * G) := by
  have hdrift : |θ T - θ 0| ≤ (T : ℝ) * (η * G) := drift_bound_of_step (η * G) hstep T
  calc
    |forgetting L i (θ T) (θ 0)| ≤ Λ * |θ T - θ 0| := forgetting_bound L i Λ _ _ hLip
    _ ≤ Λ * ((T : ℝ) * (η * G)) := mul_le_mul_of_nonneg_left hdrift hΛ
    _ = Λ * ((T : ℝ) * η * G) := by ring

/-- 回放预算 `replayGradientBudget η G T = T·η·G`。 -/
lemma replayGradientBudget_eq (η G : ℝ) (T : ℕ) :
    replayGradientBudget η G T = (T : ℝ) * η * G := rfl

/-! ## 五、对照：无正则时遗忘界随 T 无界 -/

/-- **无正则的遗忘无界**：`Λ > 0` 时 `Λ·T` 随 T 无界（灾难性遗忘的量化表述）：
    `∀ B, ∃ T, B < Λ·T`。 -/
theorem replay_forgetting_unbounded (Λ : ℝ) (hΛ : 0 < Λ) :
    ∀ B : ℝ, ∃ T : ℕ, B < Λ * (T : ℝ) := by
  intro B
  rcases exists_nat_gt (B / Λ) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have h := mul_lt_mul_of_pos_right hN hΛ
  rw [div_mul_cancel₀ B (ne_of_gt hΛ)] at h
  linarith [h]

/-! ## 注：闭环语义
  遗忘定义（forgetting）→ Lipschitz 遗忘界（forgetting_bound）→
  EWC 惩罚（ewcPenalty）→ 惩罚预算 ⟹ 漂移界（ewc_drift_bound）→
  EWC 遗忘界 Λ√(2λ/F)（ewc_forgetting_bound，与 T 无关）→
  回放累积漂移（drift_bound_of_step）→ 回放遗忘界 ΛTηG（replay_bound，线性增长）→
  对照：无正则遗忘无界（replay_forgetting_unbounded）。
  诚实假设：损失 Lipschitz 常数 Λ、EWC 惩罚预算 λ、每步漂移界 ηG。 -/

end Lattice
