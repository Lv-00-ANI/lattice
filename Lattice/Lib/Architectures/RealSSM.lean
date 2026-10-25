import Mathlib
import Lattice.Lib.Architectures.RealLoopModel
/-!
# LATTICE: 状态空间模型（Mamba 类线性递推）—— 闭式解、收缩性与并行扫描等价

状态空间模型（SSM）的离散核心是**线性时不变**递推

  `h_t = A h_{t-1} + B x_t`,   `y_t = C h_t`

其中 `A B C : E →L[ℝ] E` 是连续线性算子，`x` 是输入序列。它是 `RealLoopModel` 中
RNN 单步 `RNNStep φ W U h x = φ (W h + U x)` 在**恒等激活** `φ = id` 下的特化：
`ssmState A B h0 xs := rnnState id A B h0 xs`。

本文件给出（全部无 sorry / axiom / admit）：

  1. `ssmState` / `ssmOutput`：状态递推与输出定义；
     `ssmState_zero` / `ssmState_succ`：展开引理（`h_{t+1} = A h_t + B x_t`）；
  2. `ssmState_explicit`（**核心闭式解**，归纳）：`h_t = A^t h₀ + Σ_{s<t} A^{t−1−s} (B x_s)`
     ——线性递推的显式解（卷积形式）；
  3. `ssm_contraction`（**核心**，复用 `RealLoopModel.rnn_hidden_contraction`）：
     初值遗忘 `‖h_n − g_n‖ ≤ ‖A‖ⁿ·‖h₀ − g₀‖`——`‖A‖ < 1` 即指数遗忘；
  4. `ssm_contraction_rho`：显式收缩率版本 `‖A‖ ≤ ρ` ⟹ `≤ ρⁿ·‖h₀−g₀‖`；
  5. `ssm_stability_bound`（**核心**，复用 `RealLoopModel.rnn_stability_bound`）：
     输入扰动 `‖x_k − y_k‖ ≤ δ` 时
     `‖h_n − h'_n‖ ≤ ((1−‖A‖ⁿ)/(1−‖A‖))·(‖B‖·δ)`（`‖A‖ < 1`）——
     衔接 `rnn_stability_bound`（其中 `Lφ = 1`、`Lu = ‖B‖`）；
  6. `ssm_pow_add`：`A^{m+n} = A^m · A^n`（指数加法律）；
  7. `ssm_state_compose`（**并行扫描代数的核心**）：状态的**可组合性**——
     从时刻 `n` 的状态出发、接上后缀输入，等于原轨迹在时刻 `n+t` 的状态
     `ssmState A B (ssmState A B h0 xs n) (fun k => xs (n+k)) t = ssmState A B h0 xs (n+t)`；
     这正是并行扫描 / 结合律重排（Blelloch scan）所依赖的代数性质；
  8. `ssm_output_bound`：`‖y_t‖ ≤ ‖C‖·M`（状态有界 `M` 时）；
  9. `ssm_state_growth_bound`：**显式增长界** ——
     `‖h_t‖ ≤ ‖A‖^t·M₀ + Σ_{s<t} ‖A‖^{t−1−s}·(‖B‖·M_x)`
     （`‖h₀‖ ≤ M₀`、`∀s, ‖x_s‖ ≤ M_x`）。

**诚实假设与降级**（均显式标注）：
  · **不含选择性（selectivity / S6）门控**：Mamba 的核心是把 `A, B, C` 变成输入相关的
    `A_t, B_t, C_t`（时变系统）；本文件只处理**线性时不变**（LTI）情形。时变系统需要
    逐时刻算子序列与乘积 `A_t A_{t-1} ⋯`，本文件不涉及——这是**模型范围的缩减**，
    且已在定理名/陈述中体现（`ssm_pow_add` 只在常量 `A` 下成立）；
  · **不含离散化**：真实 SSM 从连续系统 `h'(t) = A h + B x` 经 ZOH/双线性离散化为
    `Ā = exp(ΔA)`；本文件直接从离散递推出发，不证明离散化的收敛/一致性；
  · `ssm_contraction` 等对任意 `‖A‖` 成立；指数遗忘/闭式几何界需要 `‖A‖ < 1`，只在
    相应定理中显式假设；
  · 定理 3/5 是 `RealLoopModel` 已有结果的**特例实例化**（恒等激活、`Lφ = 1`、`Lu = ‖B‖`），
    本文件的价值在于把 RNN 抽象落到 SSM 语义，并用闭式解/扫描等价补足 LTI 专属内容；
  · 闭式解定理的指标算术用 `omega` 关闭（`t − 1 − s` 形式的自然数减法）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 定义：SSM 状态与输出 -/

/-- SSM（线性时不变）隐状态递推：`h_t = A h_{t-1} + B x_t`
（`RealLoopModel.rnnState` 在恒等激活下的特化）。 -/
def ssmState (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) : ℕ → E :=
  rnnState (fun x : E => x) A B h0 xs

/-- SSM 输出：`y_t = C h_t`。 -/
def ssmOutput (C A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (t : ℕ) : E :=
  C (ssmState A B h0 xs t)

/-! ## 展开引理 -/

@[simp] theorem ssmState_zero (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) :
    ssmState A B h0 xs 0 = h0 := rfl

@[simp] theorem ssmState_succ (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (n : ℕ) :
    ssmState A B h0 xs (n + 1) = A (ssmState A B h0 xs n) + B (xs n) := by
  simp [ssmState, rnnState, RNNStep]

/-! ## 引理：`A ((A^k) y) = (A^{k+1}) y` -/

lemma ssm_pow_succ_apply (A : E →L[ℝ] E) (k : ℕ) (y : E) :
    A ((A ^ k) y) = (A ^ (k + 1)) y := by
  rw [pow_succ']
  rfl

/-- `‖A^n‖ ≤ ‖A‖^n`（算子范数次可乘；`n = 0` 时用 `‖id‖ ≤ 1`）。 -/
lemma ssm_norm_pow_le (A : E →L[ℝ] E) (n : ℕ) : ‖A ^ n‖ ≤ ‖A‖ ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  · exact norm_pow_le' A h

/-! ## 定理一（核心）：闭式解（归纳）
`h_t = A^t h₀ + Σ_{s<t} A^{t−1−s} (B x_s)`。 -/

theorem ssmState_explicit (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (t : ℕ) :
    ssmState A B h0 xs t
      = (A ^ t) h0 + ∑ s in Finset.range t, (A ^ (t - 1 - s)) (B (xs s)) := by
  induction t with
  | zero => simp [ssmState, rnnState]
  | succ n ih =>
    have hA0 : A ((A ^ n) h0) = (A ^ (n + 1)) h0 := ssm_pow_succ_apply A n h0
    have hAsum : A (∑ s in Finset.range n, (A ^ (n - 1 - s)) (B (xs s)))
        = ∑ s in Finset.range n, (A ^ (n - s)) (B (xs s)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hslt : s < n := Finset.mem_range.mp hs
      have hidx : n - 1 - s + 1 = n - s := by omega
      rw [ssm_pow_succ_apply A (n - 1 - s) (B (xs s)), hidx]
    have hsum_eq : (∑ s in Finset.range n, (A ^ (n - s)) (B (xs s)))
        = ∑ s in Finset.range n, (A ^ (n + 1 - 1 - s)) (B (xs s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hslt : s < n := Finset.mem_range.mp hs
      have hidx : n + 1 - 1 - s = n - s := by omega
      rw [hidx]
    rw [ssmState_succ, ih, map_add, hA0, hAsum, Finset.sum_range_succ]
    have hzero : n + 1 - 1 - n = 0 := by omega
    rw [hzero, pow_zero, ContinuousLinearMap.one_apply, hsum_eq]
    abel

/-! ## 定理二（核心）：初值遗忘（收缩性）
复用 `RealLoopModel.rnn_hidden_contraction`（恒等激活，`Lφ = 1`）。 -/

theorem ssm_contraction (A B : E →L[ℝ] E) (h0 g0 : E) (xs : ℕ → E) (n : ℕ) :
    ‖ssmState A B h0 xs n - ssmState A B g0 xs n‖ ≤ ‖A‖ ^ n * ‖h0 - g0‖ := by
  have hφ : ∀ a b : E, ‖(fun x : E => x) a - (fun x : E => x) b‖ ≤ (1 : ℝ) * ‖a - b‖ := by
    intro a b
    simp
  have h := rnn_hidden_contraction (fun x : E => x) A B 1 hφ (by norm_num) h0 g0 xs n
  simpa [ssmState] using h

/-- 显式收缩率版本：`‖A‖ ≤ ρ` ⟹ `‖h_n − g_n‖ ≤ ρⁿ·‖h₀ − g₀‖`。 -/
theorem ssm_contraction_rho (A B : E →L[ℝ] E) (h0 g0 : E) (xs : ℕ → E) (n : ℕ) (ρ : ℝ)
    (_hρ0 : 0 ≤ ρ) (hA : ‖A‖ ≤ ρ) :
    ‖ssmState A B h0 xs n - ssmState A B g0 xs n‖ ≤ ρ ^ n * ‖h0 - g0‖ :=
  le_trans (ssm_contraction A B h0 g0 xs n)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg A) hA n) (norm_nonneg _))

/-! ## 定理三（核心）：输入扰动稳定性（复用 `RealLoopModel.rnn_stability_bound`）
`‖A‖ < 1`、输入差 ≤ δ ⟹ `‖h_n − h'_n‖ ≤ ((1−‖A‖ⁿ)/(1−‖A‖))·(‖B‖·δ)`。 -/

theorem ssm_stability_bound (A B : E →L[ℝ] E) (δ : ℝ) (hA1 : ‖A‖ < 1)
    (h0 : E) (xs ys : ℕ → E) (n : ℕ) (hδ : ∀ k, ‖xs k - ys k‖ ≤ δ) :
    ‖ssmState A B h0 xs n - ssmState A B h0 ys n‖
      ≤ ((1 - ‖A‖ ^ n) / (1 - ‖A‖)) * (‖B‖ * δ) := by
  have hφ : ∀ a b : E, ‖(fun x : E => x) a - (fun x : E => x) b‖ ≤ (1 : ℝ) * ‖a - b‖ := by
    intro a b
    simp
  have hU : ∀ x : E, ‖B x‖ ≤ ‖B‖ * ‖x‖ := fun x => ContinuousLinearMap.le_opNorm B x
  have h := rnn_stability_bound (fun x : E => x) A B 1 ‖B‖ δ hφ (by norm_num)
    (norm_nonneg B) hU (by simpa using hA1) h0 xs ys n hδ
  simpa [ssmState] using h

/-! ## 定理四：指数加法律（常量算子） -/

theorem ssm_pow_add (A : E →L[ℝ] E) (m n : ℕ) :
    (A ^ (m + n) : E →L[ℝ] E) = A ^ m * A ^ n :=
  pow_add A m n

/-! ## 定理五（核心）：状态的可组合性（并行扫描的代数依据）
从时刻 `n` 的状态出发、接上后缀输入，等于原轨迹在时刻 `n+t` 的状态。 -/

theorem ssm_state_compose (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (n : ℕ) :
    ∀ t : ℕ, ssmState A B (ssmState A B h0 xs n) (fun k => xs (n + k)) t
      = ssmState A B h0 xs (n + t) := by
  intro t
  induction t with
  | zero => simp [ssmState, rnnState]
  | succ t ih =>
    rw [ssmState_succ, ih]
    have hstep : n + (t + 1) = (n + t) + 1 := by omega
    rw [hstep, ssmState_succ]

/-! ## 定理六：输出界 -/

theorem ssm_output_bound (C A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (M : ℝ) (t : ℕ)
    (hM : ‖ssmState A B h0 xs t‖ ≤ M) :
    ‖ssmOutput C A B h0 xs t‖ ≤ ‖C‖ * M := by
  unfold ssmOutput
  calc
    ‖C (ssmState A B h0 xs t)‖ ≤ ‖C‖ * ‖ssmState A B h0 xs t‖ := ContinuousLinearMap.le_opNorm C _
    _ ≤ ‖C‖ * M := mul_le_mul_of_nonneg_left hM (norm_nonneg C)

/-! ## 定理七：显式增长界（由闭式解 + 算子范数界） -/

theorem ssm_state_growth_bound (A B : E →L[ℝ] E) (h0 : E) (xs : ℕ → E) (M0 Mx : ℝ)
    (hM0 : ‖h0‖ ≤ M0) (hMx : ∀ s, ‖xs s‖ ≤ Mx) (t : ℕ) :
    ‖ssmState A B h0 xs t‖
      ≤ ‖A‖ ^ t * M0 + ∑ s in Finset.range t, ‖A‖ ^ (t - 1 - s) * (‖B‖ * Mx) := by
  have hterm : ∀ s ∈ Finset.range t,
      ‖(A ^ (t - 1 - s)) (B (xs s))‖ ≤ ‖A‖ ^ (t - 1 - s) * (‖B‖ * Mx) := by
    intro s _
    calc
      ‖(A ^ (t - 1 - s)) (B (xs s))‖ ≤ ‖A ^ (t - 1 - s)‖ * ‖B (xs s)‖ :=
        ContinuousLinearMap.le_opNorm (A ^ (t - 1 - s)) (B (xs s))
      _ ≤ ‖A‖ ^ (t - 1 - s) * (‖B‖ * Mx) := by
        apply mul_le_mul
        · exact ssm_norm_pow_le A (t - 1 - s)
        · calc
            ‖B (xs s)‖ ≤ ‖B‖ * ‖xs s‖ := ContinuousLinearMap.le_opNorm B (xs s)
            _ ≤ ‖B‖ * Mx := mul_le_mul_of_nonneg_left (hMx s) (norm_nonneg B)
        · exact norm_nonneg _
        · positivity
  rw [ssmState_explicit]
  calc
    ‖(A ^ t) h0 + ∑ s in Finset.range t, (A ^ (t - 1 - s)) (B (xs s))‖
        ≤ ‖(A ^ t) h0‖ + ‖∑ s in Finset.range t, (A ^ (t - 1 - s)) (B (xs s))‖ :=
          norm_add_le _ _
    _ ≤ ‖A‖ ^ t * M0 + ∑ s in Finset.range t, ‖A‖ ^ (t - 1 - s) * (‖B‖ * Mx) := by
      apply add_le_add
      · calc
          ‖(A ^ t) h0‖ ≤ ‖A ^ t‖ * ‖h0‖ := ContinuousLinearMap.le_opNorm (A ^ t) h0
          _ ≤ ‖A‖ ^ t * M0 :=
            mul_le_mul (ssm_norm_pow_le A t) hM0 (norm_nonneg h0) (by positivity)
      · calc
          ‖∑ s in Finset.range t, (A ^ (t - 1 - s)) (B (xs s))‖
              ≤ ∑ s in Finset.range t, ‖(A ^ (t - 1 - s)) (B (xs s))‖ := norm_sum_le _ _
          _ ≤ ∑ s in Finset.range t, ‖A‖ ^ (t - 1 - s) * (‖B‖ * Mx) :=
            Finset.sum_le_sum hterm

end Lattice
