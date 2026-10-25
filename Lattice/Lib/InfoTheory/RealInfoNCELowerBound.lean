import Mathlib
import Lattice.Lib.LearningTheory.RealContrastive
import Lattice.Lib.Attention.RealSoftmaxTemp
import Lattice.Lib.Convex.RealConvexToolkit
import Lattice.Lib.InfoTheory.RealCrossEntropy
/-!
# LATTICE: InfoNCE 的下界 `≥ log n`（确定性 Jensen 版 + 期望版 + 等号刻画）

补 `RealContrastive` 的缺口：该文件只给出**条件性点式上界**
（`infonce_le_log_card_of_max`、`infonce_le_log_one_add_of_gap`），
并在 docstring 中明确标注「期望版 **未做**」。本文件给出可证的**下界**版本。

## 核心恒等式

设 `p i = softmax(s/τ)_i`、`Z = Σ_j exp(s_j/τ)`、`E = Σ_j exp((s_j − s_i)/τ)`。
由 `exp(s_i/τ)` 在分子/分母中消去：

    E = Z / exp(s_i/τ)

于是

    infoNCE(s,τ,i) = −log p i = log Z − s_i/τ = log E
                   = log n + log(E/n)                       （桥接恒等式）

再对 `v_j := exp((s_j − s_i)/τ) > 0` 用 log 的凹性（Jensen）：

    (1/n)·Σ_j log v_j ≤ log((1/n)·Σ_j v_j)

即 `(Σ_j (s_j − s_i))/(n·τ) ≤ log(E/n)`（因为 `log v_j = (s_j − s_i)/τ`）。合并得

    log n + (Σ_j (s_j − s_i))/(n·τ) ≤ infoNCE(s,τ,i)          （`infonce_lower_jensen`）

**Jensen 内核的初等证法**（不依赖 mathlib 凸性引理名）：对 `z_j = v_j/m`
（`m = (1/n)Σ v_j > 0`）用 `log z ≤ z − 1`，加权 `1/n` 求和后右端恰为 0。

## 由 Jensen 下界得到的**真**命题（注意方向）

`(Σ_j (s_j − s_i))/(n·τ) = (mean_j s_j − s_i)/τ`，故当**正样本分数不高于均值**
（`s_i ≤ mean_j s_j`）时该修正项 `≥ 0`，于是 `log n ≤ infoNCE`：

    infonce_lower_of_mean_ge      : s i ≤ mean s  ⟹  log n ≤ infoNCE
    infonce_lower_of_min          : (∀ j, s i ≤ s j) ⟹ log n ≤ infoNCE

对称地，**正样本是最大点时只能得到上界** `infoNCE ≤ log n`（即 `RealContrastive`
已有的 `infonce_le_log_card_of_max`），不可能得到下界。

## 期望版（真命题）

    infonce_lower_uniform_avg : log n ≤ (Σ_i infoNCE(s,τ,i)) / n
      正样本索引 i 取均匀权时平均成立（Jensen 直接作用在 `p = softmax(s/τ)` 上，
      只用 `Σ_i p_i = 1`；这正是 NCE 估计量 ≥ log n 的经典陈述）。

    infonce_lower_expect      : (∀ω, s ω i ≤ mean_j (s ω j)) ⟹
                                log n ≤ Σ_ω w_ω · infoNCE(s ω, τ, i)
      有限概率空间 `(Ω, w)`（`w ≥ 0`、`Σ w = 1`）上逐样本用点式下界再加权求和。

## 等号刻画（**修正版**）

    infonce_eq_log_card_iff : infoNCE = log n  ⟺  E = Σ_j exp((s_j − s_i)/τ) = n

注意**并非**「所有分数相等」：`p_i = 1/n` 只要求上述**均值条件** `E/n = 1`。
例如 `n = 3`、`v = (1, 1/2, 3/2)`（即 `s = (0, −τ·log 2, τ·log(3/2))` 相对 `s_i`）
有 `E = 3`，故 `infoNCE = log 3`，但分数并不全相等。所有分数相等是**充分**条件：

    infonce_eq_log_card_of_const : (∀ j, s j = s i) ⟹ infoNCE = log n

## 诚实边界【降级/未证/诚实/标注】

- **任务原命题 `infonce_lower_of_mean_le`（`mean ≤ s i ⟹ log n ≤ infoNCE`）是假命题**，
  本文件**不证**它，并给出反例 `infonce_lower_of_mean_le_counterexample`：
  `n = 2`、`s = (0, −1)`、`i = 0`、`τ = 1` 时 `mean = −1/2 ≤ 0 = s_0`，但由
  `infonce_le_log_one_add_of_gap`（间隔 `Δ = 1`）得
  `infoNCE ≤ log(1 + e^{−1}) < log 2`。方向应修正为 `s i ≤ mean`（见上）。
- **任务原命题 `infonce_lower_of_max`（`i` 最大 ⟹ `log n ≤ infoNCE`）同样是假命题**：
  `i` 最大 ⟹ `p_i ≥ 1/n` ⟹ `infoNCE ≤ log n`，恰为既有上界
  `infonce_le_log_card_of_max`。本文件给出的是真下界 `infonce_lower_of_min`
  （`i` 最小）与更一般的 `infonce_lower_of_mean_ge`。
- **等号刻画降级**：任务所设想的「等号 ⟺ 所有 `s_j` 相等」**不成立**（见上述反例），
  本文件给出的 `infonce_eq_log_card_iff` 是**均值型**（`E = n`）的真刻画，
  并只把「全相等」证成**充分**条件（`infonce_eq_log_card_of_const`），
  **未证**其必要性（因为它为假）。Jensen 那一步的等号条件（所有 `v_j` 相等）
  本文件**未单独形式化**，标注为未证。
- 未做：`τ → 0 / τ → ∞` 的 `Tendsto` 版本；互信息与 NCE 估计量的一致性；
  连续/总体分布版（本文件全部为有限版本）。

无 sorry/axiom/admit；所有列出的定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 辅助引理：log 的 Jensen（平均值 ≥ 平均 log）

对正向量 `v`：`(Σ_j log v_j)/n ≤ log((Σ_j v_j)/n)`。
初等证法：令 `m = (Σ_j v_j)/n > 0`，对 `z_j = v_j/m > 0` 用 `log z ≤ z − 1`，
加权得 `log v_j ≤ log m + (v_j/m − 1)`；求和后 `Σ_j (v_j/m − 1) = 0`。 -/

/-- **log 的有限 Jensen 下界**：`0 < v j`（∀j，指标非空）⟹
`(Σ_j log v_j)/n ≤ log((Σ_j v_j)/n)`。这是本文件全部下界的核心内核。 -/
lemma log_mean_ge_mean_log {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (hv : ∀ j, 0 < v j) :
    (∑ j, Real.log (v j)) / (n : ℝ) ≤ Real.log ((∑ j, v j) / (n : ℝ)) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hsumpos : 0 < ∑ j, v j :=
    Finset.sum_pos (fun j _ => hv j) Finset.univ_nonempty
  have hmpos : 0 < (∑ j, v j) / (n : ℝ) := div_pos hsumpos hnpos
  -- 逐项：log v_j ≤ log m + (v_j/m − 1)
  have hbound : ∀ j, Real.log (v j)
      ≤ Real.log ((∑ k, v k) / (n : ℝ)) + (v j / ((∑ k, v k) / (n : ℝ)) - 1) := by
    intro j
    have hratio : 0 < v j / ((∑ k, v k) / (n : ℝ)) := div_pos (hv j) hmpos
    have hlog : Real.log (v j / ((∑ k, v k) / (n : ℝ)))
        ≤ v j / ((∑ k, v k) / (n : ℝ)) - 1 := Real.log_le_sub_one_of_pos hratio
    have hsplit : Real.log (v j)
        = Real.log (v j / ((∑ k, v k) / (n : ℝ)))
          + Real.log ((∑ k, v k) / (n : ℝ)) := by
      rw [Real.log_div (ne_of_gt (hv j)) (ne_of_gt hmpos)]
      ring
    linarith
  -- 求和：Σ_j (v_j/m − 1) = (Σ_j v_j)/m − n = n − n = 0
  have hsum_div : (∑ j, v j / ((∑ k, v k) / (n : ℝ))) = (n : ℝ) := by
    have hAn : (∑ k, v k) / (n : ℝ) ≠ 0 := ne_of_gt hmpos
    rw [← Finset.sum_div, div_eq_iff hAn]
    field_simp
  have hsum_rhs : (∑ j,
        (Real.log ((∑ k, v k) / (n : ℝ)) + (v j / ((∑ k, v k) / (n : ℝ)) - 1)))
      = (n : ℝ) * Real.log ((∑ k, v k) / (n : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      hsum_div, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  have hsumle : (∑ j, Real.log (v j))
      ≤ (n : ℝ) * Real.log ((∑ j, v j) / (n : ℝ)) := by
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hbound j)
    rwa [hsum_rhs] at h1
  calc
    (∑ j, Real.log (v j)) / (n : ℝ)
        ≤ ((n : ℝ) * Real.log ((∑ j, v j) / (n : ℝ))) / (n : ℝ) :=
          div_le_div_of_nonneg_right hsumle (le_of_lt hnpos)
    _ = Real.log ((∑ j, v j) / (n : ℝ)) := by field_simp

/-! ## 桥接恒等式：infoNCE = log n + log(mean_j exp((s_j − s_i)/τ)) -/

/-- **桥接恒等式**：`τ > 0`、指标非空时
`infoNCE s τ i = log n + log((Σ_j exp((s_j − s_i)/τ))/n)`。
路线：`E = Z/exp(s_i/τ)`（`exp_sub` 逐项 + `sum_div`），
`log E = log Z − s_i/τ`（`log_div` + `log_exp`），再 `E = n·(E/n)`（`log_mul`）。 -/
lemma infonce_eq_log_card_add_log_mean {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (_hτ : 0 < τ) :
    infoNCE s τ i
      = Real.log (n : ℝ)
        + Real.log ((∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ)) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hZpos : 0 < ∑ j, Real.exp (s j / τ) := softmax_denom_pos _
  have hEpos : 0 < ∑ j, Real.exp ((s j - s i) / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  -- E = Z / exp(s_i/τ)
  have hEeq : (∑ j, Real.exp ((s j - s i) / τ))
      = (∑ j, Real.exp (s j / τ)) / Real.exp (s i / τ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_sub]
    congr 1
    ring
  -- infoNCE = log Z − s_i/τ
  have hinfo : infoNCE s τ i = Real.log (∑ j, Real.exp (s j / τ)) - s i / τ := by
    rw [infoNCE]
    unfold softmax
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZpos), Real.log_exp]
    ring
  have hlogE : Real.log (∑ j, Real.exp ((s j - s i) / τ))
      = Real.log (∑ j, Real.exp (s j / τ)) - s i / τ := by
    rw [hEeq, Real.log_div (ne_of_gt hZpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  have hval : (n : ℝ) * ((∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ))
      = (∑ j, Real.exp ((s j - s i) / τ)) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnne]
  calc
    infoNCE s τ i
        = Real.log (∑ j, Real.exp ((s j - s i) / τ)) := by rw [hinfo, ← hlogE]
    _ = Real.log ((n : ℝ) * ((∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ))) := by
          rw [hval]
    _ = Real.log (n : ℝ)
          + Real.log ((∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ)) :=
          Real.log_mul hnne (ne_of_gt (div_pos hEpos hnpos))

/-! ## 定理一（核心）：确定性 Jensen 下界 -/

/-- **InfoNCE 的确定性 Jensen 下界**：`τ > 0`、指标非空时
`log n + (Σ_j (s_j − s_i))/(n·τ) ≤ infoNCE s τ i`。

修正项 `(Σ_j (s_j − s_i))/(n·τ) = (mean_j s_j − s_i)/τ` 的符号决定了与 `log n`
的关系：`mean ≥ s_i` 时它非负，得到 `infonce_lower_of_mean_ge`；
反方向（`mean ≤ s_i`）只会得到**弱于** `log n` 的界（见文件头诚实边界）。 -/
theorem infonce_lower_jensen {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n) (hτ : 0 < τ) :
    Real.log (n : ℝ) + (∑ j, (s j - s i)) / ((n : ℝ) * τ) ≤ infoNCE s τ i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  rw [infonce_eq_log_card_add_log_mean s τ i hτ]
  apply add_le_add_left
  have hJ := log_mean_ge_mean_log (fun j => Real.exp ((s j - s i) / τ)) i
    (fun j => Real.exp_pos _)
  have hlogsum : (∑ j, Real.log (Real.exp ((s j - s i) / τ)))
      = (∑ j, (s j - s i)) / τ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => Real.log_exp ((s j - s i) / τ))
  rw [hlogsum] at hJ
  have hdiv : (∑ j, (s j - s i)) / τ / (n : ℝ)
      = (∑ j, (s j - s i)) / ((n : ℝ) * τ) := by
    rw [div_div, mul_comm τ (n : ℝ)]
  rwa [hdiv] at hJ

/-! ## 定理二：由 Jensen 下界得到的真·`≥ log n`（均值 / 最小点） -/

/-- **均值版本**（真命题，修正了任务原命题的方向）：正样本分数**不高于**均值
（`s i ≤ (Σ_j s_j)/n`）时 `log n ≤ infoNCE s τ i`。
由 `infonce_lower_jensen` 加修正项非负得到。 -/
theorem infonce_lower_of_mean_ge {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (hτ : 0 < τ) (hmean : s i ≤ (∑ j, s j) / (n : ℝ)) :
    Real.log (n : ℝ) ≤ infoNCE s τ i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hJ := infonce_lower_jensen s τ i hτ
  have hnum : (∑ j, (s j - s i)) = (∑ j, s j) - (n : ℝ) * s i := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hnonneg : 0 ≤ (∑ j, (s j - s i)) / ((n : ℝ) * τ) := by
    apply div_nonneg
    · rw [hnum]
      have hle : s i * (n : ℝ) ≤ ∑ j, s j := (le_div_iff₀ hnpos).mp hmean
      nlinarith
    · exact le_of_lt (mul_pos hnpos hτ)
  linarith

/-- **最小点版本**：正样本相似度 `s i` 是所有分数中的最小者时 `log n ≤ infoNCE`。
（此时 `s i ≤ mean_j s_j`，直接引用 `infonce_lower_of_mean_ge`。） -/
theorem infonce_lower_of_min {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (hτ : 0 < τ) (hmin : ∀ j, s i ≤ s j) :
    Real.log (n : ℝ) ≤ infoNCE s τ i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  apply infonce_lower_of_mean_ge s τ i hτ
  have hsum : (∑ j, s i) ≤ ∑ j, s j := Finset.sum_le_sum (fun j _ => hmin j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hnpos]
  nlinarith

/-! ## 定理三：期望版（正样本索引均匀平均 / 有限概率空间加权） -/

/-- **均匀平均版（经典 InfoNCE ≥ log n）**：正样本索引 `i` 取均匀权时
`log n ≤ (Σ_i infoNCE s τ i)/n`。

路线：令 `p = softmax(s/τ)`（`p_i > 0`、`Σ_i p_i = 1`），对 `p` 用
`log_mean_ge_mean_log`：`(Σ_i log p_i)/n ≤ log(1/n) = −log n`；
两边取负并用 `infoNCE = −log p_i` 即得。 -/
theorem infonce_lower_uniform_avg {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (_hτ : 0 < τ) :
    Real.log (n : ℝ) ≤ (∑ k, infoNCE s τ k) / (n : ℝ) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hJ := log_mean_ge_mean_log (fun k => softmax (fun j => s j / τ) k) i
    (fun k => softmax_pos _ k)
  have hsum1 : (∑ k, softmax (fun j => s j / τ) k) = 1 := softmax_sum_one _
  rw [hsum1] at hJ
  have hloginv : Real.log ((1 : ℝ) / (n : ℝ)) = -Real.log (n : ℝ) := by
    rw [Real.log_div one_ne_zero hnne, Real.log_one]
    ring
  rw [hloginv] at hJ
  have hsum_info : (∑ k, infoNCE s τ k)
      = -(∑ k, Real.log (softmax (fun j => s j / τ) k)) := by
    have hcong : (∑ k, infoNCE s τ k)
        = ∑ k, -(Real.log (softmax (fun j => s j / τ) k)) :=
      Finset.sum_congr rfl (fun k _ => by rw [infoNCE])
    rw [hcong, Finset.sum_neg_distrib]
  rw [hsum_info, neg_div]
  linarith

/-- **有限概率空间上的期望版**：权重 `w ≥ 0`、`Σ_ω w_ω = 1`，
且每个样本的分数满足 `s ω i ≤ mean_j (s ω j)`，则
`log n ≤ Σ_ω w_ω · infoNCE (s ω) τ i`。
逐样本用 `infonce_lower_of_mean_ge` 再乘非负权求和（`Σ w = 1`）。 -/
theorem infonce_lower_expect {n : ℕ} {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (s : Ω → Fin n → ℝ) (τ : ℝ) (i : Fin n) (hτ : 0 < τ)
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hmean : ∀ ω, s ω i ≤ (∑ j, s ω j) / (n : ℝ)) :
    Real.log (n : ℝ) ≤ ∑ ω, w ω * infoNCE (s ω) τ i := by
  have hterm : ∀ ω, w ω * Real.log (n : ℝ) ≤ w ω * infoNCE (s ω) τ i :=
    fun ω => mul_le_mul_of_nonneg_left
      (infonce_lower_of_mean_ge (s ω) τ i hτ (hmean ω)) (hw ω)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hterm ω)
  rw [← Finset.sum_mul, hwsum, one_mul] at hsum
  exact hsum

/-! ## 定理四：等号刻画（均值型，真刻画） -/

/-- **等号刻画（修正版）**：`τ > 0`、指标非空时
`infoNCE s τ i = log n ⟺ Σ_j exp((s_j − s_i)/τ) = n`。

由桥接恒等式 `infoNCE = log n + log(E/n)` 归约为 `log(E/n) = 0 ⟺ E/n = 1`
（`E > 0`、`n > 0`）。**注意**等号**不等价于**「所有 `s_j` 相等」——
后者只是充分条件（见 `infonce_eq_log_card_of_const`）。 -/
theorem infonce_eq_log_card_iff {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (hτ : 0 < τ) :
    infoNCE s τ i = Real.log (n : ℝ)
      ↔ (∑ j, Real.exp ((s j - s i) / τ)) = (n : ℝ) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hEpos : 0 < ∑ j, Real.exp ((s j - s i) / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  rw [infonce_eq_log_card_add_log_mean s τ i hτ]
  constructor
  · intro h
    have hlog : Real.log ((∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ)) = 0 := by linarith
    have h1 : (∑ j, Real.exp ((s j - s i) / τ)) / (n : ℝ) = 1 := by
      rw [← Real.exp_log (div_pos hEpos hnpos), hlog, Real.exp_zero]
    exact (div_eq_one_iff_eq hnne).mp h1
  · intro hE
    rw [hE, div_self hnne, Real.log_one, add_zero]

/-- **等号的充分条件**：所有分数与 `s i` 相等（即分数完全均匀、softmax 均匀）时
`infoNCE s τ i = log n`。（这是**充分**而非必要——见 `infonce_eq_log_card_iff`。） -/
theorem infonce_eq_log_card_of_const {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (hτ : 0 < τ) (hconst : ∀ j, s j = s i) :
    infoNCE s τ i = Real.log (n : ℝ) := by
  rw [infonce_eq_log_card_iff s τ i hτ]
  have hterm : ∀ j, Real.exp ((s j - s i) / τ) = 1 := by
    intro j
    rw [hconst j, sub_self, zero_div, Real.exp_zero]
  have hsum : (∑ j, Real.exp ((s j - s i) / τ)) = (n : ℝ) := by
    simp [hterm]
  exact hsum

/-! ## 定理五：反例 —— 任务原命题 `infonce_lower_of_mean_le` 为假 -/

/-- **反例（诚实标注）**：`mean ≤ s i` **不能**推出 `log n ≤ infoNCE`。
取 `n = 2`、`s = (0, −1)`、`i = 0`、`τ = 1`：`mean = −1/2 ≤ 0 = s_0`，
但间隔 `Δ = 1` 使 `infoNCE ≤ log(1 + e^{−1}) < log 2`。

这同时也是任务原命题 `infonce_lower_of_max`（`i` 最大 ⟹ 下界）为假的原因：
`i` 最大时只能沿既有 `infonce_le_log_card_of_max` 得到**上界**。 -/
theorem infonce_lower_of_mean_le_counterexample :
    ∃ (s : Fin 2 → ℝ) (τ : ℝ) (i : Fin 2),
      (∑ j, s j) / (2 : ℝ) ≤ s i ∧ infoNCE s τ i < Real.log 2 := by
  refine ⟨![0, -1], 1, 0, ?_, ?_⟩
  · norm_num [Fin.sum_univ_two]
  · have hgap : ∀ j : Fin 2, j ≠ 0 → (![0, -1] : Fin 2 → ℝ) j
        ≤ (![0, -1] : Fin 2 → ℝ) 0 - 1 := by
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · norm_num
    have hle := infonce_le_log_one_add_of_gap (s := (![0, -1] : Fin 2 → ℝ))
      (τ := 1) (Δ := 1) 0 (by norm_num) (by norm_num) hgap
    have hle' : infoNCE (![0, -1] : Fin 2 → ℝ) 1 0 ≤ Real.log (1 + Real.exp (-1)) := by
      refine le_trans hle (le_of_eq ?_)
      norm_num
    have hlt : Real.log (1 + Real.exp (-1)) < Real.log 2 := by
      apply Real.log_lt_log
      · positivity
      · have : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        linarith
    exact lt_of_le_of_lt hle' hlt

end Lattice
