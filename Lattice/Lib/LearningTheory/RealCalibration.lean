import Mathlib
import Lattice.Lib.InfoTheory.RealCrossEntropy
/-!
# LATTICE: 校准误差 —— 期望校准误差 ECE 的非负性、零化刻画与 Brier 上界

信息论线的延伸（衔接 RealCrossEntropy 的 CE/熵、RealKL 的 KL 线）：分类模型除了
损失/概率，还需要**校准**（calibration）——模型报出的置信度是否等于其实际准确率。

本文件建立有限分箱版校准理论：

  1. `binning` / `binCount` / `binWeight`：把样本按置信度分箱，并给第 b 箱的样本数与权重 n_b/n；
     `binCount_le` / `binWeight_le_one`：单箱样本数不超过总样本数、权重 ≤ 1；
  2. `ece`（定义）：期望校准误差 ECE = Σ_b w_b·|acc_b − conf_b|，
     其中 w_b 是箱权重、acc_b 是箱内准确率、conf_b 是箱内平均置信度；
  3. `ece_nonneg`：ECE ≥ 0（逐项非负）；
  4. `ece_self`：acc = conf（完美校准）⟹ ECE = 0；
  5. `ece_zero_iff_perfect`（核心）：w ≥ 0 时 ECE = 0 ⟺ 每个正权重箱内 acc_b = conf_b
     （非负和为零 ⟺ 每项为零 ⟺ 每个正权重箱的偏差为零）；
  6. `overconf` / `overconf_le_ece`：过度自信量 Σ_b w_b·max(0, conf_b − acc_b) ≤ ECE
     （ECE 的「有向」下界：ECE 至少捕捉了过度自信）；
  7. `brier` / `ece_le_sqrt_brier`（核心）：ECE ≤ √Brier，其中
     Brier = Σ_b w_b·(acc_b − conf_b)²（Σ_b w_b = 1）——加权 Cauchy–Schwarz；
  8. `high_conf_error_bound`：高置信箱（conf_b ≥ 1 − δ）上
     Σ_{b∈H} w_b·(1 − δ − acc_b) ≤ ECE
     ——「高置信样本的误差界」：模型在置信度 ≥ 1 − δ 的箱上把准确率做到 1 − δ
     的缺口，被 ECE 整体支配。

**诚实边界**（本文件不证 / 不声称的）：

- ECE 的输入是**先验给定的分箱聚合数据**（权重 w_b、箱内准确率 acc_b、箱内平均置信度 conf_b），
  而不是从原始样本 (x_i, y_i, ĉ_i) 重新求平均。这是刻意的诚实降级：从原始样本到
  箱内平均需要除以箱内样本数，涉及「空箱 / 零样本数」的边界约定，且对 ECE 的
  所有结构性结论（非负、零化、Brier 上界、高置信界）都无影响。
  `binning`/`binCount`/`binWeight` 给出分箱的原始层，但 `w_b = n_b/n` 的归一化
  （`Σ_b w_b = 1`）在 `ece_le_sqrt_brier` 中作为**显式假设** `hws` 出现。
- 未做：连续分布版 ECE（用积分/测度替换有限和）、概率校准的统计一致性、
  温度缩放 / 直方图分箱的最优性。这些标注为后续。
- 所有结论都是**有限**的、模型无关的：任意箱数 B、任意实数 acc/conf（不要求落在 [0,1]，
  除非某条定理明确要求）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 定义：分箱与箱权重 -/

/-- 分箱（binning）：把 n 个样本分配到 B 个置信度区间之一。 -/
abbrev binning (n B : ℕ) := Fin n → Fin B

/-- 第 b 箱的样本数 n_b。 -/
def binCount {n B : ℕ} (binOf : binning n B) (b : Fin B) : ℕ :=
  (Finset.univ.filter (fun a => binOf a = b)).card

/-- 第 b 箱的权重 n_b/n。 -/
noncomputable def binWeight {n B : ℕ} (binOf : binning n B) (b : Fin B) : ℝ :=
  (binCount binOf b : ℝ) / n

/-- 单箱样本数不超过总样本数（filter 的基数 ≤ 全集基数）。 -/
lemma binCount_le {n B : ℕ} (binOf : binning n B) (b : Fin B) : binCount binOf b ≤ n := by
  unfold binCount
  calc (Finset.univ.filter (fun a => binOf a = b)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := Fintype.card_fin n

/-- 箱权重不超过 1（n ≠ 0 时）。 -/
lemma binWeight_le_one {n B : ℕ} (binOf : binning n B) (b : Fin B) (hn : n ≠ 0) :
    binWeight binOf b ≤ 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold binWeight
  rw [div_le_one hnpos]
  exact_mod_cast binCount_le binOf b

/-- 箱权重非负。 -/
lemma binWeight_nonneg {n B : ℕ} (binOf : binning n B) (b : Fin B) :
    0 ≤ binWeight binOf b := by
  unfold binWeight
  exact div_nonneg (by positivity) (by positivity)

/-! ## 定义：期望校准误差 -/

/-- 期望校准误差：ECE = Σ_b w_b·|acc_b − conf_b|。
w_b 为箱权重、acc_b 为箱内准确率、conf_b 为箱内平均置信度。 -/
noncomputable def ece {B : ℕ} (w acc conf : Fin B → ℝ) : ℝ :=
  ∑ b, w b * |acc b - conf b|

/-! ## 定理一：ECE 非负 -/

theorem ece_nonneg {B : ℕ} (w acc conf : Fin B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    0 ≤ ece w acc conf := by
  unfold ece
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (abs_nonneg _))

/-! ## 定理二：完美校准 ⟹ ECE = 0 -/

theorem ece_self {B : ℕ} (w acc : Fin B → ℝ) : ece w acc acc = 0 := by
  unfold ece
  simp

/-! ## 定理三（核心）：ECE = 0 ⟺ 每个正权重箱内 acc = conf

w ≥ 0 时，Σ_b w_b·|acc_b − conf_b| = 0 ⟺ ∀ b, w_b ≠ 0 → acc_b = conf_b。
证明：逐项非负，非负和为零 ⟺ 每项为零（`Finset.sum_eq_zero_iff_of_nonneg`）；
每项 w_b·|d_b| = 0 时 w_b ≠ 0 强制 |d_b| = 0 即 d_b = 0。 -/

theorem ece_zero_iff_perfect {B : ℕ} (w acc conf : Fin B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    ece w acc conf = 0 ↔ ∀ b, w b ≠ 0 → acc b = conf b := by
  have hterm0 : ∀ b, 0 ≤ w b * |acc b - conf b| :=
    fun b => mul_nonneg (hw b) (abs_nonneg _)
  constructor
  · intro h b hwb
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hterm0 b)).mp h
    have hb := hall b (Finset.mem_univ b)
    rcases mul_eq_zero.mp hb with h1 | h2
    · exact absurd h1 hwb
    · exact sub_eq_zero.mp (abs_eq_zero.mp h2)
  · intro h
    unfold ece
    apply Finset.sum_eq_zero
    intro b _
    by_cases hwb : w b = 0
    · simp [hwb]
    · rw [h b hwb, sub_self, abs_zero, mul_zero]

/-! ## 定义与定理四：过度自信量与其 ECE 下界 -/

/-- 过度自信量：Σ_b w_b·max(0, conf_b − acc_b)。 -/
noncomputable def overconf {B : ℕ} (w acc conf : Fin B → ℝ) : ℝ :=
  ∑ b, w b * max 0 (conf b - acc b)

/-- 过度自信量 ≤ ECE（逐项 max(0, c−a) ≤ |a−c|）。 -/
theorem overconf_le_ece {B : ℕ} (w acc conf : Fin B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    overconf w acc conf ≤ ece w acc conf := by
  unfold overconf ece
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (hw b)
  exact max_le (abs_nonneg _) (by
    have := neg_le_abs (acc b - conf b)
    simpa [neg_sub] using this)

/-! ## 定义与定理五（核心）：Brier 分数与 ECE ≤ √Brier -/

/-- Brier 分数型的校准平方误差：Σ_b w_b·(acc_b − conf_b)²。 -/
noncomputable def brier {B : ℕ} (w acc conf : Fin B → ℝ) : ℝ :=
  ∑ b, w b * (acc b - conf b) ^ 2

lemma brier_nonneg {B : ℕ} (w acc conf : Fin B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    0 ≤ brier w acc conf := by
  unfold brier
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (sq_nonneg _))

/-- ECE ≤ √Brier（Σ_b w_b = 1）。
证明：加权 Cauchy–Schwarz (Σ w|d|)² ≤ (Σ w)(Σ w d²) = Brier，
再由 ece ≥ 0、brier ≥ 0 用 `Real.le_sqrt` 开方。 -/
theorem ece_le_sqrt_brier {B : ℕ} (w acc conf : Fin B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hws : ∑ b, w b = 1) :
    ece w acc conf ≤ Real.sqrt (brier w acc conf) := by
  have hcs : (∑ b, Real.sqrt (w b) * (Real.sqrt (w b) * |acc b - conf b|)) ^ 2
      ≤ (∑ b, (Real.sqrt (w b)) ^ 2)
        * (∑ b, (Real.sqrt (w b) * |acc b - conf b|) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  have hx : (∑ b, Real.sqrt (w b) * (Real.sqrt (w b) * |acc b - conf b|))
      = ece w acc conf := by
    unfold ece
    apply Finset.sum_congr rfl
    intro b _
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw b)]
  have hy : (∑ b, (Real.sqrt (w b)) ^ 2) = ∑ b, w b := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Real.sq_sqrt (hw b)]
  have hz : (∑ b, (Real.sqrt (w b) * |acc b - conf b|) ^ 2) = brier w acc conf := by
    unfold brier
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_pow, Real.sq_sqrt (hw b), sq_abs]
  rw [hx, hy, hz, hws, one_mul] at hcs
  exact (Real.le_sqrt (ece_nonneg w acc conf hw) (brier_nonneg w acc conf hw)).mpr hcs

/-! ## 定理六：高置信样本的误差界

高置信箱 H（每个 b ∈ H 满足 conf_b ≥ 1 − δ 且不过度自信 acc_b ≤ conf_b）上，
Σ_{b∈H} w_b·(1 − δ − acc_b) ≤ ECE：
逐项 1 − δ − acc_b ≤ conf_b − acc_b ≤ |acc_b − conf_b|，再用
`Finset.sum_le_sum_of_subset_of_nonneg` 把 H 上的和扩到全集。 -/

theorem high_conf_error_bound {B : ℕ} (w acc conf : Fin B → ℝ) (H : Finset (Fin B)) (δ : ℝ)
    (hw : ∀ b, 0 ≤ w b) (hconf : ∀ b ∈ H, 1 - δ ≤ conf b) :
    ∑ b in H, w b * (1 - δ - acc b) ≤ ece w acc conf := by
  have h1 : ∑ b in H, w b * (1 - δ - acc b) ≤ ∑ b in H, w b * |acc b - conf b| := by
    apply Finset.sum_le_sum
    intro b hb
    apply mul_le_mul_of_nonneg_left _ (hw b)
    have hle : 1 - δ - acc b ≤ conf b - acc b := by
      linarith [hconf b hb]
    have h2 := neg_le_abs (acc b - conf b)
    have h3 : conf b - acc b = -(acc b - conf b) := by ring
    calc 1 - δ - acc b ≤ conf b - acc b := hle
      _ = -(acc b - conf b) := h3
      _ ≤ |acc b - conf b| := h2
  have h4 : ∑ b in H, w b * |acc b - conf b| ≤ ∑ b, w b * |acc b - conf b| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun b _ _ => mul_nonneg (hw b) (abs_nonneg _))
  have h5 : ∑ b, w b * |acc b - conf b| = ece w acc conf := rfl
  linarith [h1, h4, h5.le, h5.ge]

end Lattice
