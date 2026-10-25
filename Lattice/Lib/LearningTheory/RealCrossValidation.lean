import Mathlib

/-!
# LATTICE: k 折交叉验证的风险界（凸组合 / 无偏性 / 折间偏差 / k 单调性）

有限样本集 s 上的 k 折交叉验证：把 s 划成 k 个互不相交的折 `f 0, …, f (k−1)`，
每折作为留出集算一次风险，再取平均：

    holdoutRisk t R = (1/|t|)·Σ_{i∈t} R i
    cvRisk f R      = (1/k)·Σ_j holdoutRisk (f j) R
    fullRisk s R    = (1/|s|)·Σ_{i∈s} R i

## 主结果

1. **凸组合结构**（`cvRisk_eq_weighted`）：`cvRisk f R = (1/k)·Σ_j holdoutRisk (f j) R`
   —— CV 风险是各折留出风险的**等权凸组合**，权重 `1/k` 和为 1（`fold_weights_sum`）。
2. **对均值的无偏性**（`cv_unbiased_for_mean`）：若 `f` 是 s 的划分且各折**等大小** m > 0，
   则

       cvRisk f R = fullRisk s R

   即 k 折 CV 风险恰好等于全样本平均风险（用 `Finset.sum_biUnion` 把折和汇成全样本和，
   再用 `|s| = k·m` 化归）。这就是「CV 是留一/留出风险的平均、对有限总体均值无偏」的
   精确内容。
3. **折间偏差界**（`deviation_bound` / `cv_variance_bound`）：加权平均（权重非负、和为 1）
   与中心 c 的偏差 ≤ 各折偏差的最大值：

       |Σ_j w_j·a_j − c| ≤ Δ     （∀j, |a_j − c| ≤ Δ）

   即 CV 风险与全量风险的差被「最大折偏差」控制。
4. **k 单调性**（`cv_monotone_in_k` / `cv_monotone_bias`）：`k` 增大 ⟹ 训练比例
   `1 − 1/k` 增大；若偏差界 `B` 关于训练比例**反单调**（训练数据越多偏差越小，显式假设），
   则更大 k 的偏差界更小。

## 诚实边界

- **i.i.d. 抽样未被形式化**：本文件在**有限总体**上用「划分 + 等大小折」代替 i.i.d. 假设，
  所有结果都是有限组合恒等式/不等式，不涉及概率分布的期望。
- 定理 4 的「偏差界关于训练比例反单调」是**显式假设**（标准的 learnability/稳定性论证
  给出它，本文件不推导），因此 `cv_monotone_bias` 是条件命题而不是无条件定理。
- 折大小 `|f j| ≠ 0` 与 `|s| = k·m` 是显式假设（防除零退化）。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：折划分与风险 -/

/-- `f : Fin k → Finset ι` 是样本集 s 的一个 k 折划分：
    每折含于 s、两两不交、并集覆盖 s。 -/
def IsFoldPartition {k : ℕ} {ι : Type*} [DecidableEq ι] (f : Fin k → Finset ι)
    (s : Finset ι) : Prop :=
  (∀ i, f i ⊆ s) ∧ (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j)) ∧
    s = (Finset.univ : Finset (Fin k)).biUnion f

/-- 留出风险：`(1/|t|)·Σ_{i∈t} R i`。 -/
def holdoutRisk {ι : Type*} (t : Finset ι) (R : ι → ℝ) : ℝ :=
  (1 / (t.card : ℝ)) * ∑ i in t, R i

/-- 全量风险：`(1/|s|)·Σ_{i∈s} R i`。 -/
def fullRisk {ι : Type*} (s : Finset ι) (R : ι → ℝ) : ℝ :=
  (1 / (s.card : ℝ)) * ∑ i in s, R i

/-- k 折交叉验证风险：各折留出风险的等权平均。 -/
def cvRisk {k : ℕ} {ι : Type*} (f : Fin k → Finset ι) (R : ι → ℝ) : ℝ :=
  (1 / (k : ℝ)) * ∑ j : Fin k, holdoutRisk (f j) R

/-- 训练比例 `1 − 1/k`（k 折 CV 用 (k−1)/k 的样本训练）。 -/
def trainFraction (k : ℕ) : ℝ := 1 - 1 / (k : ℝ)

/-! ## 二、凸组合结构与权重和为 1 -/

/-- **凸组合结构**：`cvRisk f R = Σ_j (1/k)·holdoutRisk (f j) R`。 -/
theorem cvRisk_eq_weighted {k : ℕ} {ι : Type*} (f : Fin k → Finset ι) (R : ι → ℝ) :
    cvRisk f R = ∑ j : Fin k, (1 / (k : ℝ)) * holdoutRisk (f j) R := by
  unfold cvRisk
  rw [Finset.mul_sum]

/-- CV 权重 `1/k` 之和为 1（`k > 0`）。 -/
theorem fold_weights_sum {k : ℕ} (hk0 : 0 < k) :
    (∑ _j : Fin k, (1 / (k : ℝ))) = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk0)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-! ## 三、等大小折上的无偏性：cvRisk = fullRisk -/

/-- **k 折 CV：等大小折上的无偏性**。`f` 是 s 的划分、各折大小都是 m > 0、`|s| = k·m`
    ⟹ `cvRisk f R = fullRisk s R`。 -/
theorem cv_unbiased_for_mean {k m : ℕ} {ι : Type*} [DecidableEq ι] (f : Fin k → Finset ι)
    (R : ι → ℝ) (s : Finset ι)
    (hpart : IsFoldPartition f s)
    (hm : ∀ j : Fin k, (f j).card = m) (hm0 : 0 < m) (hk0 : 0 < k)
    (hcard : s.card = k * m) :
    cvRisk f R = fullRisk s R := by
  obtain ⟨hsub, hdisj, hcov⟩ := hpart
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk0)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm0)
  -- 折和 = 全样本和（划分的不交并）
  have hsum : (∑ j : Fin k, ∑ i in f j, R i) = ∑ i in s, R i := by
    rw [hcov]
    exact (Finset.sum_biUnion (s := Finset.univ) (t := f) (f := R)
      (fun x _ y _ hxy => hdisj x y hxy)).symm
  -- 把各折的 1/|f j| 换成 1/m
  have hstep : (∑ j : Fin k, (1 / ((f j).card : ℝ)) * (∑ i in f j, R i))
      = ∑ j : Fin k, (1 / (m : ℝ)) * (∑ i in f j, R i) :=
    Finset.sum_congr rfl (fun j _ => by rw [hm j])
  have h2 : (1 / (k : ℝ)) * (1 / (m : ℝ)) = 1 / ((k * m : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    field_simp
  unfold cvRisk fullRisk holdoutRisk
  rw [hstep, ← Finset.mul_sum, hsum]
  rw [← mul_assoc, h2, hcard]

/-! ## 四、折间偏差界 -/

/-- **加权平均偏差界**：非负权重、和为 1，且每项与中心 c 的距离 ≤ Δ ⟹
    `|Σ_j w_j·a_j − c| ≤ Δ`。 -/
theorem deviation_bound {k : ℕ} (w : Fin k → ℝ) (a : Fin k → ℝ) (c Δ : ℝ)
    (hw0 : ∀ j : Fin k, 0 ≤ w j) (hws : (∑ j : Fin k, w j) = 1)
    (hdev : ∀ j : Fin k, |a j - c| ≤ Δ) :
    |(∑ j : Fin k, w j * a j) - c| ≤ Δ := by
  have hdec : (∑ j : Fin k, w j * a j) - c = ∑ j : Fin k, w j * (a j - c) := by
    have h1 : c = (∑ j : Fin k, w j) * c := by rw [hws, one_mul]
    conv_lhs => rw [h1]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hdec]
  calc
    |∑ j : Fin k, w j * (a j - c)| ≤ ∑ j : Fin k, |w j * (a j - c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin k, w j * |a j - c| :=
      Finset.sum_congr rfl (fun j _ => by rw [abs_mul, abs_of_nonneg (hw0 j)])
    _ ≤ ∑ j : Fin k, w j * Δ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hdev j) (hw0 j))
    _ = (∑ j : Fin k, w j) * Δ := by rw [Finset.sum_mul]
    _ = Δ := by rw [hws, one_mul]

/-- **CV 风险的折间偏差界**：各折留出风险与 c 的偏差 ≤ Δ ⟹ `|cvRisk f R − c| ≤ Δ`。 -/
theorem cv_variance_bound {k : ℕ} {ι : Type*} (f : Fin k → Finset ι) (R : ι → ℝ)
    (c Δ : ℝ) (hk0 : 0 < k) (hdev : ∀ j : Fin k, |holdoutRisk (f j) R - c| ≤ Δ) :
    |cvRisk f R - c| ≤ Δ := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_of_lt hk0
  rw [cvRisk_eq_weighted]
  exact deviation_bound (fun _ => 1 / (k : ℝ)) (fun j => holdoutRisk (f j) R) c Δ
    (fun _ => div_nonneg zero_le_one hkR) (fold_weights_sum hk0) hdev

/-! ## 五、k 的单调性（训练比例随 k 增大） -/

/-- **训练比例随 k 单调增**：`1 ≤ k1 ≤ k2 ⟹ 1 − 1/k1 ≤ 1 − 1/k2`。 -/
theorem cv_monotone_in_k (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (h12 : k1 ≤ k2) :
    trainFraction k1 ≤ trainFraction k2 := by
  have hk1R : (0 : ℝ) < (k1 : ℝ) := by exact_mod_cast hk1
  have h12R : (k1 : ℝ) ≤ (k2 : ℝ) := by exact_mod_cast h12
  unfold trainFraction
  have h : 1 / (k2 : ℝ) ≤ 1 / (k1 : ℝ) := one_div_le_one_div_of_le hk1R h12R
  linarith

/-- **偏差界随 k 减小（条件形式）**：若偏差界函数 `B` 关于训练比例反单调
    （训练数据越多偏差越小，显式假设），则更大 k 的偏差界更小。 -/
theorem cv_monotone_bias (k1 k2 : ℕ) (B : ℝ → ℝ) (hk1 : 1 ≤ k1) (h12 : k1 ≤ k2)
    (hB : Antitone B) :
    B (trainFraction k2) ≤ B (trainFraction k1) :=
  hB (cv_monotone_in_k k1 k2 hk1 h12)

/-! ## 注：闭环语义
  折划分（IsFoldPartition）→ 留出/全量/CV 风险（holdoutRisk / fullRisk / cvRisk）→
  凸组合结构（cvRisk_eq_weighted / fold_weights_sum）→
  等大小折上的无偏性（cv_unbiased_for_mean）→
  折间偏差界（deviation_bound / cv_variance_bound）→
  k 单调性（cv_monotone_in_k / cv_monotone_bias）。
  诚实假设：用有限总体划分代替 i.i.d. 抽样；偏差界对训练比例的反单调性显式给出。 -/

end Lattice
