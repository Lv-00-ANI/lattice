import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealCausalAttention
/-!
# LATTICE: 掩码族统一抽象 —— 任意掩码注意力的行随机性与输出界

transformer 的注意力掩码有多种模式：全注意力（无掩码）、因果掩码（解码，只看
过去）、滑动窗口掩码（Longformer/稀疏注意力）、前缀掩码（prefix-LM）等。
`RealAttention` 只处理全掩码（softmax），`RealCausalAttention` 单独处理因果掩码。
本文件给出**统一的掩码抽象**，一次证明覆盖所有模式：

  1. `maskedDenom` / `maskedSoftmax`：一般掩码权重
     `w_j = (if mask i j then exp(s_j) else 0) / Σ_k (if mask i k then exp(s_k) else 0)`
     ——用 `if` 分支避免 −∞，任意 `mask : Fin n → Fin n → Prop` 都适用；
  2. `maskedSoftmax_nonneg`：**任意**掩码 ⟹ 权重非负（无需任何假设）；
  3. `maskedSoftmax_sum_one`：掩码**行非空** ⟹ `Σ_j w_j = 1`（行随机——统一性的关键）；
  4. `masked_attention_output_bound`：行随机 + 复用 `convComb_norm_bound`
     ⟹ 任意掩码的注意力输出被 `max‖V_j‖` 界住（残差稳定性对所有掩码模式统一成立）；
  5. 特例回收：`full_mask_eq_softmax`（全掩码退化回 `softmax`）、
     `causal_mask_eq_causalSoftmax`（因果掩码与 `RealCausalAttention.causalSoftmax` 一致）；
  6. `slidingMask`：滑动窗口掩码也是合法行随机掩码（`sliding_window_row_random`）。

**诚实假设**：定理 3/4 要求掩码行非空（`∃ j, mask i j`，即每个 query 至少能
attend 一个位置）——否则分母为 0，权重恒 0，行随机性不成立（这是数学事实，
不是证明困难）。定理 2 不需要任何假设。`mask` 需可判定（`DecidableRel mask`），
所有具体掩码（全 / 因果 / 滑动窗口）都自动可判定。
不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一般掩码分母与掩码 softmax -/

/-- 一般掩码分母：`Σ_k (if mask i k then exp(s_k) else 0)`（`if` 形式避免 −∞）。 -/
def maskedDenom {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin n, (if mask i k then Real.exp (s k) else 0)

/-- 一般掩码 softmax：`w_j = (if mask i j then exp(s_j) else 0) / Σ_k (if mask i k then exp(s_k) else 0)`。
任意掩码模式（全 / 因果 / 滑动窗口 / 前缀）共用此定义。 -/
def maskedSoftmax {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  fun j => (if mask i j then Real.exp (s j) else 0) / maskedDenom mask s i

/-! ## 引理：掩码分母非负（无需行非空假设） -/

lemma maskedDenom_nonneg {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) : 0 ≤ maskedDenom mask s i := by
  unfold maskedDenom
  apply Finset.sum_nonneg
  intro k _
  by_cases h : mask i k
  · simp [h]
    exact le_of_lt (Real.exp_pos (s k))
  · simp [h]

/-! ## 引理：掩码行非空 ⟹ 掩码分母为正
（行 `i` 至少要有一个可见位置 `j`；`exp(s_j) > 0` 且各项非负。） -/

lemma maskedDenom_pos {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, mask i j) : 0 < maskedDenom mask s i := by
  obtain ⟨j, hj⟩ := hne
  unfold maskedDenom
  exact Finset.sum_pos'
    (fun k _ => by
      by_cases h : mask i k
      · simp [h]
        exact le_of_lt (Real.exp_pos (s k))
      · simp [h])
    ⟨j, Finset.mem_univ j, by simp [hj, Real.exp_pos (s j)]⟩

/-! ## 定理一（核心）：任意掩码的权重非负
`∀ j, 0 ≤ w_j`——**不需要任何假设**（分子 ≥ 0，分母 ≥ 0，`div_nonneg`）。 -/

theorem maskedSoftmax_nonneg {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) (j : Fin n) : 0 ≤ maskedSoftmax mask s i j := by
  unfold maskedSoftmax
  exact div_nonneg
    (by
      by_cases h : mask i j
      · simp [h]
        exact le_of_lt (Real.exp_pos (s j))
      · simp [h])
    (maskedDenom_nonneg mask s i)

/-! ## 定理二（核心）：任意非空掩码行随机
行非空 ⟹ `Σ_j w_j = 1`——这是「统一性」的关键：无论何种掩码模式，
注意力权重都是概率分布。分母恰为掩码内的分子和。 -/

theorem maskedSoftmax_sum_one {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, mask i j) :
    ∑ j, maskedSoftmax mask s i j = 1 := by
  unfold maskedSoftmax maskedDenom
  have hD : (∑ k : Fin n, (if mask i k then Real.exp (s k) else 0)) ≠ 0 :=
    ne_of_gt (maskedDenom_pos mask s i hne)
  calc
    ∑ j, (if mask i j then Real.exp (s j) else 0) /
          (∑ k : Fin n, (if mask i k then Real.exp (s k) else 0))
        = (∑ j, (if mask i j then Real.exp (s j) else 0)) /
          (∑ k : Fin n, (if mask i k then Real.exp (s k) else 0)) := by
          rw [← Finset.sum_div]
    _ = 1 := by
          exact div_self hD

/-! ## 定理三（核心）：任意掩码的注意力输出界
行随机（定理一/二）+ 复用 `RealAttention.convComb_norm_bound`：
`‖Σ_j w_j • V_j‖ ≤ max_j ‖V_j‖`——凸组合界对所有掩码模式统一成立。 -/

theorem masked_attention_output_bound {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i : Fin n) (hne : ∃ j, mask i j)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Fin n → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (maskedSoftmax mask s i) V‖ ≤ M := by
  haveI : Nonempty (Fin n) := ⟨hne.choose⟩
  exact convComb_norm_bound (maskedSoftmax mask s i) V M
    (fun j => maskedSoftmax_nonneg mask s i j)
    (maskedSoftmax_sum_one mask s i hne) hV

/-! ## 支持引理：掩码内正、掩码外零（与因果版的对应引理平行） -/

theorem maskedSoftmax_pos_of_mask {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (s : Fin n → ℝ) (i j : Fin n) (hne : ∃ k, mask i k) (hij : mask i j) :
    0 < maskedSoftmax mask s i j := by
  unfold maskedSoftmax
  rw [if_pos hij]
  exact div_pos (Real.exp_pos (s j)) (maskedDenom_pos mask s i hne)

theorem maskedSoftmax_eq_zero_of_not_mask {n : ℕ} (mask : Fin n → Fin n → Prop)
    [DecidableRel mask] (s : Fin n → ℝ) (i j : Fin n) (hij : ¬ mask i j) :
    maskedSoftmax mask s i j = 0 := by
  unfold maskedSoftmax
  simp [hij]

/-! ## 定理四（核心/特例回收）：全掩码退化回全注意力 softmax
`mask ≡ True` ⟹ `maskedSoftmax mask s = softmax s`——
统一抽象在无掩码情形下与 `RealAttention.softmax` 完全一致。 -/

theorem full_mask_eq_softmax {n : ℕ} (s : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    maskedSoftmax (fun _ _ : Fin (n + 1) => True) s i = softmax s := by
  funext j
  simp [maskedSoftmax, maskedDenom, softmax]

/-! ## 定理五（核心/特例回收）：因果掩码与 RealCausalAttention 一致
`mask i j := j ≤ i` ⟹ `maskedSoftmax mask s i = causalSoftmax s i`——
因果掩码只是本抽象的一个实例（分母/分子逐项相同）。 -/

theorem causal_mask_eq_causalSoftmax {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    maskedSoftmax (fun _ j : Fin n => j ≤ i) s i = causalSoftmax s i := by
  funext j
  simp [maskedSoftmax, maskedDenom, causalSoftmax, causalDenom]

/-! ## 定理六（加分）：滑动窗口掩码
`slidingMask w i j := j ≤ i ∧ i − j ≤ w`（只看过去、且距离不超过窗口 `w`）。
`slidingMask w i i` 恒成立 ⟹ 每行非空 ⟹ 是合法行随机掩码。 -/

/-- 滑动窗口掩码：`j` 在 `i` 的窗口内（`j ≤ i` 且 `i − j ≤ w`）。 -/
abbrev slidingMask {n : ℕ} (w : ℕ) (i j : Fin n) : Prop :=
  (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) - (j : ℕ) ≤ w

instance instDecidableRelSlidingMask {n : ℕ} (w : ℕ) : DecidableRel (slidingMask (n := n) w) :=
  fun i j => inferInstanceAs (Decidable ((j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) - (j : ℕ) ≤ w))

/-- 对角线满足滑动窗口掩码（`i − i = 0 ≤ w`）⟹ 每行非空。 -/
theorem slidingMask_refl {n : ℕ} (w : ℕ) (i : Fin n) : slidingMask w i i := by
  constructor
  · exact le_rfl
  · rw [Nat.sub_self]
    exact Nat.zero_le w

/-- 滑动窗口掩码的注意力权重行随机（合法性）。 -/
theorem sliding_window_row_random {n : ℕ} (w : ℕ) (s : Fin n → ℝ) (i : Fin n) :
    ∑ j, maskedSoftmax (slidingMask w) s i j = 1 :=
  maskedSoftmax_sum_one (slidingMask w) s i ⟨i, slidingMask_refl w i⟩

/-- 滑动窗口掩码的注意力权重非负（合法性）。 -/
theorem sliding_window_nonneg {n : ℕ} (w : ℕ) (s : Fin n → ℝ) (i j : Fin n) :
    0 ≤ maskedSoftmax (slidingMask w) s i j :=
  maskedSoftmax_nonneg (slidingMask w) s i j

/-- 滑动窗口掩码的注意力输出界（残差稳定性对稀疏注意力同样成立）。 -/
theorem sliding_window_output_bound {n : ℕ} (w : ℕ) (s : Fin n → ℝ) (i : Fin n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Fin n → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (maskedSoftmax (slidingMask w) s i) V‖ ≤ M :=
  masked_attention_output_bound (slidingMask w) s i ⟨i, slidingMask_refl w i⟩ V M hV

/-! ## 推论：一般行非空掩码的输出界（自反掩码是常见充分条件）
任何满足 `∀ i, mask i i` 的掩码（自反掩码）自动行非空，
于是行随机性与输出界对所有自反掩码模式统一成立。 -/

theorem masked_row_nonempty_of_refl {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (hrefl : ∀ i, mask i i) (i : Fin n) : ∃ j, mask i j :=
  ⟨i, hrefl i⟩

theorem refl_mask_output_bound {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (hrefl : ∀ i, mask i i) (s : Fin n → ℝ) (i : Fin n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Fin n → F) (M : ℝ) (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (maskedSoftmax mask s i) V‖ ≤ M :=
  masked_attention_output_bound mask s i (masked_row_nonempty_of_refl mask hrefl i) V M hV

/-- 自反掩码的行随机性。 -/
theorem refl_mask_sum_one {n : ℕ} (mask : Fin n → Fin n → Prop) [DecidableRel mask]
    (hrefl : ∀ i, mask i i) (s : Fin n → ℝ) (i : Fin n) :
    ∑ j, maskedSoftmax mask s i j = 1 :=
  maskedSoftmax_sum_one mask s i (masked_row_nonempty_of_refl mask hrefl i)

end Lattice
