import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealHardAttention
/-!
# LATTICE: 因果掩码注意力 —— 行随机性、输出界与全注意力衔接（解码组件）

真实 transformer 的解码阶段（自回归生成）在位置 `i` 只能 attend 到**过去及当前**
位置 `j ≤ i`（causal mask）：未来位置 `j > i` 的注意力权重必须为 0。
本文件把 `RealAttention` 的 softmax 行随机性与凸组合范数界延伸到这个实际必需的组件：

  1. `causalMask`：因果掩码谓词（查询位置 `i` attend 到 `j` ⟺ `j ≤ i`，即
     `j.val ≤ i.val`——方向：只看过去与当前，不看未来）；
  2. `causalDenom` / `causalSoftmax`：掩码分母 `Σ_{k ≤ i} exp(s_k)` 与掩码 softmax
     `w_j = (if j ≤ i then exp(s_j) else 0) / Σ_{k ≤ i} exp(s_k)`
     ——未来位置权重恰为 0（等价于把 `j > i` 的分数设为 −∞ 的 softmax；
     用"掩码分母"定义避免了 −∞）；
  3. 行随机性：`causalSoftmax_nonneg`（`w_j ≥ 0`）与 `causalSoftmax_sum_one`
     （`Σ_j w_j = 1`，分母恰为掩码内的分子和）——因果权重仍是概率分布；
  4. 输出界：`causal_attention_output_bound`（复用 `convComb_norm_bound`：
     因果权重是凸组合 ⟹ 输出范数被最大 value 界住——解码残差稳定性）；
  5. 与全注意力的衔接：`causal_weights_dominate_prefix`（对 `j ≤ i`，
     `w_j = softmax(s)_j / (Σ_{k ≤ i} softmax(s)_k)`，前缀内重新归一化——
     exp 因子消去）、`causal_softmax_ge_full_on_prefix`（掩码分母更小 ⟹
     前缀位置权重 ≥ 全注意力权重）、`causalSoftmax_eq_softmax_at_last`
     （最后位置的全历史掩码退化为全注意力）。

模型无关：任意位置数 `n`、任意 logits、任意 value 向量。
-/

noncomputable section

namespace Lattice

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## 因果掩码 -/

/-- 因果掩码：查询位置 `i` 只 attend 到 `j ≤ i`（过去与当前；`Fin` 的 ≤ 即值序）。 -/
def causalMask {n : ℕ} (i j : Fin n) : Prop :=
  j ≤ i

@[simp] lemma causalMask_iff {n : ℕ} (i j : Fin n) : causalMask i j ↔ j ≤ i := Iff.rfl

/-! ## 掩码分母（Σ_{k ≤ i} exp(s_k)，if 形式避免 −∞） -/

/-- 因果 softmax 的掩码分母：`Σ_{k ≤ i} exp(s_k)`（用 if 分支写，避免 −∞）。 -/
def causalDenom {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k, (if k ≤ i then Real.exp (s k) else 0)

/-! ## 因果 softmax（掩码权重） -/

/-- 因果 softmax：`w_j = (if j ≤ i then exp(s_j) else 0) / Σ_{k ≤ i} exp(s_k)`。 -/
def causalSoftmax {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  fun j => (if j ≤ i then Real.exp (s j) else 0) / causalDenom s i

/-! ## 引理一：掩码分母为正
`Σ_{k ≤ i} exp(s_k) > 0`（位置 `i` 自身项 `exp(sᵢ) > 0` 且各项非负）。-/

lemma causalDenom_pos {n : ℕ} (s : Fin n → ℝ) (i : Fin n) : 0 < causalDenom s i := by
  unfold causalDenom
  have hnonneg : ∀ k : Fin n, 0 ≤ (if k ≤ i then Real.exp (s k) else 0) := by
    intro k
    by_cases h : k ≤ i
    · simp [h]
      exact le_of_lt (Real.exp_pos (s k))
    · simp [h]
  have hle : Real.exp (s i) ≤ ∑ k : Fin n, (if k ≤ i then Real.exp (s k) else 0) := by
    simpa using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n => if k ≤ i then Real.exp (s k) else 0)
        (fun k hk => hnonneg k) (Finset.mem_univ i))
  exact lt_of_lt_of_le (Real.exp_pos (s i)) hle

/-! ## 引理二：掩码分母 ≤ 全分母
`Σ_{k ≤ i} exp(s_k) ≤ Σ_k exp(s_k)`（掩码只截去非负项——质量集中在前缀的
分母基础）。-/

lemma causalDenom_le_full {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    causalDenom s i ≤ ∑ k : Fin n, Real.exp (s k) := by
  unfold causalDenom
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : k ≤ i
  · simp [h]
  · have hzero : (if k ≤ i then Real.exp (s k) else 0) = 0 := if_neg h
    rw [hzero]
    exact le_of_lt (Real.exp_pos (s k))

/-! ## 定理一：因果 softmax 非负
`∀ j, 0 ≤ w_j`（exp 正 + 掩码分母正 + 条件分支非负）。-/

theorem causalSoftmax_nonneg {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) : 0 ≤ causalSoftmax s i j := by
  unfold causalSoftmax
  apply div_nonneg
  · by_cases h : j ≤ i
    · simp [h]
      exact le_of_lt (Real.exp_pos (s j))
    · simp [h]
  · exact le_of_lt (causalDenom_pos s i)

/-! ## 定理二：因果 softmax 行随机（和为 1）
`Σ_j w_j = 1`——分母恰为掩码内的分子和：`Σ_{j ≤ i} exp(s_j) / Σ_{k ≤ i} exp(s_k) = 1`。-/

theorem causalSoftmax_sum_one {n : ℕ} (s : Fin n → ℝ) (i : Fin n) :
    ∑ j, causalSoftmax s i j = 1 := by
  unfold causalSoftmax
  have hD : causalDenom s i ≠ 0 := ne_of_gt (causalDenom_pos s i)
  calc
    ∑ j, (if j ≤ i then Real.exp (s j) else 0) / causalDenom s i
        = (∑ j, if j ≤ i then Real.exp (s j) else 0) / causalDenom s i := by
          rw [← Finset.sum_div]
    _ = 1 := by
          unfold causalDenom
          exact div_self (by simpa using hD)

/-! ## 定理三：前缀位置权重严格为正
`j ≤ i ⟹ w_j > 0`（每个可见位置都获得正注意力）。-/

theorem causalSoftmax_pos_of_le {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    0 < causalSoftmax s i j := by
  unfold causalSoftmax
  rw [if_pos hji]
  exact div_pos (Real.exp_pos (s j)) (causalDenom_pos s i)

/-! ## 定理四：未来位置被掩码掉
`¬ j ≤ i ⟹ w_j = 0`（j > i 的未来位置权重为 0——等价于分数 −∞）。-/

theorem causalSoftmax_eq_zero_of_gt {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (h : ¬ j ≤ i) :
    causalSoftmax s i j = 0 := by
  unfold causalSoftmax
  simp [h, zero_div]

/-! ## 定理五：注意力输出范数界（凸组合界）
因果权重是概率分布（非负 + 和 1，定理一/二）⟹ 输出被最大 value 界住
（复用 `convComb_norm_bound`，与 `attention_output_bound` 同一模式）。-/

theorem causal_attention_output_bound {n : ℕ} (s : Fin n → ℝ) (i : Fin n) (V : Fin n → F) (M : ℝ)
    (hV : ∀ j, ‖V j‖ ≤ M) :
    ‖convComb (causalSoftmax s i) V‖ ≤ M := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  exact convComb_norm_bound (causalSoftmax s i) V M
    (fun j => causalSoftmax_nonneg s i j) (causalSoftmax_sum_one s i) hV

/-! ## 定理六：前缀内保序
`j₁ ≤ i`、`j₂ ≤ i` 且 `s j₁ ≤ s j₂` ⟹ `w_{j₁} ≤ w_{j₂}`（exp 单调 + 公共正分母，
因果版的 `softmax_monotone`——分数序在可见前缀内保持）。-/

theorem causalSoftmax_monotone {n : ℕ} (s : Fin n → ℝ) (i j₁ j₂ : Fin n)
    (hj₁ : j₁ ≤ i) (hj₂ : j₂ ≤ i) (h : s j₁ ≤ s j₂) :
    causalSoftmax s i j₁ ≤ causalSoftmax s i j₂ := by
  unfold causalSoftmax
  rw [if_pos hj₁, if_pos hj₂]
  have he : Real.exp (s j₁) ≤ Real.exp (s j₂) := Real.exp_le_exp.mpr h
  exact div_le_div_of_nonneg_right he (le_of_lt (causalDenom_pos s i))

/-! ## 定理七：前缀位置权重 ≥ 全注意力权重
`j ≤ i ⟹ softmax(s)_j ≤ w_j`（掩码分母更小 ⟹ 前缀质量被放大——因果注意力
把全部质量压进可见前缀）。-/

theorem causal_softmax_ge_full_on_prefix {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    softmax s j ≤ causalSoftmax s i j := by
  unfold causalSoftmax softmax
  rw [if_pos hji]
  -- div_le_div_of_nonneg_left ha hc h : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
  exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos (s j))) (causalDenom_pos s i)
    (causalDenom_le_full s i)

/-! ## 定理八：前缀重新归一化（与全注意力的衔接）
`j ≤ i ⟹ w_j = softmax(s)_j / (Σ_{k ≤ i} softmax(s)_k)`
——因果权重是全注意力权重在可见前缀上的重新归一化
（exp 因子消去：`exp(s_j)/Z 除以 (Σ_{k≤i} exp(s_k))/Z = exp(s_j)/Σ_{k≤i} exp(s_k)`）。-/

theorem causal_weights_dominate_prefix {n : ℕ} (s : Fin n → ℝ) (i j : Fin n) (hji : j ≤ i) :
    causalSoftmax s i j = softmax s j / (∑ k, (if k ≤ i then softmax s k else 0)) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hZ : (∑ k : Fin n, Real.exp (s k)) ≠ 0 := ne_of_gt (softmax_denom_pos s)
  have hD : causalDenom s i ≠ 0 := ne_of_gt (causalDenom_pos s i)
  calc
    causalSoftmax s i j = Real.exp (s j) / causalDenom s i := by
      unfold causalSoftmax
      rw [if_pos hji]
    _ = (Real.exp (s j) / (∑ k : Fin n, Real.exp (s k)))
        / (causalDenom s i / (∑ k : Fin n, Real.exp (s k))) := by
      have hdiv : (Real.exp (s j) / (∑ k : Fin n, Real.exp (s k)))
            / (causalDenom s i / (∑ k : Fin n, Real.exp (s k)))
          = Real.exp (s j) / causalDenom s i := by
        -- (a/Z)/(D/Z) = a/D：两次除法化简
        rw [div_div_eq_mul_div]
        rw [div_mul_cancel₀ _ hZ]
      exact hdiv.symm
    _ = softmax s j / (∑ k, (if k ≤ i then softmax s k else 0)) := by
      have hden : (∑ k : Fin n, (if k ≤ i then Real.exp (s k) / (∑ j : Fin n, Real.exp (s j)) else 0))
          = causalDenom s i / (∑ j : Fin n, Real.exp (s j)) := by
        calc
          (∑ k : Fin n, (if k ≤ i then Real.exp (s k) / (∑ j : Fin n, Real.exp (s j)) else 0))
              = ∑ k : Fin n, (if k ≤ i then Real.exp (s k) else 0) / (∑ j : Fin n, Real.exp (s j)) := by
                apply Finset.sum_congr rfl
                intro k hk
                by_cases h : k ≤ i <;> simp [h]
          _ = (∑ k : Fin n, if k ≤ i then Real.exp (s k) else 0) / (∑ j : Fin n, Real.exp (s j)) := by
                rw [← Finset.sum_div]
          _ = causalDenom s i / (∑ j : Fin n, Real.exp (s j)) := by
                rw [causalDenom]
      unfold softmax
      rw [hden]

/-! ## 定理九：最后位置退化为全注意力
位置 `n`（最后一个 token）的历史掩码覆盖全体 ⟹ `causalSoftmax = softmax`
（解码收尾时因果注意力与全注意力一致）。-/

theorem causalSoftmax_eq_softmax_at_last {n : ℕ} (s : Fin (n + 1) → ℝ) :
    causalSoftmax s (Fin.last n) = softmax s := by
  funext j
  unfold causalSoftmax softmax causalDenom
  have hle : ∀ k : Fin (n + 1), k ≤ Fin.last n := Fin.le_last
  simp [hle]

end Lattice
