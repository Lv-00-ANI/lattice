import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.RealHardAttention
import Lattice.Lib.Attention.RealSoftmaxLipschitz
/-!
# LATTICE: softmax 平移不变性与温度缩放（注意力数学补充）

注意力数学的两条 softmax 基础性质（模型无关，任意 logits、任意维度 k）：

  1. **平移不变性**：softmax(s + c·1) = softmax(s)
     ——对每个 logit 同时加常数 c，exp 因子 e^c 在分子/分母中同时出现而消去；
     这是 logsumexp 技巧（数值稳定性、subtract max）的理论依据：
     减去最大分数不改变分布。
  2. **温度缩放**：softmax(s/τ)（τ > 0）
     ——τ 增大使分布趋近平滑/均匀（高温），τ 减小使分布更尖锐（低温）；
     · 相对序保持：sⱼ ≤ sᵢ ⟺ softmax(s/τ)ⱼ ≤ softmax(s/τ)ᵢ（exp 严格单调）；
     · 均匀化定量界：分数有界 |sᵢ| ≤ M 时
       |softmax(s/τ)ⱼ − 1/k| ≤ (2M/τ)·e^{2M/τ}（τ → ∞ 时趋于 0）；
     · 高温极限：τ → ∞ 时 softmax(s/τ)ⱼ → 1/k（均匀分布）。

与注意力的衔接：softmax 是 attention 的权重行（行随机：非负 + 和为 1，
见 RealAttention）；平移不变性支撑数值稳定实现（subtract max），温度缩放
支撑 softmax 温度参数（LLM 采样、蒸馏、注意力锐化）的语义——保序性保证
温度不改变 token 相对偏好，高温极限给出"随机均匀"的退化行为。

模型无关：任意指标数 k（Fin k）、任意分数 s、任意常数平移 c 与温度 τ > 0。
-/

noncomputable section

open Filter

open scoped Topology

namespace Lattice

/-! ## 温度缩放的 softmax（定义）
softmaxTemp s τ = softmax(s/τ)：第 j 个坐标 exp(sⱼ/τ)/Σ_k exp(s_k/τ)。-/

noncomputable def softmaxTemp {k : ℕ} (s : Fin k → ℝ) (τ : ℝ) : Fin k → ℝ :=
  fun i => Real.exp (s i / τ) / ∑ j : Fin k, Real.exp (s j / τ)

/-! ## 支撑引理：分母的平移缩放
Σ_k exp(s_k + c) = e^c · Σ_k exp(s_k)（exp_add 逐项 + Finset.mul_sum）。-/

lemma softmax_scale_invariant_denom {k : ℕ} (s : Fin k → ℝ) (c : ℝ) :
    (∑ i : Fin k, Real.exp (s i + c)) = Real.exp c * (∑ i : Fin k, Real.exp (s i)) := by
  calc
    (∑ i : Fin k, Real.exp (s i + c)) = ∑ i : Fin k, (Real.exp c * Real.exp (s i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.exp_add]
      ring
    _ = Real.exp c * (∑ i : Fin k, Real.exp (s i)) := by
      rw [Finset.mul_sum]

/-! ## 定理一：softmax 平移不变性（核心）
softmax(s + c·1)ⱼ = softmax(s)ⱼ（∀j，exp(sⱼ+c) = e^c·exp(sⱼ)，分母同乘 e^c 消去）。
与注意力的衔接：数值稳定实现（logsumexp / subtract max）不改变分布。-/

theorem softmax_translation_invariant {k : ℕ} (s : Fin k → ℝ) (c : ℝ) (j : Fin k) :
    softmax (fun i => s i + c) j = softmax s j := by
  unfold softmax
  haveI : Nonempty (Fin k) := ⟨j⟩
  have hc0 : Real.exp c ≠ 0 := Real.exp_ne_zero c
  have hS0 : (∑ i : Fin k, Real.exp (s i)) ≠ 0 := ne_of_gt (softmax_denom_pos s)
  have hden := softmax_scale_invariant_denom s c
  have hnum : Real.exp (s j + c) = Real.exp (s j) * Real.exp c := by
    rw [Real.exp_add]
  calc
    Real.exp (s j + c) / (∑ i : Fin k, Real.exp (s i + c))
        = (Real.exp (s j) * Real.exp c) / (Real.exp c * (∑ i : Fin k, Real.exp (s i))) := by
          rw [hnum, hden]
    _ = Real.exp (s j) / (∑ i : Fin k, Real.exp (s i)) := by
          field_simp [hc0, hS0]
          ring

/-! ## 定理二：温度缩放（展开式）
softmaxTemp s τ = softmax(s/τ)，即第 j 坐标 exp(sⱼ/τ)/Σ_k exp(s_k/τ)。-/

theorem softmax_temp_scale {k : ℕ} (s : Fin k → ℝ) (τ : ℝ) :
    softmaxTemp s τ = softmax (fun i => s i / τ) := by
  rfl

/-! ## 定理三：温度缩放保序
τ > 0 时 sⱼ ≤ sᵢ ⟹ softmax(s/τ)ⱼ ≤ softmax(s/τ)ᵢ：
s ↦ s/τ 是单调重参数化（除以正 τ），softmax_monotone 一行给出。
与注意力的衔接：温度不改变 token 相对偏好（软路由选择与低温一致）。-/

theorem softmax_temp_preserves_order {k : ℕ} (s : Fin k → ℝ) (τ : ℝ) (j i : Fin k)
    (hτ : 0 < τ) (h : s j ≤ s i) :
    softmaxTemp s τ j ≤ softmaxTemp s τ i := by
  rw [softmax_temp_scale]
  haveI : Nonempty (Fin k) := ⟨j⟩
  exact softmax_monotone (fun t => s t / τ) i j (div_le_div_of_nonneg_right h (le_of_lt hτ))

/-! ## 定理四：温度保序的逆方向（相对序完全保持）
τ > 0 时 sⱼ ≤ sᵢ ⟺ softmax(s/τ)ⱼ ≤ softmax(s/τ)ᵢ。
逆方向：exp 严格单调（Real.exp_le_exp 双向）+ 公共正分母消去 + 除以正 τ。-/

theorem softmax_temp_order_iff {k : ℕ} (s : Fin k → ℝ) (τ : ℝ) (j i : Fin k) (hτ : 0 < τ) :
    (s j ≤ s i) ↔ softmaxTemp s τ j ≤ softmaxTemp s τ i := by
  constructor
  · intro h
    exact softmax_temp_preserves_order s τ j i hτ h
  · intro h
    haveI : Nonempty (Fin k) := ⟨j⟩
    have hZ : 0 < ∑ t : Fin k, Real.exp (s t / τ) := softmax_denom_pos (fun t => s t / τ)
    rw [softmax_temp_scale] at h
    have hnum : Real.exp (s j / τ) ≤ Real.exp (s i / τ) := by
      unfold softmax at h
      have hle' : Real.exp (s j / τ) * (∑ t : Fin k, Real.exp (s t / τ))
          ≤ Real.exp (s i / τ) * (∑ t : Fin k, Real.exp (s t / τ)) :=
        (div_le_div_iff₀ hZ hZ).mp h
      exact (mul_le_mul_right hZ).mp hle'
    have hdiv : s j / τ ≤ s i / τ := Real.exp_le_exp.mp hnum
    exact (div_le_div_iff_of_pos_right hτ).mp hdiv

/-! ## 定理五：温度越高越均匀（定量界）
分数有界 |sᵢ| ≤ M 时，|softmax(s/τ)ⱼ − 1/k| ≤ (2M/τ)·e^{2M/τ}（τ > 0）。
路线：softmax(s/τ)ⱼ − 1/k = Σᵢ(e^{sⱼ/τ} − e^{sᵢ/τ}) / (k·Z)（Z = Σ e^{sᵢ/τ}）；
分子逐项用 exp_lipschitz_on（exp 在 [−M/τ, M/τ] 上 e^{M/τ}-Lipschitz）
+ |sⱼ/τ − sᵢ/τ| ≤ 2M/τ；分母下界 Z ≥ e^{−M/τ}（⟹ 1/Z ≤ e^{M/τ}）。-/

theorem softmax_temp_between_uniform {k : ℕ} (M : ℝ) (s : Fin k → ℝ) (τ : ℝ) (j : Fin k)
    (hτ : 0 < τ) (hbound : ∀ i : Fin k, |s i| ≤ M) :
    |softmaxTemp s τ j - 1 / (k : ℝ)| ≤ (2 * M / τ) * Real.exp (2 * M / τ) := by
  haveI : Nonempty (Fin k) := ⟨j⟩
  have hM : 0 ≤ M := le_trans (abs_nonneg (s j)) (hbound j)
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hZ : 0 < ∑ i : Fin k, Real.exp (s i / τ) := softmax_denom_pos (fun i => s i / τ)
  have hZ0 : (∑ i : Fin k, Real.exp (s i / τ)) ≠ 0 := ne_of_gt hZ
  have hdenpos : 0 < k * (∑ i : Fin k, Real.exp (s i / τ)) := mul_pos hkpos hZ
  -- 分子改写：k·e^{sⱼ/τ} = Σᵢ e^{sⱼ/τ}
  have hkexp : (k : ℝ) * Real.exp (s j / τ) = ∑ i : Fin k, Real.exp (s j / τ) := by
    simp [Finset.sum_const]
  have hnum_sum : k * Real.exp (s j / τ) - ∑ i : Fin k, Real.exp (s i / τ)
      = ∑ i : Fin k, (Real.exp (s j / τ) - Real.exp (s i / τ)) := by
    rw [hkexp, Finset.sum_sub_distrib]
  -- 分数分解：softmaxTemp s τ j − 1/k = (k·e^{sⱼ/τ} − Z) / (k·Z)
  have hfrac : softmaxTemp s τ j - 1 / (k : ℝ)
      = (k * Real.exp (s j / τ) - ∑ i : Fin k, Real.exp (s i / τ))
          / (k * (∑ i : Fin k, Real.exp (s i / τ))) := by
    unfold softmaxTemp
    field_simp [hk0, hZ0]
    ring
  -- 逐项界：|e^{sⱼ/τ} − e^{sᵢ/τ}| ≤ e^{M/τ}·(2M/τ)
  have hterm : ∀ i : Fin k, |Real.exp (s j / τ) - Real.exp (s i / τ)|
      ≤ Real.exp (M / τ) * (2 * M / τ) := by
    intro i
    have hsjM : s j / τ ≤ M / τ := div_le_div_of_nonneg_right (abs_le.mp (hbound j)).2 (le_of_lt hτ)
    have hsiM : s i / τ ≤ M / τ := div_le_div_of_nonneg_right (abs_le.mp (hbound i)).2 (le_of_lt hτ)
    have hlip := exp_lipschitz_on (M / τ) (s j / τ) (s i / τ) hsjM hsiM
    have hsub : |s j - s i| ≤ 2 * M := by
      have hsub1 : |s j - s i| ≤ |s j| + |s i| := by
        have h := abs_add (s j) (-s i)
        simpa [sub_eq_add_neg, abs_neg] using h
      exact le_trans hsub1 (by nlinarith [hbound j, hbound i])
    have hsubdiv : |s j / τ - s i / τ| ≤ 2 * M / τ := by
      calc
        |s j / τ - s i / τ| = |(s j - s i) / τ| := by rw [sub_div]
        _ = |s j - s i| / |τ| := abs_div _ _
        _ = |s j - s i| / τ := by rw [abs_of_pos hτ]
        _ ≤ 2 * M / τ := by
          exact div_le_div_of_nonneg_right hsub (le_of_lt hτ)
    exact le_trans hlip (mul_le_mul_of_nonneg_left hsubdiv (le_of_lt (Real.exp_pos (M / τ))))
  -- 和界：Σᵢ |·| ≤ k·e^{M/τ}·(2M/τ)
  have hsum_le : (∑ i : Fin k, |Real.exp (s j / τ) - Real.exp (s i / τ)|)
      ≤ (k : ℝ) * (Real.exp (M / τ) * (2 * M / τ)) := by
    calc
      (∑ i : Fin k, |Real.exp (s j / τ) - Real.exp (s i / τ)|)
          ≤ ∑ i : Fin k, (Real.exp (M / τ) * (2 * M / τ)) := by
            exact Finset.sum_le_sum (by intro i hi; exact hterm i)
      _ = (k : ℝ) * (Real.exp (M / τ) * (2 * M / τ)) := by
            simp [Finset.sum_const]
  -- 三角不等式：|Σᵢ| ≤ Σᵢ |·|
  have habs_sum : |∑ i : Fin k, (Real.exp (s j / τ) - Real.exp (s i / τ))|
      ≤ ∑ i : Fin k, |Real.exp (s j / τ) - Real.exp (s i / τ)| :=
    Finset.abs_sum_le_sum_abs (fun i : Fin k => Real.exp (s j / τ) - Real.exp (s i / τ)) Finset.univ
  -- 绝对值分解
  have habs_frac : |softmaxTemp s τ j - 1 / (k : ℝ)|
      = |∑ i : Fin k, (Real.exp (s j / τ) - Real.exp (s i / τ))|
          / (k * (∑ i : Fin k, Real.exp (s i / τ))) := by
    rw [hfrac, hnum_sum]
    rw [abs_div]
    rw [abs_of_pos (mul_pos hkpos hZ)]
  -- 分母倒数界：1/Z ≤ e^{M/τ}（Z ≥ e^{−M/τ}）
  have h1Z : 1 / (∑ i : Fin k, Real.exp (s i / τ)) ≤ Real.exp (M / τ) := by
    have hZlow : Real.exp (-(M / τ)) ≤ ∑ i : Fin k, Real.exp (s i / τ) := by
      have hneg : -M ≤ s j := (abs_le.mp (hbound j)).1
      have hdiv : (-M) / τ ≤ s j / τ := div_le_div_of_nonneg_right hneg (le_of_lt hτ)
      have hdiv' : -(M / τ) ≤ s j / τ := by
        rwa [neg_div] at hdiv
      calc
        Real.exp (-(M / τ)) ≤ Real.exp (s j / τ) := Real.exp_le_exp.mpr hdiv'
        _ ≤ ∑ i : Fin k, Real.exp (s i / τ) := by
          exact Finset.single_le_sum
            (by intro i hi; exact le_of_lt (Real.exp_pos (s i / τ))) (Finset.mem_univ j)
    have hpos : 0 < Real.exp (M / τ) := Real.exp_pos (M / τ)
    rw [div_le_iff₀ hZ]
    have hle : Real.exp (M / τ) * Real.exp (-(M / τ))
        ≤ Real.exp (M / τ) * (∑ i : Fin k, Real.exp (s i / τ)) :=
      mul_le_mul_of_nonneg_left hZlow (le_of_lt hpos)
    have hone : Real.exp (M / τ) * Real.exp (-(M / τ)) = 1 := by
      rw [← Real.exp_add]
      have hsum0 : M / τ + -(M / τ) = 0 := by ring
      rw [hsum0]
      exact Real.exp_zero
    rwa [hone] at hle
  have h2m : 2 * (M / τ) = 2 * M / τ := by ring
  -- 主链
  calc
    |softmaxTemp s τ j - 1 / (k : ℝ)|
        = |∑ i : Fin k, (Real.exp (s j / τ) - Real.exp (s i / τ))|
            / (k * (∑ i : Fin k, Real.exp (s i / τ))) := habs_frac
    _ ≤ (∑ i : Fin k, |Real.exp (s j / τ) - Real.exp (s i / τ)|)
            / (k * (∑ i : Fin k, Real.exp (s i / τ))) := by
          exact div_le_div_of_nonneg_right habs_sum (le_of_lt hdenpos)
    _ ≤ (k * (Real.exp (M / τ) * (2 * M / τ)))
            / (k * (∑ i : Fin k, Real.exp (s i / τ))) := by
          exact div_le_div_of_nonneg_right hsum_le (le_of_lt hdenpos)
    _ = (Real.exp (M / τ) * (2 * M / τ)) / (∑ i : Fin k, Real.exp (s i / τ)) := by
          field_simp [hk0, hZ0]
          ring
    _ ≤ (2 * M / τ) * Real.exp (2 * M / τ) := by
          calc
            (Real.exp (M / τ) * (2 * M / τ)) / (∑ i : Fin k, Real.exp (s i / τ))
                = (2 * M / τ) * (Real.exp (M / τ) * (1 / (∑ i : Fin k, Real.exp (s i / τ)))) := by
                  field_simp [hZ0]
                  ring
            _ ≤ (2 * M / τ) * (Real.exp (M / τ) * Real.exp (M / τ)) := by
                  have hprod : Real.exp (M / τ) * (1 / (∑ i : Fin k, Real.exp (s i / τ)))
                      ≤ Real.exp (M / τ) * Real.exp (M / τ) :=
                    mul_le_mul_of_nonneg_left h1Z (le_of_lt (Real.exp_pos (M / τ)))
                  have hc : 0 ≤ 2 * M / τ := div_nonneg (by nlinarith [hM]) (le_of_lt hτ)
                  exact mul_le_mul_of_nonneg_left hprod hc
            _ = (2 * M / τ) * Real.exp (2 * (M / τ)) := by
                  have hone : Real.exp (M / τ) * Real.exp (M / τ) = Real.exp (2 * (M / τ)) := by
                    rw [← Real.exp_add]
                    ring
                  rw [hone]
            _ = (2 * M / τ) * Real.exp (2 * M / τ) := by
                  rw [h2m]

/-! ## 定理六：高温极限 → 均匀分布
τ → ∞ 时 softmax(s/τ)ⱼ → 1/k（固定 k = Fintype.card (Fin k)）。
路线：sⱼ/τ → 0，exp 连续 ⟹ exp(sⱼ/τ) → 1；分母 Σᵢ exp(sᵢ/τ) → Σᵢ 1 = k
（tendsto_finset_sum）；商连续（Tendsto.div，分母极限 k ≠ 0）。-/

theorem softmax_temp_high_temp {k : ℕ} (s : Fin k → ℝ) (j : Fin k) :
    Tendsto (fun τ : ℝ => softmaxTemp s τ j) atTop (𝓝 (1 / (k : ℝ))) := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hnum_all : ∀ i : Fin k, Tendsto (fun τ : ℝ => Real.exp (s i / τ)) atTop (𝓝 1) := by
    intro i
    have hz : Tendsto (fun τ : ℝ => s i / τ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop (tendsto_id (α := ℝ)))
    have h := (Real.continuous_exp.tendsto 0).comp hz
    simpa [Real.exp_zero] using h
  have hnum : Tendsto (fun τ : ℝ => Real.exp (s j / τ)) atTop (𝓝 1) := hnum_all j
  have hden : Tendsto (fun τ : ℝ => ∑ i : Fin k, Real.exp (s i / τ)) atTop (𝓝 (k : ℝ)) := by
    have hsum' : Tendsto (fun τ : ℝ => ∑ i : Fin k, Real.exp (s i / τ)) atTop
        (𝓝 (∑ i : Fin k, (1 : ℝ))) := by
      refine tendsto_finset_sum Finset.univ (fun i hi => ?_)
      exact hnum_all i
    simpa [Finset.sum_const] using hsum'
  have hdiv : Tendsto (fun τ : ℝ => Real.exp (s j / τ) / (∑ i : Fin k, Real.exp (s i / τ)))
      atTop (𝓝 (1 / (k : ℝ))) := by
    exact Tendsto.div hnum hden hk0
  simpa [softmaxTemp] using hdiv

end Lattice
