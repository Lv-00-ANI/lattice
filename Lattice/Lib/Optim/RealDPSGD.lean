import Lattice.Lib.Optim.RealSGDStochastic
import Lattice.Lib.Convex.RealSubgradientDescent
import Mathlib

/-!
# LATTICE: DP-SGD 的裁剪-噪声结构与隐私-效用权衡（结构化形式化）

差分隐私 SGD（DP-SGD）的机制是「每个样本梯度先裁剪到范数 ≤ C，再加噪声」：

    clipGradient C g = g · min(1, C/‖g‖)
    dpsgdDirection C σ g ξ = clipGradient C g + ξ,    ‖ξ‖ ≤ σ·C

## 主结果

1. **裁剪范数界**（`clip_norm_le`）：`0 ≤ C ⟹ ‖clip g‖ ≤ C`；且 `‖g‖ ≤ C` 时裁剪
   不改变梯度（`clipGradient_of_le`）。
2. **裁剪偏差界**（`clip_bias_bound`）：逐点 `|clip g − g| ≤ max(0, ‖g‖ − C)`，
   期望形式 `clip_bias_expectation_bound`：

       |E[clip g] − E[g]| ≤ E[max(0, ‖g‖ − C)]

   即裁剪只在「超出阈值的部分」引入偏差；配合 Markov 不等式
   （`markov_inequality`：`C·P(‖g‖ > C) ≤ E‖g‖`）给出「大梯度概率」的控制。
3. **噪声项**（`noiseBound` / `noiseVariance`）：噪声幅度界 `σC`、方差 `σ²C²`
   （对应高斯机制 `N(0, σ²C²)` 的尺度）。
4. **效用界**（`dpsgd_utility_bound` / `dpsgd_rate_optimal`）：把带噪方向当作范数
   ≤ `C(1+σ)` 的次梯度选择，代入 `RealSubgradientDescent` 的望远镜界，得到

       ∃ t < T, f(x_t) − f x* ≤ (‖x_0 − x*‖² + η²T·(C(1+σ))²)/(2ηT)

   其中 `D = ‖x_0 − x*‖`。上式即 `dpsgd_utility_bound`（任意步长 η 下的差距界）；
   取最优步长 η = D/(C(1+σ)√T) 时（对应 `dpsgd_rate_optimal`）退化为
   `O(D·C(1+σ)/√T)`：**速率常数随噪声 σ 线性退化**。
5. **隐私-效用权衡**（`privacy_utility_tradeoff` / `privacy_proxy_antitone`）：
   `σ` 增大时效用界变大（变差），隐私代理 `1/σ` 单调下降（变好）。

## 诚实边界（重要）

- **（ε, δ)-差分隐私的定义与保证本身未形式化。** 本文件形式化的是 DP-SGD 的
  「裁剪 + 有界噪声 ⟹ 方向范数上界 ⟹ 收敛速率退化」这一**结构化效用侧**，
  以及噪声-隐私的**单调代理**。隐私预算 (ε,δ) 到噪声尺度 σ 的标准换算
  （如 σ ≥ √(2 ln(1.25/δ))/ε）需要隐私损失的组合定理与高斯机制的 Rényi DP 分析，
  本文件不做，也没有声称做过。
- 效用界中的 `hbound`（带噪方向范数 ≤ C(1+σ)）是**显式假设**：本文件给出了
  它的来源（`dpsgd_direction_bound`：裁剪 + 有界噪声），但把「带噪方向仍是
  f 的次梯度」作为假设 —— 噪声本身破坏次梯度性质，这是 DP-SGD 的固有偏差，
  诚实标注而不是掩盖。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、裁剪算子 -/

/-- 梯度裁剪：`g ↦ g · min(1, C/‖g‖)`（`g = 0` 时 `C/‖g‖` 取 Lean 的 `x/0 = 0`，结果为 0）。 -/
def clipGradient (C g : ℝ) : ℝ := g * min 1 (C / |g|)

/-- **裁剪范数界**：`0 ≤ C ⟹ ‖clip g‖ ≤ C`。 -/
theorem clip_norm_le (C g : ℝ) (hC : 0 ≤ C) : |clipGradient C g| ≤ C := by
  unfold clipGradient
  by_cases hg : g = 0
  · rw [hg]
    simpa using hC
  · have hgpos : 0 < |g| := abs_pos.mpr hg
    have hCabs : 0 ≤ C / |g| := div_nonneg hC (le_of_lt hgpos)
    have hmin0 : 0 ≤ min 1 (C / |g|) := le_min zero_le_one hCabs
    have hle : min 1 (C / |g|) ≤ C / |g| := min_le_right _ _
    have h2 : |g| * min 1 (C / |g|) ≤ |g| * (C / |g|) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg g)
    have h3 : |g| * (C / |g|) = C := by
      field_simp [ne_of_gt hgpos]
    rw [abs_mul, abs_of_nonneg hmin0]
    rw [h3] at h2
    exact h2

/-- **小梯度不被裁剪**：`‖g‖ ≤ C ⟹ clip g = g`。 -/
theorem clipGradient_of_le (C g : ℝ) (h : |g| ≤ C) : clipGradient C g = g := by
  unfold clipGradient
  by_cases hg : g = 0
  · rw [hg]; simp
  · have hgpos : 0 < |g| := abs_pos.mpr hg
    have h1 : 1 ≤ C / |g| := by
      rw [le_div_iff₀ hgpos]
      simpa using h
    rw [min_eq_left h1, mul_one]

/-- **裁剪偏差界（逐点）**：`|clip g − g| ≤ max(0, ‖g‖ − C)`。 -/
theorem clip_bias_bound (C g : ℝ) (hC : 0 ≤ C) :
    |clipGradient C g - g| ≤ max 0 (|g| - C) := by
  by_cases h : |g| ≤ C
  · rw [clipGradient_of_le C g h]
    simp only [sub_self, abs_zero]
    exact le_max_left 0 (|g| - C)
  · push_neg at h
    have hgne : g ≠ 0 := by
      intro hg
      rw [hg] at h
      simp at h
      linarith
    have hgpos : 0 < |g| := abs_pos.mpr hgne
    have hlt : C / |g| < 1 := by
      rw [div_lt_iff₀ hgpos]
      simpa using h
    unfold clipGradient
    rw [min_eq_right (le_of_lt hlt)]
    have hval : g * (C / |g|) - g = g * ((C - |g|) / |g|) := by
      field_simp [ne_of_gt hgpos]
      ring
    rw [hval, abs_mul]
    have hCmg : C - |g| < 0 := by linarith
    have hratio : abs ((C - |g|) / |g|) = (|g| - C) / |g| := by
      rw [abs_div, abs_of_neg hCmg, abs_of_pos hgpos]
      ring
    rw [hratio]
    have hsimp : |g| * ((|g| - C) / |g|) = |g| - C := by
      field_simp [ne_of_gt hgpos]
    rw [hsimp]
    exact le_max_right 0 (|g| - C)

/-! ## 二、期望形式的裁剪偏差界与 Markov 不等式 -/

/-- 有限概率空间上的事件概率：`P(A) = E[1_A]`。 -/
def ProbOf {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] : ℝ :=
  Expect p (fun ω => if P ω then 1 else 0)

/-- **期望裁剪偏差界**：`|E[clip g] − E[g]| ≤ E[max(0, ‖g‖ − C)]`（`p ≥ 0`）。 -/
theorem clip_bias_expectation_bound {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (C : ℝ)
    (g : Ω → ℝ) (hC : 0 ≤ C) (hp0 : ∀ ω, 0 ≤ p ω) :
    |Expect p (fun ω => clipGradient C (g ω)) - Expect p g| ≤
      Expect p (fun ω => max 0 (|g ω| - C)) := by
  rw [← Expect_sub]
  calc
    |Expect p (fun ω => clipGradient C (g ω) - g ω)|
        ≤ ∑ ω, |p ω * (clipGradient C (g ω) - g ω)| := by
          unfold Expect
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, p ω * |clipGradient C (g ω) - g ω| :=
          Finset.sum_congr rfl (fun ω _ => by rw [abs_mul, abs_of_nonneg (hp0 ω)])
    _ ≤ ∑ ω, p ω * max 0 (|g ω| - C) :=
          Finset.sum_le_sum (fun ω _ =>
            mul_le_mul_of_nonneg_left (clip_bias_bound C (g ω) hC) (hp0 ω))
    _ = Expect p (fun ω => max 0 (|g ω| - C)) := rfl

/-- **Markov 不等式**：`C·P(‖g‖ > C) ≤ E‖g‖`（`C ≥ 0`，`p ≥ 0`）。 -/
theorem markov_inequality {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (g : Ω → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hp0 : ∀ ω, 0 ≤ p ω) :
    C * ProbOf p (fun ω => C < |g ω|) ≤ Expect p (fun ω => |g ω|) := by
  unfold ProbOf Expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  dsimp only
  split_ifs with h
  · have h1 : C * p ω ≤ |g ω| * p ω := mul_le_mul_of_nonneg_right (le_of_lt h) (hp0 ω)
    nlinarith [h1]
  · ring_nf
    exact mul_nonneg (hp0 ω) (abs_nonneg _)

/-! ## 三、噪声项：幅度与方差 -/

/-- 噪声幅度界 `σ·C`（高斯机制尺度）。 -/
def noiseBound (σ C : ℝ) : ℝ := σ * C

/-- 高斯机制噪声方差 `σ²·C²`（对应 `N(0, σ²C²)`）。 -/
def noiseVariance (σ C : ℝ) : ℝ := σ ^ 2 * C ^ 2

lemma noiseVariance_eq (σ C : ℝ) : noiseVariance σ C = σ ^ 2 * C ^ 2 := rfl

/-- 隐私代理：`1/σ`（越大越隐私）。这是**粗糙的单调代理**，不是 (ε,δ)-DP 的 ε。 -/
def privacyProxy (σ : ℝ) : ℝ := 1 / σ

/-- DP-SGD 的带噪方向：`clip g + ξ`。 -/
def dpsgdDirection (C σ : ℝ) (g ξ : ℝ) : ℝ := clipGradient C g + ξ

/-- **带噪方向的范数界**：`‖clip g + ξ‖ ≤ C(1 + σ)`（`‖ξ‖ ≤ σC`）。 -/
theorem dpsgd_direction_bound (C σ g ξ : ℝ) (hC : 0 ≤ C) (_hσ : 0 ≤ σ)
    (hξ : |ξ| ≤ noiseBound σ C) :
    |dpsgdDirection C σ g ξ| ≤ C * (1 + σ) := by
  unfold dpsgdDirection noiseBound at *
  calc
    |clipGradient C g + ξ| ≤ |clipGradient C g| + |ξ| := abs_add _ _
    _ ≤ C + σ * C := add_le_add (clip_norm_le C g hC) hξ
    _ = C * (1 + σ) := by ring

/-! ## 四、效用界：速率常数随噪声线性退化 -/

/-- **DP-SGD 效用界**：把带噪方向当作范数 ≤ `C(1+σ)` 的次梯度选择 `d`，则
    `∃ t < T, f(x_t) − f x* ≤ (‖x_0 − x*‖² + η²T·(C(1+σ))²)/(2ηT)`。 -/
theorem dpsgd_utility_bound {f d : ℝ → ℝ} (C σ η x0 xstar : ℝ) (T : ℕ)
    (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hη : 0 < η) (hT : 0 < T)
    (hsub : ∀ x : ℝ, Subgradient f x (d x))
    (hbound : ∀ x : ℝ, |d x| ≤ C * (1 + σ)) :
    ∃ t : ℕ, t < T ∧ SubgradientGap f d η x0 xstar t ≤
      (‖x0 - xstar‖ ^ 2 + η ^ 2 * (T : ℝ) * (C * (1 + σ)) ^ 2) / (2 * η * (T : ℝ)) := by
  have hG0 : 0 ≤ C * (1 + σ) := mul_nonneg hC (by linarith)
  exact subgradient_descent_min_gap f d η x0 xstar (C * (1 + σ)) T hsub hη hG0
    (fun x => by rw [Real.norm_eq_abs]; exact hbound x) hT

/-- **DP-SGD 的最优步长 O(D·C(1+σ)/√T) 率**：噪声 σ 越大，速率常数越大（效用越差）。 -/
theorem dpsgd_rate_optimal {f d : ℝ → ℝ} (C σ x0 xstar : ℝ) (T : ℕ)
    (_hC : 0 ≤ C) (_hσ : 0 ≤ σ) (hT : 0 < T)
    (hG : 0 < C * (1 + σ)) (hD : 0 < ‖x0 - xstar‖)
    (hsub : ∀ x : ℝ, Subgradient f x (d x))
    (hbound : ∀ x : ℝ, |d x| ≤ C * (1 + σ)) :
    ∃ t : ℕ, t < T ∧
      SubgradientGap f d (‖x0 - xstar‖ / (C * (1 + σ) * Real.sqrt (T : ℝ))) x0 xstar t ≤
        ‖x0 - xstar‖ * (C * (1 + σ)) / Real.sqrt (T : ℝ) :=
  subgradient_descent_rate_bound f d x0 xstar (C * (1 + σ)) T hsub hG hT hD
    (fun x => by rw [Real.norm_eq_abs]; exact hbound x)

/-! ## 五、隐私-效用权衡（单调性） -/

/-- **效用随噪声单调变差**：`σ1 ≤ σ2 ⟹ C(1+σ1) ≤ C(1+σ2)`。 -/
theorem privacy_utility_tradeoff (C σ1 σ2 : ℝ) (hC : 0 ≤ C) (hσ : σ1 ≤ σ2) :
    C * (1 + σ1) ≤ C * (1 + σ2) := by
  have h : 1 + σ1 ≤ 1 + σ2 := by linarith
  exact mul_le_mul_of_nonneg_left h hC

/-- **隐私代理随噪声单调变好**：`0 < σ1 ≤ σ2 ⟹ 1/σ2 ≤ 1/σ1`。 -/
theorem privacy_proxy_antitone (σ1 σ2 : ℝ) (hσ1 : 0 < σ1) (hσ : σ1 ≤ σ2) :
    privacyProxy σ2 ≤ privacyProxy σ1 := by
  unfold privacyProxy
  exact one_div_le_one_div_of_le hσ1 hσ

/-! ## 注：闭环语义
  裁剪算子（clipGradient）→ 范数界/不裁剪条件/偏差界（clip_norm_le /
  clipGradient_of_le / clip_bias_bound / clip_bias_expectation_bound）→
  Markov 控制大梯度概率（markov_inequality）→
  噪声幅度与方差（noiseBound / noiseVariance）→ 带噪方向范数界（dpsgd_direction_bound）→
  效用界 O(D·C(1+σ)/√T)（最优步长，`dpsgd_rate_optimal`；其一般η形式见 `dpsgd_utility_bound`）→
  隐私-效用单调权衡（privacy_utility_tradeoff / privacy_proxy_antitone）。
  诚实标注：(ε,δ)-DP 的隐私保证本身**未形式化**；带噪方向作次梯度的假设显式给出。 -/

end Lattice