import Mathlib

/-!
# LATTICE: 感知机收敛定理（Novikoff）—— 线性可分数据的有限步收敛

训练线基础算法：经典感知机（Perceptron）在**线性可分 + 有界数据**下
的收敛保证。权重更新 w ← w + y·x 仅在误分类样本 (x, y) 上发生
（y·⟨w, x⟩ ≤ 0）。存在单位法向量 w\*（间隔 γ > 0：∀t, γ ≤ y_t·⟨x_t, w\*⟩）
且数据有界（‖x_t‖ ≤ R）时，误分类（更新）次数 ≤ R²/γ²。

证明按 Novikoff 的两条线（对更新次数 T 归纳）：

1. **增长界**（‖w_T‖² ≤ T·R²）：
   单步 ‖w + y·x‖² = ‖w‖² + 2y⟨w,x⟩ + ‖y·x‖² ≤ ‖w‖² + R²，
   其中 2y⟨w,x⟩ ≤ 0（误分类）且 ‖y·x‖ ≤ ‖x‖ ≤ R（标签范数 ≤ 1）。

2. **间隔界**（T·γ ≤ ⟨w_T, w\*⟩）：
   单步 ⟨w + y·x, w\*⟩ = ⟨w, w\*⟩ + y⟨x, w\*⟩ ≥ ⟨w, w\*⟩ + γ（间隔假设）。

3. **合流**（T ≤ R²/γ²）：
   T·γ ≤ ⟨w_T, w\*⟩ ≤ ‖w_T‖·‖w\*‖ = ‖w_T‖（Cauchy-Schwarz + ‖w\*‖ = 1），
   平方并与增长界合并：(Tγ)² ≤ ‖w_T‖² ≤ T·R²，T > 0 时除以 T·γ² 得
   T ≤ R²/γ²。

**诚实边界**（与经典陈述的差异，全部显式假设化）：
- 标签 y_t ∈ {−1, +1} 放宽为范数假设 ‖y_t‖ ≤ 1（ℝ 上即 |y_t| ≤ 1），
  增长界只需 ‖y·x‖ ≤ ‖x‖，无需 y² = 1；
- 更新序列以函数 ws : ℕ → E 与每步假设给出（∀t 形式），
  结论 ∀ T : ℕ, (T : ℝ) ≤ R²/γ² 说明：在**每步都是误分类步**的
  序列假设下，步数被 R²/γ² 界住，故这样的序列不可能无限延伸；
- `hstep`（每步都做更新）与 `hmiss`（每步都误分类）联立意味着
  序列每步都更新；本文件未建模「仅在误分类时才更新」的跳过步，
  故上述界直接刻画的是「每步皆误分类」的假设序列，而非真实运行
  中实际发生的误分类计数；
- 最终界为 ℝ 上界（未做 ⌊R²/γ²⌋ 整数地板化——地板化需要额外
  的 floor/ceil 论证，不影响收敛性结论）；
- 模型无关：任意 ℝ 内积空间 E（如 ι → ℝ 带欧氏内积）。

本文件不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## 单步更新
权重更新 w' = w + y·x（在误分类样本 (x, y) 上）。-/

def perceptronStep (w : E) (y : ℝ) (x : E) : E := w + y • x

/-! ## 定理一（增长界，单步）
误分类（y·⟨w, x⟩ ≤ 0）、标签范数 ‖y‖ ≤ 1、数据界 ‖x‖ ≤ R
⟹ ‖w + y·x‖² ≤ ‖w‖² + R²。

展开 ‖w + yx‖² = ‖w‖² + ‖yx‖² + 2·re⟨w, yx⟩：
  2·re⟨w, yx⟩ = 2y⟨w,x⟩ ≤ 0（误分类）；
  ‖yx‖ ≤ ‖y‖·‖x‖ ≤ ‖x‖ ≤ R ⟹ ‖yx‖² ≤ R²。-/

theorem perceptron_growth {w x : E} {y : ℝ} {R : ℝ}
    (hmiss : y * inner w x ≤ 0)
    (hy : ‖y‖ ≤ 1)
    (hx : ‖x‖ ≤ R) :
    ‖w + y • x‖ ^ 2 ≤ ‖w‖ ^ 2 + R ^ 2 := by
  have hR : 0 ≤ R := le_trans (norm_nonneg x) hx
  have hyx : ‖y • x‖ ≤ R := by
    calc
      ‖y • x‖ = ‖y‖ * ‖x‖ := norm_smul y x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hy (norm_nonneg x)
      _ = ‖x‖ := by ring
      _ ≤ R := hx
  have hyx2 : ‖y • x‖ ^ 2 ≤ R ^ 2 := by nlinarith [hyx, norm_nonneg (y • x), hR]
  have hcross : 2 * RCLike.re (inner w (y • x) : ℝ) ≤ 0 := by
    rw [inner_smul_right]
    simp
    nlinarith [hmiss]
  calc
    ‖w + y • x‖ ^ 2 = ‖w‖ ^ 2 + 2 * RCLike.re (inner w (y • x) : ℝ) + ‖y • x‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℝ)]
    _ ≤ ‖w‖ ^ 2 + R ^ 2 := by nlinarith [hyx2, hcross]

/-! ## 定理二（增长界，迭代）
w₀ = 0、每步为误分类更新（‖y_t‖ ≤ 1、‖x_t‖ ≤ R）
⟹ T 次更新后 ‖w_T‖² ≤ T·R²。-/

theorem perceptron_growth_iter {ws xs : ℕ → E} {ys : ℕ → ℝ} {R : ℝ}
    (hw0 : ws 0 = 0)
    (hstep : ∀ t : ℕ, ws (t + 1) = perceptronStep (ws t) (ys t) (xs t))
    (hmiss : ∀ t : ℕ, ys t * inner (ws t) (xs t) ≤ 0)
    (hy : ∀ t : ℕ, ‖ys t‖ ≤ 1)
    (hx : ∀ t : ℕ, ‖xs t‖ ≤ R) :
    ∀ T : ℕ, ‖ws T‖ ^ 2 ≤ (T : ℝ) * R ^ 2 := by
  intro T
  -- 先证带初始范数的一般形式，再代入 w₀ = 0
  have hbase : ∀ T : ℕ, ‖ws T‖ ^ 2 ≤ ‖ws 0‖ ^ 2 + (T : ℝ) * R ^ 2 := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        have h1 : ‖ws (T + 1)‖ ^ 2 ≤ ‖ws T‖ ^ 2 + R ^ 2 := by
          rw [hstep T]
          exact perceptron_growth (hmiss T) (hy T) (hx T)
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith
  have h00 : ‖ws 0‖ ^ 2 = 0 := by simp [hw0]
  simpa [h00] using hbase T

/-! ## 定理三（间隔界，单步）
间隔假设 γ ≤ y·⟨x, w\*⟩ ⟹ ⟨w + y·x, w\*⟩ ≥ ⟨w, w\*⟩ + γ。

展开 ⟨w + yx, w\*⟩ = ⟨w, w\*⟩ + y⟨x, w\*⟩（ℝ 上无共轭）。-/

theorem perceptron_progress {w x wstar : E} {y γ : ℝ}
    (hmargin : γ ≤ y * inner x wstar) :
    (inner w wstar : ℝ) + γ ≤ (inner (perceptronStep w y x) wstar : ℝ) := by
  unfold perceptronStep
  calc
    (inner w wstar : ℝ) + γ ≤ (inner w wstar : ℝ) + y * inner x wstar :=
      add_le_add_left hmargin (inner w wstar : ℝ)
    _ = (inner (w + y • x) wstar : ℝ) := by
      rw [inner_add_left, inner_smul_left]
      simp

/-! ## 定理四（间隔界，迭代）
w₀ = 0、每步满足间隔假设 ⟹ T 次更新后 T·γ ≤ ⟨w_T, w\*⟩。-/

theorem perceptron_progress_iter {ws xs : ℕ → E} {ys : ℕ → ℝ} {wstar : E} {γ : ℝ}
    (hw0 : ws 0 = 0)
    (hstep : ∀ t : ℕ, ws (t + 1) = perceptronStep (ws t) (ys t) (xs t))
    (hmargin : ∀ t : ℕ, γ ≤ ys t * inner (xs t) wstar) :
    ∀ T : ℕ, (T : ℝ) * γ ≤ (inner (ws T) wstar : ℝ) := by
  intro T
  -- 先证带 ⟨w₀, w\*⟩ 的一般形式，再代入 w₀ = 0
  have hiter : ∀ T : ℕ, (inner (ws 0) wstar : ℝ) + (T : ℝ) * γ ≤ (inner (ws T) wstar : ℝ) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
        have h1 : (inner (ws T) wstar : ℝ) + γ ≤ (inner (ws (T + 1)) wstar : ℝ) := by
          rw [hstep T]
          exact perceptron_progress (hmargin T)
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith
  have h0 : (inner (ws 0) wstar : ℝ) = 0 := by simp [hw0]
  simpa [h0] using hiter T

/-! ## 定理五（合流，平方形式）
增长界 + 间隔界 + Cauchy-Schwarz + ‖w\*‖ = 1
⟹ (T·γ)² ≤ T·R²。

  T·γ ≤ ⟨w_T, w\*⟩ ≤ ‖w_T‖·‖w\*‖ = ‖w_T‖，平方（两边非负）
  并与增长界 ‖w_T‖² ≤ T·R² 合并。-/

theorem perceptron_bound {ws xs : ℕ → E} {ys : ℕ → ℝ} {wstar : E} {R γ : ℝ}
    (hw0 : ws 0 = 0)
    (hstep : ∀ t : ℕ, ws (t + 1) = perceptronStep (ws t) (ys t) (xs t))
    (hmiss : ∀ t : ℕ, ys t * inner (ws t) (xs t) ≤ 0)
    (hy : ∀ t : ℕ, ‖ys t‖ ≤ 1)
    (hx : ∀ t : ℕ, ‖xs t‖ ≤ R)
    (hmargin : ∀ t : ℕ, γ ≤ ys t * inner (xs t) wstar)
    (hnorm : ‖wstar‖ = 1)
    (hγ : 0 ≤ γ) :
    ∀ T : ℕ, ((T : ℝ) * γ) ^ 2 ≤ (T : ℝ) * R ^ 2 := by
  intro T
  have hprogress : (T : ℝ) * γ ≤ (inner (ws T) wstar : ℝ) :=
    perceptron_progress_iter hw0 hstep hmargin T
  -- Cauchy-Schwarz：⟨w_T, w\*⟩ ≤ ‖w_T‖·‖w\*‖
  have hcs0 : (inner (ws T) wstar : ℝ) ≤ ‖ws T‖ * ‖wstar‖ :=
    le_trans (le_abs_self (inner (ws T) wstar : ℝ)) (abs_real_inner_le_norm (ws T) wstar)
  have hTγ_nonneg : 0 ≤ (T : ℝ) * γ := mul_nonneg (Nat.cast_nonneg T) hγ
  have hTγ_le : (T : ℝ) * γ ≤ ‖ws T‖ := le_trans hprogress (by simpa [hnorm] using hcs0)
  -- 平方（两边非负）：(T·γ)² ≤ ‖w_T‖²
  have hsq1 : ((T : ℝ) * γ) ^ 2 ≤ ‖ws T‖ ^ 2 := pow_le_pow_left₀ hTγ_nonneg hTγ_le 2
  -- 增长界：‖w_T‖² ≤ T·R²
  have hgrowth : ‖ws T‖ ^ 2 ≤ (T : ℝ) * R ^ 2 :=
    perceptron_growth_iter hw0 hstep hmiss hy hx T
  exact le_trans hsq1 hgrowth

/-! ## 定理六（感知机收敛，主定理）
存在单位法向量 w\*、间隔 γ > 0、数据界 R、标签范数 ≤ 1、且更新序列
每步都是误分类步时，任意步数 T 满足 T ≤ R²/γ²。

  (Tγ)² ≤ T·R² 且 T > 0 时两边除以 T：T·γ² ≤ R²，
  再除以 γ² > 0：T ≤ R²/γ²。T = 0 时平凡（R²/γ² ≥ 0）。

推论（收敛）：在「每步都是误分类步」的假设下，这样的更新序列只能
执行有限多步——若它无限延伸，取充分大的 T 将违反 T ≤ R²/γ²；
本文件未建模「仅在误分类时更新」的跳过步，故该推论刻画的是
假设序列而非真实运行中的更新计数。-/

theorem perceptron_converges {ws xs : ℕ → E} {ys : ℕ → ℝ} {wstar : E} {R γ : ℝ}
    (hw0 : ws 0 = 0)
    (hstep : ∀ t : ℕ, ws (t + 1) = perceptronStep (ws t) (ys t) (xs t))
    (hmiss : ∀ t : ℕ, ys t * inner (ws t) (xs t) ≤ 0)
    (hy : ∀ t : ℕ, ‖ys t‖ ≤ 1)
    (hx : ∀ t : ℕ, ‖xs t‖ ≤ R)
    (hmargin : ∀ t : ℕ, γ ≤ ys t * inner (xs t) wstar)
    (hnorm : ‖wstar‖ = 1)
    (hγ : 0 < γ) :
    ∀ T : ℕ, (T : ℝ) ≤ R ^ 2 / γ ^ 2 := by
  intro T
  by_cases hT : T = 0
  · subst T
    simp
    exact div_nonneg (sq_nonneg R) (sq_pos_of_pos hγ).le
  · have hTpos : 0 < (T : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hT)
    -- 合流平方形式：(Tγ)² ≤ T·R²
    have hsq2 : ((T : ℝ) * γ) ^ 2 ≤ (T : ℝ) * R ^ 2 :=
      perceptron_bound hw0 hstep hmiss hy hx hmargin hnorm (le_of_lt hγ) T
    have hγ2pos : 0 < γ ^ 2 := sq_pos_of_pos hγ
    -- (Tγ)² = T²γ² = T·(T·γ²)，除以 T（>0）：T·γ² ≤ R²
    have hsq2' : (T : ℝ) * γ ^ 2 ≤ R ^ 2 := by
      have hsq2a : (T : ℝ) ^ 2 * γ ^ 2 ≤ (T : ℝ) * R ^ 2 := by nlinarith
      have hdividend : (T : ℝ) * ((T : ℝ) * γ ^ 2) ≤ (T : ℝ) * R ^ 2 := by nlinarith
      exact le_of_mul_le_mul_left hdividend hTpos
    -- T ≤ R²/γ² ⟺ T·γ² ≤ R²（γ² > 0）
    exact (le_div_iff₀ hγ2pos).mpr hsq2'

end Lattice
