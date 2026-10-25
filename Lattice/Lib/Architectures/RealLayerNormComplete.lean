import Mathlib
import Lattice.Lib.Architectures.RealLayerNorm
import Lattice.Lib.Architectures.RealRMSNorm
import Lattice.Lib.Architectures.RealNormFamily
/-!
# LATTICE: LayerNorm 完整理论 —— 平移不变、仿射复合、与 RMSNorm 的代数关系、幂等性

RealLayerNorm 已证 LayerNorm 的**缩放不变性**（normalize(α·x) = normalize x，α > 0）。
本文件补全 LayerNorm 的完整不变量刻画（模型无关，任意有限指标集 ι）：

  1. **平移不变性**： LN(x + c·1) = LN(x)
     （mean(x + c·1) = mean x + c 需要 card ι ≠ 0；center 消去常数 ⟹ 归一化不变）。
     与缩放不变配套：LayerNorm 在「正相似变换」x ↦ α·x + c·1（α > 0）下完全不变。
  2. **仿射复合**： LayerNorm 与逐元素仿射 γ⊙(·)+β 的复合
     · 固定 γ/β 时仍保平移/缩放不变（仿射项不变）；
     · 两个逐元素仿射的复合仍是逐元素仿射（参数 γ₂γ₁ / γ₂β₁+β₂）。
  3. **与 RMSNorm 的代数关系**（ln_rms_relation）：
       normalize x = RMSNorm(center x) / √n
     （center 去掉均值，RMSNorm 再做无中心化的单位化；√n 来自 centerSq 与均值平方和的换算）。
  4. **幂等性与超平面刻画**（诚实版本）：
     · 零均值超平面上、且 centerSq = 1 的向量是 LN 的不动点（单位球面上的恒等）；
     · LN 幂等：normalize(normalize x) = normalize x；
     · LN **不是单射**（normalize_not_injective：常数 1 与 0 同像），故不是双射；
       结合缩放不变，LN 在零均值超平面上收缩到单位球，而非等距/双射。

诚实标注：LN 在超平面上是「径向塌缩到单位球」，不是等距/双射；本文件证明其
真正成立的对偶事实（幂等 + 球面恒等 + 非单射）。

全部定理真实可证，无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 平移（加常向量）的线性 -/

/-- 均值对加常向量平移：mean(x + c·1) = mean x + c（需 card ι ≠ 0）。 -/
lemma mean_add_const (x : ι → ℝ) (c : ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    mean (fun i => x i + c) = mean x + c := by
  unfold mean
  have hsum : ∑ i, (x i + c) = (∑ i, x i) + (Fintype.card ι : ℝ) * c := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum, add_div, mul_div_cancel_left₀ c hι]

/-- 中心化对平移不变：center(x + c·1) = center x（需 card ι ≠ 0）。 -/
lemma center_add_const (x : ι → ℝ) (c : ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    center (fun i => x i + c) = center x := by
  funext i
  unfold center
  rw [mean_add_const x c hι]
  ring

/-- 中心平方和对平移不变（需 card ι ≠ 0）。 -/
lemma centerSq_add_const (x : ι → ℝ) (c : ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    centerSq (fun i => x i + c) = centerSq x := by
  unfold centerSq
  rw [center_add_const x c hι]

/-! ## 定理一：LayerNorm 平移不变性（与缩放不变配套的完整刻画） -/

/-- LN(x + c·1) = LN(x)：LayerNorm 对输入整体平移不敏感（需 card ι ≠ 0）。 -/
theorem normalize_translation_invariant (x : ι → ℝ) (c : ℝ)
    (hι : (Fintype.card ι : ℝ) ≠ 0) :
    normalize (fun i => x i + c) = normalize x := by
  funext i
  unfold normalize
  rw [center_add_const x c hι, centerSq_add_const x c hι]

/-- 命名别名：LayerNorm 的平移不变性。 -/
theorem layernorm_translation_invariant (x : ι → ℝ) (c : ℝ)
    (hι : (Fintype.card ι : ℝ) ≠ 0) :
    normalize (fun i => x i + c) = normalize x :=
  normalize_translation_invariant x c hι

/-! ## 逐元素仿射 γ⊙(·)+β 与 LayerNorm 的复合 -/

/-- 逐元素仿射：y ↦ γ ⊙ y + β。 -/
def elementwiseAffine (γ β : ι → ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun i => γ i * y i + β i

/-- 带仿射的 LayerNorm：LN_{γ,β}(x) = γ ⊙ normalize(x) + β。 -/
def lnAffine (γ β x : ι → ℝ) : ι → ℝ :=
  elementwiseAffine γ β (normalize x)

omit [Fintype ι] in
/-- 逐元素仿射复合仍是逐元素仿射（参数 γ₂γ₁ / γ₂β₁ + β₂）。 -/
theorem elementwiseAffine_comp (γ₁ β₁ γ₂ β₂ : ι → ℝ) :
    elementwiseAffine γ₂ β₂ ∘ elementwiseAffine γ₁ β₁
      = elementwiseAffine (fun i => γ₂ i * γ₁ i) (fun i => γ₂ i * β₁ i + β₂ i) := by
  funext y i
  simp only [Function.comp_apply, elementwiseAffine]
  ring

/-- 带仿射 LayerNorm 的缩放不变性（α > 0，仿射项不变）。 -/
theorem lnAffine_scale_invariant (γ β x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    lnAffine γ β (fun i => α * x i) = lnAffine γ β x := by
  unfold lnAffine elementwiseAffine
  rw [normalize_scale_invariant x α hα]

/-- 带仿射 LayerNorm 的平移不变性（card ι ≠ 0，仿射项不变）。 -/
theorem lnAffine_translation_invariant (γ β x : ι → ℝ) (c : ℝ)
    (hι : (Fintype.card ι : ℝ) ≠ 0) :
    lnAffine γ β (fun i => x i + c) = lnAffine γ β x := by
  unfold lnAffine elementwiseAffine
  rw [normalize_translation_invariant x c hι]

/-! ## 中心化的均值与补充引理 -/

/-- center 的均值为零：mean(center x) = 0（需 card ι ≠ 0）。 -/
lemma mean_center (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    mean (center x) = 0 := by
  have hsum : ∑ i, center x i = 0 := by
    unfold center
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold mean
    field_simp [hι]
  unfold mean
  rw [hsum, zero_div]

/-- center 幂等：center(center x) = center x（需 card ι ≠ 0）。 -/
lemma center_center (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    center (center x) = center x := by
  have h := mean_center x hι
  funext i
  show center x i - mean (center x) = center x i
  rw [h, sub_zero]

/-- 中心平方和非负。 -/
lemma centerSq_nonneg (x : ι → ℝ) : 0 ≤ centerSq x := by
  unfold centerSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-! ## 定理二：LN 与 RMSNorm 的代数关系 -/

/-- LN(x) = RMSNorm(center x) / √n：
    归一化 = 先中心化、再做 RMSNorm，最后除以 √n（card ι ≠ 0）。 -/
theorem ln_rms_relation (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    normalize x = fun i => rmsNorm (center x) i / Real.sqrt (Fintype.card ι : ℝ) := by
  have hpos : 0 < (Fintype.card ι : ℝ) := by
    have h0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    exact lt_of_le_of_ne h0 (Ne.symm hι)
  have hden : Real.sqrt (centerSq x)
      = Real.sqrt (Fintype.card ι : ℝ) * rms (center x) := by
    have hsplit : centerSq x
        = (Fintype.card ι : ℝ) * ((∑ i, (center x i) ^ 2) / (Fintype.card ι : ℝ)) := by
      unfold centerSq
      field_simp [hι]
    rw [hsplit, Real.sqrt_mul (le_of_lt hpos)]
    rfl
  funext i
  unfold normalize rmsNorm
  rw [hden, div_div, mul_comm]

/-! ## 定理三：幂等性与零均值超平面刻画 -/

/-- LN 输出的均值为零（card ι ≠ 0）。 -/
lemma normalize_mean_zero (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    mean (normalize x) = 0 := by
  have hfun : normalize x = fun i => (1 / Real.sqrt (centerSq x)) * center x i := by
    funext i
    unfold normalize
    ring
  rw [hfun, mean_scale, mean_center x hι, mul_zero]

/-- 非退化输入上 LN 输出的中心平方和为 1（centerSq x ≠ 0）。 -/
lemma normalize_centerSq_eq_one (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0)
    (hx : centerSq x ≠ 0) :
    centerSq (normalize x) = 1 := by
  have hmean := normalize_mean_zero x hι
  have hctr : center (normalize x) = normalize x := by
    funext i
    show normalize x i - mean (normalize x) = normalize x i
    rw [hmean, sub_zero]
  have hcs : 0 ≤ centerSq x := centerSq_nonneg x
  have hs2 : Real.sqrt (centerSq x) ^ 2 = centerSq x := Real.sq_sqrt hcs
  have hfun : normalize x = fun i => center x i / Real.sqrt (centerSq x) := rfl
  calc
    centerSq (normalize x) = ∑ i, (center x i / Real.sqrt (centerSq x)) ^ 2 := by
      rw [centerSq, hctr, hfun]
    _ = ∑ i, (center x i) ^ 2 / (Real.sqrt (centerSq x)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [div_pow]
    _ = (∑ i, (center x i) ^ 2) / (Real.sqrt (centerSq x)) ^ 2 := by
          rw [Finset.sum_div]
    _ = centerSq x / centerSq x := by rw [hs2]; rfl
    _ = 1 := div_self hx

/-- 零均值、单位中心平方和的向量是 LN 的不动点（单位球面上的恒等）。 -/
theorem normalize_id_on_unit_sphere (x : ι → ℝ) (hmean : mean x = 0)
    (hcs : centerSq x = 1) :
    normalize x = x := by
  have hc : center x = x := by
    funext j
    unfold center
    rw [hmean, sub_zero]
  funext i
  unfold normalize
  rw [hc, hcs, Real.sqrt_one, div_one]

/-- LayerNorm 幂等：normalize(normalize x) = normalize x（card ι ≠ 0）。 -/
theorem normalize_idempotent (x : ι → ℝ) (hι : (Fintype.card ι : ℝ) ≠ 0) :
    normalize (normalize x) = normalize x := by
  by_cases hs : Real.sqrt (centerSq x) = 0
  · -- 退化：normalize x = 0，两侧都为零向量
    have hzero : normalize x = 0 := by
      funext i
      simp [normalize, hs]
    rw [hzero]
    have hc0 : center (0 : ι → ℝ) = 0 := by
      funext i
      unfold center
      simp [mean]
    have hcs0 : centerSq (0 : ι → ℝ) = 0 := by
      unfold centerSq
      rw [hc0]
      simp
    funext i
    simp [normalize, hc0, hcs0]
  · -- 非退化：mean = 0 且 centerSq = 1
    have hx : centerSq x ≠ 0 := by
      intro hz
      exact hs (by rw [hz, Real.sqrt_zero])
    have hmean : mean (normalize x) = 0 := normalize_mean_zero x hι
    have hcs1 : centerSq (normalize x) = 1 := normalize_centerSq_eq_one x hι hx
    funext i
    show center (normalize x) i / Real.sqrt (centerSq (normalize x)) = normalize x i
    rw [hcs1, Real.sqrt_one, div_one]
    show normalize x i - mean (normalize x) = normalize x i
    rw [hmean, sub_zero]

/-- LN 在零均值超平面上**不是双射**（缩放不变 ⟹ 非单射）：
    常数向量 1 与 0 都映到 0。 -/
theorem normalize_not_injective [Nonempty ι] :
    ¬ Function.Injective (normalize : (ι → ℝ) → (ι → ℝ)) := by
  intro hinj
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
    exact_mod_cast ne_of_gt hpos
  have hcenter_one : center (fun _ : ι => (1 : ℝ)) = 0 := by
    funext j
    unfold center mean
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard]
  have h1 : normalize (fun _ : ι => (1 : ℝ)) = 0 := by
    funext i
    simp [normalize, centerSq, hcenter_one]
  have h0 : normalize (fun _ : ι => (0 : ℝ)) = 0 := by
    funext i
    simp [normalize, centerSq, center, mean]
  have heq : normalize (fun _ : ι => (1 : ℝ)) = normalize (fun _ : ι => (0 : ℝ)) := by
    rw [h1, h0]
  have hneq : (fun _ : ι => (1 : ℝ)) ≠ (fun _ : ι => (0 : ℝ)) := by
    intro h
    have := congrFun h (Classical.arbitrary ι)
    norm_num at this
  exact hneq (hinj heq)

end Lattice
