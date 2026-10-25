import Mathlib
import Lattice.Lib.Concentration.RealHoeffdingMeasure
/-!
# LATTICE: 一般测度论 Hoeffding 引理 —— 有界零均值变量的 MGF 界

`RealHoeffdingMeasure` 把「逐坐标 MGF 界 ⟹ 和的指数尾界」完整证了出来，但**明确
把 Hoeffding 引理本身留作外部输入**（该文件 docstring 第 50–58 行：「逐坐标
『有界 + 均值为零 ⟹ mgf ≤ exp(t²cᵢ²/2)』这一 Hoeffding 引理，在一般测度论情形下
本文件未重证」）。本文件**补上这个缺口**，给出该引理的一般测度论证明：

  1. `convexOn_exp_mul`（**凸性基座**）：`x ↦ e^{tx}` 在 `ℝ` 上凸
     （`Real.convexOn_exp` 与线性映射 `x ↦ t·x` 的复合；`t = 0` 时退化为常值 1）。
  2. `chord_hull`（**弦不等式，一般区间**）：`a < b`、`x ∈ [a,b]` ⟹
     `e^{tx} ≤ ((b−x)/(b−a))·e^{ta} + ((x−a)/(b−a))·e^{tb}`
     （**对任意 `t : ℝ` 成立**，无需 `t > 0`）。
     证明：把 `x` 写成端点凸组合 `((b−x)/(b−a)) • a + ((x−a)/(b−a)) • b`，
     直接代入 `ConvexOn` 定义（`ℝ` 上 `•` 即 `*`）。
  3. `chord_hull_abs`（**对称弦界，cosh/sinh 形式**）：`|y| ≤ c`、`c > 0` ⟹
     `e^{ty} ≤ cosh(tc) + (y/c)·sinh(tc)`。
     证明：定理 2 取 `a = −c`、`b = c`，再用 `Real.cosh_eq`/`Real.sinh_eq` 整理。
     这个形式的关键好处：`y` 只以一次项出现，取期望后被 `E[Y] = 0` 直接消掉。
  4. `hoeffding_lemma_measure`（**主交付：一般测度论 Hoeffding 引理**）：
     `[IsProbabilityMeasure μ]`、`|X| ≤ c` a.e.、`μ[X] = 0`、`c > 0` ⟹
     `mgf X μ t ≤ exp(t²c²/2)`（**对任意 `t : ℝ`**）。
     证明：`mgf X μ t = ∫ e^{tX}` → 逐点弦界（定理 3）→ `integral_mono_ae`
     取期望 → 用零均值消去 `sinh` 项 → 得 `mgf ≤ cosh(tc)` →
     `Real.cosh_le_exp_half_sq : cosh u ≤ e^{u²/2}` 收尾。
  5. `hoeffding_lemma_measure_symmetric`：定理 4 的同义显式入口。
  6. `hoeffding_lemma_measure_interval`（**任意区间 `[a,b]` 形式，半径版**）：
     `0 ≤ b`、`a < b`、`a ≤ X ≤ b` a.e.、`μ[X] = 0` ⟹
     `mgf X μ t ≤ exp(t²R²/2)`，其中 `R = max b (−a)` 是事实上界半径
     （由 `a ≤ X ≤ b` 直接得 `−R ≤ a ≤ X ≤ b ≤ R`）。
  7. `hoeffding_lemma_measure_symmetric_interval`（**对称区间推论**）：`[−b,b]`
     （`b > 0`）时 `R = b = (b−a)/2`，退化为标准常数 `exp(t²(b−a)²/8)`。
  8. `hoeffding_lemma_measure_centered`（**非零均值复用**）：把
     「`a ≤ X ≤ b`、`μ[X] = m`」归约为中心化变量 `X − m` 的零均值形式。

**与既有文件的分工（重要）**：
- `RealHoeffding.hoeffding_lemma` 是**有限计数概率空间**版本（`Finset` 求和），
  本文件是**一般测度论**版本（`∫` 与 `Measure`），二者互补；
- `RealAzumaMartingale.condExpFiber_hoeffding` 是**有限纤维条件期望**版本
  （单步鞅差），本文件给出其**无条件测度论对应物**；
- 本文件的输出形式正好喂给 `RealHoeffdingMeasure` 的 `hcoord` 假设，
  从而把该文件「MGF 界 ⟹ 尾界」的链条**闭合为完整的测度论 Hoeffding 尾界**。

**诚实边界与降级（重要）**：
- **一般区间的常数是 `exp(t²R²/2)`（`R = max b (−a)`），不是 `exp(t²(b−a)²/8)`**。
  本文件**先前草稿曾误称**：`a + b ≥ 0` 时 `|X| ≤ (b−a)/2`，从而可直接取
  `(b−a)/2`。**该声称是错的**：`|X| ≤ (b−a)/2` 需要 `a+b ≥ 0`（左边）与
  `a+b ≤ 0`（右边）**同时**成立，故一般只有 `a = −b` 时可能
  （反例 `a = −1`、`b = 1/2`：`(b−a)/2 = 3/4`，但 `X ≡ a` 时 `|X| = 1 > 3/4`）。
  正确的标准常数只在**对称区间**（定理 7）下成立。此错误已更正并保留记录。
- **`t` 无符号限制**（比任务书要求的 `t > 0` 更强）：弦界对任意 `t` 成立，
  且 `t = 0` 时两边皆 `1`、`t < 0` 由 `X ↦ −X` 的对称性覆盖，故本文件不设
  `t > 0` 假设；若下游需要 `t > 0` 形式，直接传入即可。
- **`μ[X] = 0` 以显式假设引入**（`hmean`）——它是 Hoeffding 引理的标准前提，
  本文件不证「零均值」本身；
- **可积性显式给出**：`Integrable X μ` 与 `Integrable (fun ω => exp (t * X ω)) μ`
  作为假设（不证可测性/可积性），与 `RealHoeffdingMeasure` 的 `h_int` 约定一致；
- **定理 6 的 `0 ≤ b` 与 `a < b` 用于保证半径 `R > 0`**（`R = 0` 时 `|X| ≤ 0`
  使 `X` 几乎处处为 0，结论平凡，但 `hoeffding_lemma_measure` 要求 `c > 0`，
  故以 `R > 0` 排除该退化分支）；
- **未做**：多变量 Hoeffding、条件版（鞅差）的测度论 `condexp` 形式
  （由 `RealAzumaMartingale` 的有限纤维版与 `RealMartingaleChain` 承担）。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-! ## 一、凸性基座与弦不等式 -/

/-- **凸性基座**：`x ↦ e^{tx}` 在 `ℝ` 上凸。`t = 0` 时为常值 `1`（凸）；
`t ≠ 0` 时由 `Real.convexOn_exp` 与线性映射 `x ↦ t·x` 复合而得
（需 `MonotoneOn exp`，由 `Real.exp_le_exp` 给出；映像是满射故 `= univ`）。 -/
theorem convexOn_exp_mul (t : ℝ) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => Real.exp (t * x)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · have hconst : (fun x : ℝ => Real.exp (0 * x)) = fun _ : ℝ => (1 : ℝ) := by
      funext x; rw [zero_mul, Real.exp_zero]
    rw [hconst]
    exact convexOn_const 1 convex_univ
  · have hlin : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => t * x) := by
      refine ⟨convex_univ, ?_⟩
      intro x _ y _ a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith
    have hsurj : Function.Surjective (fun x : ℝ => t * x) := fun y => ⟨y / t, by field_simp⟩
    have himg : (fun x : ℝ => t * x) '' (Set.univ : Set ℝ) = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
    have hmono : MonotoneOn Real.exp ((fun x : ℝ => t * x) '' Set.univ) := by
      intro x _ y _ hxy
      exact Real.exp_le_exp.mpr hxy
    have hexp' : ConvexOn ℝ ((fun x : ℝ => t * x) '' Set.univ) Real.exp := by
      rw [himg]; exact convexOn_exp
    have h := hexp'.comp hlin hmono
    simpa [Function.comp] using h

/-- **弦不等式（一般区间，核心）**：`a < b`、`x ∈ [a,b]` ⟹
`e^{tx} ≤ ((b−x)/(b−a))·e^{ta} + ((x−a)/(b−a))·e^{tb}`（对任意 `t : ℝ` 成立，
不需要 `t > 0`）。

证明：把 `x` 写成端点凸组合 `((b−x)/(b−a)) • a + ((x−a)/(b−a)) • b`
（组合系数非负且和为 1），代入 `convexOn_exp_mul t` 的 `ConvexOn` 定义；
`ℝ` 上 `•` 就是 `*`，故结论直接读作乘法形式。 -/
theorem chord_hull {a b x t : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.exp (t * x) ≤ ((b - x) / (b - a)) * Real.exp (t * a)
      + ((x - a) / (b - a)) * Real.exp (t * b) := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hne : b - a ≠ 0 := ne_of_gt hba
  set ca : ℝ := (b - x) / (b - a) with hca
  set cb : ℝ := (x - a) / (b - a) with hcb
  have hca0 : 0 ≤ ca := div_nonneg (sub_nonneg.mpr hxb) hba.le
  have hcb0 : 0 ≤ cb := div_nonneg (sub_nonneg.mpr hax) hba.le
  have hsum : ca + cb = 1 := by
    rw [hca, hcb, ← add_div, show (b - x) + (x - a) = b - a by ring, div_self hne]
  have hcomb : ca * a + cb * b = x := by
    rw [hca, hcb]; field_simp; ring
  obtain ⟨-, hineq⟩ := convexOn_exp_mul t
  have hkey := hineq (Set.mem_univ a) (Set.mem_univ b) hca0 hcb0 hsum
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hkey
  rwa [hcomb] at hkey

/-- **对称弦界（cosh/sinh 形式）**：`|y| ≤ c`、`c > 0` ⟹
`e^{ty} ≤ cosh(tc) + (y/c)·sinh(tc)`（对任意 `t : ℝ` 成立）。

证明：定理 `chord_hull` 取 `a = −c`、`b = c`（此时 `b − a = 2c`），
再用 `Real.cosh_eq`、`Real.sinh_eq` 整理右端。这个形式的**关键好处**是
`y` 只以一次项出现，取期望后被 `E[Y] = 0` 直接消掉。 -/
theorem chord_hull_abs {y c t : ℝ} (hc : 0 < c) (hy : |y| ≤ c) :
    Real.exp (t * y) ≤ Real.cosh (t * c) + (y / c) * Real.sinh (t * c) := by
  have hle : y ≤ c := (abs_le.mp hy).2
  have hge : -c ≤ y := (abs_le.mp hy).1
  have h := chord_hull (a := -c) (b := c) (x := y) (t := t) (by linarith) hge hle
  have hden : c - (-c) = 2 * c := by ring
  rw [hden] at h
  have hrewrite : ((c - y) / (2 * c)) * Real.exp (t * (-c))
        + ((y - (-c)) / (2 * c)) * Real.exp (t * c)
      = Real.cosh (t * c) + (y / c) * Real.sinh (t * c) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    field_simp
    ring
  rwa [hrewrite] at h

/-! ## 二、主交付：一般测度论 Hoeffding 引理 -/

/-- **一般测度论 Hoeffding 引理（主交付，对称形式）**：`μ` 是概率测度、
`|X| ≤ c` 几乎处处、`μ[X] = 0`、`c > 0` ⟹
`mgf X μ t ≤ exp(t²c²/2)`（对任意 `t : ℝ` 成立）。

证明路线：
1. `mgf X μ t = ∫ e^{tX}`（`mgf` 定义）；
2. 逐点弦界 `chord_hull_abs`：`e^{tX} ≤ cosh(tc) + (X/c)·sinh(tc)`（a.e.）；
3. `integral_mono_ae` 取期望；右端积分 = `cosh(tc)·∫1 + (sinh(tc)/c)·∫X`；
4. 用概率归一 `∫1 = 1` 与零均值 `∫X = 0` 得 `mgf ≤ cosh(tc)`；
5. mathlib `Real.cosh_le_exp_half_sq : cosh u ≤ e^{u²/2}` 取 `u = tc` 收尾。

**可积性、零均值、`|X| ≤ c` 均为显式假设**（见文件头诚实边界）。 -/
theorem hoeffding_lemma_measure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c t : ℝ}
    (hc : 0 < c)
    (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ)
    (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  -- 逐点弦界（几乎处处）
  have hpt : ∀ᵐ ω ∂μ, Real.exp (t * X ω)
      ≤ Real.cosh (t * c) + (X ω / c) * Real.sinh (t * c) :=
    hX.mono fun ω hω => chord_hull_abs hc hω
  -- 弦函数可积
  have hchord_int : Integrable (fun ω => Real.cosh (t * c) + (X ω / c) * Real.sinh (t * c)) μ :=
    (integrable_const _).add ((hXint.div_const c).mul_const _)
  have hmono := integral_mono_ae hint hchord_int hpt
  -- 计算右端积分：`∫ (cosh + (X/c)·sinh) = cosh·∫1 + (∫X)/c·sinh = cosh`
  have hval : ∫ ω, (Real.cosh (t * c) + (X ω / c) * Real.sinh (t * c)) ∂μ
      = Real.cosh (t * c) := by
    rw [integral_add (integrable_const _) ((hXint.div_const c).mul_const _)]
    rw [integral_const, MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]
    -- `integral_mul_const` 在 mathlib 4.14 **只存在于 `IntervalIntegral`**（见 STYLE.md），
    -- 全空间版的正确名字是 `integral_mul_right`。
    have hsin : ∫ ω, (X ω / c) * Real.sinh (t * c) ∂μ
        = (∫ ω, X ω / c ∂μ) * Real.sinh (t * c) :=
      integral_mul_right (Real.sinh (t * c)) (fun ω => X ω / c)
    rw [hsin, integral_div, hmean]
    ring
  -- `mgf` 的定义就是该积分，先把目标改写为积分形式
  change ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 2)
  refine hmono.trans ?_
  rw [hval]
  have hcosh := Real.cosh_le_exp_half_sq (t * c)
  have hexp : (t * c) ^ 2 / 2 = t ^ 2 * c ^ 2 / 2 := by ring
  rwa [hexp] at hcosh

/-- **对称形式的主交付（显式调用点）**：与 `hoeffding_lemma_measure` 同陈述，
便于下游文件按名字引用（语义完全一致）。 -/
theorem hoeffding_lemma_measure_symmetric {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {c t : ℝ}
    (hc : 0 < c)
    (hX : ∀ᵐ ω ∂μ, |X ω| ≤ c)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ)
    (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * c ^ 2 / 2) :=
  hoeffding_lemma_measure hc hX hmean hXint hint

/-- **任意区间 `[a,b]` 形式（半径版）**：`0 ≤ b`、`a < b`、`a ≤ X ≤ b` a.e.、
`μ[X] = 0` ⟹ `mgf X μ t ≤ exp(t²·R²/2)`，其中 `R = max b (−a)`
是 `X` 的**事实上界半径**（由 `a ≤ X ≤ b` 直接得 `−R ≤ a ≤ X ≤ b ≤ R`，
故 `|X| ≤ R`）。

**诚实标注（重要，此前的错误已更正）**：本文件**先前草稿**曾声称
`a + b ≥ 0` 时 `|X| ≤ (b−a)/2`，从而直接给出 `exp(t²(b−a)²/8)`。
该声称**是错的**：`|X| ≤ (b−a)/2` 需要 `a ≥ (a−b)/2`（即 `a+b ≥ 0`）
**且** `b ≤ (b−a)/2`（即 `a+b ≤ 0`）同时成立，故一般只有 `a = −b` 时才可能。
正确的常数是 `exp(t²R²/2)`，`R = max b (−a)`；
在**对称区间**（`a = −b`）下才退化为标准常数 `exp(t²(b−a)²/8)`
—— 见推论 `hoeffding_lemma_measure_symmetric_interval`。 -/
theorem hoeffding_lemma_measure_interval {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b t : ℝ}
    (hb : 0 ≤ b) (hab : a < b)
    (hX : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ)
    (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * (max b (-a)) ^ 2 / 2) := by
  -- `R = max b (−a) > 0`：若 `b > 0` 由 `le_max_left` 得；若 `b = 0` 则
  -- `a < b = 0` 给出 `-a > 0`，由 `le_max_right` 得。
  have hR : 0 < max b (-a) := by
    rcases lt_or_eq_of_le hb with hbpos | hb0
    · exact lt_of_lt_of_le hbpos (le_max_left b (-a))
    · have : 0 < -a := by rw [← hb0] at hab; linarith
      exact lt_of_lt_of_le this (le_max_right b (-a))
  -- `R ≥ −a` 故 `−R ≤ a`；`R ≥ b` 故 `X ω ≤ b ≤ R`。
  have hneg : -(max b (-a)) ≤ a := by
    have := le_max_right b (-a); linarith
  have hbound : ∀ᵐ ω ∂μ, |X ω| ≤ max b (-a) := by
    refine hX.mono fun ω hω => ?_
    rw [abs_le]
    exact ⟨by linarith [hω.1, hneg], by linarith [hω.2, le_max_left b (-a)]⟩
  exact hoeffding_lemma_measure hR hbound hmean hXint hint

/-- **对称区间推论（标准 Hoeffding 常数）**：区间为 `[−b, b]`（`b > 0`）、
`μ[X] = 0` ⟹ `mgf X μ t ≤ exp(t²(b−(−b))²/8)` —— 此时
`max b (−(−b)) = b = (b−a)/2`，故化为**标准 Hoeffding 引理的一般区间常数**。 -/
theorem hoeffding_lemma_measure_symmetric_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {b t : ℝ}
    (hb : 0 < b)
    (hX : ∀ᵐ ω ∂μ, -b ≤ X ω ∧ X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hXint : Integrable X μ)
    (hint : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    mgf X μ t ≤ Real.exp (t ^ 2 * (b - (-b)) ^ 2 / 8) := by
  have hmain := hoeffding_lemma_measure_interval (a := -b) (b := b) hb.le
    (by linarith) hX hmean hXint hint
  have hmax : max b (-(-b)) = b := by rw [neg_neg, max_self]
  have hbr : b - (-b) = 2 * b := by ring
  rw [hmax] at hmain
  have hexp : t ^ 2 * b ^ 2 / 2 = t ^ 2 * (b - (-b)) ^ 2 / 8 := by rw [hbr]; ring
  rwa [hexp] at hmain

/-- **中心化归约（非零均值复用）**：若 `a ≤ X ≤ b`、`μ[X] = m`，则中心化变量
`X − m` 满足 `a − m ≤ X − m ≤ b − m` 且 `μ[X − m] = 0`；在 `0 ≤ b − m` 与
`a < b` 下可直接调用区间版得
`mgf (X − m) μ t ≤ exp(t²·(max (b−m) (m−a))²/2)`。

本定理把「非零均值」归约为零均值情形，供非零均值场景复用。 -/
theorem hoeffding_lemma_measure_centered {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b m t : ℝ}
    (hbm : 0 ≤ b - m) (hab : a < b)
    (hX : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ b)
    (hmean : ∫ ω, X ω ∂μ = m)
    (hXint : Integrable X μ)
    (hint : Integrable (fun ω => Real.exp (t * (X ω - m))) μ) :
    mgf (fun ω => X ω - m) μ t
      ≤ Real.exp (t ^ 2 * (max (b - m) (-(a - m))) ^ 2 / 2) := by
  have hX' : ∀ᵐ ω ∂μ, a - m ≤ (fun ω => X ω - m) ω ∧ (fun ω => X ω - m) ω ≤ b - m :=
    hX.mono fun ω hω => ⟨by simp only []; linarith [hω.1], by simp only []; linarith [hω.2]⟩
  have hmean' : ∫ ω, (X ω - m) ∂μ = 0 := by
    rw [integral_sub hXint (integrable_const m), hmean, integral_const,
      MeasureTheory.measure_univ, ENNReal.one_toReal, one_smul]
    ring
  have hab' : a - m < b - m := by linarith
  exact hoeffding_lemma_measure_interval hbm hab' hX' hmean'
    (hXint.sub (integrable_const m)) hint

end Lattice
