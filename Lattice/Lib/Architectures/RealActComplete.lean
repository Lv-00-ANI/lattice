import Mathlib
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealSwiGLU
/-!
# LATTICE: 激活函数族完备化 —— 现代激活（SiLU / hard-sigmoid / hard-swish / tanh）纳入软掩码类 + Lipschitz 常数

延续 RealActClass 的**模型无关范式**（SoftMasked：f(x) = s(x)·x，s ∈ [0,1]）：

  1. **hard-sigmoid**（MobileNet 版，clamp 形式）：hs(x) = clamp(x/6 + 1/2, 0, 1)。
     · 有界：0 ≤ hs(x) ≤ 1（min/max 直接）；
     · 1/6-Lipschitz：分段线性（三区：0 / x/6+1/2 / 1），case 分析直接证
       |hs(x) − hs(y)| ≤ |x−y|/6（不依赖 MVT——hs 在 ±3 处不可导）。
  2. **SiLU / swish**：silu(x) = x·σ(x)，σ = sigmoid ∈ (0,1)（复用 RealSwiGLU.sigmoid）。
     · SoftMasked 实例：掩码 = σ ∈ [0,1]（sigmoid_bounds）；
     · Lipschitz：**有界域版本 (1 + M/4)**——本文件证 [-M,M] 上的界（M ≥ 0，MVT：
       Convex.norm_image_sub_le_of_norm_deriv_le）。
       ⚠ **更正（v13，CORRECTIONS B2 已撤回）**：本文件早期版本声称"silu 导数
       σ + x·σ(1−σ) 无全局上界，故 silu 在 ℝ 上不是全局 Lipschitz"——**该论断为假**。
       事实上 `x·σ(x)(1−σ(x)) → 0`（`x → ±∞` 时 `σ(1−σ) ~ e^{−|x|}` 指数衰减），
       故 `sup|silu'| ≈ 1.0998` **有界**。silu **是**全局 Lipschitz 的：
       `RealCounterexamples.cex_silu_globally_lipschitz` 机器验证
       `|silu x − silu y| ≤ 2·|x − y|`（取 L = 2）。
       因此本文件的有界域界**仍然正确，只是弱于必要的**；全局版见 `RealCounterexamples`。
       注意 澄清：**本文件不证全局版**——本文件定理清单中关于 silu 的 Lipschitz 结论
       只有 `silu_lipschitz_on`（有界域版本，常数 1 + M/4）；全局 Lipschitz 定理
       `cex_silu_globally_lipschitz`（及存在性形式 `cex_silu_global_lipschitz_exists`）
       均位于 `RealCounterexamples`，不在本文件的定理清单内。
  3. **hard-swish**：hardSwish(x) = x·hs(x)。
     · SoftMasked 实例：掩码 = hs ∈ [0,1]（hardSigmoid_bounds）。
  4. **tanh 激活**：tanh 不是 x·σ(x) 形式的门控激活（值域 [-1,1]，不按点乘 x 分解），
     故不属 SoftMasked 类，单独证其 **1-Lipschitz**：
     导数 1 − tanh² ∈ [0,1]（|tanh| ≤ 1，复用 tanh_abs_le_one）+ MVT。
     mathlib 4.14 无 `Real.hasDerivAt_tanh`，此处用 tanh = sinh/cosh 与商法则自证。

  FFN 实例化：silu / hardSwish 经 softMask_FFN_effective 得到有效线性映射
  Σ Wᵢ·f(hᵢ) = Σ (Wᵢ·s(hᵢ))·hᵢ（类实例化，与 relu/gelu/swiglu 同范式）。

  全部定理真实可证，无 sorry/axiom/admit；Lipschitz 常数给出保守上界。
-/

noncomputable section

open Lattice.Lib.Architectures.RealActClass

namespace Lattice
/-! ## hard-sigmoid（MobileNet 版，clamp 形式）
hs(x) = min 1 (max 0 (x/6 + 1/2))：x ≤ −3 → 0；−3 ≤ x ≤ 3 → x/6+1/2；3 ≤ x → 1。-/

def hardSigmoid (x : ℝ) : ℝ := min 1 (max 0 (x / 6 + 1 / 2))

/-! ### 分段取值引理（三区等价的 rewrite 引理） -/

lemma hardSigmoid_affine_calc (x : ℝ) : x / 6 + 1 / 2 = (x + 3) / 6 := by
  ring

lemma hardSigmoid_eq_zero (x : ℝ) (hx : x ≤ -3) : hardSigmoid x = 0 := by
  unfold hardSigmoid
  have ht : x / 6 + 1 / 2 ≤ 0 := by
    rw [hardSigmoid_affine_calc]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
  rw [max_eq_left ht]
  rw [min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma hardSigmoid_eq_affine (x : ℝ) (hlo : -3 ≤ x) (hhi : x ≤ 3) :
    hardSigmoid x = (x + 3) / 6 := by
  unfold hardSigmoid
  have ht1 : 0 ≤ x / 6 + 1 / 2 := by
    rw [hardSigmoid_affine_calc]
    exact div_nonneg (by linarith) (by norm_num)
  have ht2 : x / 6 + 1 / 2 ≤ 1 := by
    rw [hardSigmoid_affine_calc]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith
  rw [max_eq_right ht1]
  rw [min_eq_right ht2]
  rw [hardSigmoid_affine_calc]

lemma hardSigmoid_eq_one (x : ℝ) (hx : 3 ≤ x) : hardSigmoid x = 1 := by
  unfold hardSigmoid
  have ht0 : 0 ≤ x / 6 + 1 / 2 := by
    rw [hardSigmoid_affine_calc]
    exact div_nonneg (by linarith) (by norm_num)
  have ht1 : 1 ≤ x / 6 + 1 / 2 := by
    rw [hardSigmoid_affine_calc]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    nlinarith
  rw [max_eq_right ht0]
  rw [min_eq_left ht1]

/-! ### 定理：hard-sigmoid 有界 [0,1] -/

theorem hardSigmoid_bounds (x : ℝ) : 0 ≤ hardSigmoid x ∧ hardSigmoid x ≤ 1 := by
  unfold hardSigmoid
  constructor
  · -- 0 ≤ min 1 (max 0 t)：min 的下界（1 与 max 0 t 均 ≥ 0）
    exact le_min (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 0 (x / 6 + 1 / 2))
  · -- min 1 (max 0 t) ≤ 1：min 的左分量
    exact min_le_left 1 (max 0 (x / 6 + 1 / 2))

/-! ### 定理：hard-sigmoid 是 1/6-Lipschitz（case 分析，不经 MVT）
先证 x ≤ y 的定向版本（用 |x−y| = y−x），再对称化。三区 × 三区逐格验证。-/

lemma hardSigmoid_lipschitz_of_le (x y : ℝ) (hxy : x ≤ y) :
    |hardSigmoid x - hardSigmoid y| ≤ |x - y| / 6 := by
  have h6 : (0 : ℝ) < 6 := by norm_num
  by_cases hy : y ≤ -3
  · -- 双低端（x ≤ y ≤ −3）：hs x = hs y = 0
    have hx : x ≤ -3 := le_trans hxy hy
    rw [hardSigmoid_eq_zero x hx, hardSigmoid_eq_zero y hy]
    simp
    exact div_nonneg (abs_nonneg _) (le_of_lt h6)
  · have hyge : -3 ≤ y := le_of_not_ge hy
    by_cases hxhi : 3 ≤ x
    · -- 双高端（3 ≤ x ≤ y）：hs x = hs y = 1
      have hyhi : 3 ≤ y := le_trans hxhi hxy
      rw [hardSigmoid_eq_one x hxhi, hardSigmoid_eq_one y hyhi]
      simp
      exact div_nonneg (abs_nonneg _) (le_of_lt h6)
    · have hxlt : x < 3 := lt_of_not_ge hxhi
      -- x ≤ y 下 |x−y| = y−x
      have hxabs : |x - y| = y - x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
      by_cases hxlo : x ≤ -3
      · -- x 低端，y > −3
        by_cases hyhi : 3 ≤ y
        · -- x 低端，y 高端：|0 − 1| = 1 ≤ (y−x)/6（y−x ≥ 6）
          rw [hardSigmoid_eq_zero x hxlo, hardSigmoid_eq_one y hyhi]
          norm_num
          rw [hxabs]
          rw [le_div_iff₀ h6]
          nlinarith
        · -- x 低端，y 中段：|0 − (y+3)/6| = (y+3)/6 ≤ (y−x)/6 ⟺ x ≤ −3
          rw [hardSigmoid_eq_zero x hxlo]
          rw [hardSigmoid_eq_affine y hyge (le_of_not_ge hyhi)]
          have hpos : 0 ≤ (y + 3) / 6 := div_nonneg (by linarith) (le_of_lt h6)
          rw [abs_sub_comm]
          simp
          rw [abs_of_nonneg hpos]
          rw [hxabs]
          rw [div_le_div_iff_of_pos_right h6]
          nlinarith
      · -- x 中段或高端（x < 3，−3 < x）
        have hxge : -3 ≤ x := le_of_not_ge hxlo
        by_cases hyhi : 3 ≤ y
        · -- x 中段，y 高端：|(x+3)/6 − 1| = (3−x)/6 ≤ (y−x)/6 ⟺ 3 ≤ y
          rw [hardSigmoid_eq_affine x hxge (le_of_lt hxlt)]
          rw [hardSigmoid_eq_one y hyhi]
          have hcalc : (x + 3) / 6 - 1 = (x - 3) / 6 := by ring
          rw [hcalc]
          have hnonpos : (x - 3) / 6 ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt h6)
          rw [abs_of_nonpos hnonpos]
          have hcalc2 : -((x - 3) / 6) = (3 - x) / 6 := by ring
          rw [hcalc2]
          rw [hxabs]
          rw [div_le_div_iff_of_pos_right h6]
          nlinarith
        · -- 双中段：|(x+3)/6 − (y+3)/6| = |x−y|/6 = |x−y|/6
          rw [hardSigmoid_eq_affine x hxge (le_of_lt hxlt)]
          rw [hardSigmoid_eq_affine y hyge (le_of_not_ge hyhi)]
          have hcalc : (x + 3) / 6 - (y + 3) / 6 = (x - y) / 6 := by ring
          rw [hcalc]
          rw [abs_div]
          have h6abs : |(6 : ℝ)| = 6 := by norm_num
          rw [h6abs]

theorem hardSigmoid_lipschitz (x y : ℝ) : |hardSigmoid x - hardSigmoid y| ≤ |x - y| / 6 := by
  by_cases hxy : x ≤ y
  · exact hardSigmoid_lipschitz_of_le x y hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h' : |hardSigmoid y - hardSigmoid x| ≤ |y - x| / 6 :=
      hardSigmoid_lipschitz_of_le y x hyx
    -- 对称性：|hs y − hs x| = |hs x − hs y|，|y − x| = |x − y|
    simpa [abs_sub_comm] using h'

/-! ## sigmoid 的可导性与 Lipschitz（SiLU 的组件）
mathlib 4.14 无 `Real.sigmoid`，故对 RealSwiGLU 的 `sigmoid` 自证：
σ'(x) = σ(x)(1−σ(x))（链式 + 商法则），|σ'| ≤ 1/4 ⟹ σ 是 1/4-Lipschitz（ℝ 全局）。-/

lemma sigmoid_hasDerivAt (x : ℝ) : HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  -- σ(x) = 1/(1 + e^{−x})：exp∘neg 链式 + 常数平移 + 倒数
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have h2 : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (-Real.exp (-x)) x := h1.const_add 1
  have hf : 1 + Real.exp (-x) ≠ 0 := by
    have hpos : 0 < 1 + Real.exp (-x) := by linarith [Real.exp_pos (-x)]
    exact ne_of_gt hpos
  have h3 := h2.inv hf
  -- (fun t => (1 + e^{−t})⁻¹) 与 sigmoid 逐点相等（1/a = a⁻¹）
  have hbody : (fun t : ℝ => (1 + Real.exp (-t))⁻¹) = sigmoid := by
    funext t
    simp [sigmoid]
  rw [hbody] at h3
  convert h3 using 1
  -- 导数相等：σ(1−σ) = e^{−x}/(1+e^{−x})²（field 代数）
  unfold sigmoid
  field_simp [hf]
  ring

lemma sigmoid_deriv (x : ℝ) : deriv sigmoid x = sigmoid x * (1 - sigmoid x) :=
  (sigmoid_hasDerivAt x).deriv

lemma sigmoid_lipschitz (a b : ℝ) : |sigmoid a - sigmoid b| ≤ (1 / 4 : ℝ) * |a - b| := by
  have hf : ∀ x : ℝ, x ∈ Set.univ → DifferentiableAt ℝ sigmoid x := by
    intro x hx
    exact (sigmoid_hasDerivAt x).differentiableAt
  have hbound : ∀ x : ℝ, x ∈ Set.univ → ‖deriv sigmoid x‖ ≤ 1 / 4 := by
    intro x hx
    rw [sigmoid_deriv]
    rw [Real.norm_eq_abs]
    have hσ0 : 0 ≤ sigmoid x := le_of_lt (sigmoid_bounds x).1
    have hσ1 : sigmoid x ≤ 1 := le_of_lt (sigmoid_bounds x).2
    -- σ(1−σ) ≥ 0（0 ≤ σ ≤ 1）
    have hnonneg : 0 ≤ sigmoid x * (1 - sigmoid x) := by nlinarith
    rw [abs_of_nonneg hnonneg]
    -- σ(1−σ) ≤ 1/4：σ(1−σ) = 1/4 − (σ − 1/2)²（配平方）
    have hsq : 0 ≤ (sigmoid x - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith
  -- 一维 MVT（全局凸集 ℝ）：σ 是 1/4-Lipschitz
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (x := a) (y := b) (s := Set.univ) hf hbound
    convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-! ## SiLU / swish：silu(x) = x·σ(x)
与 RealSwiGLU.swiglu 定义相同（rfl 等式桥接）；掩码 = σ ∈ [0,1] ⟹ SoftMasked 实例。
Lipschitz：**有界域版本 (1 + M/4)**。注意 **更正（v13）**：早期版本称"silu 导数无全局上界、
ℝ 上非全局 Lipschitz"——**该论断为假**（`x·σ(1−σ) → 0`，`sup|silu'| ≈ 1.0998`）。
silu **是**全局 Lipschitz 的：见 `RealCounterexamples.cex_silu_globally_lipschitz`
（机器验证 `|silu x − silu y| ≤ 2|x − y|`）；本文件的界正确但弱于必要的。
（记录于 CORRECTIONS.md B2「已撤回」）。-/

def silu (x : ℝ) : ℝ := x * sigmoid x

theorem silu_eq_swiglu : silu = swiglu := rfl

theorem silu_is_soft_masked : SoftMasked silu sigmoid := by
  constructor
  · -- silu(x) = σ(x)·x（定义，交换乘序）
    intro x
    unfold silu
    ring
  · constructor
    · -- σ ≥ 0
      intro x
      exact le_of_lt (sigmoid_bounds x).1
    · -- σ ≤ 1
      intro x
      exact le_of_lt (sigmoid_bounds x).2

/-! ### 定理：silu 在 [-M,M] 上有界域 Lipschitz（常数 1 + M/4，M ≥ 0）
silu 导数 = σ(x) + x·σ'(x) = σ(x) + x·σ(x)(1−σ(x))，
|·| ≤ σ(x) + |x|·σ(x)(1−σ(x)) ≤ 1 + M·(1/4)（MVT 常数）。-/

theorem silu_lipschitz_on (M x y : ℝ) (hM : 0 ≤ M)
    (hx : x ∈ Set.Icc (-M) M) (hy : y ∈ Set.Icc (-M) M) :
    |silu x - silu y| ≤ (1 + M / 4) * |x - y| := by
  have hf : ∀ z : ℝ, z ∈ Set.Icc (-M) M → DifferentiableAt ℝ silu z := by
    intro z hz
    have hd : HasDerivAt silu (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z := by
      -- silu = fun t => t * sigmoid t：乘积法则（id · σ）
      have h : HasDerivAt (fun t : ℝ => t * sigmoid t)
          (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z :=
        (hasDerivAt_id' z).mul (sigmoid_hasDerivAt z)
      simpa [silu] using h
    exact hd.differentiableAt
  have hbound : ∀ z : ℝ, z ∈ Set.Icc (-M) M → ‖deriv silu z‖ ≤ 1 + M / 4 := by
    intro z hz
    have hderiv : deriv silu z = sigmoid z + z * (sigmoid z * (1 - sigmoid z)) := by
      have hprod : HasDerivAt (fun t : ℝ => t * sigmoid t)
          (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z :=
        (hasDerivAt_id' z).mul (sigmoid_hasDerivAt z)
      have hd : deriv (fun t : ℝ => t * sigmoid t) z =
          1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z)) := hprod.deriv
      simpa [silu] using hd
    rw [hderiv]
    rw [Real.norm_eq_abs]
    have hσ0 : 0 ≤ sigmoid z := le_of_lt (sigmoid_bounds z).1
    have hσ1 : sigmoid z ≤ 1 := le_of_lt (sigmoid_bounds z).2
    have hσder : 0 ≤ sigmoid z * (1 - sigmoid z) := by nlinarith
    have hquad : sigmoid z * (1 - sigmoid z) ≤ 1 / 4 := by
      -- 配平方：σ(1−σ) = 1/4 − (σ − 1/2)²
      have hsq : 0 ≤ (sigmoid z - 1 / 2) ^ 2 := sq_nonneg _
      nlinarith
    have hzabs : |z| ≤ M := by
      rcases hz with ⟨hlo, hhi⟩
      rw [abs_le]
      constructor <;> nlinarith
    calc
      |sigmoid z + z * (sigmoid z * (1 - sigmoid z))|
          ≤ |sigmoid z| + |z * (sigmoid z * (1 - sigmoid z))| := abs_add _ _
      _ = sigmoid z + |z| * (sigmoid z * (1 - sigmoid z)) := by
            rw [abs_of_nonneg hσ0]
            rw [abs_mul]
            rw [abs_of_nonneg hσder]
      _ ≤ 1 + M * (1 / 4) := by
            -- σ ≤ 1，|z| ≤ M，σ(1−σ) ≤ 1/4（乘积有界）
            have hmul : |z| * (sigmoid z * (1 - sigmoid z)) ≤ M * (1 / 4) :=
              mul_le_mul hzabs hquad hσder hM
            nlinarith [hσ1, hmul]
      _ = 1 + M / 4 := by ring
  -- 一维 MVT 于 [-M,M]（凸集）
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (-M) M) hf hbound
    (convex_Icc (-M) M) hx hy
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-! ## hard-swish：hardSwish(x) = x·hs(x)
掩码 = hardSigmoid ∈ [0,1]（hardSigmoid_bounds）⟹ SoftMasked 实例。-/

def hardSwish (x : ℝ) : ℝ := x * hardSigmoid x

theorem hardSwish_is_soft_masked : SoftMasked hardSwish hardSigmoid := by
  constructor
  · -- hardSwish(x) = hs(x)·x（定义，交换乘序）
    intro x
    unfold hardSwish
    ring
  · constructor
    · -- hs ≥ 0
      intro x
      exact (hardSigmoid_bounds x).1
    · -- hs ≤ 1
      intro x
      exact (hardSigmoid_bounds x).2

/-! ## tanh 激活：1-Lipschitz（不属 SoftMasked 类，单独处理）
tanh 值域 [-1,1]，不是 x·σ(x) 形式；导数 1 − tanh² ∈ [0,1]（|tanh| ≤ 1）。
mathlib 4.14 无 `Real.hasDerivAt_tanh`，用 tanh = sinh/cosh 与商法则自证。-/

lemma tanh_hasDerivAt (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hs : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x
  have hc : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x
  have hcpos : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  -- 商法则：d/dx (sinh/cosh) = (cosh² − sinh²)/cosh²
  have hq : HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / (Real.cosh x) ^ 2) x :=
    hs.div hc hcpos
  have htanh : (fun y : ℝ => Real.sinh y / Real.cosh y) = Real.tanh := by
    funext y
    rw [Real.tanh_eq_sinh_div_cosh]
  rw [htanh] at hq
  convert hq using 1
  -- (cosh² − sinh²)/cosh² = 1 − tanh²（field 代数，cosh ≠ 0）
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hcpos]
  -- 剩余：1 = cosh·cosh − sinh·sinh（Real.cosh_sq：cosh² = sinh² + 1）
  nlinarith [Real.cosh_sq x]

lemma tanh_deriv (x : ℝ) : deriv Real.tanh x = 1 - Real.tanh x ^ 2 :=
  (tanh_hasDerivAt x).deriv

theorem tanh_lipschitz (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have hf : ∀ z : ℝ, z ∈ Set.univ → DifferentiableAt ℝ Real.tanh z := by
    intro z hz
    exact (tanh_hasDerivAt z).differentiableAt
  have hbound : ∀ z : ℝ, z ∈ Set.univ → ‖deriv Real.tanh z‖ ≤ 1 := by
    intro z hz
    rw [tanh_deriv]
    rw [Real.norm_eq_abs]
    -- |tanh z| ≤ 1 ⟹ tanh² ≤ 1 ⟹ 0 ≤ 1 − tanh² ≤ 1
    have ht : |Real.tanh z| ≤ 1 := tanh_abs_le_one z
    have hsq : Real.tanh z ^ 2 ≤ 1 := by
      have ht' : |Real.tanh z| ≤ |(1 : ℝ)| := by simpa using ht
      simpa using (sq_le_sq.mpr ht')
    have hnonneg : 0 ≤ 1 - Real.tanh z ^ 2 := by nlinarith
    rw [abs_of_nonneg hnonneg]
    nlinarith [hsq]
  -- 一维 MVT（全局凸集 ℝ）：tanh 是 1-Lipschitz
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (x := x) (y := y) (s := Set.univ) hf hbound
    convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-! ## FFN 有效线性映射：新激活的类实例化
silu / hardSwish 经软掩码 FFN 定理（softMask_FFN_effective）直接实例化，
与 relu（relu_FFN_effective_via_class）、gelu、swiglu 同范式。-/

theorem silu_FFN_effective_via_class {ι : Type*} [Fintype ι] (W h : ι → ℝ) :
    ∑ i, W i * silu (h i) = ∑ i, (W i * sigmoid (h i)) * h i := by
  apply Finset.sum_congr rfl
  intro i hi
  -- silu(hᵢ) = σ(hᵢ)·hᵢ（silu 是软掩码实例的分解）
  have hdec : silu (h i) = sigmoid (h i) * h i := silu_is_soft_masked.1 (h i)
  rw [hdec]
  ring

theorem hardSwish_FFN_effective_via_class {ι : Type*} [Fintype ι] (W h : ι → ℝ) :
    ∑ i, W i * hardSwish (h i) = ∑ i, (W i * hardSigmoid (h i)) * h i := by
  apply Finset.sum_congr rfl
  intro i hi
  -- hardSwish(hᵢ) = hs(hᵢ)·hᵢ（hardSwish 是软掩码实例的分解）
  have hdec : hardSwish (h i) = hardSigmoid (h i) * h i := hardSwish_is_soft_masked.1 (h i)
  rw [hdec]
  ring

end Lattice
