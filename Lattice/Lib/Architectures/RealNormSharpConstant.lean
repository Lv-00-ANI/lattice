import Mathlib
import Lattice.Lib.Architectures.RealNormLipschitz
import Lattice.Lib.Architectures.RealRMSNorm
/-!
# LATTICE: 归一化层 Lipschitz 常数的紧性 —— 单位化 / RMSNorm / 中心化投影

RealNormLipschitz 给出**保守上界**：
  · 单位化 x ↦ x/‖x‖ 在 ‖x‖ ≥ c > 0 上是 (2/c)-Lipschitz；
  · RMSNorm 是 (2√n/c)-Lipschitz；
  · 中心化 center 是 1-Lipschitz（正交投影）。

本文件研究这些常数的**紧性（sharpness）**，并如实纠正「2/c 最优」的直觉：

  1. **单位化映射**：
     · 在任意实内积空间（含 EuclideanSpace）中，真正常数就是 **1/c**：
         ‖x/‖x‖ − y/‖y‖‖ ≤ (1/c)·‖x−y‖   （‖x‖,‖y‖ ≥ c > 0）
       （用 ‖u−v‖² = 2−2⟪u,v⟫、‖x−y‖² = ‖x‖²+‖y‖²−2‖x‖‖y‖⟪u,v⟫，
        配合 ⟪u,v⟫ ≤ 1 与 ‖x‖‖y‖ ≥ c² 作平方比较）；
     · 1/c **可达**：取 x = c、y = −c（ℝ 上）即取等 —— 于是 2/c 不是最优常数，
       任何有效的 Lipschitz 常数 K 必须满足 K ≥ 1/c（lipschitz_constant_lower_bound）。
     · 一般赋范空间（非内积）本文件**不主张** 1/c 成立；标准 (2/c) 界仍最保险，
       本文件对一般空间只证**下界** K ≥ 1/c（由取等点对给出）。
  2. **RMSNorm**：同法给出下界 K ≥ √n/c，并展示 (2√n/c) 界在取等点对上严格（不取等）。
  3. **中心化映射是正交投影**：
     ctr(z) = z − mean(z)·1 幂等、像落在零均值超平面、与常向量正交、
     1-Lipschitz 且不增范数；该 1-常数是**紧的**（超平面上 ctr = id，故取等）。

全部定理真实可证，无 sorry/axiom/admit；已诚实标注一般赋范空间的局限。
-/

noncomputable section

namespace Lattice

/-! ## 下界原理：一组取定的点对给出任意有效常数的下界 -/

/-- 若 K 对点对 (a,b) 成立，则比值 ‖f a − f b‖ / ‖a − b‖ ≤ K。 -/
theorem lipschitz_constant_lower_bound {E : Type*} [NormedAddCommGroup E]
    (f : E → E) (K : ℝ) (a b : E)
    (hK : ‖f a - f b‖ ≤ K * ‖a - b‖) (hd : 0 < ‖a - b‖) :
    ‖f a - f b‖ / ‖a - b‖ ≤ K := by
  rw [div_le_iff₀ hd]
  exact hK

/-! ## 单位化映射：内积空间中的紧常数 1/c -/

/-- **单位化映射的紧 Lipschitz 界（实内积空间）**：
    ‖x/‖x‖ − y/‖y‖‖ ≤ (1/c)·‖x−y‖（‖x‖,‖y‖ ≥ c > 0）。
    改进 RealNormLipschitz 的 (2/c) 界；在 EuclideanSpace 上真正常数是 1/c。 -/
theorem unit_normalize_lipschitz_sharp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y : E) (c : ℝ) (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (1 / c) * ‖x - y‖ := by
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hc hx
  have hypos : 0 < ‖y‖ := lt_of_lt_of_le hc hy
  set u : E := (1 / ‖x‖) • x with hu
  set v : E := (1 / ‖y‖) • y with hv
  set α : ℝ := inner u v with hα
  have hcoefx : ‖(1 : ℝ) / ‖x‖‖ = (1 : ℝ) / ‖x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hxpos))]
  have hcoefy : ‖(1 : ℝ) / ‖y‖‖ = (1 : ℝ) / ‖y‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hypos))]
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, norm_smul, hcoefx, one_div, inv_mul_cancel₀ (ne_of_gt hxpos)]
  have hv_norm : ‖v‖ = 1 := by
    rw [hv, norm_smul, hcoefy, one_div, inv_mul_cancel₀ (ne_of_gt hypos)]
  have hxsplit : ‖x‖ • u = x := by
    rw [hu, one_div]
    exact smul_inv_smul₀ (ne_of_gt hxpos) x
  have hysplit : ‖y‖ • v = y := by
    rw [hv, one_div]
    exact smul_inv_smul₀ (ne_of_gt hypos) y
  have hinner : inner x y = (‖x‖ * ‖y‖) * α := by
    calc
      inner x y = inner (‖x‖ • u) (‖y‖ • v) := by rw [hxsplit, hysplit]
      _ = (‖x‖ * ‖y‖) * α := by
            rw [real_inner_smul_left, real_inner_smul_right, hα]
            ring
  have hxy : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (‖x‖ * ‖y‖) * α := by
    rw [norm_sub_sq_real, hinner]
    ring
  have huv : ‖u - v‖ ^ 2 = 2 - 2 * α := by
    rw [norm_sub_sq_real, hu_norm, hv_norm, ← hα]
    ring
  have hα_le : α ≤ 1 := by
    have h := real_inner_le_norm u v
    rw [hu_norm, hv_norm] at h
    simp at h
    rwa [hα]
  have hrs : c ^ 2 ≤ ‖x‖ * ‖y‖ := by
    have h := mul_le_mul hx hy hc.le (norm_nonneg x)
    simpa [pow_two] using h
  have hprod : α * (‖x‖ * ‖y‖ - c ^ 2) ≤ 1 * (‖x‖ * ‖y‖ - c ^ 2) :=
    mul_le_mul_of_nonneg_right hα_le (by linarith [hrs])
  have hkey : c ^ 2 * ‖u - v‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [huv, hxy]
    nlinarith [hprod, hrs, sq_nonneg (‖x‖ - ‖y‖)]
  have hsq : (c * ‖u - v‖) ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [mul_pow]
    exact hkey
  have h1 : 0 ≤ c * ‖u - v‖ := mul_nonneg hc.le (norm_nonneg _)
  have h2 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hle : c * ‖u - v‖ ≤ ‖x - y‖ := by
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this
  have hle' : ‖u - v‖ * c ≤ ‖x - y‖ := by
    rwa [mul_comm] at hle
  have hfin : ‖u - v‖ ≤ ‖x - y‖ / c := (le_div_iff₀ hc).mpr hle'
  calc
    ‖u - v‖ ≤ ‖x - y‖ / c := hfin
    _ = (1 / c) * ‖x - y‖ := by rw [one_div, div_eq_mul_inv, mul_comm]

/-- 取等点对上单位化映射的距离恰为 2：‖c/|c| − (−c)/|−c|‖ = 2。 -/
lemma unit_normalize_antipodal_real (c : ℝ) (hc : 0 < c) :
    ‖(1 / ‖(c : ℝ)‖) • (c : ℝ) - (1 / ‖(-c : ℝ)‖) • (-c : ℝ)‖ = 2 := by
  have hc' : ‖(c : ℝ)‖ = c := by rw [Real.norm_eq_abs, abs_of_pos hc]
  have hnc : ‖(-c : ℝ)‖ = c := by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hc]
  have e1 : (1 / c) • (c : ℝ) = 1 := by
    rw [smul_eq_mul, one_div, inv_mul_cancel₀ (ne_of_gt hc)]
  have e2 : (1 / c) • (-c : ℝ) = -1 := by
    rw [smul_eq_mul, mul_neg, one_div, inv_mul_cancel₀ (ne_of_gt hc)]
  rw [hc', hnc, e1, e2]
  norm_num

/-- 常数 1/c **可达**（取等）：x = c、y = −c 时两侧同为 2。 -/
theorem unit_normalize_sharp (c : ℝ) (hc : 0 < c) :
    ‖(1 / ‖(c : ℝ)‖) • (c : ℝ) - (1 / ‖(-c : ℝ)‖) • (-c : ℝ)‖
      = (1 / c) * ‖(c : ℝ) - (-c : ℝ)‖ := by
  rw [unit_normalize_antipodal_real c hc]
  have e3 : (c : ℝ) - (-c) = 2 * c := by ring
  rw [e3, Real.norm_eq_abs, abs_of_pos (by linarith)]
  field_simp [ne_of_gt hc]

/-- 由 x = c、y = −c 的取等点，任何有效常数 K 都满足 K ≥ 1/c。 -/
theorem unit_normalize_constant_lower_bound (c : ℝ) (hc : 0 < c) (K : ℝ)
    (hK : ∀ x y : ℝ, c ≤ ‖x‖ → c ≤ ‖y‖ →
      ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ K * ‖x - y‖) :
    1 / c ≤ K := by
  have hx : c ≤ ‖(c : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_pos hc]
  have hy : c ≤ ‖(-c : ℝ)‖ := by rw [norm_neg, Real.norm_eq_abs, abs_of_pos hc]
  have h := hK c (-c) hx hy
  have heq2 : ‖(c : ℝ) - (-c : ℝ)‖ = 2 * c := by
    rw [show (c : ℝ) - (-c) = 2 * c by ring, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [unit_normalize_antipodal_real c hc, heq2] at h
  rw [div_le_iff₀ hc]
  nlinarith [h]

/-- (2/c) 界在取等点对上是**严格**的：在 ℝ 上取 x = c、y = −c，则
    比值 2/‖x−y‖ = 1/c < 2/c，即 2 < (2/c)·(2c) = 4
    ⟹ RealNormLipschitz 的 2/c 界不是紧界。
    **边界**：本式仅在 ℝ 这一具体空间上证明 2/c 不取等；1/c 的普遍上界
    另由本节 `unit_normalize_lipschitz_sharp` 与 `unit_normalize_constant_lower_bound`
    给出（本文件对一般赋范空间只证下界，不主张 1/c 成立）。 -/
theorem unit_normalize_two_div_not_attained (c : ℝ) (hc : 0 < c) :
    ‖(1 / ‖(c : ℝ)‖) • (c : ℝ) - (1 / ‖(-c : ℝ)‖) • (-c : ℝ)‖
      < (2 / c) * ‖(c : ℝ) - (-c : ℝ)‖ := by
  have heq2 : ‖(c : ℝ) - (-c : ℝ)‖ = 2 * c := by
    rw [show (c : ℝ) - (-c) = 2 * c by ring, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [unit_normalize_antipodal_real c hc, heq2]
  have hval2 : (2 / c) * (2 * c) = 4 := by field_simp [ne_of_gt hc]; ring
  rw [hval2]
  norm_num

/-! ## RMSNorm：常数下界与 (2√n/c) 的非紧性 -/

/-- RMSNorm 的向量映射形式（与 RealRMSNorm.rmsNorm 同构，
    在 EuclideanSpace 上 = √n · 单位化）。 -/
def rmsNormE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (Real.sqrt n) • ((1 / ‖x‖) • x)

/-! 注意 **WIRE1 (S12 行动项 ②) 已删除一处死链**：原 `:169` 的
`rmsNormE_lipschitz`（松弛版 `2√n/c`）经**全库 `.Contains` 扫描**确认
**唯一出现处即其自身声明行**（`:169`），且其证明体（原 `:172`）调用的
`RealNormLipschitz.rmsNorm_lipschitz` 在本文件中的**唯一**使用点也是该处
⟹ **三层套娃纯死链**：
  · ① 顶层 `rmsNormE_lipschitz`（`2√n/c`）—— 0 消费者（本次删除）；
  · ② 中层 `RealNormLipschitz.rmsNorm_lipschitz`（`2√n/c`）—— **保留**，见下；
  · ③ 底层 `RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`（**紧** `√n/c`）—— 主干采用。
**删除理由**：紧版早已被主干采用且**严格更强**（因子 2），松弛版无任何下游；
按 STYLE §5.3「常数收紧不删旧版」的精神，被删者在本文件内**无保留价值**
（其"旧版"角色已由 `RealNormLipschitz.rmsNorm_lipschitz` 自身承担）。
**未删 ②**：`RealNormLipschitz` 是 `RealNormSharpConstant` / `RealRMSNormSharpness`
的**依赖基底**（`RealNormLipschitz.lean:1` 仅 `import Mathlib`），反向引用会**成环**；
且 S12 已标注"删 `:98` 需先核 import 方向"，S7 曾判定其为循环依赖下的**正确自足基底**。
本文件对 ② 的依赖**仍然存在**且不可删：`constOne`（此处 `ctr_eq`）、
`center_norm_le`（`ctr_norm_le`）、`center_lipschitz`（`ctr_lipschitz`）均来自该文件
⟹ **`import RealNormLipschitz` 必须保留**。 -/

/-- RMSNorm 换号：RMSNorm(−x) = −RMSNorm(x)。 -/
lemma rmsNormE_neg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    rmsNormE (-x) = -rmsNormE x := by
  unfold rmsNormE
  rw [norm_neg, smul_neg, smul_neg]

/-- ‖x‖ = c 时 ‖RMSNorm(x)‖ = √n。 -/
lemma norm_rmsNormE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) : ‖rmsNormE x‖ = Real.sqrt n := by
  have hxpos : 0 < ‖x‖ := by rw [hx]; exact hc
  unfold rmsNormE
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n)]
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (le_of_lt hxpos)), hx, one_div,
    inv_mul_cancel₀ (ne_of_gt hc), mul_one]

/-- 取等点对 (x, −x)：‖RMSNorm(x) − RMSNorm(−x)‖ = 2√n。 -/
lemma rmsNormE_antipodal_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormE x - rmsNormE (-x)‖ = 2 * Real.sqrt n := by
  rw [rmsNormE_neg]
  have hsub : rmsNormE x - -rmsNormE x = (2 : ℝ) • rmsNormE x := by
    rw [sub_neg_eq_add, two_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, norm_rmsNormE x c hc hx]
  norm_num

/-- 取等点对给出 RMSNorm 常数的下界：任何有效 K 满足 K ≥ √n/c。 -/
theorem rmsNorm_constant_lower_bound {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c K : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c)
    (hK : ∀ y : EuclideanSpace ℝ (Fin n), ‖rmsNormE x - rmsNormE y‖ ≤ K * ‖x - y‖) :
    Real.sqrt n / c ≤ K := by
  have h := hK (-x)
  have h2 : ‖x - (-x)‖ = 2 * c := by
    have hsub : x - (-x) = (2 : ℝ) • x := by rw [sub_neg_eq_add, two_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, hx]
    norm_num
  rw [rmsNormE_antipodal_norm x c hc hx, h2] at h
  rw [div_le_iff₀ hc]
  nlinarith [h]

/-- (2√n/c) 界在取等点对上是严格的（n > 0）：2√n < 4√n，
    故 RMSNorm 的 2√n/c 不是紧界（真常数 ≤ √n/c）。 -/
theorem rmsNorm_two_sqrt_not_attained {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) (hn : 0 < n) :
    ‖rmsNormE x - rmsNormE (-x)‖ < (2 * Real.sqrt n / c) * ‖x - (-x)‖ := by
  have h2 : ‖x - (-x)‖ = 2 * c := by
    have hsub : x - (-x) = (2 : ℝ) • x := by rw [sub_neg_eq_add, two_smul]
    rw [hsub, norm_smul, Real.norm_eq_abs, hx]
    norm_num
  rw [rmsNormE_antipodal_norm x c hc hx, h2]
  have hval : (2 * Real.sqrt n / c) * (2 * c) = 4 * Real.sqrt n := by
    field_simp [ne_of_gt hc]; ring
  rw [hval]
  have hpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  linarith

/-! ## 中心化映射是正交投影（1-Lipschitz 且紧） -/

/-- 中心化（在 EuclideanSpace 上，坐标形式）。 -/
def ctr {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  fun i => z i - (∑ j : Fin n, z j) / (n : ℝ)

/-- ctr 与 RealNormLipschitz 中的表达形式一致。 -/
lemma ctr_eq {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ctr z = z - ((∑ i : Fin n, z i) / (n : ℝ)) • (constOne : EuclideanSpace ℝ (Fin n)) := by
  funext i
  simp [ctr, constOne]

/-- 中心化输出的坐标和为零（等价的零均值）。 -/
lemma sum_ctr_eq_zero {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n, ctr z i = 0 := by
  simp only [ctr]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases hn : (n : ℝ) = 0
  · have hn0 : n = 0 := by exact_mod_cast hn
    subst hn0
    simp
  · field_simp [hn]

/-- ctr 与常向量正交（正交投影的刻画）。 -/
lemma inner_ctr_constOne {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    inner (ctr z) (constOne : EuclideanSpace ℝ (Fin n)) = (0 : ℝ) := by
  have h1 : inner (ctr z) (constOne : EuclideanSpace ℝ (Fin n)) = ∑ i : Fin n, ctr z i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.dotProduct, constOne]
  rw [h1, sum_ctr_eq_zero z]

/-- 零均值向量是 ctr 的不动点。 -/
lemma ctr_fixes {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (h : (∑ i : Fin n, z i) / (n : ℝ) = 0) : ctr z = z := by
  funext i
  simp [ctr, h]

/-- ctr 幂等（投影的核心性质）。 -/
lemma ctr_idempotent {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ctr (ctr z) = ctr z := by
  funext i
  show ctr z i - (∑ j : Fin n, ctr z j) / (n : ℝ) = ctr z i
  rw [sum_ctr_eq_zero z, zero_div, sub_zero]

/-- ctr 不增范数（正交投影的收缩性）。 -/
lemma ctr_norm_le {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ‖ctr z‖ ≤ ‖z‖ := by
  rw [ctr_eq]
  exact center_norm_le z

/-- ctr 是 1-Lipschitz。 -/
lemma ctr_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ‖ctr x - ctr y‖ ≤ ‖x - y‖ := by
  rw [ctr_eq x, ctr_eq y]
  exact center_lipschitz x y

/-- **中心化映射是正交投影**：幂等、正交于常向量、零均值超平面上恒等、
    1-Lipschitz 且不增范数。 -/
theorem center_map_is_projection (n : ℕ) :
    (∀ z : EuclideanSpace ℝ (Fin n), ctr (ctr z) = ctr z) ∧
    (∀ z : EuclideanSpace ℝ (Fin n),
      inner (ctr z) (constOne : EuclideanSpace ℝ (Fin n)) = (0 : ℝ)) ∧
    (∀ z : EuclideanSpace ℝ (Fin n),
      (∑ i : Fin n, z i) / (n : ℝ) = 0 → ctr z = z) ∧
    (∀ z : EuclideanSpace ℝ (Fin n), ‖ctr z‖ ≤ ‖z‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), ‖ctr x - ctr y‖ ≤ ‖x - y‖) :=
  ⟨fun z => ctr_idempotent z,
   fun z => inner_ctr_constOne z,
   fun z h => ctr_fixes z h,
   fun z => ctr_norm_le z,
   fun x y => ctr_lipschitz x y⟩

/-- 1-常数是**紧的**：在零均值超平面上 ctr 是恒等，故任意两个超平面向量
    使 ‖ctr x − ctr y‖ = 1·‖x − y‖ 取等。 -/
theorem center_lipschitz_sharp {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (hx : (∑ i : Fin n, x i) / (n : ℝ) = 0)
    (hy : (∑ i : Fin n, y i) / (n : ℝ) = 0) :
    ‖ctr x - ctr y‖ = 1 * ‖x - y‖ := by
  rw [ctr_fixes x hx, ctr_fixes y hy, one_mul]

/-- 中心化 Lipschitz 常数的下界：超平面上任意两个不同点给出 K ≥ 1。 -/
theorem center_lipschitz_constant_optimal {n : ℕ} (x y : EuclideanSpace ℝ (Fin n))
    (hx : (∑ i : Fin n, x i) / (n : ℝ) = 0)
    (hy : (∑ i : Fin n, y i) / (n : ℝ) = 0) (K : ℝ)
    (hK : ‖ctr x - ctr y‖ ≤ K * ‖x - y‖) (hxy : x ≠ y) :
    1 ≤ K := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have heq : ‖ctr x - ctr y‖ = ‖x - y‖ := by
    rw [ctr_fixes x hx, ctr_fixes y hy]
  rw [heq] at hK
  have hdiv : ‖x - y‖ / ‖x - y‖ ≤ K := (div_le_iff₀ hd).mpr hK
  rwa [div_self (ne_of_gt hd)] at hdiv

end Lattice
