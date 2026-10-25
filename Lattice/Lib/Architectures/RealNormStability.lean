import Mathlib

/-!
# LATTICE: 归一化的数值稳定性 —— 安全归一化（分母加 ε）的界与 Lipschitz

归一化层在实现中必须处理 `‖x‖ = 0` 的退化（`x/‖x‖` 未定义）与浮点下溢。
工程标准做法是**安全归一化**：把分母写成 `‖x‖ + ε`（ε > 0 为稳定化常数）：

    safeNormalize ε x = (‖x‖ + ε)⁻¹ • x

本文件建立其可直接引用的性质：

  1. `safe_normalize_zero`：`safeNormalize ε 0 = 0`（退化输入有定义，不再除零）；
  2. `safe_normalize_norm`（精确式）：`0 < ε` ⟹ `‖safeNormalize ε x‖ = ‖x‖ / (‖x‖ + ε)`；
  3. `safe_normalize_bound`：`0 < ε` ⟹ `‖safeNormalize ε x‖ ≤ 1`（**永不放大**）；
  4. `safe_normalize_sub_decomp`：差分解 `f x − f y = a⁻¹•(x−y) + (a⁻¹ − b⁻¹)•y`（`a = ‖x‖+ε`、`b = ‖y‖+ε`）；
  5. `safe_normalize_lipschitz_on`：在半径 `R` 的球内，Lipschitz 常数 `(R + ε)/ε²`（**有限**）；
  6. `variance_floor_nonneg`：方差非负 + ε > 0 ⟹ 方差加 ε 后严格正（可开方）。

**诚实边界**：
- 不建模浮点舍入的逐位语义（那属 `RealFloatFormat` 的舍入算子公理）；本文件只给"分母加 ε"这一
  **算法级**稳定化的数学性质；
- 未做 ε → 0 的极限（`x/‖x‖` 的收敛）——需 Filter 与 `x ≠ 0` 的邻域论证，标注为后续；
- 与真实归一化的对比：`x ↦ x/‖x‖` 在原点附近**无**有限 Lipschitz 常数
  （`RealNormSharpConstant` 给的是 `c ≤ ‖x‖` 条件下的紧常数 `1/c`），安全归一化用 ε 换取全局有界；
- 球内 Lipschitz 常数 `(R+ε)/ε²` 是**充分**上界（未声称紧）；
- 模型无关：任意实赋范空间 `E`。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 定义：安全归一化 -/

/-- 安全归一化：`x ↦ (‖x‖ + ε)⁻¹ • x`（分母加稳定化常数 ε，零输入有定义）。 -/
def safeNormalize (ε : ℝ) (x : E) : E := (‖x‖ + ε)⁻¹ • x

/-! ## 基础性质 -/

/-- 零输入：`safeNormalize ε 0 = 0`（不再出现 0/0）。 -/
lemma safe_normalize_zero (ε : ℝ) : safeNormalize ε (0 : E) = 0 := by
  unfold safeNormalize
  simp

omit [NormedSpace ℝ E] in
/-- 分母下界：`ε ≤ ‖x‖ + ε`（稳定性的来源）。 -/
lemma safe_normalize_denom_ge (ε : ℝ) (x : E) : ε ≤ ‖x‖ + ε := by
  linarith [norm_nonneg x]

/-- 分母严格正：`0 < ε` ⟹ `0 < ‖x‖ + ε`。 -/
lemma safe_normalize_denom_pos (ε : ℝ) (x : E) (hε : 0 < ε) : 0 < ‖x‖ + ε :=
  lt_of_lt_of_le hε (safe_normalize_denom_ge ε x)

/-! ## 定理一：范数的精确式 -/

/-- `0 < ε` ⟹ `‖safeNormalize ε x‖ = ‖x‖ / (‖x‖ + ε)`。 -/
theorem safe_normalize_norm (ε : ℝ) (x : E) (hε : 0 < ε) :
    ‖safeNormalize ε x‖ = ‖x‖ / (‖x‖ + ε) := by
  unfold safeNormalize
  rw [norm_smul, Real.norm_eq_abs]
  have hd : 0 < ‖x‖ + ε := safe_normalize_denom_pos ε x hε
  rw [abs_of_pos (inv_pos.mpr hd), inv_mul_eq_div]

/-! ## 定理二：永不放大 -/

/-- `0 < ε` ⟹ `‖safeNormalize ε x‖ ≤ 1`（输出落在单位球内）。 -/
theorem safe_normalize_bound (ε : ℝ) (x : E) (hε : 0 < ε) : ‖safeNormalize ε x‖ ≤ 1 := by
  rw [safe_normalize_norm ε x hε, div_le_one (safe_normalize_denom_pos ε x hε)]
  linarith [norm_nonneg x]

/-! ## 定理三：差的分解与 Lipschitz 界 -/

/-- **差的分解**：`f x − f y = a⁻¹•(x − y) + (a⁻¹ − b⁻¹)•y`，`a = ‖x‖+ε`、`b = ‖y‖+ε`。
（把它拆成"平行分量 + 径向修正"两项，分别可控。） -/
lemma safe_normalize_sub_decomp (ε : ℝ) (x y : E) :
    safeNormalize ε x - safeNormalize ε y
      = (‖x‖ + ε)⁻¹ • (x - y) + ((‖x‖ + ε)⁻¹ - (‖y‖ + ε)⁻¹) • y := by
  unfold safeNormalize
  rw [smul_sub, sub_smul]
  abel

/-- 倒数差的代数式：`a⁻¹ − b⁻¹ = (b − a)/(a·b)`（a, b ≠ 0）。 -/
lemma inv_sub_inv_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  field_simp

/-- 径向修正项的界：`|a⁻¹ − b⁻¹| ≤ ‖x − y‖ / ε²`（`a = ‖x‖+ε`、`b = ‖y‖+ε`、`0 < ε`）。 -/
lemma safe_normalize_radial_bound (ε : ℝ) (x y : E) (hε : 0 < ε) :
    |(‖x‖ + ε)⁻¹ - (‖y‖ + ε)⁻¹| ≤ ‖x - y‖ / ε ^ 2 := by
  have ha : 0 < ‖x‖ + ε := safe_normalize_denom_pos ε x hε
  have hb : 0 < ‖y‖ + ε := safe_normalize_denom_pos ε y hε
  have hprod : ε ^ 2 ≤ (‖x‖ + ε) * (‖y‖ + ε) := by
    have hxa : ε ≤ ‖x‖ + ε := safe_normalize_denom_ge ε x
    have hyb : ε ≤ ‖y‖ + ε := safe_normalize_denom_ge ε y
    calc ε ^ 2 = ε * ε := by ring
      _ ≤ (‖x‖ + ε) * (‖y‖ + ε) := mul_le_mul hxa hyb hε.le ha.le
  have hnum : |(‖y‖ + ε) - (‖x‖ + ε)| = |‖y‖ - ‖x‖| := by ring_nf
  have hnorm : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le x y
  rw [inv_sub_inv_eq (ne_of_gt ha) (ne_of_gt hb), abs_div, abs_of_pos (mul_pos ha hb), hnum]
  calc |‖y‖ - ‖x‖| / ((‖x‖ + ε) * (‖y‖ + ε))
      ≤ ‖x - y‖ / ((‖x‖ + ε) * (‖y‖ + ε)) := by
        exact div_le_div_of_nonneg_right hnorm (mul_pos ha hb).le
    _ ≤ ‖x - y‖ / ε ^ 2 := by
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε 2) hprod

/-- **球内 Lipschitz 界**：`‖x‖ ≤ R`、`‖y‖ ≤ R`、`0 ≤ R`、`0 < ε` ⟹
`‖safeNormalize ε x − safeNormalize ε y‖ ≤ ((R + ε)/ε²)·‖x − y‖`。 -/
theorem safe_normalize_lipschitz_on (ε R : ℝ) (hε : 0 < ε) (_hR : 0 ≤ R) (x y : E)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖safeNormalize ε x - safeNormalize ε y‖ ≤ ((R + ε) / ε ^ 2) * ‖x - y‖ := by
  have ha : 0 < ‖x‖ + ε := safe_normalize_denom_pos ε x hε
  have hterm1 : ‖(‖x‖ + ε)⁻¹ • (x - y)‖ ≤ ε⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    have hle : (‖x‖ + ε)⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ ha hε).mpr (safe_normalize_denom_ge ε x)
    exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hterm2 : ‖((‖x‖ + ε)⁻¹ - (‖y‖ + ε)⁻¹) • y‖ ≤ (‖x - y‖ / ε ^ 2) * R := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (safe_normalize_radial_bound ε x y hε) hy (norm_nonneg y)
      (div_nonneg (norm_nonneg _) (pow_pos hε 2).le)
  calc ‖safeNormalize ε x - safeNormalize ε y‖
      = ‖(‖x‖ + ε)⁻¹ • (x - y) + ((‖x‖ + ε)⁻¹ - (‖y‖ + ε)⁻¹) • y‖ := by
          rw [safe_normalize_sub_decomp]
    _ ≤ ‖(‖x‖ + ε)⁻¹ • (x - y)‖ + ‖((‖x‖ + ε)⁻¹ - (‖y‖ + ε)⁻¹) • y‖ := norm_add_le _ _
    _ ≤ ε⁻¹ * ‖x - y‖ + (‖x - y‖ / ε ^ 2) * R := add_le_add hterm1 hterm2
    _ = ((R + ε) / ε ^ 2) * ‖x - y‖ := by
          field_simp
          ring

/-! ## 定理四：方差下限（Batchnorm 型稳定化） -/

/-- 方差非负 + ε > 0 ⟹ 方差加 ε 后严格正（`sqrt(var + ε)` 有定义且非零）。 -/
lemma variance_floor_nonneg (ε v : ℝ) (hε : 0 < ε) (hv : 0 ≤ v) : 0 < v + ε := by
  linarith

end Lattice
