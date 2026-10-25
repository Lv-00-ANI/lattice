import Mathlib
import Lattice.Lib.Chain.RealComplexTrain
/-!
# LATTICE: Wirtinger 微积分 —— 实可微性与 `∂f/∂z`、`∂f/∂z̄`

补两个缺口的出处各不相同：
`RealComplexGD.lean` 文末明确标注「未形式化」的 `complex_GD_matches_real`
（ℂ 上一步 GD = ℝ² 上两步独立 GD），
以及 `RealComplexTrain.lean` 标注「未做」的 Wirtinger 微积分结构。

对 `f : ℂ → ℂ` 与 `z : ℂ`，`fderiv ℝ f z : ℂ →L[ℝ] ℂ` 是实 Fréchet 导数（ℝ-线性）。定义

    wirtingerZ    f z = (1/2)·(L 1 − I·L I)
    wirtingerZbar f z = (1/2)·(L 1 + I·L I),      L := fderiv ℝ f z

本文件证明：

  1. `wirtinger_decomposition`（**核心**）：对任意 `w`，
     `L w = wirtingerZ f z · w + wirtingerZbar f z · conj w`
     —— 这就是 Wirtinger 微积分的基本分解，即「ℝ-线性映射 = ℂ-线性部分 + ℂ-反线性部分」；
  2. `complex_cr_iff_wirtinger_zbar_eq_zero`（**Cauchy–Riemann ⟺ 复可微**，一维版本）：
     `∂f/∂z̄ = 0` ⟺ `L` 是某个 ℂ-线性连续映射的实限制（复可微性）；
  3. `complex_GD_matches_real`：ℂ 上的一步梯度下降 `cgd eta g z` 在实部/虚部上
     **恰好等于** ℝ² 上的两步独立梯度下降（复用只读的 `RealComplexTrain.cgd_re`/`cgd_im`）。

**诚实标注（降级/未做）**：
- `ComplexDifferentiableAt` 定义的是「`fderiv ℝ f z` 可写成 ℂ-线性映射的实限制」，
  **而不是**「存在 ℂ-线性 `HasFDerivAt`」。二者在有可微性假设时等价，但本文件不引入
  `HasFDerivAt` 的存在性讨论（`fderiv` 在不可微点退化为 0，本文件直接对 `fderiv` 陈述，
  因此**不需**任何可微性假设），这是**有意的降级**，已在定理 docstring 标注；
- Cauchy–Riemann 的**实偏导形式**（`∂u/∂x = ∂v/∂y`、`∂u/∂y = −∂v/∂x`）**未做**：
  需要把 `fderiv ℝ` 与一元实偏导 `HasPartialDeriv` 逐一桥接，超出本文件范围，标注未做；
- 高维（`f : E → ℂ`）Wirtinger 与全纯函数族的性质（Cauchy 积分、Liouville 等）**未做**；
- 与 `RealComplexGD` 的 `complex_GD_converges` 的衔接未做（那属于优化线）。

无 `sorry`/`axiom`/`admit`。模型无关：任意 `f : ℂ → ℂ`。
-/

noncomputable section

namespace Lattice

open scoped ComplexConjugate

/-! ## 第一节：ℝ-标量与 ℂ-乘法的桥 -/

/-- ℝ-标量乘法与 ℂ-乘法一致：`r • c = (r:ℂ) * c`。
（ℂ 作为 ℝ-向量空间的标量作用就是实数乘。） -/
lemma real_smul_complex_eq_mul (r : ℝ) (c : ℂ) : r • c = (r : ℂ) * c := by
  apply Complex.ext <;>
    simp [Complex.smul_re, Complex.smul_im, Complex.mul_re, Complex.mul_im]

/-- 共轭与 ℝ-标量作用交换：`conj (r • c) = r • conj c`。 -/
lemma conj_real_smul_c (r : ℝ) (c : ℂ) : conj (r • c) = r • conj c := by
  rw [real_smul_complex_eq_mul, real_smul_complex_eq_mul, map_mul, Complex.conj_ofReal]

/-- 基分解：`1` 与 `I` 张成 ℂ 作为 ℝ-向量空间，故 `w = w.re • 1 + w.im • I`。 -/
lemma complex_eq_smul_one_add_smul_I (w : ℂ) :
    w = w.re • (1 : ℂ) + w.im • Complex.I := by
  apply Complex.ext <;> simp [Complex.smul_re, Complex.smul_im]

/-! ## 第二节：Wirtinger 导数的定义 -/

/-- **Wirtinger 导数 `∂f/∂z`**：`(1/2)(L 1 − I·L I)`，`L = fderiv ℝ f z`。 -/
def wirtingerZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)

/-- **Wirtinger 导数 `∂f/∂z̄`**：`(1/2)(L 1 + I·L I)`，`L = fderiv ℝ f z`。 -/
def wirtingerZbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- `∂f/∂z + ∂f/∂z̄ = L 1`。 -/
lemma wirtinger_z_add_zbar (f : ℂ → ℂ) (z : ℂ) :
    wirtingerZ f z + wirtingerZbar f z = fderiv ℝ f z 1 := by
  unfold wirtingerZ wirtingerZbar
  ring

/-- `∂f/∂z − ∂f/∂z̄ = −I·(L I)`。 -/
lemma wirtinger_z_sub_zbar (f : ℂ → ℂ) (z : ℂ) :
    wirtingerZ f z - wirtingerZbar f z = -(Complex.I * fderiv ℝ f z Complex.I) := by
  unfold wirtingerZ wirtingerZbar
  ring

/-- `L I = I·(∂f/∂z − ∂f/∂z̄)`（由上式乘 `I` 并用 `I·I = −1`）。 -/
lemma wirtinger_I_smul_diff (f : ℂ → ℂ) (z : ℂ) :
    Complex.I * (wirtingerZ f z - wirtingerZbar f z) = fderiv ℝ f z Complex.I := by
  rw [wirtinger_z_sub_zbar f z]
  rw [mul_neg, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]

/-! ## 第三节：Wirtinger 基本分解（核心） -/

/-- **Wirtinger 基本分解（参数形式）**：对任意实数 `a b`，
`L (a•1 + b•I) = ∂f/∂z·(a•1+b•I) + ∂f/∂z̄·conj(a•1+b•I)`。

这是核心分解的直接计算形式；证明只用 `L` 的 ℝ-线性性与 `{1, I}` 是 ℂ 的 ℝ-基。 -/
theorem wirtinger_decomposition_pair (f : ℂ → ℂ) (z : ℂ) (a b : ℝ) :
    fderiv ℝ f z (a • (1 : ℂ) + b • Complex.I) =
      wirtingerZ f z * (a • (1 : ℂ) + b • Complex.I)
        + wirtingerZbar f z * conj (a • (1 : ℂ) + b • Complex.I) := by
  rw [map_add, map_smul, map_smul, ← wirtinger_z_add_zbar f z, ← wirtinger_I_smul_diff f z]
  rw [map_add, conj_real_smul_c, conj_real_smul_c, map_one, Complex.conj_I]
  simp only [real_smul_complex_eq_mul]
  ring

/-- **Wirtinger 基本分解**：对任意 `w`，
`fderiv ℝ f z w = ∂f/∂z · w + ∂f/∂z̄ · conj w`。

这是「ℝ-线性映射 = ℂ-线性部分 ⊕ ℂ-反线性部分」的一维版本；证明只用
`fderiv ℝ f z` 的 ℝ-线性性与 `{1, I}` 是 ℂ 的 ℝ-基（`complex_eq_smul_one_add_smul_I`）。 -/
theorem wirtinger_decomposition (f : ℂ → ℂ) (z w : ℂ) :
    fderiv ℝ f z w = wirtingerZ f z * w + wirtingerZbar f z * conj w := by
  have h := wirtinger_decomposition_pair f z w.re w.im
  rwa [← complex_eq_smul_one_add_smul_I w] at h

/-- 应用形式：`fderiv ℝ f z` 在 `1` 与 `I` 上的值决定整个映射（分解的推论）。 -/
theorem wirtinger_decomposition_apply_one (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z 1 = wirtingerZ f z + wirtingerZbar f z :=
  (wirtinger_z_add_zbar f z).symm

/-- `fderiv ℝ f z I = ∂f/∂z·I + ∂f/∂z̄·conj I = I·∂f/∂z − I·∂f/∂z̄`。 -/
theorem wirtinger_decomposition_apply_I (f : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ f z Complex.I =
      wirtingerZ f z * Complex.I + wirtingerZbar f z * conj Complex.I :=
  wirtinger_decomposition f z Complex.I

/-! ## 第四节：Cauchy–Riemann ⟺ 复可微 -/

/-- **复可微性（对 `fderiv` 陈述的版本）**：`fderiv ℝ f z` 是某个 ℂ-线性连续映射的实限制。

诚实标注：这是**降级**后的定义——不讨论 `HasFDerivAt` 的存在性，只问 `fderiv ℝ f z`
这一具体的 ℝ-线性映射是否落在「ℂ-线性映射的实限制」这一子空间里。 -/
def ComplexDifferentiableAt (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ g : ℂ →L[ℂ] ℂ, fderiv ℝ f z = g.restrictScalars ℝ

/-- **Cauchy–Riemann ⟺ 复可微**：`∂f/∂z̄ = 0` ⟺ `fderiv ℝ f z` ℂ-线性（复可微）。

(→) 若 `L = g|_ℝ`（`g` ℂ-线性），则 `L I = g I = I·g 1 = I·L 1`，故
`L 1 + I·L I = L 1 − L 1 = 0`。
(←) 若 `∂f/∂z̄ = 0`，则 `g := ∂f/∂z • 1` 是 ℂ-线性映射且 `g|_ℝ = L`
（由 Wirtinger 分解，反线性项消失）。

诚实标注：本定理对 `fderiv`（而**非** `HasFDerivAt`）陈述，故不需要可微性假设；
这与「存在 ℂ-线性 `HasFDerivAt`」在有可微性时等价，但本文件不形式化该等价（**降级**）。 -/
theorem complex_cr_iff_wirtinger_zbar_eq_zero (f : ℂ → ℂ) (z : ℂ) :
    ComplexDifferentiableAt f z ↔ wirtingerZbar f z = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    -- L I = g I = I * g 1 = I * L 1
    have hLI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
      have hg1 : g 1 = fderiv ℝ f z 1 := by
        have h := congrArg (fun (h : ℂ →L[ℝ] ℂ) => h 1) hg
        exact h.symm
      calc fderiv ℝ f z Complex.I = g Complex.I := by rw [hg]; rfl
        _ = g (Complex.I • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
        _ = Complex.I • g 1 := map_smul g Complex.I 1
        _ = Complex.I * g 1 := by rw [smul_eq_mul]
        _ = Complex.I * fderiv ℝ f z 1 := by rw [hg1]
    unfold wirtingerZbar
    rw [hLI]
    have hII : Complex.I * (Complex.I * fderiv ℝ f z 1) = -fderiv ℝ f z 1 := by
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    rw [hII]
    ring
  · intro hb
    refine ⟨wirtingerZ f z • (1 : ℂ →L[ℂ] ℂ), ?_⟩
    ext w
    change fderiv ℝ f z w = (wirtingerZ f z • (1 : ℂ →L[ℂ] ℂ)) w
    rw [wirtinger_decomposition f z w, hb, zero_mul, add_zero,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]

/-- **复可微 ⟹ `∂f/∂z̄ = 0`**（上定理的 (→) 方向，单独暴露便于复用）。 -/
theorem wirtinger_zbar_eq_zero_of_complex_differentiable {f : ℂ → ℂ} {z : ℂ}
    (h : ComplexDifferentiableAt f z) : wirtingerZbar f z = 0 :=
  (complex_cr_iff_wirtinger_zbar_eq_zero f z).mp h

/-- **`∂f/∂z̄ = 0` ⟹ 复可微**（上定理的 (←) 方向）。 -/
theorem complex_differentiable_of_wirtinger_zbar_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (h : wirtingerZbar f z = 0) : ComplexDifferentiableAt f z :=
  (complex_cr_iff_wirtinger_zbar_eq_zero f z).mpr h

/-- **复可微时导数闭式**：若 `∂f/∂z̄ = 0`，则 `fderiv ℝ f z w = ∂f/∂z · w`
（即实导数是复数乘法）。 -/
theorem complex_differentiable_fderiv_apply {f : ℂ → ℂ} {z : ℂ}
    (h : wirtingerZbar f z = 0) (w : ℂ) :
    fderiv ℝ f z w = wirtingerZ f z * w := by
  rw [wirtinger_decomposition f z w, h, zero_mul, add_zero]

/-! ## 第五节：`complex_GD_matches_real`（补 `RealComplexGD` 未形式化的缺口） -/

/-- ℂ → ℝ×ℝ 的实部/虚部配对。 -/
def toPair (z : ℂ) : ℝ × ℝ := (z.re, z.im)

/-- ℝ×ℝ → ℂ 的重建。 -/
def ofPair (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- `ofPair ∘ toPair = id`（即 `↑re + ↑im·I = z`）。 -/
@[simp] lemma ofPair_toPair (z : ℂ) : ofPair (toPair z) = z :=
  Complex.re_add_im z

/-- `toPair ∘ ofPair = id`。 -/
@[simp] lemma toPair_ofPair (p : ℝ × ℝ) : toPair (ofPair p) = p := by
  apply Prod.ext <;> simp [toPair, ofPair]

/-- 把 ℂ 上的梯度映射 `g` 沿 `toPair`/`ofPair` 搬到 ℝ² 上。 -/
def toPairMap (g : ℂ → ℂ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((g (ofPair p)).re, (g (ofPair p)).im)

/-- ℝ² 上的一步梯度下降（两个坐标**独立**更新）。 -/
def realGDSq (eta : ℝ) (G : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 - eta * (G p).1, p.2 - eta * (G p).2)

/-- **`complex_GD_matches_real`（补缺口）**：ℂ 上的一步梯度下降
`cgd eta g z = z − (eta:ℂ)·g z` 在实部/虚部上恰好是 ℝ² 上的两步独立梯度下降。

证明只复用只读的 `RealComplexTrain.cgd_re` / `cgd_im`——这正是 `RealComplexGD.lean`
文末标注「未形式化」的那条命题。 -/
theorem complex_GD_matches_real (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    toPair (cgd eta g z) = realGDSq eta (toPairMap g) (toPair z) := by
  apply Prod.ext <;>
    simp [toPair, ofPair, toPairMap, realGDSq, cgd_re, cgd_im]

/-- 推论：ℂ-GD 的实部就是 ℝ²-GD 的第一坐标。 -/
theorem complex_GD_matches_real_fst (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    (cgd eta g z).re = z.re - eta * (g z).re :=
  cgd_re eta g z

/-- 推论：ℂ-GD 的虚部就是 ℝ²-GD 的第二坐标。 -/
theorem complex_GD_matches_real_snd (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    (cgd eta g z).im = z.im - eta * (g z).im :=
  cgd_im eta g z

end Lattice
