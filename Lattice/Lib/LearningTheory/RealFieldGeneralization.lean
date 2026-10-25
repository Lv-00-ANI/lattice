import Mathlib
import Lattice.Lib.LinearAlgebra.RealInnerScalar
import Lattice.Lib.Optim.RealGradDescent
import Lattice.Lib.Convex.RealConvexToolkit
/-!
# LATTICE: 𝕜 泛化样本 —— 把 ℝ-专用结论抬到 `RCLike 𝕜` / 任意域

**本文件是「如何把新模块泛化」的范式文件**：既有 `Real*` 系列里大量结论其实是
「任意 `RCLike 𝕜`（ℝ/ℂ）上的内积空间事实」或「任意 `NontriviallyNormedField 𝕜` 上的
分析事实」，把它们在 `RCLike 𝕜` 下重述/实例化即可自动覆盖 ℝ 与 ℂ。

范式分三种：

  1. **回收（mathlib 已是 `RCLike 𝕜` 通用）**：`gen_norm_sq_eq_re_inner`、
     `gen_inner_self_re_nonneg`、`gen_cauchy_schwarz`、`gen_parallelogram` —— 一行调用
     mathlib 的 `RCLike 𝕜` 版本；
  2. **实例化（既有 LATTICE 文件已是 𝕜-通用）**：`gen_isometry_preserves_norm`
     复用 `RealInnerScalar.isometry_preserves_norm_scalar`；
     `gen_GD_contraction_step` 复用 `RealGradDescent.GD_contraction_step`——
     `RealComplexGD`/`RealComplex.lean` 已用 `(𝕜 := ℂ)` 做过同样的实例化；
  3. **不可泛化（诚实边界）**：`RealConvexToolkit` 的 Gibbs/log 族依赖 ℝ 的全序与
     `Real.log`，**不能**抬到 ℂ —— 已在文末标注，不含定理。

**诚实标注（降级/未做）**：
- 本文件不复制任何既有证明（`RealInnerScalar`/`RealGradDescent` 的证明只在原文件），
  只做一行实例化或调用 mathlib；
- **未做**：把 `RealNormalEquation` 的 `fderiv` 法方程抬到 `RCLike 𝕜`——
  需要 ℝ-值损失在 𝕜-内积空间上的 `fderiv ℝ` 计算（ℝ-模结构 `IsScalarTower ℝ 𝕜 E` 的
  相容性），超出本文件范围，标注未做；
- **未做**：`RealConvexToolkit` 的凸性/log 族泛化（依赖 ℝ 序，见文末说明）。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

namespace Lattice

/-! mathlib 4.14 中 `⟪x, y⟫` 只在 ℝ/ℂ 有裸记法；对任意 `RCLike 𝕜` 需显式
`@inner 𝕜 E _`。**本文件不用 `local notation`**：记法的 `𝕜` 会在定理自身 `{𝕜 E}`
绑定之前被解析，导致类型类卡在元变量上（`RCLike ?m` / `Norm ?m` / `Inner 𝕜✝ E`）——
故直接写全 `@inner 𝕜 E _`，这是 STYLE.md「`inner` 无类型上下文时类型类卡死」一条的本文件解法。 -/

/-! ## 第一节：回收 —— mathlib 的 `RCLike 𝕜` 通用内积事实 -/

/-- **范数平方恒等式**（任意 `RCLike 𝕜`）：`‖x‖² = re⟪x, x⟫`
（`RealInnerScalar.inner_self_norm_sq_scalar` 的同款命题；此处直接回收 mathlib
`inner_self_eq_norm_sq`，它本身已是 `RCLike 𝕜` 通用、方向为 `re⟪x,x⟫ = ‖x‖^2`）。 -/
theorem gen_norm_sq_eq_re_inner {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
    ‖x‖ ^ 2 = RCLike.re (@inner 𝕜 E _ x x) :=
  (inner_self_eq_norm_sq (𝕜 := 𝕜) x).symm

/-- **自内积实部非负**（任意 `RCLike 𝕜`）。 -/
theorem gen_inner_self_re_nonneg {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
    0 ≤ RCLike.re (@inner 𝕜 E _ x x) :=
  inner_self_nonneg (𝕜 := 𝕜) (x := x)

/-- **Cauchy–Schwarz 不等式**（任意 `RCLike 𝕜`，复数域下为内积的复模界）：
`‖⟪x, y⟫‖ ≤ ‖x‖·‖y‖`（回收 mathlib `norm_inner_le_norm`，它已是 `RCLike 𝕜` 通用）。 -/
theorem gen_cauchy_schwarz {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖@inner 𝕜 E _ x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm (𝕜 := 𝕜) x y

/-- **平行四边形恒等式**（任意 `RCLike 𝕜`）：`‖x+y‖² + ‖x−y‖² = 2(‖x‖² + ‖y‖²)`
（回收 mathlib `parallelogram_law_with_norm`；mathlib 用 `*` 书写平方）。 -/
theorem gen_parallelogram {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := parallelogram_law_with_norm (𝕜 := 𝕜) x y
  simpa [sq, mul_add] using h

/-! ## 第二节：实例化 —— 既有 𝕜-通用 LATTICE 定理的展开 -/

/-- **等距保范数（𝕜 版实例）**：保 `𝕜`-内积的映射保范数。
一行实例化 `RealInnerScalar.isometry_preserves_norm_scalar`——
这正是「既有文件在 `RCLike 𝕜` 下陈述 ⟹ ℂ/ℝ 自动获得」的范式。 -/
theorem gen_isometry_preserves_norm {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E → E)
    (hT : ∀ q k : E, @inner 𝕜 E _ (T q) (T k) = @inner 𝕜 E _ q k) :
    ∀ x : E, ‖T x‖ = ‖x‖ :=
  isometry_preserves_norm_scalar (𝕜 := 𝕜) T (fun q k => hT q k)

/-- **梯度下降单步收缩（𝕜 版实例）**：谱界 `‖1 − 2η·A∘A†‖ ≤ c` ⟹
`‖A·x' − b‖ ≤ c·‖A·x − b‖`。
一行实例化 `RealGradDescent.GD_contraction_step`；`RealComplexGD.complex_GD_contraction_step`
是同一个定理在 `𝕜 := ℂ` 的实例化，本定理说明其对**任意** `RCLike 𝕜` 成立。 -/
theorem gen_GD_contraction_step {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
    (A : E →L[𝕜] F) (b : F) (eta : ℝ) (x : E) (c : ℝ)
    (hspec : ‖(1 : F →L[𝕜] F) - (2 * eta : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate A b eta x) - b‖ ≤ c * ‖A x - b‖ :=
  GD_contraction_step A b eta x c hspec

/-- **ℝ 实例**（`𝕜 := ℝ`，即 `RealGradDescent` 本身的领域）。 -/
theorem gen_GD_contraction_step_real {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →L[ℝ] F) (b : F) (eta : ℝ) (x : E) (c : ℝ)
    (hspec : ‖(1 : F →L[ℝ] F) - (2 * eta : ℝ) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate (𝕜 := ℝ) A b eta x) - b‖ ≤ c * ‖A x - b‖ :=
  gen_GD_contraction_step (𝕜 := ℝ) A b eta x c hspec

/-- **ℂ 实例**（`𝕜 := ℂ`，与 `RealComplexGD.complex_GD_contraction_step` 一致）。 -/
theorem gen_GD_contraction_step_complex {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    (A : E →L[ℂ] F) (b : F) (eta : ℝ) (x : E) (c : ℝ)
    (hspec : ‖(1 : F →L[ℂ] F) - (2 * eta : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate (𝕜 := ℂ) A b eta x) - b‖ ≤ c * ‖A x - b‖ :=
  gen_GD_contraction_step (𝕜 := ℂ) A b eta x c hspec

/-! ## 第三节：不可泛化边界（诚实标注，无定理）

`RealConvexToolkit` 的三条内核（`gibbs_ineq`、`log_concave_pair`、`mul_log_convex_pair`）
**不能**抬到 `RCLike 𝕜`：

- 它们的陈述依赖 `≤`（ℝ 的全序）与 `Real.log`；
- `ℂ` 上没有与 `Real.log` 相容的全序，`RCLike 𝕜` 只提供到 ℝ 的投影 `RCLike.re`，
  log 族无法在其上重述；
- 因此这类结论的泛化范围是 `𝕜 = ℝ` 的**实分析层**，而非数域层 —— 这是「哪些能泛化、
  哪些不能」的**边界样本**，与 `NAMING.md`/`REFACTOR.md` 的诚实性要求一致。

同样**未做**（需额外基础设施）：`RealNormalEquation` 的 `fderiv` 法方程在 `RCLike 𝕜` 上的
版本（ℝ-值损失 + ℝ-模结构的相容性桥接）。
-/

end Lattice
