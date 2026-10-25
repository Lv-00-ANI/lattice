import Mathlib
import Lattice.Lib.Optim.RealGradDescent
import Lattice.Lib.Chain.RealComplex
/-!
# LATTICE: ℂ 上的梯度下降收敛（§5 数域行·优化线）

把 RealGradDescent 的梯度下降收敛**在 ℂ 上实例化**（𝕜 := ℂ）。
RealGradDescent 的全部定理都在任意 `RCLike 𝕜` 内积空间上陈述，
ℂ 是 mathlib 的 `RCLike` 实例，故所有定理在 ℂ 上自动成立。
本文件把它们展开成 ℂ 实例定理，并给具体空间 `EuclideanSpace ℂ (Fin d)` 做实例：

  1. `complex_GD_error_identity`：A·x' − b = (1 − (2η)·A∘A†)(A·x − b)（ℂ 版）；
  2. `complex_GD_contraction_step`：谱界 ⟹ ‖A·x' − b‖ ≤ c·‖A·x − b‖；
  3. `complex_GD_converges`（核心）：0 ≤ c < 1 谱界 ⟹ ∀ ε > 0, ∃ n, 误差 < ε；
  4. `complex_euclid_GD_converges`：具体空间 `EuclideanSpace ℂ (Fin d)` 上的版本；
  5. `complex_GD_matches_real`：把 ℂ 上的一步梯度下降与 ℝ² 上的独立梯度下降对齐
     （`toPair (cgd eta g z) = realGDSq eta (toPairMap g) (toPair z)`）——已在
     `RealComplexWirtinger.complex_GD_matches_real` 中形式化（本文件不重复；
     见文末注释的沿革说明）。

诚实性：全部定理是一行实例化（`GD_* (𝕜 := ℂ) ...`），无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-! ## 定理一：ℂ 版误差恒等式
A·x' − b = (1 − (2η)·A∘A†)(A·x − b)（RealGradDescent.GD_error_identity 的 ℂ 实例）。-/

theorem complex_GD_error_identity (A : E →L[ℂ] F) (b : F) (η : ℝ) (x : E) :
    A (GDUpdate (𝕜 := ℂ) A b η x) - b =
      ((1 : F →L[ℂ] F) - (2 * η : ℂ) • (A ∘L A.adjoint)) (A x - b) :=
  GD_error_identity (𝕜 := ℂ) A b η x

/-! ## 定理二：ℂ 版单步收缩
谱界 ‖1 − (2η)·A∘A†‖ ≤ c ⟹ ‖A·x' − b‖ ≤ c·‖A·x − b‖（`GD_contraction_step` 的 ℂ 实例）。-/

theorem complex_GD_contraction_step (A : E →L[ℂ] F) (b : F) (η : ℝ) (x : E) (c : ℝ)
    (hspec : ‖(1 : F →L[ℂ] F) - (2 * η : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate (𝕜 := ℂ) A b η x) - b‖ ≤ c * ‖A x - b‖ :=
  GD_contraction_step (𝕜 := ℂ) A b η x c hspec

/-! ## 定理三：ℂ 版单步平方收缩
‖A·x' − b‖² ≤ c²·‖A·x − b‖²（`GD_sq_contraction_step` 的 ℂ 实例）。-/

theorem complex_GD_sq_contraction_step (A : E →L[ℂ] F) (b : F) (η : ℝ) (x : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hspec : ‖(1 : F →L[ℂ] F) - (2 * η : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (GDUpdate (𝕜 := ℂ) A b η x) - b‖ ^ 2 ≤ c ^ 2 * ‖A x - b‖ ^ 2 :=
  GD_sq_contraction_step (𝕜 := ℂ) A b η x c hc0 hspec

/-! ## 定理四（核心）：ℂ 版梯度下降收敛（ε-终止）
0 ≤ c < 1 谱界 ⟹ ∀ ε > 0，∃ n，误差 < ε（`GD_converges` 的 ℂ 实例，
底层接 RealConvergence 的收缩收敛骨架）。-/

theorem complex_GD_converges (A : E →L[ℂ] F) (b : F) (η : ℝ) (x0 : E) (c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ∀ x : E, ‖(1 : F →L[ℂ] F) - (2 * η : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, GDError (𝕜 := ℂ) A b η x0 n < ε :=
  GD_converges (𝕜 := ℂ) A b η x0 c hc0 hc1 hspec

/-! ## 推论：ℂ 版迭代收缩（每步误差平方收缩 c²）。-/

theorem complex_GD_iterate_contraction (A : E →L[ℂ] F) (b : F) (η : ℝ) (x0 : E) (c : ℝ)
    (hc0 : 0 ≤ c)
    (hspec : ∀ x : E, ‖(1 : F →L[ℂ] F) - (2 * η : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ∀ n : ℕ, GDError (𝕜 := ℂ) A b η x0 (n + 1) ≤ c ^ 2 * GDError (𝕜 := ℂ) A b η x0 n :=
  GD_iterate_contraction (𝕜 := ℂ) A b η x0 c hc0 hspec

/-! ## 定理五（加分）：具体空间 `EuclideanSpace ℂ (Fin d)` 上的收敛 -/

theorem complex_euclid_GD_converges (d : ℕ)
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (b x0 : EuclideanSpace ℂ (Fin d)) (η c : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hspec : ∀ x : EuclideanSpace ℂ (Fin d),
      ‖(1 : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) -
        (2 * η : ℂ) • (A ∘L A.adjoint)‖ ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, GDError (𝕜 := ℂ) A b η x0 n < ε :=
  complex_GD_converges A b η x0 c hc0 hc1 hspec

/-! ## 定理六（加分）：具体空间 `EuclideanSpace ℂ (Fin d)` 上的误差恒等式 -/

theorem complex_euclid_GD_error_identity (d : ℕ)
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (b x : EuclideanSpace ℂ (Fin d)) (η : ℝ) :
    A (GDUpdate (𝕜 := ℂ) A b η x) - b =
      ((1 : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) -
        (2 * η : ℂ) • (A ∘L A.adjoint)) (A x - b) :=
  complex_GD_error_identity A b η x

/-! ## 注：`complex_GD_matches_real`（本文件未做，已在别处形式化）
命题「若 A、b 是实矩阵/实向量的复化，则 ℂ 版 GD 的误差与 ℝ 版一致」在本文件中**未形式化**。

**历史沿革（已否证 / 已补齐）**：本文件曾以「本库尚无此定理」框定该缺口；该结论已被否证——
`RealComplexWirtinger.complex_GD_matches_real`（见其 `toPair`、`ofPair`、`toPairMap`、`realGDSq`、
`cgd` 的定义处）现已形式化。需注意其陈述是 `toPair (cgd eta g z) = realGDSq eta (toPairMap g) (toPair z)`，
即「ℂ 上的一步下降在实部/虚部上等于 ℝ² 上的两步独立下降」；这比此处原先「误差一致」的措辞更窄。

原因（针对一般复化，仍然成立）：mathlib 4.14 没有现成的「实向量空间复化」函子（`E ↦ ℂ ⊗[ℝ] E`）与其到
`InnerProductSpace ℂ` 的相容性基础设施；要陈述一般复化的版本必须先建复化空间、
复线性算子的复化、以及伴随在复化下与实伴随的交换律（`(A_ℂ)† = (A†)_ℂ`），
远超本文件的实例化范围。这里保留为后续工作，而不是用一个不可证/含糊的陈述充数。

一个**部分**可陈述的事实是：ℂ 版链的每个定理都是 ℝ 版同一算子的逐字实例化
（`GD_* (𝕜 := ℂ)`），故在 ℂ 自身上（E = F = ℂ，A = 实标量乘）两版退化一致——
但一般复化的等式仍缺基础设施。 -/

end Lattice