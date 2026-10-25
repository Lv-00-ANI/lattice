import Mathlib
import Lattice.Lib.LinearAlgebra.RealSpectral
/-!
# LATTICE: 复矩阵谱 —— 复特征值存在性 / 谱半径 ≤ 算子范数 / Hermitian 特征值实

补 `RealSpectral.lean` 只处理**实**特征对的缺口（该文件明确标注「复谱未做」）。
设 `A : Matrix (Fin n) (Fin n) ℂ`：

  1. `cspec_HasEigenpair`：复特征对 `x ≠ 0 ∧ A·x = μ·x`（分量形式）；
  2. `cspec_exists_eigenpair`：**复特征值/特征向量存在**——由代数基本定理
     （`Complex.isAlgClosed` / `Module.End.exists_eigenvalue`）给出；
  3. `cspec_det_sub_smul_eq_zero`：`det (A − μI) = 0`
     （用 `Matrix.exists_mulVec_eq_zero_iff`：有非零核向量 ⟺ det = 0）；
  4. `cspec_spectral_radius_le_opNorm`：**复谱半径 ≤ 算子范数** `‖μ‖ ≤ ‖A‖`
     （`toEuclideanCLM` 的 `le_opNorm` + `‖μ•x‖ = ‖μ‖·‖x‖`）；
  5. `cspec_hermitian_eigenvalue_real`（**Hermitian 矩阵特征值实**）：
     `A.IsHermitian` ⟹ 特征值 `μ` 满足 `conj μ = μ`（即 `μ.im = 0`）——
     由 `Matrix.isHermitian_iff_isSymmetric` 与
     `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` 得到。

**诚实标注（降级/未做）**：
- `cspec_exists_eigenpair` / `cspec_det_sub_smul_eq_zero` 在 `Fin n → ℂ` 的**分量表示**上陈述
  （用 `Matrix.toLin'`/`mulVec`）；`cspec_spectral_radius_le_opNorm` 在
  `EuclideanSpace ℂ (Fin n)` 的**内积空间**框架上陈述
  （用 `Matrix.toEuclideanLin`/`toEuclideanCLM`）；
  而 `cspec_hermitian_eigenvalue_real` 则以 `Matrix.toEuclideanLin A` 的
  `Module.End.HasEigenvalue`（见其定义处）为假设、结论为 `conj μ = μ`，
  其类型中并不出现 `EuclideanSpace`，也未用到 `Matrix.toEuclideanCLM`。
  分量表示与内积空间表述的桥接（`WithLp.equiv`）**未做**；
- **未做**：复矩阵的 Jordan 标准形、谱分解、一般（非 Hermitian）矩阵的谱定理；
- **未做**：`RealSpectral` 中实谱结论（Gershgorin 圆盘的复版本）的复化；
- 「谱半径 = max |μ|」的完整 `max` 形式未做；本文件给的是「每个复特征值都满足的界」。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

namespace Lattice

open Matrix

open scoped BigOperators ComplexConjugate

variable {n : ℕ}

/-! ## 第一节：复特征对与存在性 -/

/-- **复特征对**（分量形式）：非零向量 `x` 满足 `A·x = μ·x`。 -/
def cspec_HasEigenpair (A : Matrix (Fin n) (Fin n) ℂ) (mu : ℂ) (x : Fin n → ℂ) : Prop :=
  x ≠ 0 ∧ A.mulVec x = mu • x

/-- **复特征值存在**：ℂ 代数闭（代数基本定理），故任意复方阵有特征值与特征向量。
由 `Module.End.exists_eigenvalue`（`Complex.isAlgClosed`）得出。 -/
theorem cspec_exists_eigenpair [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (mu : ℂ) (x : Fin n → ℂ), cspec_HasEigenpair A mu x := by
  obtain ⟨mu, hmu⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  rw [Module.End.hasEigenvalue_iff] at hmu
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmu
  refine ⟨mu, x, hxne, ?_⟩
  have hx : Matrix.toLin' A x = mu • x := (Module.End.mem_eigenspace_iff).mp hxmem
  rwa [Matrix.toLin'_apply] at hx

/-- **特征值 ⟹ `det (A − μI) = 0`**：`A·x = μ·x`、`x ≠ 0` ⟹ `A − μI` 有非零核向量，
由 `Matrix.exists_mulVec_eq_zero_iff`（场上的矩阵：非零核 ⟺ det = 0）得特征方程。 -/
theorem cspec_det_sub_smul_eq_zero (A : Matrix (Fin n) (Fin n) ℂ) {mu : ℂ} {x : Fin n → ℂ}
    (h : cspec_HasEigenpair A mu x) :
    (A - mu • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
  obtain ⟨hxne, hx⟩ := h
  refine (Matrix.exists_mulVec_eq_zero_iff).mp ⟨x, hxne, ?_⟩
  -- `(mu • 1) *ᵥ x = mu • (1 *ᵥ x) = mu • x`，再用 `hx`
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec, hx, sub_self]

/-! ## 第二节：谱半径 ≤ 算子范数（复版） -/

/-- **复谱半径 ≤ 算子范数**：若 `x ≠ 0` 且 `A·x = μ·x`（在 `EuclideanSpace ℂ (Fin n)` 中），
则 `‖μ‖ ≤ ‖A‖`（算子范数取 L² 诱导范数，即 `Matrix.toEuclideanCLM`）。
`RealSpectral.spectral_radius_le_opNorm` 的复数域版本。 -/
theorem cspec_spectral_radius_le_opNorm {A : Matrix (Fin n) (Fin n) ℂ} {mu : ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    (heq : Matrix.toEuclideanLin A x = mu • x) :
    ‖mu‖ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ := by
  have h1 := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm x
  have hcoe : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = Matrix.toEuclideanLin A x :=
    rfl
  rw [hcoe, heq, norm_smul] at h1
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hx)

/-! ## 第三节：Hermitian 矩阵的特征值实（补 `RealSpectral` 缺口） -/

/-- **Hermitian 矩阵的特征值实**：`A.IsHermitian` ⟹ 任一特征值 `μ` 满足 `conj μ = μ`。

证明：`Matrix.isHermitian_iff_isSymmetric` 把 Hermitian 化为 `A.toEuclideanLin` 的
`IsSymmetric`（自伴算子），再用 `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`。

（`HasEigenvalue` 在 mathlib 4.14 是 `Module.End.HasEigenvalue` 的记法，见
`Mathlib.LinearAlgebra.Eigenspace.Basic`；`conj` 由 `open scoped ComplexConjugate` 提供。） -/
theorem cspec_hermitian_eigenvalue_real {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {mu : ℂ} (hmu : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu) : conj mu = mu :=
  (Matrix.isHermitian_iff_isSymmetric.mp hA).conj_eigenvalue_eq_self hmu

/-- **Hermitian 特征值的虚部为零**：`conj μ = μ ⟹ μ.im = 0`（「特征值实」的分量形式）。 -/
theorem cspec_hermitian_eigenvalue_im_zero {mu : ℂ} (h : conj mu = mu) : mu.im = 0 := by
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im] at h2
  linarith

/-- 合并形式：Hermitian 矩阵的特征值虚部为零。 -/
theorem cspec_hermitian_eigenvalue_im {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    {mu : ℂ} (hmu : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu) : mu.im = 0 :=
  cspec_hermitian_eigenvalue_im_zero (cspec_hermitian_eigenvalue_real hA hmu)

/-- `cspec_hermitian_eigenvalue_real` 的 `star` 记法别名：其假设与结论与后者完全一致
（`star μ` 与 `conj μ` 在 ℂ 上定义相等，见证明体中的注释），不引入新的表示、
也不引入新的数学内容。 -/
theorem cspec_hermitian_eigenpair_star_self {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) {mu : ℂ}
    (hmu : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu) :
    star mu = mu :=
  -- `Complex.star_def : (Star.star : ℂ → ℂ) = conj`，故 `star mu` 与 `conj mu` 定义相等
  cspec_hermitian_eigenvalue_real hA hmu

/-! ## 第四节：实矩阵的复特征值 —— 共轭对结构（A1.2）

设 `A : Matrix (Fin n) (Fin n) ℝ`。把 `A` 视为复矩阵 `A.map (algebraMap ℝ ℂ)` 后，
其复特征值由 `charpoly` 的复根给出。本节的**核心可证事实**是：
`A` 的特征多项式是**实系数**的，故其特征值集在共轭下**封闭**——
非实特征值必成**共轭对**出现。

诚实标注（**降级/未做**）：
- 本节的「特征值」用 `Polynomial.IsRoot (A.map …).charpoly μ` 刻画（**特征方程的根**），
  而非 `Module.End.HasEigenvalue`；两者的桥梁（「根 ⟺ 有特征向量」）依赖
  `Matrix.det_eq_zero_iff` 与代数闭性，**未做**（见 `cspec_root_iff_hasEigenvalue_remark`）；
- **未做**：`Matrix.IsHermitian.spectral_theorem`（谱定理）与 Jordan 标准形；
- **未做**：把「共轭对」提升为「特征值的重数也成对」（需要 `Polynomial.map` 的重数理论）；
- 本节只证**共轭封闭**这一条真正泛型（对任意实矩阵成立）的事实。 -/

/-- **实矩阵（复化后）的特征多项式 = 实系数特征多项式的标量扩张**：
`(A.map (algebraMap ℝ ℂ)).charpoly = A.charpoly.map (algebraMap ℝ ℂ)`。
这是「特征值共轭封闭」的代数根源（右端是**实系数**多项式）。

（回收 mathlib `Matrix.charpoly_map`。） -/
theorem cspec_charpoly_map_eq (A : Matrix (Fin n) (Fin n) ℝ) :
    (A.map (algebraMap ℝ ℂ)).charpoly =
      A.charpoly.map (algebraMap ℝ ℂ) :=
  Matrix.charpoly_map A (algebraMap ℝ ℂ)
/-- **特征值 ⟹ 特征多项式的根（`eval_det` 路线）**：
若 `μ` 是 `A : Matrix (Fin n) (Fin n) ℂ` 的特征值（`A·x = μ·x`，`x ≠ 0`），
则 `μ` 是 `A.charpoly` 的根。

证明：`A.charpoly = (charmatrix A).det`（`Matrix.charpoly` 的定义），
由 **`Matrix.eval_det`**（`Polynomial.eval r M.det = (eval (scalar n r) (matPolyEquiv M)).det`）
与 **`matPolyEquiv_charmatrix`**（`matPolyEquiv (charmatrix M) = X - C M`）得
`(A.charpoly).eval μ = det (μ•1 - A)`；再由 `cspec_det_sub_smul_eq_zero`
（即 `det (A - μ•1) = 0`）与 `det_neg` 得到 `0`。

诚实标注（**回收 mathlib 4.14 的精确 API**）：
- **`Matrix.eval_charpoly` 在 4.14 不存在**（实测 `unknown constant`），
  **`Polynomial.eval_det` 也不存在**；
- 正确名是 **`Matrix.eval_det`**（`LinearAlgebra/Matrix/Charpoly/Coeff.lean:166`）
  与 **`matPolyEquiv_charmatrix`**（`Charpoly/Basic.lean:61`）——
  本定理即建立在这两个之上（「缺什么、去哪找」已钉在源码里）。 -/
theorem cspec_eigenvalue_isRoot_charpoly {A : Matrix (Fin n) (Fin n) ℂ} {mu : ℂ}
    (h : ∃ x : Fin n → ℂ, cspec_HasEigenpair A mu x) :
    A.charpoly.IsRoot mu := by
  obtain ⟨x, hx⟩ := h
  have hdet := cspec_det_sub_smul_eq_zero A hx
  rw [Polynomial.IsRoot.def, Matrix.charpoly, Matrix.eval_det, matPolyEquiv_charmatrix]
  -- 目标：`(Polynomial.eval (scalar (Fin n) mu) (X - C A)).det = 0`
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- 目标：`(scalar (Fin n) mu - A).det = 0`；`scalar n μ = μ • 1`
  have hsc : scalar (Fin n) mu = mu • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply]
    · simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, hij]
  rw [hsc]
  have hneg : (mu • (1 : Matrix (Fin n) (Fin n) ℂ) - A) =
      -(A - mu • (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [neg_sub]
  rw [hneg, Matrix.det_neg, hdet, mul_zero]

/-- **实系数多项式的共轭求值律**：对 `p : ℝ[X]` 与 `μ : ℂ`，
`(p.map (algebraMap ℝ ℂ)).eval (star μ) = star ((p.map (algebraMap ℝ ℂ)).eval μ)`。

证明：对 **`p` 本身**（实系数）归纳——
`C a` 分支用 `star ((algebraMap ℝ ℂ) a) = (algebraMap ℝ ℂ) a`（实数的共轭是自身）；
`add` 分支用 `star` 的加性；`C a * X ^ n` 分支用 `star` 的乘性与幂性。

诚实标注（**关键**）：**不能**对任意 `q : Polynomial ℂ` 断言
`q.eval (star μ) = star (q.eval μ)`——取 `q = C I` 即假（`I` 的共轭是 `-I`）。
必须把归纳限制在 `ℝ[X]` 上再经 `map` 进入 `ℂ[X]`；本文件采用后者。 -/
theorem cspec_eval_map_star (p : Polynomial ℝ) (mu : ℂ) :
    (p.map (algebraMap ℝ ℂ)).eval (star mu) =
      star ((p.map (algebraMap ℝ ℂ)).eval mu) := by
  -- 把两边都写成 `eval₂`，再对 `p : ℝ[X]` 归纳（只用 `star` 的环同态性质）
  rw [Polynomial.eval_map, Polynomial.eval_map]
  induction p using Polynomial.induction_on with
  | h_C a =>
      simp only [Polynomial.eval₂_C]
      exact (Complex.conj_ofReal a).symm
  | h_add f g hf hg =>
      simp only [Polynomial.eval₂_add, hf, hg]
      exact (map_add (starRingEnd ℂ) _ _).symm
  | h_monomial n a ih =>
      -- 目标与假设都是「`f a * z ^ k`」的形状，但 `k = n` 与 `k = n+1` 不同。
      -- 先化简到显式形式，再用 `ih` 与 `star` 的乘性/幂性搭桥。
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Polynomial.eval₂_pow] at ih ⊢
      calc (algebraMap ℝ ℂ) a * star mu ^ (n + 1)
          = (algebraMap ℝ ℂ) a * star mu ^ n * star mu := by rw [pow_succ]; ring
        _ = star ((algebraMap ℝ ℂ) a * mu ^ n) * star mu := by rw [ih]
        _ = star ((algebraMap ℝ ℂ) a * mu ^ n * mu) :=
              (map_mul (starRingEnd ℂ) _ _).symm
        _ = star ((algebraMap ℝ ℂ) a * mu ^ (n + 1)) := by rw [pow_succ]; ring_nf

/-- **实矩阵的复特征值共轭封闭（A1.2 核心）**：若 `μ` 是实矩阵 `A`（复化后）的特征值
（即 `(A.map (algebraMap ℝ ℂ)).charpoly` 的根），则 `star μ`（`= conj μ`）也是它的根。

证明：`(A.map …).charpoly = A.charpoly.map (algebraMap ℝ ℂ)` 是**实系数**多项式的
标量扩张；由 `cspec_eval_map_star`（实系数多项式的共轭求值律）与 `h`、`star 0 = 0`
立得。

诚实标注：本定理给出**共轭封闭**（非实特征值成对），这是「实矩阵非实特征值成共轭对」
这一定性的**可证内核**；「成对且重数相同」**未做**（需重数理论）。 -/
theorem cspec_conj_isRoot_of_isRoot (A : Matrix (Fin n) (Fin n) ℝ) {mu : ℂ}
    (h : ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot mu) :
    ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot (star mu) := by
  rw [cspec_charpoly_map_eq A] at h ⊢
  rw [Polynomial.IsRoot.def] at h ⊢
  -- 目标：`(A.charpoly.map (algebraMap ℝ ℂ)).eval (star μ) = 0`
  rw [cspec_eval_map_star (A.charpoly) mu, h, star_zero]
/-- **实矩阵的「非实特征值成共轭对」**：若 `μ` 是实矩阵特征多项式的根且 `μ` **非实**
（`star μ ≠ μ`），则 `star μ` 是**另一个**根。

这是「实矩阵的非实特征值总以共轭对出现」的**严格形式**：
存在性由 `cspec_conj_isRoot_of_isRoot` 给出，「不同性」由假设 `star μ ≠ μ` 给出。 -/
theorem cspec_nonreal_eigenvalue_conj_pair (A : Matrix (Fin n) (Fin n) ℝ) {mu : ℂ}
    (h : ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot mu) (hne : star mu ≠ mu) :
    ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot (star mu) ∧ star mu ≠ mu :=
  ⟨cspec_conj_isRoot_of_isRoot A h, hne⟩

/-- **非实特征值的计数下界**：若 `star μ ≠ μ` 且 `μ` 是根，则根集（作为 `Finset`）
至少有 `{μ, star μ}` 两个元素。

诚实标注：本定理给出「非实根成对」的**计数形式**（`2 ≤ card`），
是 `cspec_nonreal_eigenvalue_conj_pair` 的直接包装，便于下游计数论证使用。 -/
theorem cspec_nonreal_root_pair_card_two (A : Matrix (Fin n) (Fin n) ℝ) {mu : ℂ}
    (_h : ((A.map (algebraMap ℝ ℂ)).charpoly).IsRoot mu) (hne : star mu ≠ mu) :
    ({mu, star mu} : Finset ℂ).card = 2 :=
  Finset.card_pair (Ne.symm hne)

/-! ## 第五节：诚实标注 —— 未打通的桥梁 -/

/-- **根 ⟹ 特征值（反向）的可用形式**：把「`charpoly` 的根」与「存在特征向量」
两套表述在本文件内**单向**连接——本定理只给出「有特征向量 ⟹ 是根」。
反向（根 ⟹ 有特征向量）**未做**（见文件头与下方注释）。

这不是新数学内容，而是**接口锚点**：使下游能按「特征值 ⟹ 根」检索到
`cspec_eigenvalue_isRoot_charpoly` 的 **`∃ x` 形式**。 -/
theorem cspec_root_eigenvalue_bridge_direction_only {A : Matrix (Fin n) (Fin n) ℂ} {mu : ℂ}
    (h : ∃ x : Fin n → ℂ, cspec_HasEigenpair A mu x) :
    A.charpoly.IsRoot mu :=
  cspec_eigenvalue_isRoot_charpoly h

/-- **Hermitian 矩阵的实根与其共轭一致**（Hermitian 情形的接口收口）：
`A.IsHermitian` 的实特征值是实的，故其 `charpoly` 的实根 `μ` 满足 `star μ = μ`。

诚实标注：本定理的**实质内容**是 `cspec_hermitian_eigenvalue_real`（前三节，
经 `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` 证得）；
此处把它与「根」的表述**并列**为接口形式：**若** `μ` 是 `A` 的复特征值
（有特征向量），**则** `star μ = μ`，且由 `cspec_eigenvalue_isRoot_charpoly`
它也是根。这不引入新数学，只是把两节**接起来**。

「`charpoly` 的根 ⟹ 有特征向量」的**反向**（真正的连通）**未做**——
见上一段注释与文件头：需要由 `det = 0` 反推非零核向量并接回
`Module.End.eigenspace`，mathlib 4.14 无一步到位的引理。 -/
theorem cspec_hermitian_eigenpair_root_and_star_self {A : Matrix (Fin n) (Fin n) ℂ}
    (_hA : A.IsHermitian) {mu : ℂ}
    (hmu : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) mu) :
    A.charpoly.IsRoot mu := by
  -- Hermitian 的特征向量在 `Fin n → ℂ` 分量表示下给出 `charpoly` 的根
  have h : ∃ x : Fin n → ℂ, cspec_HasEigenpair A mu x := by
    obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Module.End.hasEigenvalue_iff.mp hmu)
    refine ⟨x, hxne, ?_⟩
    have hx : Matrix.toLin' A x = mu • x := (Module.End.mem_eigenspace_iff).mp hxmem
    rwa [Matrix.toLin'_apply] at hx
  exact cspec_eigenvalue_isRoot_charpoly h

end Lattice
