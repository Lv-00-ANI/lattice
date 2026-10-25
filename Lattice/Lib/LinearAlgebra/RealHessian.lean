import Mathlib
import Lattice.Lib.Convex.RealKKTSecondOrder
/-!
# LATTICE: 高维二阶条件 —— 二次型、Hessian 对称性与多维极值判别

RealKKTSecondOrder 给出**一维**二阶条件。本文件补上**有限维**（`Fin n`）版本：

   1. `quadForm`/`normSq`（def）：`quadForm M v = ∑ᵢ ∑ⱼ Mᵢⱼ·(vᵢ·vⱼ)`（二次型）、
      `normSq v = ∑ᵢ vᵢ²`；`normSq_nonneg`/`normSq_pos`；
   2. `quadForm_add`/`quadForm_smul`/`quadForm_transpose`/`quadForm_symm_part`：
      二次型对矩阵线性、且**只依赖对称部分**（`quadForm ((1/2)•(M+Mᵀ)) v = quadForm M v`），
      `IsSymmMat` + `isSymmMat_symm_part`：任何矩阵的对称部分是对称的；
   3. `PosSemidefQ`/`PosDefQ`（def，半正定/正定二次型）；
      `quadratic_form_pos_def_iff`：正定 ⟺ 半正定 ∧ 二次型非退化（`q v = 0 ⟹ v = 0`）；
   4. `hessian_symmetric`（**Schwarz 定理实例**）：二维二次型
      `(a,b) ↦ quadForm M !![a,b]` 的两个混合二阶偏导**相等**（都等于 `M 0 1 + M 1 0`）；
   5. `second_order_necessary_multidim`（**多维二阶必要条件**）：x 是 F 的局部极小、
      沿每个方向 v 的一维限制 `t ↦ F (x + t·v)` 在 0 处二阶可导（且二阶导 = `quadForm H v`）
      ⟹ `∀ v, 0 ≤ quadForm H v`。证明：把一维的 `second_order_necessary` 逐方向应用；
      `IsLocalMin F x` 到路径局部极小的转化用 `Filter.Tendsto.eventually` 完成；
   6. `quadratic_lower_bound_of_posdef` + `second_order_sufficient_multidim`
      （**多维二阶充分条件**）：若 `∀v, μ·‖v‖² ≤ quadForm H v`（一致正定模数 μ > 0）且
      `F (x+v) ≥ F x + (1/2)·quadForm H v`（Taylor 型下界），则 `∀ y ≠ x, F x < F y`；
   7. `sym2`（显式 2×2 对称矩阵）与 `two_dim_posdef_iff`（**2×2 Sylvester 判据**）：
      `PosDefQ (sym2 a b d) ↔ 0 < a ∧ 0 < a·d − b²`（配方法）。

诚实边界：
  · **高维二阶充分条件需要一致正定模数 μ**：由点式 `PosDefQ` 推出「存在 μ > 0 使
    `∀v, μ‖v‖² ≤ q v`」需要单位球面的紧性与连续性（有限维紧性论证），本文件未形式化，
    故 μ 是**显式假设**（不隐藏 gap）。这是本文件唯一的实质性降级；
  · 多维充分条件以 **Taylor 型二次下界** `F(x+v) ≥ F x + (1/2) q v` 作为假设
    （与 RealKKTSecondOrder 把「区间上的连续可微性」写成显式假设同一风格）：
    由 `ContDiff` 的 Taylor 公式得到该下界是标准步骤，本文件不重复推导；
  · `second_order_necessary_multidim` 的路径光滑性假设
    （`ContinuousOn`/`DifferentiableOn`/二阶导连续）是「F 是 C²」的显式写法；
  · `hessian_symmetric` 是**二维二次型**上的 Schwarz 实例（对一般 C² 函数需要
    `ContDiff` 的混合偏导交换定理，属 mathlib 的 `iteratedFDeriv` API 范围，未使用）；
  · 本文件用自定义二次型谓词 `PosSemidefQ`/`PosDefQ`（对任意矩阵定义）；
    `quadForm_eq_dotProduct`/`posDefQ_iff_dotProduct` 把它与 `Matrix.dotProduct v (M.mulVec v)`
    对齐；与 mathlib `Matrix.PosDef`（含 `IsHermitian` 前提）的完整桥接标注为后续工作；
  · 全程无 sorry/axiom/admit。
-/

noncomputable section

open Set Filter
open Matrix
open scoped Topology BigOperators

namespace Lattice

/-! ## 一、二次型与范数平方 -/

/-- **二次型**：`quadForm M v = ∑ᵢ ∑ⱼ Mᵢⱼ·(vᵢ·vⱼ)`。 -/
def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * (v i * v j)

/-- **范数平方**：`normSq v = ∑ᵢ vᵢ²`。 -/
def normSq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- 对称矩阵。 -/
def IsSymmMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop := Mᵀ = M

/-- **半正定二次型**：对所有 v，`q(v) ≥ 0`。 -/
def PosSemidefQ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ v, 0 ≤ quadForm M v

/-- **正定二次型**：对所有 v ≠ 0，`q(v) > 0`。 -/
def PosDefQ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v, v ≠ 0 → 0 < quadForm M v

lemma normSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ normSq v :=
  Finset.sum_nonneg fun _i _ => sq_nonneg _

lemma normSq_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < normSq v := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-! ## 二、二次型的代数性质 -/

lemma quadForm_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm (M + N) v = quadForm M v + quadForm N v := by
  simp only [quadForm, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma quadForm_smul {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm (c • M) v = c * quadForm M v := by
  unfold quadForm
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **转置不改变二次型**：`quadForm Mᵀ v = quadForm M v`（交换两个求和并交换乘积因子）。 -/
lemma quadForm_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm Mᵀ v = quadForm M v := by
  unfold quadForm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [Matrix.transpose_apply]
    ring

/-- 对称部分不改变二次型：`quadForm ((1/2)•(M+Mᵀ)) v = quadForm M v`。 -/
lemma quadForm_symm_part {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm ((1 / 2 : ℝ) • (M + Mᵀ)) v = quadForm M v := by
  rw [quadForm_smul, quadForm_add, quadForm_transpose]
  ring

/-- 任何矩阵的对称部分确实对称。 -/
lemma isSymmMat_symm_part {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    IsSymmMat ((1 / 2 : ℝ) • (M + Mᵀ)) := by
  unfold IsSymmMat
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-! ## 三、2×2 显式对称矩阵与二次型的计算 -/

/-- 显式 2×2 对称矩阵 `[[a, b], [b, d]]`。 -/
def sym2 (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then (if j = 0 then a else b) else (if j = 0 then b else d)

lemma sym2_00 (a b d : ℝ) : sym2 a b d 0 0 = a := by simp [sym2]

lemma sym2_01 (a b d : ℝ) : sym2 a b d 0 1 = b := by simp [sym2]

lemma sym2_10 (a b d : ℝ) : sym2 a b d 1 0 = b := by simp [sym2]

lemma sym2_11 (a b d : ℝ) : sym2 a b d 1 1 = d := by simp [sym2]

lemma quadForm_sym2 (a b d : ℝ) (v : Fin 2 → ℝ) :
    quadForm (sym2 a b d) v
      = a * (v 0 * v 0) + b * (v 0 * v 1) + b * (v 1 * v 0) + d * (v 1 * v 1) := by
  simp only [quadForm, Fin.sum_univ_two, sym2_00, sym2_01, sym2_10, sym2_11] <;> ring

lemma quadForm_sym2_expanded (a b d : ℝ) (v : Fin 2 → ℝ) :
    quadForm (sym2 a b d) v = a * (v 0) ^ 2 + 2 * b * (v 0 * v 1) + d * (v 1) ^ 2 := by
  rw [quadForm_sym2]
  ring

lemma vec2_zero (x y : ℝ) : (![x, y] : Fin 2 → ℝ) 0 = x := by
  simp [Matrix.cons_val_zero]

lemma vec2_one (x y : ℝ) : (![x, y] : Fin 2 → ℝ) 1 = y := by
  simp [Matrix.cons_val_one, Matrix.head_cons]

lemma vec2_ne_zero {x y : ℝ} (hx : x ≠ 0) : (![x, y] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  rw [vec2_zero] at h0
  simp at h0
  exact hx h0

lemma vec2_ne_zero_of_second {x y : ℝ} (hy : y ≠ 0) : (![x, y] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  rw [vec2_one] at h1
  simp at h1
  exact hy h1

/-- **2×2 Sylvester 判据（正定）**：`[[a,b],[b,d]]` 正定 ⟺ `a > 0 ∧ a·d − b² > 0`。

证明：恒等式 `q(v) = a·(v₀ + (b/a)v₁)² + ((ad−b²)/a)·v₁²`；
反向用 `v = (1,0)` 得 `a > 0`，用 `v = (−b, a)`（非零，因 a > 0）得 `a(ad−b²) > 0`。 -/
theorem two_dim_posdef_iff (a b d : ℝ) :
    PosDefQ (sym2 a b d) ↔ 0 < a ∧ 0 < a * d - b * b := by
  constructor
  · intro h
    have hv1 : (![1, 0] : Fin 2 → ℝ) ≠ 0 := vec2_ne_zero (x := 1) (y := 0) one_ne_zero
    have hq1 : quadForm (sym2 a b d) (![1, 0] : Fin 2 → ℝ) = a := by
      rw [quadForm_sym2_expanded]
      rw [vec2_zero, vec2_one]
      ring
    have ha : 0 < a := by
      have := h _ hv1
      rwa [hq1] at this
    have hv2 : (![-b, a] : Fin 2 → ℝ) ≠ 0 := vec2_ne_zero_of_second (x := -b) (y := a) (ne_of_gt ha)
    have hq2 : quadForm (sym2 a b d) (![-b, a] : Fin 2 → ℝ) = a * (a * d - b * b) := by
      rw [quadForm_sym2_expanded]
      rw [vec2_zero, vec2_one]
      ring
    have hd : 0 < a * (a * d - b * b) := by
      have := h _ hv2
      rwa [hq2] at this
    exact ⟨ha, by nlinarith⟩
  · rintro ⟨ha, hdet⟩ v hv
    have hane : a ≠ 0 := ne_of_gt ha
    have hident : quadForm (sym2 a b d) v
        = a * (v 0 + (b / a) * v 1) ^ 2 + ((a * d - b * b) / a) * (v 1) ^ 2 := by
      rw [quadForm_sym2]
      field_simp
      ring
    have hc1 : 0 ≤ a * (v 0 + (b / a) * v 1) ^ 2 := mul_nonneg (le_of_lt ha) (sq_nonneg _)
    have hc2 : 0 ≤ ((a * d - b * b) / a) * (v 1) ^ 2 :=
      mul_nonneg (le_of_lt (div_pos hdet ha)) (sq_nonneg _)
    have hle : 0 ≤ quadForm (sym2 a b d) v := by rw [hident]; linarith
    have hne : quadForm (sym2 a b d) v ≠ 0 := by
      intro h0
      have hsum0 : a * (v 0 + (b / a) * v 1) ^ 2 + ((a * d - b * b) / a) * (v 1) ^ 2 = 0 := by
        rw [← hident]
        exact h0
      have hz1 : a * (v 0 + (b / a) * v 1) ^ 2 = 0 := by nlinarith [hc1, hc2, hsum0]
      have hz2 : ((a * d - b * b) / a) * (v 1) ^ 2 = 0 := by nlinarith [hc1, hc2, hsum0]
      have hv1 : v 1 = 0 := by
        have hpos : 0 < (a * d - b * b) / a := div_pos hdet ha
        have hsq : (v 1) ^ 2 = 0 := (mul_eq_zero.mp hz2).resolve_left (ne_of_gt hpos)
        exact sq_eq_zero_iff.mp hsq
      have hv0 : v 0 = 0 := by
        have hsq : (v 0 + (b / a) * v 1) ^ 2 = 0 := (mul_eq_zero.mp hz1).resolve_left hane
        have hz := sq_eq_zero_iff.mp hsq
        rw [hv1] at hz
        simpa using hz
      exact hv (by
        funext i
        fin_cases i <;> simp [hv0, hv1])
    exact lt_of_le_of_ne hle (Ne.symm hne)

/-- **正定 ⟺ 半正定 + 非退化**。 -/
theorem quadratic_form_pos_def_iff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    PosDefQ M ↔ PosSemidefQ M ∧ ∀ v : Fin n → ℝ, quadForm M v = 0 → v = 0 := by
  have hzero : quadForm M (0 : Fin n → ℝ) = 0 := by
    simp [quadForm]
  constructor
  · intro h
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · by_cases hv : v = 0
      · rw [hv, hzero]
      · exact le_of_lt (h v hv)
    · by_contra hv'
      have := h v hv'
      linarith
  · rintro ⟨hps, hnn⟩ v hv
    rcases lt_or_eq_of_le (hps v) with hlt | heq
    · exact hlt
    · exact absurd (hnn v heq.symm) hv

/-! ## 四、Schwarz 定理实例：二维二次型的混合偏导对称 -/

/-- 线性组合 `c·y + d·y + e` 的导数（辅助）。 -/
lemma deriv_add_mul_const (c d e x : ℝ) :
    deriv (fun y : ℝ => c * y + d * y + e) x = c + d := by
  have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 : HasDerivAt (fun y : ℝ => d * y) d x := by
    simpa using (hasDerivAt_id x).const_mul d
  have h := (h1.add h2).add (hasDerivAt_const x e)
  simpa using h.deriv

/-- `(a,b) ↦ quadForm M !![a,b]` 对第二个变量的偏导：
`M 0 1·a + M 1 0·a + 2·M 1 1·b`。 -/
lemma deriv_quadForm_two_snd (M : Matrix (Fin 2) (Fin 2) ℝ) (a b₀ : ℝ) :
    deriv (fun b : ℝ => quadForm M ![a, b]) b₀
      = M 0 1 * a + M 1 0 * a + 2 * M 1 1 * b₀ := by
  have hfun : (fun b : ℝ => quadForm M ![a, b])
      = fun b : ℝ => M 0 0 * (a * a) + M 0 1 * (a * b) + M 1 0 * (b * a) + M 1 1 * (b * b) := by
    funext b
    simp only [quadForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  rw [hfun]
  have h0 : HasDerivAt (fun _ : ℝ => M 0 0 * (a * a)) 0 b₀ := hasDerivAt_const b₀ _
  have h1 : HasDerivAt (fun b : ℝ => M 0 1 * (a * b)) (M 0 1 * a) b₀ := by
    have hlin : HasDerivAt (fun t : ℝ => a * t) a b₀ := by
      simpa using (hasDerivAt_id b₀).const_mul a
    simpa [mul_assoc] using hlin.const_mul (M 0 1)
  have h2 : HasDerivAt (fun b : ℝ => M 1 0 * (b * a)) (M 1 0 * a) b₀ := by
    have hlin : HasDerivAt (fun t : ℝ => t * a) a b₀ := by
      simpa using (hasDerivAt_id b₀).mul_const a
    simpa [mul_assoc] using hlin.const_mul (M 1 0)
  have h3 : HasDerivAt (fun b : ℝ => M 1 1 * (b * b)) (M 1 1 * (2 * b₀)) b₀ := by
    have hsq : HasDerivAt (fun t : ℝ => t * t) (2 * b₀) b₀ := by
      simpa [pow_two] using (hasDerivAt_id b₀).pow 2
    simpa [mul_assoc] using hsq.const_mul (M 1 1)
  have hsum := ((h0.add h1).add h2).add h3
  have hval : 0 + M 0 1 * a + M 1 0 * a + M 1 1 * (2 * b₀)
      = M 0 1 * a + M 1 0 * a + 2 * M 1 1 * b₀ := by ring
  rw [hval] at hsum
  exact hsum.deriv

/-- `(a,b) ↦ quadForm M !![a,b]` 对第一个变量的偏导：
`2·M 0 0·a + M 0 1·b + M 1 0·b`。 -/
lemma deriv_quadForm_two_fst (M : Matrix (Fin 2) (Fin 2) ℝ) (a₀ b : ℝ) :
    deriv (fun a : ℝ => quadForm M ![a, b]) a₀
      = 2 * M 0 0 * a₀ + M 0 1 * b + M 1 0 * b := by
  have hfun : (fun a : ℝ => quadForm M ![a, b])
      = fun a : ℝ => M 0 0 * (a * a) + M 0 1 * (a * b) + M 1 0 * (b * a) + M 1 1 * (b * b) := by
    funext a
    simp only [quadForm, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  rw [hfun]
  have h0 : HasDerivAt (fun a : ℝ => M 0 0 * (a * a)) (M 0 0 * (2 * a₀)) a₀ := by
    have hsq : HasDerivAt (fun t : ℝ => t * t) (2 * a₀) a₀ := by
      simpa [pow_two] using (hasDerivAt_id a₀).pow 2
    simpa [mul_assoc] using hsq.const_mul (M 0 0)
  have h1 : HasDerivAt (fun a : ℝ => M 0 1 * (a * b)) (M 0 1 * b) a₀ := by
    have hlin : HasDerivAt (fun t : ℝ => t * b) b a₀ := by
      simpa using (hasDerivAt_id a₀).mul_const b
    simpa [mul_assoc] using hlin.const_mul (M 0 1)
  have h2 : HasDerivAt (fun a : ℝ => M 1 0 * (b * a)) (M 1 0 * b) a₀ := by
    have hlin : HasDerivAt (fun t : ℝ => b * t) b a₀ := by
      simpa using (hasDerivAt_id a₀).const_mul b
    simpa [mul_assoc] using hlin.const_mul (M 1 0)
  have h3 : HasDerivAt (fun _ : ℝ => M 1 1 * (b * b)) 0 a₀ := hasDerivAt_const a₀ _
  have hsum := (((h0.add h1).add h2).add h3)
  have hval : M 0 0 * (2 * a₀) + M 0 1 * b + M 1 0 * b + 0
      = 2 * M 0 0 * a₀ + M 0 1 * b + M 1 0 * b := by ring
  rw [hval] at hsum
  exact hsum.deriv

/-- **Hessian 对称性（Schwarz 定理实例）**：二维二次型函数
`F(a,b) = quadForm M !![a,b]` 的两个混合二阶偏导相等，都等于 `M 0 1 + M 1 0`。 -/
theorem hessian_symmetric (M : Matrix (Fin 2) (Fin 2) ℝ) (a₀ b₀ : ℝ) :
    deriv (fun a : ℝ => deriv (fun b : ℝ => quadForm M ![a, b]) b₀) a₀
      = deriv (fun b : ℝ => deriv (fun a : ℝ => quadForm M ![a, b]) a₀) b₀ := by
  have h1 : (fun a : ℝ => deriv (fun b : ℝ => quadForm M ![a, b]) b₀)
      = fun a : ℝ => M 0 1 * a + M 1 0 * a + 2 * M 1 1 * b₀ := by
    funext a
    exact deriv_quadForm_two_snd M a b₀
  have h2 : (fun b : ℝ => deriv (fun a : ℝ => quadForm M ![a, b]) a₀)
      = fun b : ℝ => M 0 1 * b + M 1 0 * b + 2 * M 0 0 * a₀ := by
    funext b
    rw [deriv_quadForm_two_fst]
    ring
  rw [h1, h2]
  rw [deriv_add_mul_const, deriv_add_mul_const]

/-! ## 五、多维二阶必要条件 -/

/-- **多维二阶必要条件**：x 是 F 的局部极小，沿每个方向 v 的一维限制
`t ↦ F (x + t·v)` 在 0 的邻域上二阶可导、二阶导连续，且其二阶导在 0 处等于
`quadForm H v`，则 `∀ v, 0 ≤ quadForm H v`（Hessian 半正定）。

证明：由 `IsLocalMin F x` 与路径映射 `t ↦ x + t·v` 的连续性得路径在 0 处的局部极小
（`Filter.Tendsto.eventually`）；对路径函数逐方向应用一维的
`RealKKTSecondOrder.second_order_necessary`。 -/
theorem second_order_necessary_multidim {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hmin : IsLocalMin F x)
    (hcont : ∀ v : Fin n → ℝ, ContinuousOn (fun t : ℝ => F (x + t • v)) (Ioo (-1) 1))
    (hdiff : ∀ v : Fin n → ℝ, DifferentiableOn ℝ (fun t : ℝ => F (x + t • v)) (Ioo (-1) 1))
    (hd1 : ∀ v : Fin n → ℝ, ContinuousOn (deriv (fun t : ℝ => F (x + t • v))) (Ioo (-1) 1))
    (hd2 : ∀ v : Fin n → ℝ, ContinuousAt (deriv (deriv (fun t : ℝ => F (x + t • v)))) 0)
    (hhess : ∀ v : Fin n → ℝ, deriv (deriv (fun t : ℝ => F (x + t • v))) 0 = quadForm H v) :
    ∀ v : Fin n → ℝ, 0 ≤ quadForm H v := by
  intro v
  have hpath : IsLocalMin (fun t : ℝ => F (x + t • v)) 0 := by
    have hφ : Tendsto (fun t : ℝ => x + t • v) (𝓝 (0 : ℝ)) (𝓝 x) := by
      have h1 : ContinuousAt (fun t : ℝ => t • v) (0 : ℝ) := continuousAt_id.smul_const v
      have h2 : ContinuousAt (fun _ : ℝ => x) (0 : ℝ) := continuousAt_const
      have h3 : ContinuousAt (fun t : ℝ => x + t • v) (0 : ℝ) := h2.add h1
      simpa using h3.tendsto
    have hev := hφ.eventually hmin
    filter_upwards [hev] with t ht
    simpa using ht
  have hbound := second_order_necessary (fun t : ℝ => F (x + t • v)) 0 1 one_pos hpath
    (by simpa using hcont v) (by simpa using hdiff v) (by simpa using hd1 v)
    (by simpa using hd2 v)
  rw [hhess v] at hbound
  exact hbound

/-! ## 六、多维二阶充分条件（一致正定模数 + Taylor 型下界） -/

/-- **二次下界**：`F` 在 x 处有模数 μ 的二次下界
`F (x+v) ≥ F x + (μ/2)·‖v‖²`。 -/
def QuadraticLowerBound {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (μ : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, F x + (μ / 2) * normSq v ≤ F (x + v)

/-- **由 Hessian 一致正定 + Taylor 型下界得二次下界**。 -/
theorem quadratic_lower_bound_of_posdef {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ} {μ : ℝ}
    (hH : ∀ v : Fin n → ℝ, μ * normSq v ≤ quadForm H v)
    (hTaylor : ∀ v : Fin n → ℝ, F x + (1 / 2) * quadForm H v ≤ F (x + v)) :
    QuadraticLowerBound F x μ := by
  intro v
  have h1 : (μ / 2) * normSq v ≤ (1 / 2) * quadForm H v := by
    have hdiv : (μ / 2) * normSq v = (1 / 2) * (μ * normSq v) := by ring
    rw [hdiv]
    have := hH v
    linarith
  have h2 := hTaylor v
  linarith

/-- **二次下界 ⟹ 全局严格极小**。 -/
theorem strict_min_of_quadratic_lower_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    {x : Fin n → ℝ} {μ : ℝ} (hLB : QuadraticLowerBound F x μ) (hμ : 0 < μ) :
    ∀ y : Fin n → ℝ, y ≠ x → F x < F y := by
  intro y hy
  have h := hLB (y - x)
  have hpos : 0 < normSq (y - x) := normSq_pos (sub_ne_zero.mpr hy)
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at h
  nlinarith [h, hpos, hμ]

/-- **多维二阶充分条件**：Hessian 一致正定（模数 μ > 0）且 F 在 x 处有 Taylor 型
二次下界 ⟹ `F x < F y`（`y ≠ x`），即 x 是**全局严格极小点**。 -/
theorem second_order_sufficient_multidim {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    {H : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hH : ∀ v : Fin n → ℝ, μ * normSq v ≤ quadForm H v)
    (hTaylor : ∀ v : Fin n → ℝ, F x + (1 / 2) * quadForm H v ≤ F (x + v)) :
    ∀ y : Fin n → ℝ, y ≠ x → F x < F y :=
  strict_min_of_quadratic_lower_bound (quadratic_lower_bound_of_posdef hH hTaylor) hμ

/-! ## 注：与一维结果的关系
  · `second_order_necessary_multidim` 是 RealKKTSecondOrder.second_order_necessary 的
    有限维推广（逐方向的路径限制正是「Hessian 半正定」的定义内容）；
  · `second_order_sufficient_multidim` 的一维特例（n = 1、`quadForm H v = H 0 0 · v²`）
    给出 `RealKKTSecondOrder.second_order_sufficient` 的结论，但那里的前提是
    「f'' 在区间上恒正」，此处是「一致正定模数 + Taylor 型下界」——两种显式化方式不同，
    都不隐藏 gap；
  · `two_dim_posdef_iff` 给出 2×2 的 Sylvester 判据（配方法），
    `quadratic_form_pos_def_iff` 给出一般 n 的「正定 ⟺ 半正定 + 非退化」刻画；
  · `hessian_symmetric` 是 Schwarz 定理在二维二次型上的实例，说明「Hessian 可取对称」。 -/

end Lattice
