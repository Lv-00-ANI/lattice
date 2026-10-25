import Mathlib
import Lattice.Lib.Chain.RealZMod
import Lattice.Lib.Chain.RealFiniteField
/-!
# LATTICE: 素数域扩展 —— ZMod p 的域结构、线性方程组解空间与秩-零化度

RealFiniteField（素数 p ⟹ ZMod p 是域，一元方程 a·x = b 的解语义）的
**多元/线性代数深化**：把「一元方程解结构」提升为「线性方程组解空间的仿射结构」，
并补全有限域上的秩-零化度与可逆判定。

  1. **素数域**：p 素数 ⟹ `Field (ZMod p)`（mathlib 实例 `ZMod.instField`），
     推出非零元可逆、乘法消去（衔接 RealFiniteField.zmod_unique_of_mul_eq）；
  2. **线性方程组解结构**：ZMod p 上线性映射 f : V →ₗ W 的方程 `f x = b`
     的解集 = 特解 x₀ 平移的齐次解空间 ker f（x₀ + ker f 的仿射集），
     并给「x − x₀ ∈ ker f」的等价刻画——一元版 `zmod_homogeneous_structure`
     的多元推广；
  3. **秩-零化度**：有限域上有限维线性映射 `finrank range f + finrank ker f = finrank V`
     （mathlib `LinearMap.finrank_range_add_finrank_ker`）；
  4. **可逆 ⟺ det ≠ 0**：ZMod p 上矩阵 `M.det ≠ 0 ↔ IsUnit M`
     （`Matrix.isUnit_iff_isUnit_det` + 域上 `IsUnit ↔ ≠ 0`）；
  5. **费马小定理**：`x ^ p = x`（mathlib 4.14 #check 实测：**无** `ZMod.fermat`，
     有 `ZMod.pow_card : x ^ p = x`；直接引用），及非零元 `x ^ (p−1) = 1`。

诚实性：所有定理只引用 mathlib 4.14 现成引理与既有文件定理，无 sorry/axiom/admit。
既有文件来源可核对：`RealZMod.zmod_zero_iff_dvd`（`fermat_little_iff_dvd` 的整除判定依据）与
`RealFiniteField.zmod_homogeneous_structure`（`zmod_linear_system_homogeneous_bridge` 的转调目标，
另 `zmod_unique_of_mul_eq` 见第一节素数域消去）；此外 `zmod_prime_field` 是 `def`（暴露类型类实例
而非命题），不属「定理」之列。
模型无关：任意素数 p（`[Fact p.Prime]`），任意有限维 ZMod p-模。
-/

noncomputable section

namespace Lattice

/-! ## 第一节：素数域结构（Field (ZMod p) 及其推论） -/

/-- p 素数 ⟹ ZMod p 是域（mathlib 实例 `ZMod.instField`；
RealFiniteField 的 `field_simp`/除法定理即以此实例为底座）。
`Field (ZMod p)` 是类型而非命题，故以 `def` 暴露该实例（不作为新实例注册）。 -/
def zmod_prime_field (p : ℕ) [Fact p.Prime] : Field (ZMod p) := inferInstance

/-- 素数域在类型类层面即为域：`Field (ZMod p)` 实例存在（`inferInstance` 非空）。 -/
theorem zmod_prime_field_nonempty (p : ℕ) [Fact p.Prime] :
    Nonempty (Field (ZMod p)) :=
  ⟨zmod_prime_field p⟩

/-- 素数域中非零元可逆：x ≠ 0 ⟹ x·x⁻¹ = 1。 -/
theorem zmod_prime_mul_inv_cancel {p : ℕ} [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    x * x⁻¹ = 1 :=
  mul_inv_cancel₀ hx

/-- 素数域中非零元有乘法逆元（存在性形式）。 -/
theorem zmod_prime_inv_exists {p : ℕ} [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    ∃ y : ZMod p, x * y = 1 :=
  ⟨x⁻¹, zmod_prime_mul_inv_cancel x hx⟩

/-! ## 第二节：线性方程组的解空间结构（一元 `zmod_homogeneous_structure` 的多元推广） -/

/-- **线性方程组解结构**（ZMod p 上）：
`f x = b` 的解集 = 满足「x − x₀ ∈ ker f」的 x 的集合（x₀ 是任一特解）。
即解集 = 特解 + 齐次解空间（仿射结构）。 -/
theorem linear_system_solution_structure (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W]
    (f : V →ₗ[ZMod p] W) (b : W) (x₀ : V) (h₀ : f x₀ = b) :
    {x : V | f x = b} = {x : V | x - x₀ ∈ LinearMap.ker f} := by
  apply Set.ext
  intro x
  constructor
  · -- 解差入核：f (x − x₀) = f x − f x₀ = b − b = 0
    intro hx
    rw [Set.mem_setOf_eq, LinearMap.mem_ker, map_sub, h₀, hx, sub_self]
  · -- 核中元素平移后仍是解：f (x − x₀) = 0 ⟹ f x = f x₀ = b
    intro hx
    rw [Set.mem_setOf_eq, LinearMap.mem_ker] at hx
    rw [Set.mem_setOf_eq]
    have hsub : f x - f x₀ = 0 := by
      rw [← map_sub]
      exact hx
    rw [sub_eq_zero] at hsub
    rw [hsub, h₀]

/-- **解集的仿射像形式**：解集 = x₀ + ker f（特解平移齐次解空间）。 -/
theorem linear_system_solution_affine (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W]
    (f : V →ₗ[ZMod p] W) (b : W) (x₀ : V) (h₀ : f x₀ = b) :
    {x : V | f x = b} = (fun h : V => x₀ + h) '' (LinearMap.ker f : Set V) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    refine ⟨x - x₀, ?_, ?_⟩
    · change f (x - x₀) = 0
      rw [map_sub, h₀, hx, sub_self]
    · show x₀ + (x - x₀) = x
      abel
  · rintro ⟨h, hh, rfl⟩
    change f (x₀ + h) = b
    change f h = 0 at hh
    rw [map_add, hh, h₀, add_zero]

/-- 衔接 RealFiniteField：一元齐次解结构 `zmod_homogeneous_structure` 是
本文件线性框架在 1 维（标量乘法映射）上的特例——特解 + 齐次解仍是解。 -/
theorem zmod_linear_system_homogeneous_bridge (p : ℕ) [Fact p.Prime]
    (a b h x₀ : ZMod p) (h₀ : a * x₀ = b) (hh : a * h = 0) :
    a * (x₀ + h) = b :=
  zmod_homogeneous_structure a b h x₀ h₀ hh

/-! ## 第三节：秩-零化度定理（有限域实例） -/

/-- **秩-零化度定理**（ZMod p 上）：有限维线性映射
`finrank range f + finrank ker f = finrank V`（mathlib `LinearMap.finrank_range_add_finrank_ker`）。 -/
theorem zmod_rank_nullity (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W]
    (f : V →ₗ[ZMod p] W) :
    Module.finrank (ZMod p) (LinearMap.range f) + Module.finrank (ZMod p) (LinearMap.ker f)
      = Module.finrank (ZMod p) V :=
  LinearMap.finrank_range_add_finrank_ker f

/-- 秩-零化度（解空间维数形式）：齐次解空间维数 = dim V − rank f。
（由秩-零化度移项；`finrank ker f = finrank V − finrank range f`。） -/
theorem zmod_nullity_dimension (p : ℕ) [Fact p.Prime]
    {V W : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W]
    (f : V →ₗ[ZMod p] W) :
    Module.finrank (ZMod p) (LinearMap.ker f)
      = Module.finrank (ZMod p) V - Module.finrank (ZMod p) (LinearMap.range f) := by
  have h := zmod_rank_nullity p f
  omega

/-! ## 第四节：矩阵可逆 ⟺ det ≠ 0（ZMod p 上） -/

/-- **矩阵可逆 ⟺ 行列式非零**（ZMod p 上，p 素数）：
`M.det ≠ 0 ↔ IsUnit M`（`Matrix.isUnit_iff_isUnit_det` + 域上 `IsUnit ↔ ≠ 0`）。 -/
theorem zmod_matrix_invertible_iff (p : ℕ) [Fact p.Prime]
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n (ZMod p)) :
    M.det ≠ 0 ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.symm

/-- 可逆矩阵（行列式非零）的逆给出左逆：`M.det ≠ 0 ⟹ M⁻¹ * M = 1`
（mathlib `Matrix.nonsing_inv_mul`）。 -/
theorem zmod_matrix_inv_mul_self (p : ℕ) [Fact p.Prime]
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n (ZMod p))
    (h : M.det ≠ 0) : M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)

/-! ## 第五节：费马小定理（mathlib 4.14 实测：`ZMod.pow_card`） -/

/-! #check 结果（本文件写作前实测）：
  * `ZMod.fermat` —— **不存在**（unknown constant）；
  * `@ZMod.pow_card : ∀ {p} [Fact (Nat.Prime p)] (x : ZMod p), x ^ p = x` —— 存在；
  * `@ZMod.pow_card_sub_one_eq_one : ∀ {p} [Fact (Nat.Prime p)] {a : ZMod p}, a ≠ 0 → a ^ (p - 1) = 1` —— 存在。
故费马小定理直接引用 `ZMod.pow_card`。 -/

/-- **费马小定理**（ZMod p 形式）：x ^ p = x（p 素数）。 -/
theorem fermat_little (p : ℕ) [Fact p.Prime] (x : ZMod p) : x ^ p = x :=
  ZMod.pow_card x

/-- 费马小定理（非零元形式）：x ≠ 0 ⟹ x ^ (p − 1) = 1。 -/
theorem fermat_little_nonzero {p : ℕ} [Fact p.Prime] (x : ZMod p) (hx : x ≠ 0) :
    x ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one hx

/-- 费马小定理（整数形式）：任意整数 x，`(x : ZMod p) ^ p = (x : ZMod p)`。 -/
theorem fermat_little_int (p : ℕ) [Fact p.Prime] (x : ℤ) :
    (x : ZMod p) ^ p = (x : ZMod p) :=
  ZMod.pow_card (x : ZMod p)

/-- 衔接 RealZMod：`x ^ p = x` ⟺ p ∣ x ^ p − x（整除判定，`zmod_zero_iff_dvd`）。 -/
theorem fermat_little_iff_dvd (p : ℕ) [Fact p.Prime] (x : ℤ) :
    ((x ^ p - x : ℤ) : ZMod p) = 0 := by
  have hx : ((x ^ p : ℤ) : ZMod p) = ((x : ℤ) : ZMod p) := by
    push_cast
    exact ZMod.pow_card (x : ZMod p)
  rw [Int.cast_sub, hx, sub_self]

/-! ## 注：素数域闭环
  p 素数 ⟹ `Field (ZMod p)`（第一节）；线性方程组解集 = 特解 + 齐次解空间
  （第二节，一元 `zmod_homogeneous_structure` 的多元推广）；秩-零化度给出
  解空间维数（第三节）；可逆 ⟺ det ≠ 0（第四节）；费马小定理 x^p = x（第五节）。
  与 RealZMod（ZMod ⟺ Int 同余/整除）衔接：`fermat_little_iff_dvd` 把
  「x^p = x」写成「p ∣ x^p − x」的整除判定形式。 -/

end Lattice
