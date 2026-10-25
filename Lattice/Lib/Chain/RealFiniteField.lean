import Mathlib

/-!
# LATTICE: 素数域 —— ZMod p 线性方程的解语义（有限域深化）

RealZMod（ZMod ⟺ Int 同余桥）的**素数域深化**：p 素数时
ZMod p 是域（Field），线性方程 a·x = b 的解语义完整：

  1. 唯一性：a ≠ 0 且 a·x₁ = a·x₂ ⟹ x₁ = x₂（域是整环）；
  2. 解存在：a·(b/a) = b（域除法）；
  3. 解刻画：a·x = b ⟺ x = b/a（唯一解闭式）；
  4. 解结构：特解 + 齐次解仍是解（线性，a·h = 0 ⟹ a·(x₀+h) = b）。

闭环：离散约束体系（Int 同余 / ZMod 有限域 / 整除判定）的
方程求解语义——数域缺口的除法部分补全（ZMod p 域结构）。

模型无关：任意素数 p（[Fact p.Prime] ⟹ Field (ZMod p)）。
-/

namespace Lattice

variable {p : ℕ} [Fact p.Prime]

/-! ## 定理一：解唯一（域是整环）
a ≠ 0 且 a·x₁ = a·x₂ ⟹ x₁ = x₂。-/

theorem zmod_unique_of_mul_eq (a x₁ x₂ : ZMod p) (ha : a ≠ 0) (h : a * x₁ = a * x₂) :
    x₁ = x₂ := by
  -- a·(x₁−x₂) = 0，域无零因子，a ≠ 0 ⟹ x₁−x₂ = 0
  have hmul : a * (x₁ - x₂) = 0 := by
    rw [mul_sub]
    rw [h]
    ring
  have hzero : x₁ - x₂ = 0 := (mul_eq_zero.mp hmul).resolve_left ha
  exact sub_eq_zero.mp hzero

/-! ## 定理二：解存在（域除法）
a ≠ 0 ⟹ a·(b/a) = b。-/

theorem zmod_field_solution (a b : ZMod p) (ha : a ≠ 0) :
    a * (b / a) = b := by
  field_simp [ha]

/-! ## 定理三：解刻画（唯一解闭式）
a ≠ 0 ⟹ a·x = b ⟺ x = b/a。-/

theorem zmod_field_iff_solution (a b x : ZMod p) (ha : a ≠ 0) :
    a * x = b ↔ x = b / a := by
  constructor
  · intro h
    have h1 : a⁻¹ * (a * x) = a⁻¹ * b := congrArg (fun t : ZMod p => a⁻¹ * t) h
    rw [← mul_assoc, inv_mul_cancel₀ ha] at h1
    simpa [div_eq_mul_inv, mul_comm] using h1
  · intro h
    rw [h]
    exact zmod_field_solution a b ha

/-! ## 定理四：解结构（特解 + 齐次解）
x₀ 是特解（a·x₀ = b）且 h 是齐次解（a·h = 0）⟹ x₀+h 也是解。-/

theorem zmod_homogeneous_structure (a b h x₀ : ZMod p) (h₀ : a * x₀ = b) (hh : a * h = 0) :
    a * (x₀ + h) = b := by
  rw [mul_add, h₀, hh]
  simp

/-! ## 注：域语义闭环
  素数 p ⟹ ZMod p 是域：线性方程 a·x = b（a ≠ 0）有唯一解
  x = b/a（定理三），解空间是特解 + 齐次解仿射结构（定理四）；
  与 RealZMod（有限域 ⟺ Int 同余）衔接——离散约束体系从
  「判定语义」（同余/整除）深化到「求解语义」（唯一解/仿射结构）。-/

end Lattice
