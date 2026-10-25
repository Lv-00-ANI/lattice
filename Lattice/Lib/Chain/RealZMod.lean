import Mathlib

/-!
# LATTICE: 有限域 —— ZMod 约束 ⟺ Int 同余/整除（数域桥）

数域缺口（VERIFICATION 展望：有限域）的补全：把有限域（ZMod p）
的约束语义与 Int 同余（ModConstraint 线）桥接：

  1. Int 同余 ⟺ ZMod 相等：(x : ZMod p) = (y : ZMod p) ⟺ x ≡ y [ZMOD p]
     （mathlib intCast_eq_intCast_iff，本文件复述为桥）；
  2. ZMod 零化 ⟺ 整除：(x : ZMod p) = 0 ⟺ p ∣ x；
  3. 有限域线性约束编译保语义：a·x + b = 0（ZMod p）
     ⟺ p ∣ a·x + b（解集不变）；
  4. 衔接同余判定：⟺ a·x + b ≡ 0 [ZMOD p]
     （连接 ModConstraint 的 congruent 线）。

闭环：有限域约束（ZMod p）经整除桥与 Int 同余等价——
「同余 ⟺ 整除判定」（ModConstraint.mod_preserves）的域参数化：
离散约束体系（Int 同余 / 有限域）统一。

模型无关：任意模 p（ZMod p 是环，无需素数假设）。
-/

namespace Lattice

/-! ## 定理一：Int 同余 ⟺ ZMod 相等（桥） -/

theorem zmod_eq_iff_modEq (p : ℕ) (x y : ℤ) :
    (x : ZMod p) = (y : ZMod p) ↔ x ≡ y [ZMOD p] :=
  ZMod.intCast_eq_intCast_iff x y p

/-! ## 定理二：ZMod 零化 ⟺ 整除 -/

theorem zmod_zero_iff_dvd (p : ℕ) (x : ℤ) :
    (x : ZMod p) = 0 ↔ (p : ℤ) ∣ x :=
  ZMod.intCast_zmod_eq_zero_iff_dvd x p

/-! ## 定理三：有限域线性约束 ⟺ 整除判定（编译保语义）
a·x + b = 0（ZMod p）⟺ p ∣ a·x + b（解集经整除判定编码）。-/

theorem zmod_linear_constraint_iff (p : ℕ) (a b x : ℤ) :
    ((a : ZMod p) * (x : ZMod p) + (b : ZMod p) = 0) ↔ (p : ℤ) ∣ a * x + b := by
  -- a·x + b 的环同态：先整环乘法/加法再取模
  rw [← Int.cast_mul, ← Int.cast_add]
  exact zmod_zero_iff_dvd p (a * x + b)

/-! ## 定理四：编译保解集
有限域约束的解集 = 整除判定的解集（编译不改变解集）。-/

theorem zmod_constraint_preserves (p : ℕ) (a b : ℤ) :
    {x : ℤ | (a : ZMod p) * (x : ZMod p) + (b : ZMod p) = 0}
      = {x : ℤ | (p : ℤ) ∣ a * x + b} := by
  apply Set.ext
  intro x
  exact zmod_linear_constraint_iff p a b x

/-! ## 定理五：衔接同余判定（ModConstraint 线）
有限域约束 ⟺ a·x + b ≡ 0 [ZMOD p]（同余形式的编译判定）。-/

theorem zmod_constraint_iff_congruent (p : ℕ) (a b x : ℤ) :
    ((a : ZMod p) * (x : ZMod p) + (b : ZMod p) = 0) ↔ (a * x + b ≡ 0 [ZMOD p]) := by
  -- 有限域约束 ⟺ 整除判定（定理三）⟺ 同余（Int.modEq_zero_iff_dvd）
  rw [← Int.cast_mul, ← Int.cast_add]
  rw [zmod_zero_iff_dvd p (a * x + b)]
  exact (Int.modEq_zero_iff_dvd (a := a * x + b) (n := p)).symm

/-! ## 注：数域闭环
  ModConstraint（Int 同余 ⟺ 整除判定）与有限域（ZMod p ⟺ 同余）
  双向桥接——离散约束体系统一；ZMod p 无需素数（环结构足够），
  域结构（素数时）留给解方程/除法语义（FiniteField 线）。
  解集 {x | a·x+b ≡ 0 mod p} 经 zmod_constraint_preserves 精确保持。-/

end Lattice
