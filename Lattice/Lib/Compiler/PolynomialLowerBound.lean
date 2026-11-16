import Mathlib

/-!
# 下界定理（三）：多项式的**根计数唯一性**——一般 `N` 的维数计数核心（阶段 C，P8）

## 第 944/945 轮做到了哪里

**第 944 轮：仿射对 `x²` 的一致误差 `≥ 1/8`。**
**第 945 轮：仿射在三点上必有 `≥ 1/6` 偏差；机制是「2 个参数 < 3 个约束」。**

**=> 一般 `N` 需要同一机制的严格形式：**

**> 次数 `< N` 的多项式若有 `N` 个互异零点，则它恒等于零。**

**=> Mathlib 已提供精确工具
`eq_zero_of_natDegree_lt_card_of_eval_eq_zero`，
本文件用它把机制陈述干净，而不重新发明根计数。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`poly_zero_of_many_roots`** | **⭐⭐⭐ 次数 `< N` 且在 `N` 个点上取零 ⟹ 恒零** |
| **`poly_eq_of_agree`** | **⭐⭐⭐ 两次数 `< N` 的多项式在 `N` 点一致 ⟹ 恒等** |
| **`dimension_counting`** | **⭐⭐⭐ `N` 个参数唯一决定 `N` 个值（单射形式）** |

**=> 下界用第三条的**逆否**：`N+1` 个目标值不能被 `N` 个参数同时满足。** -/

namespace Lattice.Lib.Compiler.PolynomialLowerBound

open Polynomial

/-- **⭐⭐⭐ 次数 `< N` 且在 `N` 个互异点上取零 ⟹ 恒零。**

**=> 证明用 Mathlib 的 `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`，
把点集编索成有限类型 `pts`。** -/
theorem poly_zero_of_many_roots {N : ℕ} (p : Polynomial ℝ)
    (hdeg : p.natDegree < N)
    (pts : Finset ℝ) (hcard : pts.card = N)
    (hzero : ∀ x ∈ pts, p.eval x = 0) :
    p = 0 := by
  classical
  have hf : Function.Injective (fun i : pts => (i : ℝ)) := Subtype.val_injective
  have heval : ∀ i : pts, p.eval ((i : ℝ)) = 0 := fun i => hzero i.1 i.2
  have hcard' : p.natDegree < Fintype.card pts := by
    rw [Fintype.card_coe, hcard]
    exact hdeg
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hf heval hcard'

/-- **⭐⭐⭐ 两个次数 `< N` 的多项式在 `N` 个点上一致 ⟹ 恒等。** -/
theorem poly_eq_of_agree {N : ℕ} (p q : Polynomial ℝ)
    (hp : p.natDegree < N) (hq : q.natDegree < N)
    (pts : Finset ℝ) (hcard : pts.card = N)
    (hagree : ∀ x ∈ pts, p.eval x = q.eval x) :
    p = q := by
  have hdeg : (p - q).natDegree < N := by
    have h1 : (p - q).natDegree ≤ max p.natDegree q.natDegree := natDegree_sub_le p q
    omega
  have hz : ∀ x ∈ pts, (p - q).eval x = 0 := by
    intro x hx
    rw [Polynomial.eval_sub, hagree x hx, sub_self]
  have hzero : p - q = 0 := poly_zero_of_many_roots (p - q) hdeg pts hcard hz
  exact sub_eq_zero.mp hzero

/-- **⭐⭐⭐ 维数计数（单射形式）。**

**=> 把次数 `< N` 的多项式映到它在 `N` 个互异点上的取值，是**单射**。** -/
theorem dimension_counting {N : ℕ} (pts : Finset ℝ) (hcard : pts.card = N) :
    Function.Injective (fun p : { p : Polynomial ℝ // p.natDegree < N } =>
      (fun x : ℝ => (p.val).eval x)) := by
  intro p q hpq
  have hagree : ∀ x ∈ pts, p.val.eval x = q.val.eval x := by
    intro x _hx
    exact congrFun hpq x
  exact Subtype.ext (poly_eq_of_agree p.val q.val p.property q.property pts hcard hagree)


end Lattice.Lib.Compiler.PolynomialLowerBound
