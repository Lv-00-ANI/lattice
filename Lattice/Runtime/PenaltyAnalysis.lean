/-
# 平方残差的局部极小分析

## 为什么这一层放在 `lift` 而不是 `lib`

这三条引理（`hasFDerivAt_sq`、`sq_localMin_dichotomy`、`sq_eq_zero_of_localMin`）
只依赖 Mathlib 的分析库与 Fermat 一阶条件，**不使用 `lib` 层的任何概念**。
它们原先位于 `Lattice.Lib.Penalty.PolyExact`，而该模块为了多项式惩罚的其它结论
必须引用 `Lib.Linear.PenaltyMatrix`。结果是：任何 `lift` 层的模块若要用
「局部极小处残差为零」，就必须反向 import `lib`，违反分层铁律
`core < slots < lift < lib < root`（门禁 I4 会报）。

把纯分析部分下沉到 `lift` 消除了这个反向依赖。`lib` 层的
`PolyExact` 保留多项式特有的内容，并**引用**这里的引理，
所以不产生重复：每个命题只有一处定义（门禁 I3）。

## 本文件的内容

| 命题 | 陈述 |
|:--|:--|
| `hasFDerivAt_sq` | `∇(f²)(x) = 2·f(x) • ∇f(x)` |
| `sq_localMin_dichotomy` | 平方的局部极小处，`f x = 0` 或 `f' = 0` |
| `sq_eq_zero_of_localMin` | 若另有 `f' ≠ 0`，则 `f x = 0` |

这三条合起来是四类几何精确性定理（标量、对角、满射矩阵、垂直约束）的共同落点。
第三条是前两条的直接推论，它被单独列出是因为下游引用的是「残差为零」，
而不是二分法本身。

## 边界

`f' ≠ 0` 是实质前提，不可省：双线性残差（如 `perpendicular`）的梯度在整个子空间上
消失，那里二分法的第二个分支被占据，结论为假。这不是技术困难，而是命题的必要条件。
-/
import Mathlib

open scoped ContinuousLinearMap

namespace Lattice.Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **平方残差的导数。** `∇(f²)(x) = 2·f(x) • ∇f(x)`，由乘积法则得到。

系数 `2` 不是装饰：下面的 Fermat 论证在 `f' ≠ 0` 时要把它除掉。 -/
theorem hasFDerivAt_sq {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => f y ^ 2) ((2 * f x) • f') x := by
  have hmul : HasFDerivAt (fun y => f y * f y) (f x • f' + f x • f') x := h.mul h
  have hcoe : (f x • f' + f x • f') = (2 * f x) • f' := by
    ext v
    simp [two_mul, add_mul]
  have hfun : (fun y => f y * f y) = (fun y => f y ^ 2) := by
    funext y; ring
  rw [hfun, hcoe] at hmul
  exact hmul

/-- **平方残差的二分支。** 在平方的局部极小点处，要么残差为零，要么它的导数为零。

这是 Fermat 条件在此处的确切内容，也是反例存在的原因：「导数为零」这一分支
对多项式是被占据的（`constEmbedding` 就是常数情形）。 -/
theorem sq_localMin_dichotomy {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hmin : IsLocalMin (fun y => f y ^ 2) x) :
    f x = 0 ∨ f' = 0 := by
  by_cases hf : f x = 0
  · exact Or.inl hf
  · right
    -- `f' ≠ 0` 给出一个方向使 `f'` 非零：恒零映射是唯一处处为零的映射
    by_contra hne
    have hnotall : ¬ ∀ v, f' v = 0 := by
      intro h
      exact hne (ContinuousLinearMap.ext h)
    obtain ⟨v, hv⟩ := not_forall.mp hnotall
    have hzero : (2 * f x) • f' = 0 :=
      IsLocalMin.hasFDerivAt_eq_zero hmin (hasFDerivAt_sq hderiv)
    have hval : (2 * f x) * f' v = 0 := by
      have := congrFun (congrArg DFunLike.coe hzero) v
      simpa using this
    rcases mul_eq_zero.mp hval with h | h
    · rcases mul_eq_zero.mp h with h2 | hfx
      · norm_num at h2
      · exact absurd hfx hf
    · exact hv h

/-- **非零导数处的平方惩罚精确性。**

若残差的导数在平方的局部极小点处不为零，则残差在该点为零。

与「无此假设则命题为假」相对照：反例是 `Lattice.Lift.PenaltyEmbedding.sound_not_exact`，
那是被**证明**的，不是被假定的。 -/
theorem sq_eq_zero_of_localMin {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hmin : IsLocalMin (fun y => f y ^ 2) x) : f x = 0 := by
  rcases sq_localMin_dichotomy hderiv hmin with h | h
  · exact h
  · exact absurd h hne

end Lattice.Lift
