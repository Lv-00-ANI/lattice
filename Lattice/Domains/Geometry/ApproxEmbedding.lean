/-
# 几何约束的逼近嵌入：把抽象链实例化到具体载体

## 0. 本节做什么

`Lattice.Lift.EndToEndApproximation` 给出了**抽象**的逼近链：

```
采样点验证通过  ⟹  全域残差 ≤ ε₀ + L·δ
```

抽象链要能用，必须有一个**具体的 `ResidualEmbedding` 实例**。本文件为几何约束
`EqConstraint n` 建立这个实例。

## 1. 为什么几何约束天然满足 `ResidualEmbedding`

`ResidualEmbedding` 要求 `loss = resid ^ 2`。几何损失的定义（`Geo/Loss.lean:87`）是

```lean
noncomputable def loss (c : EqConstraint n) (pts : ℕ → Pt n) : ℝ := poly c pts ^ 2
```

——**恰好是残差的平方**，残差就是 `poly c pts`。实例化因此不需要新数学，
只需把已有定义接进结构。

这不是巧合：`ApproxExact` 之所以坚持加这个字段（而不是直接对任意 `loss` 陈述界），
正因为**只有 `loss = resid²` 时「损失小 ⟹ 残差小」才成立**。
几何损失从一开始就是这个形状，所以它是这个框架的**原生载体**。

## 2. `Sat` 的取法

`Sat c pts` 取 `poly c pts = 0`，即「残差为零」。

这比构造一个 `GeoConstraint` 再调 `Holds` 更合适，理由有三：

1. `Holds` 对 `leZero`/`ltZero`/`collinear`/`parallel` 的分支**不是**「某个多项式为零」，
   把它们强行塞进同一形状会丢掉信息；
2. `poly` 的零点集**按构造**就是 `EqConstraint` 的解集（见 `Geo/Loss.lean` 的
   `loss_eq_zero_*` 系列定理）；
3. 本文件是**残差层**的实例，不是约束语义层的结论，后者由 `Geo/Exact` 承担。

## 3. 本节给出的定理

| 定理 | 内容 |
|:--|:--|
| `eqConstraintResidualEmbedding` | `EqConstraint n` 的 `ResidualEmbedding` 实例 |
| `eqConstraint_loss_le_sq_of_resid_le` | 残差 ≤ ε ⟹ 损失 ≤ ε² |

## 4. 边界

- 本节**不**给出 `poly` 的 Lipschitz 常数。那需要先界定 `poly` 的次数与点集定义域，
  是另一个计算（当前库中没有）。因此本文件只做「实例化」这一步，
  **不声称几何约束满足采样界**。
- `loss_eq_sq` 用 `rfl` 证明，因为 `EqConstraint.loss` 的定义就是 `poly ^ 2`。
  若将来损失定义改为非平方形式，这条会编译失败——这正是我们要的：
  结构的一致性由编译器看守。
-/
import Mathlib
import Lattice.Runtime.EndToEndApproximation
import Lattice.Domains.Constraints.Loss

open scoped ContinuousLinearMap

namespace Lattice.Geo

open Lattice.Lift

/-! ## 一、几何约束上的残差嵌入 -/

/-- 点序列上的乘积拓扑：两点靠近指在**每个坐标**上靠近。

`ResidualEmbedding` 要求 `TopologicalSpace`（B 层义务是拓扑性的，见 `ApproxExact` 头部），
而 `ℕ → Pt n` 是函数类型，其拓扑是乘积拓扑。这里显式给出，
因为 `Pt n` 是 `Core.Point ℝ n` 的 `abbrev`，实例推断不会自动展开。

选乘积拓扑而非其它，是因为它正是残差界需要的那一个：
「配置靠近」应当意味着「每个点的位置都靠近」。 -/
instance (n : ℕ) : TopologicalSpace (ℕ → Pt n) := inferInstance

/-- **`EqConstraint` 是 `ResidualEmbedding` 的一个实例。**

损失按定义是 `poly c pts ^ 2`（`Geo/Loss.lean:87`），所以残差取 `poly c pts`，
`loss_eq_sq` 因此是 `rfl`。

`Sat` 取 `poly c pts = 0`。 -/
noncomputable def eqConstraintResidualEmbedding (n : ℕ) :
    ResidualEmbedding (EqConstraint n) (ℕ → Pt n) where
  loss := fun c pts => EqConstraint.loss c pts
  Sat := fun c pts => EqConstraint.poly c pts = 0
  resid := fun c pts => EqConstraint.poly c pts
  loss_eq_sq := fun c pts => rfl

/-- **残差界 ⟹ 损失界（几何实例）。**

这是 `ApproxExact.loss_le_sq_of_resid_le` 在几何载体上的实例化：
若 `poly c pts` 的绝对值不超过 `ε`，则损失不超过 `ε²`。

它的用处是**把采样验证的结论转回损失层**，从而可以与其他损失层的定理（如
`RealTotalLoss` 的界）并列使用。 -/
theorem eqConstraint_loss_le_sq_of_resid_le (n : ℕ) (c : EqConstraint n) (pts : ℕ → Pt n)
    {ε : ℝ} (hε : 0 ≤ ε) (h : |EqConstraint.poly c pts| ≤ ε) :
    EqConstraint.loss c pts ≤ ε ^ 2 :=
  loss_le_sq_of_resid_le (eqConstraintResidualEmbedding n) hε c h

end Lattice.Geo
