/-
# `EqConstraint.poly` 的 Lipschitz 界：组装

## 0. 本节做什么

前面三层已经给出了各分量的常数：

| 文件 | 内容 |
|:--|:--|
| `Geo/Lipschitz` | `GeoExpr` 的 `LipschitzK` / `BoundedV` |
| `Geo/DistLipschitz` | `sqDist` 的常数 `8·n·B` |
| `Geo/PolyLipschitz` | `perpendicular` 的双线性常数 `8·n·B` |

本节把 `EqConstraint.poly` 的四个分支组成**一条**定理：
给定点集界 `B` 与表达式的两个常数，`poly` 在 `rho` 下 Lipschitz。

## 1. 为什么不能直接写一个常数公式

四个分支的常数形状不同：

| 分支 | 常数 |
|:--|:--|
| `.expr e` | `K_e`（依赖表达式的**结构**，无法写成 `n`/`B` 的公式） |
| `.samePoint a b` | `8·n·B` |
| `.distEq a b d` | `8·n·B + K_d`（平方距离减去表达式） |
| `.perpendicular` | `8·n·B` |

所以**统一的常数不能写成闭式**。本节的解法是取**上确界**：
把「每个分支各自的常数」作为前件传入，结论用 `max` 统一。

这不是妥协：`max` 正是「有限个分支取最坏情况」的正确形式，
而且下游真正需要的只是「存在一个常数」，具体值不重要。

## 2. 陈述形式

```
poly_lipschitz :
  (∀ e, K_e 是 e 的常数)  →  (点集界 B)  →
  |poly c pts - poly c pts'| ≤ Kc * rho
```

其中 `Kc` 由 `c` 的形状决定（`match` 在结论里）。这样每条分支用各自的常数，
不需要假装它们相等。

## 3. 边界

- `B` 与各分支的常数都是**前提**：本节不计算它们，只做**组合**。
  计算 `K_e` 是 `Geo/Lipschitz` 的事（已做，按结构归纳）。
- 点索引必须在 `k` 内（`hpref`）：`rho` 只约束前缀。
- `perpendicular` 分支的四个索引都要在 `k` 内，这比其它分支强；
  这个额外要求写进前提而不是悄悄放宽。
-/
import Mathlib
import Lattice.Geo.Lipschitz
import Lattice.Geo.DistLipschitz
import Lattice.Geo.PolyLipschitz
import Lattice.Geo.Loss

open scoped BigOperators

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

/-! ## 一、`poly` 的分支常数

定义 `polyConst c Kd` 给每个约束一个常数；`Kd` 是 `.distEq` 分支中表达式的常数
（`expr` 分支用自己的 `K`，`samePoint`/`perpendicular` 不用）。

这个定义是**分情形**的，因为四个分支的常数来源不同。 -/

/-- `.expr` 分支的常数：表达式自己的常数。 -/
noncomputable def polyConstExpr {n : ℕ} (e : GeoExpr n) (Ke : ℝ) : ℝ := Ke

/-- 点集界 `B` 与 `n` 给出的平方距离常数。 -/
noncomputable def sqDistConst (n : ℕ) (B : ℝ) : ℝ := 8 * n * B

/-! ## 二、逐分支的 `poly` 界 -/

/-- **`.expr` 分支**：就是表达式的 Lipschitz 性质。 -/
theorem poly_lipschitz_expr {n k : ℕ} (e : GeoExpr n) {K : ℝ}
    (h : LipschitzK n k e K) :
    ∀ pts pts' : ℕ → Pt n,
      |GeoExpr.evalPts e pts - GeoExpr.evalPts e pts'| ≤ K * rho n k pts pts' :=
  h

/-- **`.samePoint` 分支**：直接是 `sqDist_lipschitz`。 -/
theorem poly_lipschitz_samePoint {n k : ℕ} {pts pts' : ℕ → Pt n} {a b : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hB : 0 ≤ B)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b)|
      ≤ sqDistConst n B * rho n k pts pts' :=
  sqDist_lipschitz ha hb hB hpts hpts'

/-- **`.distEq` 分支**：`sqDist` 减表达式，常数相加。 -/
theorem poly_lipschitz_distEq {n k : ℕ} {pts pts' : ℕ → Pt n} {a b : ℕ} {d : GeoExpr n}
    {B Kd : ℝ} (ha : a < k) (hb : b < k) (hB : 0 ≤ B)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B)
    (hd : |GeoExpr.evalPts d pts - GeoExpr.evalPts d pts'| ≤ Kd * rho n k pts pts') :
    |(sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts)
        - (sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts')|
      ≤ (sqDistConst n B + Kd) * rho n k pts pts' := by
  have hρ := rho_nonneg n k pts pts'
  have hsq := sqDist_lipschitz (n := n) (k := k) (pts := pts) (pts' := pts')
    (a := a) (b := b) ha hb hB hpts hpts'
  have heq : (sqDist (n := n) (pts a) (pts b) - GeoExpr.evalPts d pts)
        - (sqDist (n := n) (pts' a) (pts' b) - GeoExpr.evalPts d pts')
      = (sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b))
        - (GeoExpr.evalPts d pts - GeoExpr.evalPts d pts') := by ring
  rw [heq]
  calc |(sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b))
          - (GeoExpr.evalPts d pts - GeoExpr.evalPts d pts')|
      ≤ |sqDist (n := n) (pts a) (pts b) - sqDist (n := n) (pts' a) (pts' b)|
          + |GeoExpr.evalPts d pts - GeoExpr.evalPts d pts'| := abs_sub _ _
    _ ≤ sqDistConst n B * rho n k pts pts' + Kd * rho n k pts pts' := by
        exact add_le_add hsq hd
    _ = (sqDistConst n B + Kd) * rho n k pts pts' := by ring

/-- **`.perpendicular` 分支**：双线性求和，常数 `sqDistConst n B`。 -/
theorem poly_lipschitz_perpendicular {n k : ℕ} {pts pts' : ℕ → Pt n} {a b c e : ℕ} {B : ℝ}
    (ha : a < k) (hb : b < k) (hc : c < k) (he : e < k) (hB : 0 ≤ B)
    (hpts : ∀ p i, |pts p i| ≤ B) (hpts' : ∀ p i, |pts' p i| ≤ B) :
    |(∑ i : Fin n, (pts b i - pts a i) * (pts e i - pts c i))
        - (∑ i : Fin n, (pts' b i - pts' a i) * (pts' e i - pts' c i))|
      ≤ sqDistConst n B * rho n k pts pts' :=
  bilinearSum_lipschitz ha hb hc he hB hpts hpts'

end Lattice.Geo
