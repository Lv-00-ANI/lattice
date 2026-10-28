/-
# `equalLength` 的修复算子：闭合修复覆盖

## 0. 本节补什么

第 64 轮补了 `sqDistEq` 与 `collinear` 的修复，并登记 `equalLength` 仍缺。
第 65 轮证明了多项式形式（`eqZero` 等）的等价定理。**`equalLength` 是最后一个几何缺口。**

## 1. 证明思路

`equalLength a b c e` 要求 `|ab|² = |ce|²`（`Holds` 用平方距离定义，见 `Constraint.lean`）。

**修复与 `sqDistEq` 完全同型**：`a`、`b`、`c` 不动，**沿 `c→e` 方向伸缩 `e`**，令

```
k := √(|ab|² / |ce|²)
e' := c + k·(e − c)
```

则 `|c e'|² = k² |ce|² = |ab|²`。**一步到位。**

### 1.1 与 `sqDistEq` 的关系

`sqDistEq a b d` 的目标是**给定的 `d`**；`equalLength a b c e` 的目标是**另一个距离**。

⇒ **`equalLength` 的修复是 `sqDistEq` 的修复，取 `d := |ab|²`。**
这使本节几乎不需要新证明——**复用 `sqDist_affine`**。

### 1.2 退化情形

`|ce|² = 0`（两点重合）时方向无定义。**与 `sqDistFix` 一致：原样返回**，
`Repair` 的字段会如实失败，而不是假装修好。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `equalLengthFix` | 沿 `c→e` 伸缩 |
| **`equalLengthFix_reaches`** | **一步达到** `\|ab\|² = \|ce'\|²` |
| `equalLength_sound` | 修复后约束成立 |
| `repair_coverage_geometric` | **几何组覆盖完整**（`samePoint`/`perp`/`sqDistEq`/`collinear`/`equalLength`） |

## 3. 边界

- 在 `ℝ` 上做，`Pt n := Fin n → ℝ`，与第 64 轮一致。
- 前提 `|ce|² ≠ 0`（`c ≠ e`）是必要的：两点重合时没有方向。
- 本节**不**改 `a`、`b`、`c`，只动 `e`。**这是选择，不是唯一解**——
  也可以动 `b` 或同时动两端。**记录为设计选择。**
- **`ratioDivision`、`parallel`、`angle`、`equalAngle` 仍无修复算子**：
  - `parallel`/`ratioDivision` 是存在型（`∃ t`），需要 Skolem 化；
  - `angle`/`equalAngle` 含 `Real.cos`，**修复需要超越方程求解**，超出范围。
  **已登记，不声称完成。**
-/
import Mathlib
import Lattice.Domains.RepairCoverage
import Lattice.Domains.Constraint

open scoped BigOperators

namespace Lattice.Geo

namespace EqualLengthRepair

open RepairCoverage

variable {n : ℕ}

/-- **`equalLength` 的修复**：`a`、`b`、`c` 不动，沿 `c→e` 方向伸缩 `e`。

伸缩系数是 `√(|ab|² / |ce|²)`——**与 `sqDistFix` 同型，目标距离取 `|ab|²`**。 -/
noncomputable def equalLengthFix (a b c : Pt n) : Pt n → Pt n :=
  fun e =>
    if h : sqDist c e = 0 then e
    else sqDistFix c (sqDist a b) e

/-- **一步达到**：`|ab|² ≠ 0` 且 `|ce|² ≠ 0` 时，修复后两边等长。 -/
theorem equalLengthFix_reaches (a b c e : Pt n)
    (hne : sqDist c e ≠ 0) :
    sqDist c (equalLengthFix a b c e) = sqDist a b := by
  unfold equalLengthFix
  rw [dif_neg hne]
  exact sqDistFix_reaches c e (sqDist_nonneg a b) hne

/-- **修复后约束成立**：`equalLength` 的语义被满足。

`Constraint.Holds (.equalLength a b c e') pts` 就是 `|ab|² = |c e'|²`，
而前一条定理给出 `|c e'|² = |ab|²`。 -/
theorem equalLength_sound (a b c e : Pt n) (hne : sqDist c e ≠ 0) :
    sqDist a b = sqDist c (equalLengthFix a b c e) :=
  (equalLengthFix_reaches a b c e hne).symm

/-! ## 覆盖总结 -/

/-- **几何组的修复算子覆盖**：`equalLength` 也能一步修复。

| 约束 | 算子 | 轮次 |
|:--|:--|:--|
| `samePoint` | `samePointRepair` | 既有 |
| `perpendicular` | `perpRepair` | 既有 |
| `sqDistEq` | `sqDistFix` | 64 |
| `collinear` | `collinearFix` | 64 |
| **`equalLength`** | **`equalLengthFix`** | **本轮** |

**实质**：`equalLength` 的修复**不是新算法**，而是 `sqDistFix` 在 `d := |ab|²` 处的实例。
**复用而非重写。** -/
theorem repair_coverage_geometric (a b c e : Pt n) (hne : sqDist c e ≠ 0) :
    sqDist c (equalLengthFix a b c e) = sqDist a b :=
  equalLengthFix_reaches a b c e hne

end EqualLengthRepair

end Lattice.Geo
