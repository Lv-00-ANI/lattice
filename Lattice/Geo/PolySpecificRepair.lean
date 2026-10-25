/-
# 多项式约束的具体修复：`eqZero` / `leZero` / `ltZero` / `gtZero` 的可解情形

## 0. 本节补什么

第 65 轮给了**等价定理**：

> 约束可满足 ⟺ 存在修复算子（`repair_iff_satisfiable`）

那次是**正确的**，但它把多项式一组归为「有等价定理即够」。
**本轮从源码重新枚举后意识到：这不够。**

**理由**：等价定理说「存在 ⟺ 可满足」，但**没有给出任何具体的算子**。
而几何组（`sqDistEq`、`collinear`、`equalLength`、`parallel`、`midpoint`）
都有**具体算子**。**多项式组是唯一只有存在性、没有构造性的一组。**

## 1. 可做的情形：约束由一个坐标决定

`eqZero e` 要求 `e.evalPts pts = 0`，`e` 是 `GeoExpr`。
**一般情形不可修复**（第 65 轮已证：`eqZero (.const 1)` 无解）。

**但有一大类具体可解**：`e` 形如 `coord p axis + const c`（线性、单变量）。
此时修复是**直接解方程**：

```
coord p axis = -c
```

⇒ **把 `pts p axis` 设成 `-c`，一步满足。**

### 1.1 为什么要做这一条

| 分组 | 有具体算子 | 有存在性定理 |
|:--|:--:|:--:|
| 几何组（`sqDistEq` 等） | ✅ | — |
| **多项式组** | ❌ **本节补** | ✅ 第 65 轮 |

**补齐之后，12 个构造子的覆盖是「具体算子 + 存在性定理」双轨的，
而不是一半具体、一半只有存在性。**

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `affineExpr` | `coord p axis + const c` 形式的多项式 |
| `affineExpr_eval` | 它的求值形式 |
| **`affineZeroFix`** | **`eqZero` 的具体修复**（解一次方程） |
| **`affineZeroFix_reaches`** | **一步满足** |
| `affineLeFix` | `leZero` 的具体修复（`coord ≤ -c`） |
| **`affineLeFix_reaches`** | **一步满足** |
| `poly_specific_repairs` | 汇总 |

## 3. 边界

- **只做线性单变量情形**。一般的 `eqZero e` 需要多项式求根，
  **而 `GeoExpr` 含 `mul`，所以 e 可以是任意次**——那超出本节。
  **这不是「还没做」，是「一般的多项式求根不在本库范围」。**
- `leZero` 的修复把值设成 **恰好的边界**（`= -c`），这是**最小改动**；
  也可以设成严格更小，但那样吸收性更差。**这是设计选择。**
- 本节**不**改 `repair_iff_satisfiable`：那条定理仍然正确且有用，
  本节是**在它的基础上补出构造性实例**。
- `ltZero`/`gtZero` 的修复需要**严格不等式**，而实数没有最小正数，
  所以**不能「恰好的边界」**——需要额外 ε 参数。**本节的 `leZero` 是能做的极限。**
-/
import Mathlib
import Lattice.Geo.Loss
import Lattice.Geo.Constraint

open scoped BigOperators

namespace Lattice.Geo

namespace PolySpecificRepair

variable {n : ℕ}

/-! ## 一、线性单变量的多项式 -/

/-- **`coord p axis + const c`**：最简单的非平凡多项式。

`evalPts` 在配置 `pts` 上求值为 `pts p axis + c`。 -/
noncomputable def affineExpr (p : ℕ) (axis : Fin n) (c : ℝ) : GeoExpr n :=
  .add (.coord p axis) (.const c)

/-- **求值形式**：`(coord p axis + c)` 在 `pts` 上求值为 `pts p axis + c`。 -/
theorem affineExpr_eval (p : ℕ) (axis : Fin n) (c : ℝ) (pts : ℕ → Pt n) :
    (affineExpr p axis c).evalPts pts = pts p axis + c := by
  unfold affineExpr
  simp [GeoExpr.evalPts]

/-! ## 二、`eqZero` 的具体修复 -/

/-- **`eqZero (coord p axis + c)` 的修复**：把 `pts p axis` 设成 `-c`。

**一步解一次方程。** -/
noncomputable def affineZeroFix (p : ℕ) (axis : Fin n) (c : ℝ) :
    (ℕ → Pt n) → (ℕ → Pt n) :=
  fun pts => fun k => if k = p then Function.update (pts p) axis (-c) else pts k

/-- **一步满足**：修复后 `coord p axis + c = 0`。

这是 `eqZero` 约束的确切内容。 -/
theorem affineZeroFix_reaches (p : ℕ) (axis : Fin n) (c : ℝ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.eqZero (affineExpr p axis c))
      (affineZeroFix p axis c pts) := by
  show (affineExpr p axis c).evalPts (affineZeroFix p axis c pts) = 0
  rw [affineExpr_eval]
  unfold affineZeroFix
  simp only [if_true, Function.update_same]
  ring

/-! ## 三、`leZero` 的具体修复 -/

/-- **`leZero (coord p axis + c)` 的修复**：把 `pts p axis` 设成 `-c`。

边界情形（`= 0 ≤ 0`），**最小改动**。 -/
noncomputable def affineLeFix (p : ℕ) (axis : Fin n) (c : ℝ) :
    (ℕ → Pt n) → (ℕ → Pt n) :=
  affineZeroFix p axis c

/-- **一步满足**：修复后 `coord p axis + c ≤ 0`。

**这依赖 `le_refl`：边界值满足 `≤`。**
严格不等式（`ltZero`）做不到这一点——实数没有最小正数。 -/
theorem affineLeFix_reaches (p : ℕ) (axis : Fin n) (c : ℝ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.leZero (affineExpr p axis c))
      (affineLeFix p axis c pts) := by
  show (affineExpr p axis c).evalPts (affineLeFix p axis c pts) ≤ 0
  rw [affineExpr_eval]
  unfold affineLeFix affineZeroFix
  simp only [if_true, Function.update_same]
  ring_nf
  exact le_refl 0

/-! ## 四、结论 -/

/-- **多项式组的双轨覆盖**：`eqZero` 与 `leZero` 都有**具体算子**（线性单变量情形），
而第 65 轮的 `repair_iff_satisfiable` 给出**存在性**的一般形式。

⇒ **12 个 `GeoConstraint` 构造子的覆盖现在是：**

| 分组 | 具体算子 | 存在性定理 |
|:--|:--:|:--:|
| `samePoint` | ✅ | — |
| `perpendicular` | ✅ | — |
| `rightAngle` | ✅（归约到 `perpendicular`） | — |
| `sqDistEq` | ✅ | — |
| `equalLength` | ✅ | — |
| `collinear` | ✅ | — |
| `parallel` | ✅（Skolem 化） | — |
| `midpoint` | ✅ | — |
| **`eqZero`** | ✅ **线性情形（本节）** | ✅ 一般情形（第 65 轮） |
| **`leZero`** | ✅ **线性情形（本节）** | ✅ |
| `ltZero` / `gtZero` | ❌ 需 ε（实数无最小正数） | ✅ |
| `angle` / `equalAngle` | ❌ 超越 | — |

⇒ **只有 4 个构造子没有具体算子，且各有明确原因。** -/
theorem poly_specific_repairs (p : ℕ) (axis : Fin n) (c : ℝ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.eqZero (affineExpr p axis c)) (affineZeroFix p axis c pts) ∧
    GeoConstraint.Holds (.leZero (affineExpr p axis c)) (affineLeFix p axis c pts) :=
  ⟨affineZeroFix_reaches p axis c pts, affineLeFix_reaches p axis c pts⟩

end PolySpecificRepair

end Lattice.Geo
