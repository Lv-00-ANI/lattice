/-
# `poly` 常数的具体值：单位框下的可计算常数

## 0. 本节补上什么

`Geo/PolyAssemble` 给出 `poly` 四个分支的 Lipschitz 常数，但形式是
`sqDistConst n B = 8·n·B`——含自由参数 `B`（点集界）。
`STATE-2026-10.md` 把「常数是具体值而非存在性」列为验收基线之一。

本节把 `B` 固定为几何中最自然的选择——**单位框**（每个坐标 `|xᵢ| ≤ 1`）——
于是所有常数变成**只依赖 `n` 的具体表达式**，且**可以被求值器算出数**。

## 1. 为什么单位框是自然的选择

几何约束的点列通常已归一化（三角形顶点可缩放至单位圆内）。把 `B = 1` 代入不是
特化到无意义的情形，而是**选定一个规范尺度**：

| `B` | 含义 | 常数 |
|:--|:--|:--|
| 单位框 `B = 1` | 每个坐标 `\|xᵢ\| ≤ 1` | `sqDistConst n 1 = 8n` |
| 一般 `B` | 坐标界 `B` | `8·n·B` |

关键关系：`sqDistConst n B = B · sqDistConst n 1`。单位框的常数是**基数**，
一般 `B` 只是乘以 `B`。所以算清单位框就够了一般情形。

## 2. `GeoExpr` 常数的可计算形式

`Geo/Lipschitz` 的 `K`/`B` 是抽象参数。在单位框下 `coord` 的值界是 `1`，
于是每个表达式都有**一个可计算的常数**。本节的递归函数：

```
K(coord p i) = 1              K(const c) = 0
K(add e₁ e₂) = K(e₁) + K(e₂)  K(sub e₁ e₂) = K(e₁) + K(e₂)
K(mul e₁ e₂) = K(e₁)·B(e₂) + K(e₂)·B(e₁)
```

`B` 也递归计算（值界）。两函数都由 `GeoExpr` 结构递归定义，
因此在**具体表达式上可以被求值**——这正是「常数是具体值」的意思。

## 3. 边界

- 单位框是**选定**的规范尺度，不是定理的局限：一般 `B` 由 `sqDistConst_scale` 给出。
- 本节给**常数的数值**，不重新证明 Lipschitz 性质——后者已在
  `PolyLipschitz`/`PolyAssemble` 证完。本节做的是**求值**。
- `exprConst` 的递归式与 `lipschitz_mul` 的常数一致，但本节**不重新证明**
  它对任意表达式给出有效常数；那需要一次结构归纳，属后续工作。
  本节给的是**规则与计算**，用于让常数落地为数字。
-/
import Mathlib
import Lattice.Reference.Geometry.Constraints.Lipschitz
import Lattice.Reference.Geometry.Constraints.DistLipschitz
import Lattice.Reference.Geometry.Geometry.PolyAssemble

open scoped BigOperators

namespace Lattice.Geo

/-! ## 一、常数对 `B` 的线性依赖 -/

/-- **`sqDistConst` 对 `B` 是线性的。** 单位框的常数 `8n` 是基数。 -/
theorem sqDistConst_scale (n : ℕ) (B : ℝ) :
    sqDistConst n B = B * sqDistConst n 1 := by
  unfold sqDistConst
  ring

/-- 单位框下 `sqDist` 的常数是 `8n`。 -/
theorem sqDistConst_one (n : ℕ) : sqDistConst n 1 = 8 * n := by
  unfold sqDistConst
  ring

/-! ## 二、`GeoExpr` 常数的可计算定义

`exprConst` 与 `exprBound` 都由 `GeoExpr` 结构递归。规则与
`Geo/Lipschitz` 的 `lipschitz_*`/`boundedV_*` 一致（单位框下 `coord` 的值界为 1）。 -/

mutual

/-- 单位框下表达式的 **Lipschitz 常数**。

递归规则与 `lipschitz_coord`/`lipschitz_add`/`lipschitz_mul` 一致，
但直接作用在语法树上，因此**可以求值**。 -/
def exprConst : {n : ℕ} → GeoExpr n → ℝ
  | _, .coord _ _ => 1
  | _, .const _ => 0
  | _, .add e₁ e₂ => exprConst e₁ + exprConst e₂
  | _, .sub e₁ e₂ => exprConst e₁ + exprConst e₂
  | _, .mul e₁ e₂ => exprConst e₁ * exprBound e₂ + exprConst e₂ * exprBound e₁

/-- 单位框下表达式的 **值界**。

`coord` 取单位框的 `1`；`const c` 取 `|c|`；其余按 `boundedV_*` 的规则组合。 -/
def exprBound : {n : ℕ} → GeoExpr n → ℝ
  | _, .coord _ _ => 1
  | _, .const c => |c|
  | _, .add e₁ e₂ => exprBound e₁ + exprBound e₂
  | _, .sub e₁ e₂ => exprBound e₁ + exprBound e₂
  | _, .mul e₁ e₂ => exprBound e₁ * exprBound e₂

end

/-! ## 三、具体数值（「常数是具体值」的直接证据）

`exprConst` 由 `mutual` 递归定义，其方程不是 `rfl` 形的，因此这里用
`simp only` 展开方程后 `norm_num` 收口。每条 `example` 给出**一个数字**。 -/

/-- 单个坐标的常数是 `1`。 -/
example : exprConst (n := 2) (.coord 0 0) = 1 := by
  simp only [exprConst]

/-- 常数表达式 `const 3` 的 Lipschitz 常数是 `0`（与点无关）。 -/
example : exprConst (n := 2) (.const 3) = 0 := by
  simp only [exprConst]

/-- 两个坐标相加：常数 `1 + 1 = 2`。 -/
example : exprConst (n := 2) (.add (.coord 0 0) (.coord 1 0)) = 2 := by
  simp only [exprConst]
  norm_num

/-- **两个坐标相乘：常数 `1·1 + 1·1 = 2`。** -/
example : exprConst (n := 2) (.mul (.coord 0 0) (.coord 1 1)) = 2 := by
  simp only [exprConst, exprBound]
  norm_num

/-- 值与常数混合：`mul (coord 0 0) (const 5)` 的常数是 `1·5 + 0·1 = 5`。 -/
example : exprConst (n := 2) (.mul (.coord 0 0) (.const 5)) = 5 := by
  simp only [exprConst, exprBound]
  norm_num

/-- 嵌套：`(x + y) * z` 的常数是 `2·1 + 1·2 = 4`。 -/
example : exprConst (n := 3)
    (.mul (.add (.coord 0 0) (.coord 1 1)) (.coord 2 2)) = 4 := by
  simp only [exprConst, exprBound]
  norm_num

/-! ## 四、四个分支的常数汇总（单位框） -/

/-- **`samePoint`**：单位框下常数 `8n`。 -/
theorem poly_const_samePoint (n : ℕ) : sqDistConst n 1 = 8 * n := sqDistConst_one n

/-- **`perpendicular`**：与 `samePoint` 相同，也是 `8n`。
两者是同一个双线性型估计（见 `PolyLipschitz` 文件头）。 -/
theorem poly_const_perpendicular (n : ℕ) : sqDistConst n 1 = 8 * n := sqDistConst_one n

/-- **`distEq`**：`8n + K_d`。 -/
theorem poly_const_distEq (n : ℕ) (Kd : ℝ) :
    sqDistConst n 1 + Kd = 8 * n + Kd := by
  rw [sqDistConst_one]

/-! ## 五、`sqDistConst` 的具体数值 -/

-- `n = 2` 时是 16
example : sqDistConst 2 1 = 16 := by rw [sqDistConst_one]; norm_num
-- `n = 3` 时是 24
example : sqDistConst 3 1 = 24 := by rw [sqDistConst_one]; norm_num
-- 一般 `B`：`B = 2`、`n = 3` 时是 48
example : sqDistConst 3 2 = 48 := by unfold sqDistConst; norm_num

end Lattice.Geo
