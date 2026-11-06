# `Lattice/Domains/Constraints` -- **[待移除]**

> **本目录待移除。仅作参考与反例来源。主线在 [`Lattice/Core/CIC/`](../../Core/CIC/)。**
> **移动时机：CIC 版 T0–T8 就绪后（规划阶段 3）。**

## 为什么待移除

**这个目录定义 `GeoConstraint` —— 几何载体的十二个约束构造子。**

**它是 `Lattice/Domains/Geometry` 的语法基础，随它一起归档。**

### 十二个构造子的语义

| 构造子 | 几何语义 | CIC 对应 |
|:--|:--|:--|
| **`samePoint a b`** | **`Φ a = Φ b`** | **`Eq (pt a) (pt b)`** |
| **`midpoint a b c`** | **`2·Φ c = Φ a + Φ b`** | **`Eq (mul 2 (pt c)) (add (pt a) (pt b))`** |
| **`eqZero e`** | **`eval e Φ = 0`** | **`Eq (evalTerm e) zero`** |
| **`leZero` / `ltZero` / `gtZero`** | **多项式不等式** | **`Le` / `Lt`** |
| **`sqDistEq` / `equalLength`** | **距离** | **`Eq (sqDistTerm ...)`** |
| **`perpendicular` / `parallel` / `collinear` / `rightAngle`** | **点积 / 叉积** | **`Eq (dotTerm ...) zero`** |

**每一条「几何见证 ⟹ term 见证」都要跨过同一个障碍：点配置与构造项之间没有自然的桥。**
**=> 详见 [`Lattice/Domains/Geometry/README.md`](../Geometry/README.md)。**

## 现在能做什么，不能做什么

**能：**

- **读这些构造子作为几何约束的参考；**
- **从中取反例；**
- **在移入 `Reference/` 之后继续引用（但不再参与 `lake build`）。**

**不能：**

- **在主线里新增对 `Domains/Constraints` 的 import；**
- **让新的 `ProofComplete` 合取项依赖本目录。**

## 相关内容

- **[`Lattice/Domains/Geometry/README.md`](../Geometry/README.md)** —— 几何载体的归档说明
- **[`CARRIER-CIC.md`](../../../CARRIER-CIC.md)** —— CIC 载体，主线
- **[`Lattice/Core/CIC/Syntax.lean`](../../Core/CIC/Syntax.lean)** —— `Term` / `Level` / `SortKind`
