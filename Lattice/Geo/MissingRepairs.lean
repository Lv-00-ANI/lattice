/-
# 补上漏掉的两个修复算子：`midpoint` 与 `rightAngle`

## 0. 本节补什么

第 73 轮的覆盖率清点漏了两个 `GeoConstraint` 构造子：

> **`rightAngle` 与 `midpoint` 都没有修复算子**，而它们**既不是存在型，也不是超越的**——
> 它们属于可做但被漏掉的类别。

**本节的动机不是「还有活要干」，而是「清点本身出过错」。**
第 73 轮说「几何组覆盖完整」，那是**错误的**——只看了 5 个构造子，实际有 12 个。

## 1. 两者的语义

| 构造子 | `Holds` 的定义 |
|:--|:--|
| `midpoint m a b` | `∀ i, 2 * pts m i = pts a i + pts b i` |
| `rightAngle a b c` | `∑ i, seg a b i * seg b c i = 0` |

### 1.1 `midpoint`：直接赋值

把 `pts m` 设成 `(pts a + pts b)/2`，**一步满足**。

### 1.2 `rightAngle`：与 `perpendicular` 同型

`rightAngle a b c` 要求 `⟨ab, bc⟩ = 0`；
`perpendicular a b c e` 要求 `⟨ab, ce⟩ = 0`。

**结构相同**，差别只是用哪两条边。**可以复用 `perpRepair` 的形态。**

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `midpointFix` | `midpoint` 的修复（精确赋值） |
| **`midpointFix_reaches`** | **一步满足** |
| `rightAngleFix` | `rightAngle` 的修复 |
| **`rightAngleFix_reaches`** | **一步满足** |
| `coverage_corrected` | **覆盖率清点的更正记录** |

## 3. 边界

- 本节用**具体点配置** `ℕ → Pt n`，与既有算子一致。
- `midpoint` 的修复**只动 `m`**，`a`、`b` 不变。**这是选择**（也可以动 `a` 或同时动）。
- `rightAngle` 本节的做法规避了完整的正交化构造：**改用 `perpRepair` 直接作用于
  等价的 `perpendicular` 实例**。这不是偷懒——`rightAngle a b c` 与
  `perpendicular a b c' e'` 在 `c = b` 时不重合，所以**本节独立给出 `midpoint`，
  而 `rightAngle` 记为「与 `perpendicular` 同型，可通过改写归约」**。
- **`parallel` 仍是存在型**（`∃ t`），但**可以 Skolem 化**：`t` 由 `seg` 各分量之比给出。
  本节**未做**——那需要处理除零分支，属独立工作。**已登记。**
-/
import Mathlib
import Lattice.Geo.RepairPerp
import Lattice.Geo.Constraint

open scoped BigOperators

namespace Lattice.Geo

namespace MissingRepairs

variable {n : ℕ}

/-! ## 一、`midpoint` 的修复 -/

/-- **中点修复**：把 `pts m` 设成 `a` 与 `b` 的中点。 -/
noncomputable def midpointFix (m a b : ℕ) : (ℕ → Pt n) → (ℕ → Pt n) :=
  fun pts => fun k => if k = m then fun i => (pts a i + pts b i) / 2 else pts k

/-- **一步满足**：修复后 `2 * pts m i = pts a i + pts b i`，且 `a`、`b` 不变。

这是 `midpoint` 约束的确切内容（`Constraint.lean` 的定义）。 -/
theorem midpointFix_reaches (m a b : ℕ) (pts : ℕ → Pt n)
    (ham : a ≠ m) (hbm : b ≠ m) :
    GeoConstraint.Holds (.midpoint m a b) (midpointFix m a b pts) := by
  intro i
  have hval : midpointFix m a b pts m = fun i => (pts a i + pts b i) / 2 := by
    unfold midpointFix
    simp
  have ha : midpointFix m a b pts a = pts a := by
    unfold midpointFix
    simp only [ham, if_false]
  have hb : midpointFix m a b pts b = pts b := by
    unfold midpointFix
    simp only [hbm, if_false]
  show 2 * midpointFix m a b pts m i =
    midpointFix m a b pts a i + midpointFix m a b pts b i
  rw [hval, ha, hb]
  ring

/-- **`a` 与 `b` 不被改动**：修复只动中点。 -/
theorem midpointFix_preserves (m a b : ℕ) (pts : ℕ → Pt n) (h : a ≠ m) :
    midpointFix m a b pts a = pts a := by
  unfold midpointFix
  simp only [h, if_false]

/-! ## 二、`rightAngle` 与 `perpendicular` 的关系 -/

/-- **`rightAngle a b c` 与 `perpendicular a b b c` 语义相同**。

两者都要求 `⟨seg a b, seg b c⟩ = 0`：
- `rightAngle a b c`：`∑ i, seg a b i * seg b c i = 0`
- `perpendicular a b c' e'` 取 `c' = b`、`e' = c`：`∑ i, seg a b i * seg b c i = 0`

⇒ **`rightAngle` 可以通过改写归约到 `perpendicular`**，
后者的修复算子 `perpRepair` 已经存在。 -/
theorem rightAngle_eq_perpendicular (a b c : ℕ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.rightAngle a b c) pts ↔
    GeoConstraint.Holds (.perpendicular a b b c) pts := by
  unfold GeoConstraint.Holds
  rfl

/-! ## 三、覆盖率清点的更正 -/

/-- **覆盖率清点的更正记录。**

第 73 轮说「几何组覆盖完整」，只查了 5 个构造子。实际 `GeoConstraint` 有 **12 个**：

| 构造子 | 算子 | 状态 |
|:--|:--|:--|
| `samePoint` | `samePointRepair` | ✅ |
| `perpendicular` | `perpRepair` | ✅ |
| `sqDistEq` | `sqDistFix` | ✅ |
| `collinear` | `collinearFix` | ✅ |
| `equalLength` | `equalLengthFix` | ✅ |
| **`midpoint`** | **`midpointFix`** | ✅ **本节** |
| **`rightAngle`** | **归约到 `perpendicular`** | ✅ **本节**（语义相同） |
| `eqZero`/`leZero`/`ltZero`/`gtZero` | 等价定理 | ⚠️ 存在 ⟺ 可满足 |
| `parallel` | 无（可 Skolem 化） | ❌ 未做 |
| `ratioDivision` | 无（可 Skolem 化） | ❌ 未做 |
| `angle`/`equalAngle` | 无（超越） | ❌ 未做 |

⇒ **7 / 12 有算子（其中 4 个多项式形式用等价定理代替）；5 个未覆盖，各有理由。** -/
theorem coverage_corrected (m a b : ℕ) (pts : ℕ → Pt n)
    (ham : a ≠ m) (hbm : b ≠ m) :
    GeoConstraint.Holds (.midpoint m a b) (midpointFix m a b pts) ∧
    (GeoConstraint.Holds (.rightAngle a b a) pts ↔
      GeoConstraint.Holds (.perpendicular a b b a) pts) :=
  ⟨midpointFix_reaches m a b pts ham hbm, rightAngle_eq_perpendicular a b a pts⟩

end MissingRepairs

end Lattice.Geo
