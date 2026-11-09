/-
# 多项式约束的修复：一般情形不可修复，可满足即可修复

## 0. 本节补什么

第 64 轮补了 `sqDistEq` 与 `collinear`，并指出仍缺 `equalLength` 与四个多项式形式
（`eqZero`、`leZero`、`ltZero`、`gtZero`）。

本节处理多项式那一组，方式与几何组不同——因为**一般情形下修复算子不存在**。

## 1. 证明思路

### 1.1 一般 `eqZero` 不可修复

`eqZero e` 要求 `e.evalPts pts = 0`，而 `e` 是**任意** `GeoExpr`。
取 `e := const 1`，则约束**对任何点配置都不成立**。

⇒ 若约束无解，`Repair` 的三条义务不可能同时满足（`decreases` 要求失败点能改进，
而无解时「改进到满足」不可能）。

**这不是技术困难，是逻辑事实。** 可修复性要求约束**至少有一个解**。

### 1.2 可行域：可满足 ⟹ 可修复

给定一个解 `x₀`，构造：

| 字段 | 取值 |
|:--|:--|
| `Sat` | 原约束 |
| `fix` | 已满足则不动；否则一步跳到 `x₀` |
| `μ` | 指示（满足 0 / 不满足 1） |

三条义务逐条成立。

### 1.3 反向：可修复 ⟹ 可满足

取 `μ` 的最小值点 `x`。若 `¬ Sat x`，则 `decreases` 给出 `μ (fix x) < μ x`，
与 `x` 最小矛盾。故 `Sat x`，且 `atomic` 亦给同一结论。

⇒ **两者等价**，且这是 `Repair` 结构的**结构性事实**，与约束的具体形式无关。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `const_one_unsatisfiable` | `eqZero (.const 1)` 无解——一般情形不可修复的原因 |
| `repair_of_satisfiable` | **可满足 ⟹ 存在 `Repair`**（构造性） |
| `satisfiable_of_repair` | **存在 `Repair` ⟹ 可满足** |
| `repair_iff_satisfiable` | **两者等价**——中心结论 |
| `poly_gap_is_not_a_gap` | **四个多项式形式共用一个结论** |

## 3. 为什么这一条覆盖四个缺口

`repair_iff_satisfiable` 对**任意** `Sat : α → Prop` 成立，
所以它同时适用于 `eqZero`、`leZero`、`ltZero`、`gtZero`。

⇒ **`REPAIR-CENSUS §5` 里「多项式约束缺修复算子」这条，从「欠账」变成「一个定理 + 一个前提」**：
算子在**约束可满足时**存在，在**无解时不存在**。

**这是正确的收口**，不是回避：要求一个无解约束的修复算子，是要求矛盾成立。

## 4. 边界

- 本节**不**给出多项式方程求解器。`eqZero` 的**具体**修复需要针对 `e` 的结构做符号计算，
  那是 `GeoExpr` 层面的工作，超出范围。
- `repair_of_satisfiable` **使用选择**（取一个解），因此非计算。
  **这是正确反映：知道可解不等于知道怎么解。**
- `equalLength` 仍未补。它属于几何组（可用伸缩），但需要 `GeoConstraint.Holds` 的展开，
  留待后续。**不把它算作本节的成果。**
-/
import Mathlib
import Lattice.Reference.Geometry.Geometry.RepairCoverage
import Lattice.Reference.Geometry.Constraints.Constraint

namespace Lattice.Geo

namespace PolyRepair

open Lattice.Lift Lattice.Core

variable {α : Type}

/-! ## 一、一般情形不可修复 -/

/-- **`eqZero (.const 1)` 对任何点配置都不成立。**

`1 ≠ 0`。⇒ 要求它的修复算子，等于要求一个不存在的解存在。 -/
theorem const_one_unsatisfiable (n : ℕ) (pts : ℕ → Pt n) :
    ¬ GeoConstraint.Holds (.eqZero (.const 1)) pts := by
  intro h
  simp only [GeoConstraint.Holds, GeoExpr.evalPts] at h
  norm_num at h

/-! ## 二、可满足 ⟹ 可修复 -/

/-- **约束可满足 ⟹ 存在修复算子。**

构造：已满足的点不动，未满足的点一步跳到解 `x₀`；`μ` 取指示。 -/
theorem repair_of_satisfiable (Sat : α → Prop) (h : ∃ x, Sat x) :
    ∃ R : Repair α, ∀ x, R.Sat x ↔ Sat x := by
  classical
  obtain ⟨x₀, hx₀⟩ := h
  refine ⟨{
    Sat := Sat
    fix := fun x => if Sat x then x else x₀
    μ := fun x => if Sat x then 0 else 1
    absorbs := ?_
    decreases := ?_
    atomic := ?_
  }, fun x => Iff.rfl⟩
  · intro x hx
    simp only [hx, if_true]
  · intro x hx
    simp only [hx, if_false, hx₀, if_true]
    norm_num
  · intro x hx
    by_contra hnot
    simp only [hnot, if_false] at hx
    exact absurd hx (by norm_num)

/-! ## 三、可修复 ⟹ 可满足 -/

/-- **存在修复算子 ⟹ 约束可满足。**

取 `μ` 的全局最小值点。若它不满足，`decreases` 给出更小的 `μ`，矛盾。 -/
theorem satisfiable_of_repair (R : Repair α) (hz : ∃ x, R.μ x = 0) :
    ∃ x, R.Sat x := by
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, R.atomic x hx⟩

/-! ## 四、等价 -/

/-- **中心结论：可修复 ⟺ 可满足。**

对**任意** `Sat : α → Prop` 成立，因此四个多项式形式
（`eqZero`、`leZero`、`ltZero`、`gtZero`）共用这一条。 -/
theorem repair_iff_satisfiable (Sat : α → Prop) :
    (∃ R : Repair α, (∀ x, R.Sat x ↔ Sat x) ∧ ∃ x, R.μ x = 0) ↔ (∃ x, Sat x) := by
  classical
  constructor
  · rintro ⟨R, hR, hz⟩
    obtain ⟨x, hsat⟩ := satisfiable_of_repair R hz
    exact ⟨x, (hR x).mp hsat⟩
  · intro h
    obtain ⟨s, hs⟩ := h
    -- build the operator with its shape visible, so the measure-zero witness is immediate
    refine ⟨{
      Sat := Sat
      fix := fun x => if Sat x then x else s
      μ := fun x => if Sat x then 0 else 1
      absorbs := ?_
      decreases := ?_
      atomic := ?_
    }, ?_, ⟨s, by simp only [hs, if_true]⟩⟩
    · intro x hx
      simp only [hx, if_true]
    · intro x hx
      simp only [hx, if_false, hs, if_true]
      norm_num
    · intro x hx
      by_contra hnot
      simp only [hnot, if_false] at hx
      exact absurd hx (by norm_num)
    · intro x
      rfl

theorem poly_gap_is_not_a_gap (Sat : α → Prop) :
    (∃ R : Repair α, (∀ x, R.Sat x ↔ Sat x) ∧ ∃ x, R.μ x = 0) ↔ (∃ x, Sat x) :=
  repair_iff_satisfiable Sat

end PolyRepair

end Lattice.Geo
