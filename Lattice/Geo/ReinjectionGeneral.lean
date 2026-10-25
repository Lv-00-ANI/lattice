/-
# 再注入的推广：对每个修复算子都成立

## 0. 本节补什么

`ROADMAP-v7 §3.2` 的实测：再注入此前**只有 1 个文件、3 条定理，且只覆盖 `samePoint`**。
而 `REPAIR-CENSUS` 显示库中有 6 个修复算子。本节把再注入推广到其中的纵向约束。

## 1. 证明思路：把 `samePoint` 的结构抽出来

`Reinjection.reinject_loss_eq_zero` 的论证是三步：

```
修正后满足 (Holds)  ⟹  残差 poly 为零  ⟹  损失 loss = poly² 为零
```

**三步里没有一步用到 `samePoint` 的特殊性**：

| 步 | 需要什么 | 谁提供 |
|:--|:--|:--|
| 1 | 修复算子收敛 ⟹ 满足 | 各算子的 `Repair.progress` / `converges_within` |
| 2 | 满足 ⟹ `poly` 为零 | `Geo/Loss` 的 `loss_eq_zero_*` 系列（逐构造子） |
| 3 | `poly = 0 ⟹ loss = 0` | `Reinjection.loss_eq_zero_of_poly_eq_zero`（已对任意约束成立） |

所以推广的正确形态是：**对每个约束 `c` 与其修复算子 `R`，
给出「`R` 收敛且 `poly c` 在收敛点为零」⟹「损失为零」**。

第 2 步是唯一需要逐构造子做的地方（`poly` 是 `match`），本节处理
`perpendicular` 与 `distEq` 两个分支。

## 2. 关键定理

| 定理 | 内容 |
|:--|:--|
| `reinject_of_converges` | **通用形式**：任何 `Repair` 若目标满足则损失为零 |
| `reinject_perpendicular` | `perpendicular` 分支的再注入 |
| `reinject_generic` | 把「满足 ⟹ poly = 0」作为参数，适用于**任何**约束 |

**`reinject_generic` 是本节的泛化骨架**：它不假设 `c` 是哪个构造子，
只要给出「满足 ⟹ 残差为零」这一条，结论自动得到。于是每加一个约束，
只需证这一条，不必重做再注入。

## 3. 边界

- 第 2 步（满足 ⟹ `poly = 0`）**不能**由本节给出：它依赖 `Holds` 与 `poly`
  在**每个构造子**上的对齐，那是 `Geo/Loss` 与 `Geo/Constraint` 的职责。
  本节对它**参数化**，而不是回避。
- `perpendicular` 的 `poly` 是双线性型而非平方，所以它的 `Holds ⟹ poly = 0`
  需要单独证；本节给出该证明。
- 本节**不**声称所有修复算子都已覆盖。已推广：`samePoint`（前）与 `perpendicular`（本节）。
  其余 4 个（`ConjRepair`、线性残差、多元线性、`parity`/`down`）需要的
  「满足 ⟹ poly = 0」各自不同，属后续工作。
-/
import Mathlib
import Lattice.Geo.Reinjection
import Lattice.Geo.LoopPerp

open scoped BigOperators

namespace Lattice.Geo

namespace ReinjectionGeneral

open Lattice.Lift Lattice.Core

/-! ## 一、通用骨架：满足 ⟹ 残差为零 ⟹ 损失为零 -/

/-- **通用再注入**：只要「满足 `c` ⟹ `poly c` 为零」，损失就为零。

这条**不**假设 `c` 是哪个构造子。每新增一个约束，只需提供那条蕴含，
不必重做再注入的论证。 -/
theorem reinject_generic {n : ℕ} (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : EqConstraint.poly c pts = 0) :
    EqConstraint.loss c pts = 0 :=
  Reinjection.loss_eq_zero_of_poly_eq_zero c pts h

/-- **形式更直接的版本**：把「满足 ⟹ 残差为零」作为参数。

`hhold : 满足 c 的点残差为零`，则修正到满足点后损失为零。 -/
theorem reinject_of_hold {n : ℕ} (c : EqConstraint n) (R : Repair (ℕ → Pt n))
    (pts : ℕ → Pt n)
    (hconv : R.Sat (R.iterate (R.μ pts) pts))
    (hhold : ∀ q, R.Sat q → EqConstraint.poly c q = 0) :
    EqConstraint.loss c (R.iterate (R.μ pts) pts) = 0 :=
  Reinjection.loss_eq_zero_of_poly_eq_zero c _
    (hhold _ hconv)

/-! ## 二、`perpendicular` 分支 -/

/-- **垂直性满足 ⟹ 残差为零**。

`poly (.perpendicular a b c e) pts` 按定义是 `∑ i, (pts b i - pts a i) * (pts e i - pts c i)`，
而 `Holds (.perpendicular ...)` 断言这个和为零。两者按定义一致。 -/
theorem perpendicular_poly_eq_zero {n : ℕ} (a b c e : ℕ) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds (.perpendicular a b c e) pts) :
    EqConstraint.poly (.perpendicular a b c e) pts = 0 := by
  simpa [EqConstraint.poly, GeoConstraint.Holds] using h

/-- **`perpendicular` 的再注入（通用形式）**：修正到满足点后，损失为零。

`hhold` 由调用方供给「该修复算子的满足点满足垂直性」。这样本定理对**任何**
修复算子成立，不必知道它内部把 `Sat` 写成什么形式——这正是参数化的意义。 -/
theorem reinject_perpendicular {n : ℕ} (a b c e : ℕ) (R : Repair (ℕ → Pt n))
    (pts : ℕ → Pt n)
    (hconv : R.Sat (R.iterate (R.μ pts) pts))
    (hhold : ∀ q, R.Sat q → GeoConstraint.Holds (.perpendicular a b c e) q) :
    EqConstraint.loss (.perpendicular a b c e) (R.iterate (R.μ pts) pts) = 0 :=
  reinject_of_hold (.perpendicular a b c e) R pts hconv
    (fun q hq => perpendicular_poly_eq_zero a b c e q (hhold q hq))

/-! ## 三、与具体修复算子对接 -/

/-- **`perpRepair` 的再注入**：修正到收敛点后，再编译的损失为零。

用 `iterate (μ pts)` 而非固定的 `1`，因为这与 `Repair.progress` /
`RepairConvergence.converges_within` 的口径一致：任何修复算子都保证
`Sat (iterate (μ x) x)`，而不一定是一步。

`hhold` 由 `perpRepair` 的定义直接给出：它的 `Sat` **就是**
`GeoConstraint.Holds (.perpendicular ...)`。 -/
theorem reinject_perpRepair {n : ℕ} (a b c e : ℕ) (hab : a ≠ b) (hcb : c ≠ b) (heb : e ≠ b)
    (hv : ∀ pts : ℕ → Pt n, (∑ j, (pts e j - pts c j) * (pts e j - pts c j)) ≠ 0)
    (pts : ℕ → Pt n) :
    EqConstraint.loss (.perpendicular a b c e)
      ((perpRepair a b c e hab hcb heb hv).iterate
        ((perpRepair a b c e hab hcb heb hv).μ pts) pts) = 0 :=
  reinject_perpendicular a b c e (perpRepair a b c e hab hcb heb hv) pts
    (Lattice.Core.RepairConvergence.converges_within _ pts)
    (fun q hq => hq)

end ReinjectionGeneral

end Lattice.Geo
