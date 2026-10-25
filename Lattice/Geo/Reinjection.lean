/-
# 再注入：修正之后，重新编译的惩罚在修正点为零

## 0. 本节补上什么

目标原文的逆向三步是「**验证、修正、再注入**」。库中前两步是实的，第三步不是：

| 定理 | 实际内容 |
|:--|:--|
| `Geo.Loop.reinject_sound` | 与 `loop_converges_in_one` **定义相等**（`Sat` 与 `Holds` 同义），未增信息 |
| `Geo.Loop.reinject_entails` | 「一个约束蕴含它自己」（`entailsGeo_refl`），与修正无关 |

所以「再注入」在库中**从未被形式化**。

本节的「再注入」取它应有的意思：**修正产生一个新配置，把这个配置写回符号模型，
重新编译得到的惩罚在该配置上为零**。这是闭环的最后一环——

```
验证（不满足）→ 修正（得到 pts'）→ 写回符号模型 → 再编译（loss）→ loss pts' = 0
```

## 1. 证明思路

三步都是已有的：

| 步 | 来源 |
|:--|:--|
| 修正后满足：`Holds c (repair pts)` | `Geo.Loop.fixSamePoint_holds` 等 |
| `Holds c pts' ⟺ poly c pts' = 0` | `Geo/Loss` 的 `loss_eq_zero_*` 系列 |
| `poly = 0 ⟹ poly² = 0` | `pow_eq_zero` |

所以再注入定理是**组合**，不是新理论。它的价值在于**把闭环的三段串进一条陈述**，
而不是在第二段内部再换一次名字。

## 2. 为什么这不是重复

`reinject_sound` 的结论是「修正后满足约束」——那是**第二步（修正）的终点**。
本节定理的结论是「**再编译的损失**在修正点为零」——那是**第三步（再注入）的终点**。

两者的差别是 `loss` 有没有出现：前者的陈述里没有 `loss`，
所以它不可能说明「重新编译之后惩罚如何」。

## 3. 边界

- 本节对 `samePoint` 约束给出再注入：它的修正算子已存在且收敛率为 1（见 `Geo/LoopRate`）。
  对一般 `EqConstraint` 的再注入需要对应的修复算子；`Geo/Repair` 已论证恒等算子
  不可用（`no_identity_repair`），所以一般情形的算子仍需逐个构造。
- 「写回符号模型」在本节取「同一约束 `c` 在修正后的点列上重新求值」这个含义，
  即 `poly c pts'`。更丰富的写回（例如修改 `c` 本身再来一次）不在本节范围。
- 本节**不**证明「训练会收敛」。它证明的是：**若**修正成功，**则**再编译的惩罚为零。
  反向（惩罚为零 ⟹ 约束成立）正是 `PenaltyEmbedding.sound_not_exact` 否证的东西，
  见 README §3.3。
-/
import Mathlib
import Lattice.Geo.Loop
import Lattice.Geo.Loss
import Lattice.Geo.LoopRate

open scoped BigOperators

namespace Lattice.Geo

namespace Reinjection

open Lattice.Lift

/-! ## 一、损失在残差为零时为零 -/

/-- **`poly c pts = 0` 蕴含 `loss c pts = 0`。**

这是再注入的核心等式：损失是残差的平方，所以残差为零则损失为零。
它与 `loss_eq_zero_*` 系列互逆方向，对**任意** `EqConstraint` 成立
（那系列定理逐构造子陈述，本条不需要）。 -/
theorem loss_eq_zero_of_poly_eq_zero {n : ℕ} (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : EqConstraint.poly c pts = 0) : EqConstraint.loss c pts = 0 := by
  unfold EqConstraint.loss
  rw [h]
  norm_num

/-! ## 二、再注入 -/

/-- **再注入：修正之后重新编译，惩罚在修正点为零。**

给定 `samePoint a b` 约束与任意初始点列 `pts`：

1. 修正得到 `pts' := (samePointRepair a b).iterate 1 pts`；
2. 修正后满足该约束（`fixSamePoint_holds`）；
3. 该约束的残差在 `pts'` 处为零（`samePoint` 分支的 `poly` 就是 `sqDist a b`，
   而满足即 `pts' a = pts' b`，故 `sqDist = 0`）；
4. 于是**再编译**得到的损失 `loss (.samePoint a b) pts'` 为零。

第 4 步是本节与 `reinject_sound` 的区别：那里没有 `loss`。 -/
theorem reinject_loss_eq_zero (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) ((samePointRepair a b).iterate 1 pts) = 0 := by
  apply loss_eq_zero_of_poly_eq_zero
  -- `poly (.samePoint a b) pts' = sqDist (pts' a) (pts' b)`, and they coincide
  have hhold : GeoConstraint.Holds (.samePoint a b) ((samePointRepair a b).iterate 1 pts) :=
    reinject_sound a b pts
  -- the `samePoint` case of `Holds` is exactly `pts a = pts b`
  have hsame : ((samePointRepair a b).iterate 1 pts) a
      = ((samePointRepair a b).iterate 1 pts) b := by
    simpa [GeoConstraint.Holds] using hhold
  -- `poly (.samePoint a b) pts = sqDist (pts a) (pts b)`, which vanishes when a = b
  show EqConstraint.poly (.samePoint a b) ((samePointRepair a b).iterate 1 pts) = 0
  unfold EqConstraint.poly
  rw [sqDist_eq_zero_iff]
  exact hsame

/-- **再注入的完整陈述：修正后，惩罚为零。**

这条定理把闭环的三段串成一条：修正（`iterate 1`）→ 满足（隐含）→ 再编译（`loss`）为零。
`a`、`b` 与初始配置任意，所以它对**每一个**初始状态成立。 -/
theorem reinject_correct (a b : ℕ) (pts : ℕ → Pt n) :
    (GeoConstraint.Holds (.samePoint a b) ((samePointRepair a b).iterate 1 pts))
      ∧ EqConstraint.loss (.samePoint a b) ((samePointRepair a b).iterate 1 pts) = 0 :=
  ⟨reinject_sound a b pts, reinject_loss_eq_zero a b pts⟩

end Reinjection

end Lattice.Geo
