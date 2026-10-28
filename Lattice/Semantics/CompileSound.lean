/-
# S9：`compile_sound`——合并后的 profile 编译成**权重**仍保持语义

## 0. 为什么这条与 S20 不同

S20（`vocab_align_merge_sound`）**被阻塞**：`MergeSound` 里没有词表类型，所以「保持」要么是重言、
要么需要一条库里不存在的 `behavior ↔ Holds` 桥（`SEMANTICS-MAINLINE.md` §6.1）。

**S9 不是那个情况。** 它需要的是：

```
MergeSound R pts  ⟹  HoldsSet R.merged pts  ⟹  权重侧饱和
```

三段**都在库里**：

| 段 | 定理 | 位置 |
|:--|:--|:--|
| 证书 → 逐条成立 | `merge_sound` | `Semantics/Merge.lean`（第 202 轮） |
| 「`samePoint` 单条」↔「坐标相等」 | `holdsSet_samePoint_single`（**本节**） | 本节 |
| 坐标相等 → **真权重**饱和 | `samePointLadder_forward` / `satW_iff` | `Geo/WeightSideLadder.lean`（第 223 轮） |

**所以 S9 是组装，不是新数学。**

## 1. 为什么选 `samePoint` 这个情形

因为**它是唯一能真正走到权重的形状之一**（另一是 `midpoint`）。
`Geo/WeightSideLadder.lean` §六 已经把 12 个构造子分好类：

- **逐坐标仿射**：`samePoint`、`midpoint` —— **能编译成 `List (AffineLayer (Fin n))`**；
- 单个仿射泛函（4 个）、二次（2 个）、双线性（4 个） —— **不能**，
  且二次那一类的不可能性已由 `no_affine_represents_sphere` 证明。

**所以 S9 在一个子类上是真的 `compile_sound`，而不是「对所有约束都成立」的假声称。**
本节**不声称**一般情形——那需要非仿射载体，而目标里「权重」的标准含义是仿射层。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| `holdsSet_samePoint_single` | **`HoldsSet [samePoint a b] pts ↔ pts a = pts b`** |
| **`compile_sound`** | **`MergeSound R pts` + `R.merged = [samePoint a b]` ⟹ 权重侧 `satW` 在编译结果上成立** |
| `compile_sound_midpoint` | 同一件事对 `midpoint`（第二个能到权重的构造子） |

## 3. 边界的实质

- **只覆盖 `samePoint` / `midpoint`**。其余 10 个构造子**到不了仿射权重**，理由已在 §一的分类里，
  并由 `no_affine_represents_sphere` 支撑。**不是遗漏，是分类的结果。**
- **`R.merged` 恰好是单条约束**是本节的前提。多条的情形需要把各条的权重层**串起来**——
  `netAct` 的折叠可以做，但「多条约束各自的 `satW` 合成一个」需要一个新的合取谓词，
  **本节不做**（见 §4）。
- **`MergeSound` 仍是逐配置的**（`pts` 是参数）。对**所有**配置成立的记录级证书会强得多，
  本节不声称。
- **本节不碰词表**。理由同 S20：`MergeSound` 不含词表类型。 -/
import Mathlib
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Geometry.WeightSideLadder
import Lattice.Semantics.Merge

namespace Lattice.Semantics.CompileSound

open Lattice.Geo Lattice.Geo.ConstraintSet Lattice.Geo.WeightSide Lattice.Semantics.Merge

variable {n : ℕ}

/-! ## 一、从 `HoldsSet` 到坐标相等（及 `midpoint` 的对应形式） -/

/-- **`HoldsSet` 在单条 `samePoint` 约束上就是坐标相等。**

`HoldsSet` 对单元素列表展开成 `Holds c pts`，而 `Holds (.samePoint a b) pts` 按定义是 `pts a = pts b`。 -/
theorem holdsSet_samePoint_single {a b : ℕ} {pts : ℕ → Pt n} :
    HoldsSet [GeoConstraint.samePoint a b] pts ↔ pts a = pts b := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, trivial⟩

/-- **`HoldsSet` 在单条 `midpoint` 约束上就是逐坐标的 `2m = a + b`。** -/
theorem holdsSet_midpoint_single {m a b : ℕ} {pts : ℕ → Pt n} :
    HoldsSet [GeoConstraint.midpoint m a b] pts ↔
      ∀ j, 2 * pts m j = pts a j + pts b j := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, trivial⟩

/-! ## 二、S9：编译到**真权重**仍保持语义 -/

/-- **S9 `compile_sound`（`samePoint` 情形）**：整合证书 + 合并结果恰为一条 `samePoint`
⟹ **编译出的仿射权重层**在其上饱和。

三段的合取就是证明：`merge_sound` 给出 `HoldsSet R.merged pts`，
`holdsSet_samePoint_single` 把它翻成坐标相等，
`samePointLadder_satW_iff` 再把它翻成权重侧。

**终点是 `List (AffineLayer (Fin n))`——真正的权重，不是损失。** -/
theorem compile_sound (R : MergeRecord n) (a b : ℕ) (pts : ℕ → Pt n)
    (hR : R.merged = [GeoConstraint.samePoint a b])
    (h : MergeSound R pts) :
    (samePointLadder pts a b).satW ((samePointLadder pts a b).l2l3 []) := by
  have hmerged : HoldsSet R.merged pts := merge_sound R pts h
  rw [hR] at hmerged
  have hcoord : pts a = pts b := holdsSet_samePoint_single.mp hmerged
  exact (samePointLadder_satW_iff pts a b).mpr (fun j => congrFun hcoord j)

/-- **S9 `compile_sound`（`midpoint` 情形）**：第二个能走到真权重的构造子。 -/
theorem compile_sound_midpoint (R : MergeRecord n) (m a b : ℕ) (pts : ℕ → Pt n)
    (hR : R.merged = [GeoConstraint.midpoint m a b])
    (h : MergeSound R pts) :
    (midpointLadder pts m a b).satW ((midpointLadder pts m a b).l2l3 []) := by
  have hmerged : HoldsSet R.merged pts := merge_sound R pts h
  rw [hR] at hmerged
  have hcoord : ∀ j, 2 * pts m j = pts a j + pts b j :=
    holdsSet_midpoint_single.mp hmerged
  exact (midpointLadder_satW_iff pts m a b).mpr hcoord

/-! ## 三、这两条不是重言：反向不成立

`compile_sound` 只说「证书成立 ⟹ 权重饱和」。**但它没有说「权重饱和 ⟹ 证书成立」**——
那需要**编码可逆**（`pts` 能由权重侧恢复），而 `samePointLayer` 丢掉 `pts a` 之外的一切。

**本节不声称反向**，也不声称 `compile_sound` 是双条件。**单向就是它说的全部。** -/

end Lattice.Semantics.CompileSound
