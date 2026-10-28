/-
# `Compose/ForwardChain` —— 前向链 capstone，**在组合层**

## 0. 这是第 227 轮矛盾三的裁决执行

`DIRECTORY-DESIGN.md` §2.6 要求「`Primitives` 之间零 import」，而 §10 把 `NetLoss`、`PenaltyLoss`、
`ConstraintDescent` 都映射到 `Primitives/Train`。**但前向链 capstone 恰恰是 `ConstraintDescent` 用
`NetLoss` 与 `PenaltyLoss`** —— 三者不能同处 `Primitives/Train`。

**第 228 轮的裁决：capstone 搬到 `Compose` 并重写陈述。** 本节执行它。

## 1. 搬运不是复制：**陈述变了**

`Geo/ConstraintDescent.lean` 里那条是**一个裸定理**：

```lean
theorem forward_chain_capstone (c β) (hne : β + c ≠ 0) (pts) :
    netLoss [shiftLayer (step (1/2) c β)] ... < netLoss [shiftLayer β] ... ∧
    netLoss ... = 0 ∧ Holds ... ∧ (netLoss ... = 0 ↔ Holds ...)
```

**它无法被组合**：它不是一个 `Primitive`，所以 `compose`/`parallel`/`Matrix` 都用不上它。

**搬到 `Compose` 之后，它变成一个 `Primitive`**：

| 字段 | 值 |
|:--|:--|
| `Input` / `Output` | `ℝ` / `ℝ`（参数空间的一维情形） |
| `pre` | `β + c ≠ 0`——**「约束尚未满足」** |
| `post` | **损失严格下降 ∧ 损失归零** |
| `run` | `some (step (1/2) c β)` |

**所以新陈述的内容是：这一步是一个合法的 `Primitive`，它的 `sound` 是第 200–204 轮那些定理。**
capstone 从「一条孤立定理」变成「**一个可被组合的契约实例**」——**这是搬到 `Compose` 的全部收益**。

## 2. 交付

| 声明 | 内容 |
|:--|:--|
| **`descentStep`** | **一步梯度下降，作为一个 `Primitive`**（`pre` = 未满足，`post` = 严格下降且归零） |
| **`descentStep_sound`** | 它的 `sound`——由 `netLoss_step_half` 与 `netLoss_pos_of_ne` 得出 |
| **`forward_chain_capstone`** | **四环**：严格下降、归零、约束成立、零损失 ⟺ 成立 |
| `forward_chain_at_solution` | 已满足时一步不改变损失（保守性） |

## 3. 边界

- **`Input`/`Output` 都是 `ℝ`**：这是**一维参数空间**的实例，与第 200–204 轮同范围。
  多维版本要用 `Fin n → ℝ`，它的 `post` 相同，但 `netLoss` 的实例化不同。
- **`pts` 是 `Primitive` 的参数而不是输入**：配置不由训练步改变（只改参数），
  所以它进 `Input` 会让 `Input` 变成 `ℝ × (ℕ → Pt 1)`，而 `Output` 只需参数。
  **本节的取法把「不改变的东西」放进闭包，而不是放进类型**——这与 §2.1「一个 primitive 只做一件事」一致。
- **强度是 `exact`**：结论是等式与严格不等式，不是近似。**覆盖**登记为单约束、单坐标。
- **本节只搬 capstone 与保守性两条**。`netLoss_pos_of_ne`、`netLoss_zero_iff_holds` 留在 `Geo`——
  它们是 `Geo` 层的损失事实，不是组合层的东西。
- **`Geo/ConstraintDescent.lean` 里那两条已删除**（裁决是「搬」，不是「复制」）。 -/
import Mathlib
import Lattice.Domains.ConstraintDescent
import Lattice.Compose.Primitive

namespace Lattice.Compose.ForwardChain

open Lattice.Core Lattice.Geo Lattice.Geo.NetLoss Lattice.Geo.ConstraintDescent Lattice.Compose

/-- **一步训练的 `Primitive`**：`pre` 是「约束尚未满足」，`post` 是「损失严格下降且归零」。

**它把第 200–204 轮的四条定理收成一个契约实例**，从而使 `compose`/`parallel`/`Matrix` 能用它。

**类型是 `Primitive ℝ ℝ`**（第 232 轮参数化）：`Input`/`Output` 是**参数**，不是字段，
所以它可以与任何 `Primitive ℝ ℝ` 直接 `compose`，**不需要适配器**。 -/
noncomputable def descentStep (c : ℝ) (pts : ℕ → Pt 1) : Primitive ℝ ℝ where
  pre := fun β => β + c ≠ 0
  post := fun β β' =>
    netLoss [shiftLayer β'] [linearConstraint c] pts
        < netLoss [shiftLayer β] [linearConstraint c] pts
      ∧ netLoss [shiftLayer β'] [linearConstraint c] pts = 0
  run := fun β => some (step (1 / 2) c β)
  sound := by
    intro β hβ
    refine ⟨step (1 / 2) c β, rfl, ?_, ?_⟩
    · -- strict decrease: the new loss is 0 and the old was positive
      have hpos := netLoss_pos_of_ne c β hβ pts
      have hzero := netLoss_step_half c β pts
      rw [hzero]
      exact hpos
    · exact netLoss_step_half c β pts
  strength := .exact
  coverage := some ({"constraint.eqZero"} : Finset String)
  frame := fun _ _ => True

/-- **`descentStep` 的 `sound`**：可直接引用的一条。 -/
theorem descentStep_sound (c β : ℝ) (hβ : β + c ≠ 0) (pts : ℕ → Pt 1) :
    ∃ β', (descentStep c pts).run β = some β' ∧ (descentStep c pts).post β β' :=
  (descentStep c pts).sound β hβ

/-- **前向链 capstone（组合层版本）**：四环，一条陈述。

1. `run` 给出 `step (1/2) c β`——**梯度的执行是显式的**；
2. 损失**严格下降**；
3. 损失**归零**；
4. 约束**成立**，且**零损失 ⟺ 约束成立**。

**与 `Geo` 里那一条的区别**：`post` 现在是**结构字段**，所以这条定理说的是
「`descentStep` 这个 `Primitive` 在 `pre` 下产出满足 `post` 的结果」，
**而 `post` 可被 `compose` 消费**。 -/
theorem forward_chain_capstone (c β : ℝ) (hne : β + c ≠ 0) (pts : ℕ → Pt 1) :
    (descentStep c pts).run β = some (step (1 / 2) c β) ∧
      netLoss [shiftLayer (step (1 / 2) c β)] [linearConstraint c] pts
          < netLoss [shiftLayer β] [linearConstraint c] pts ∧
      netLoss [shiftLayer (step (1 / 2) c β)] [linearConstraint c] pts = 0 ∧
      GeoConstraint.Holds (linearConstraint c)
          (fun k => netAct [shiftLayer (step (1 / 2) c β)] (pts k)) ∧
      (netLoss [shiftLayer (step (1 / 2) c β)] [linearConstraint c] pts = 0 ↔
        GeoConstraint.Holds (linearConstraint c)
          (fun k => netAct [shiftLayer (step (1 / 2) c β)] (pts k))) := by
  -- The two `post` conjuncts are proved DIRECTLY from the Geo lemmas rather than through
  -- `descentStep.sound`'s existential: the witness there is `.choose`, which is only propositionally
  -- — not syntactically — `step (1/2) c β`, and aligning it costs more than reusing the lemmas.
  -- `descentStep.sound` is proved separately below/above from the same facts, so nothing is duplicated
  -- in substance: this is the same proof at the composition layer.
  refine ⟨rfl, ?_, netLoss_step_half c β pts,
          constraint_satisfied_after_one_step c β pts,
          netLoss_zero_iff_holds c (step (1 / 2) c β) pts⟩
  have hpos := netLoss_pos_of_ne c β hne pts
  rw [netLoss_step_half c β pts]
  exact hpos

/-- **已满足时一步不改变损失**：保守性。

与 `Geo/LoopPerp.fixPerp_absorbs` 是同一件事在训练侧的形式，**现在它与 `descentStep` 在同一个模块**，
所以「训练步 + 保守性」可以被一起引用。 -/
theorem forward_chain_at_solution (c β : ℝ) (h : β + c = 0) (pts : ℕ → Pt 1) :
    netLoss [shiftLayer (step (1 / 2) c β)] [linearConstraint c] pts
      = netLoss [shiftLayer β] [linearConstraint c] pts := by
  rw [netLoss_step_half, netLoss_shiftLayer, h]
  ring

end Lattice.Compose.ForwardChain
