/-
# `Compose/Primitive` —— 基础调用的契约（P0）

## 0. 这一层为什么先建

`DIRECTORY-DESIGN.md` §2.1 的定位是「库只提供基础 `Primitive`，不打包任何能力」。**这个契约本身
是新的**：现有 816 个模块里没有 `Primitive` 结构，也没有 `strength`/`coverage` 的类型化表示
（第 219 轮的六维审计是在**散文里**做这件事的）。

**所以 P0 从契约开始，而不是从搬目录开始**——契约能独立编译、能被证、能立刻约束后续工作；
搬目录不能。

## 1. 强度格（§2.7）

`DIRECTORY-DESIGN.md` §2.7 要求
`strength: exact | approx(ε) | conditional | existence | negative`
且「**不允许把 `approx` 静默升级成 `exact`**」。

本文件把它做成**带 `rank` 的归纳类型**，于是「取最小」是一条 `min`，
「不允许升级」是一条**可证的单调性**（`min_le_left`），不是一句口头纪律。

## 2. 覆盖（§2.7）

`coverage: all | 12/12 | n=2 | single-point`。本文件把它做成**被覆盖情形的集合**（`Finset String`），
于是「取交集」是一条 `∩`，而「组合不会扩大覆盖」是一条可证的 `inter_subset_left`。

**为什么不用「12/12 这样的分数」**：分数不能表达「覆盖了哪些 12 个」——两个都报 `11/12` 的
primitive 可能覆盖不同的 11 个，交集是 `10/12` 而不是 `11/12`。**集合能表达，分数不能。**

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `Strength` / `rank` / `min` | 强度格 |
| `Coverage` | 被覆盖情形的集合 |
| **`Primitive`** | **§4 的七个字段**（`Input/Output/pre/post/run/sound/strength/coverage/frame`） |
| `Primitive.withCoverage` | 收窄覆盖（用于组合） |

## 4. 边界

- **`sound` 是字段**：一个没有 `sound` 的 `Primitive` **构造不出来**（§11.2 第 5 条：
  「不写 `Sound` 的 primitive 不注册；不用 `True`/`sorry`」）。**这是类型级别的纪律，不是文档纪律。**
- **本节不注册任何具体 primitive**：那是 P1。**本节只给契约。**
- **`frame` 是字段但没有定律**：帧条件的内容因 primitive 而异，P1 才逐条写。
- **`Strength.approx` 不带 `ε`**：带 `ε` 会让「取最小」没有全序。**代价**是精度数值不在类型里，
  **收益**是 `min` 与单调性可证。ε 属于具体 primitive 的 `post`，不属于强度格。 -/
import Mathlib

namespace Lattice.Compose

/-! ## 一、强度格 -/

/-- **强度**：一个 `Primitive` 对它的 `post` 承诺到什么程度。

次序（由弱到强）：`negative < existence < conditional < approx < exact`。

`negative` 是**否证性**结果（「这条路走不通」），它在 `DIRECTORY-DESIGN.md` §2.7 里与其余并列，
但**不是「更弱」的正面结论**——它是另一类。`rank` 把它排在最低，只是为了让 `min` 有全序；
**读 `min` 的结论时不能把 `negative` 读成「弱的存在性」**。 -/
inductive Strength where
  | negative
  | existence
  | conditional
  | approx
  | exact
  deriving DecidableEq, Repr

/-- **强度的秩**：`negative = 0` … `exact = 4`。 -/
def Strength.rank : Strength → ℕ
  | .negative => 0
  | .existence => 1
  | .conditional => 2
  | .approx => 3
  | .exact => 4

/-- **强度取最小**——§2.7 的「组合时强度取最小」。 -/
def Strength.min (a b : Strength) : Strength :=
  if a.rank ≤ b.rank then a else b

/-- **取最小确实不大于两边**——这就是「不允许把 `approx` 静默升级成 `exact`」的可证形式。

`min` 若可能变大，组合就能凭空加强结论；这条定理排除了那件事。 -/
theorem Strength.min_rank_le_left (a b : Strength) :
    (a.min b).rank ≤ a.rank := by
  unfold Strength.min
  split_ifs with h
  · exact le_refl _
  · exact le_of_lt (Nat.lt_of_not_le h)

/-- 取最小也不大于右边。 -/
theorem Strength.min_rank_le_right (a b : Strength) :
    (a.min b).rank ≤ b.rank := by
  unfold Strength.min
  split_ifs with h
  · exact h
  · exact le_refl _

/-! ## 二、覆盖 -/

/-- **覆盖**：这个 `Primitive` 真正处理了**哪些**情形。

`none` 表示**不限制**（例如恒等），`some s` 表示**恰好**处理 `s` 里点名的情形。

**为什么用 `Option (Finset String)` 而不是 `Finset String`**：
`String` 不是 `Fintype`，所以 `Finset.univ` 造不出来——**「不限制」不能用一个集合表示**。
第二版试过 `Finset String` 直接配 `Finset.univ`，编译器报
`failed to synthesize Fintype String`。`Option` 把「不限制」变成一个**显式的构造子**。

**为什么不用「12/12」这样的分数**：分数不能表达「覆盖了哪 12 个中的哪几个」，
而两个都报 `11/12` 的 primitive 可能覆盖**不同的** 11 个，交集是 `10/12` 而不是 `11/12`。
**集合能表达这件事，分数不能。** -/
abbrev Coverage := Option (Finset String)

/-- **覆盖取交集**——§2.7 的「组合时覆盖取交集」。

`none` 是单位元：不限制 ∩ 任何 = 任何。这正是把 `none` 读成「不限制」而不是「什么都不覆盖」的理由。 -/
def Coverage.inter : Coverage → Coverage → Coverage
  | none, b => b
  | a, none => a
  | some a, some b => some (a ∩ b)

/-- **覆盖取并**：`choice` 用。

`none`（不限制）与任何集合取并仍是 `none`——**不限制吸收一切**。这与 `inter` 里 `none` 是单位元
是对偶的两条。 -/
def Coverage.union : Coverage → Coverage → Coverage
  | none, _ => none
  | _, none => none
  | some a, some b => some (a ∪ b)

/-- **`none` 是左零元**（取并）。 -/
theorem Coverage.union_none_left (b : Coverage) : Coverage.union none b = none := by
  cases b <;> rfl

/-- **`none` 是左单位**。 -/
theorem Coverage.inter_none_left (b : Coverage) : Coverage.inter none b = b := by
  cases b <;> rfl

/-- **`none` 是右单位**。 -/
theorem Coverage.inter_none_right (a : Coverage) : Coverage.inter a none = a := by
  cases a <;> rfl

/-- **组合不会扩大覆盖**（`some` 情形的集合包含）。 -/
theorem Coverage.inter_subset_left (a b : Finset String) :
    some (a ∩ b) = Coverage.inter (some a) (some b) := rfl

/-! ## 三、契约本身 -/

/-- **基础调用的契约**（`DIRECTORY-DESIGN.md` §4）。

**`sound` 是字段**：没有它，一个 `Primitive` **构造不出来**。
§11.2 第 5 条要求「不写 `Sound` 的 primitive 不注册；不用 `True`/`sorry`」——
把 `sound` 放进结构，那条要求就从**文档纪律**变成**类型纪律**。 -/
structure Primitive where
  /-- 输入类型。 -/
  Input : Type
  /-- 输出类型。 -/
  Output : Type
  /-- 前置条件。 -/
  pre : Input → Prop
  /-- 后置条件。 -/
  post : Input → Output → Prop
  /-- 执行。失败用 `none` 传播。 -/
  run : Input → Option Output
  /-- **正确性**：前置成立则执行成功且后置成立。 -/
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  /-- 这个 primitive 承诺到什么程度。 -/
  strength : Strength
  /-- 它真正处理了哪些情形。 -/
  coverage : Coverage
  /-- 帧条件：它不改变什么。内容因 primitive 而异，P1 才逐条写。 -/
  frame : Input → Output → Prop

/-- **收窄覆盖**：把一个 `Primitive` 的覆盖声明改成给定的集合。

**不是「让它覆盖更多」**——`Coverage.inter` 只能变小。这个函数用于把一个 primitive
**登记为**它在某次组合里实际被用到的部分，从而让 `Registry` 的记录与实际一致。 -/
def Primitive.withCoverage (p : Primitive) (c : Coverage) : Primitive :=
  { p with coverage := c }

/-- **收窄覆盖不改变正确性**：`sound` 与覆盖无关。 -/
theorem Primitive.withCoverage_sound (p : Primitive) (c : Coverage) :
    (p.withCoverage c).sound = p.sound := rfl

end Lattice.Compose
