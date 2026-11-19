/-
# `Compose/Primitive` —— 基础调用的契约（**参数版**）

## 0. ⚠ 第 232 轮：`Input`/`Output` 从**字段**改成**参数**

`sections §4` 原先写成结构字段：

```lean
structure Primitive where
  Input : Type
  Output : Type
  ...
```

**那让组合无法干净地类型化。** 第 228 轮实测到两处后果：

1. `compose` 的 `f.Output` 与 `g.Input` 是两个独立类型字段，**没有任何东西强制它们相等**，
   所以 `g.pre y`（`y : f.Output`）通不过类型检查——必须补一个适配器；
2. `choice` 更糟：它只能取一支的 `Output`，另一支的输出要经等式搬运，
   而 `hio.symm ▸ (hio ▸ z)` **不是** `rfl` 相等（`hio` 是变量，两次 `Eq.rec` 卡住），
   于是 `choice` **根本写不出来**。

**第 232 轮的裁决：改成参数。**

```lean
structure Primitive (I O : Type) where
  pre : I → Prop
  post : I → O → Prop
  run : I → Option O
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  strength : Strength
  coverage : Coverage
  frame : I → O → Prop
```

**第 981 轮又删掉了 `frame`**：它没有自己的定理（唯一可能的定律与 `post` 逐字同形，第 39 轮那条被别名普查判为 `copy`），
11 个 primitive 里 10 个填字面 `True`，全树零消费者，13 个构造点全部只是把子 primitive 的 `frame` 再包一层。
**⇒ 上面的代码块是第 232 轮的**历史**形状；现在的结构是**六字段**，理由见 `AssocLaws.lean` 里那段 `⚠` 记录。**

**收益是决定性的**：

| 组合子 | 字段版 | 参数版 |
|:--|:--|:--|
| `compose` | 必须带适配器 + `Eq` 等式 | **`Primitive I M` 接 `Primitive M O`，直接** |
| 不同中间类型 | 适配器 | `composeWith`（**保留**——§7 第 5 条要的就是它） |
| `choice` | **写不出** | **两个 `Primitive I O`，无 cast** |
| `optional` | 需 `Output = Input` 等式 | **`Primitive I I`，无 cast** |
| `parallel` | 字段投影 | **`Primitive (I₁ × I₂) (O₁ × O₂)`** |

**代价**：「一个 `Primitive` 列表」需要 `Sigma` 包装（见 `Registry.MatrixRow`）。
**这是类型系统要求我付的价，不是设计缺陷。**

## 1. 强度格（§2.7）

次序（由弱到强）：`negative < existence < conditional < approx < exact`。

`negative` 是**否证性**结果（「这条路走不通」），不是「更弱的正面结论」。
`rank` 把它排在最低只是为了让 `min` 有全序。

## 2. 覆盖（§2.7）

`Coverage := Option (Finset String)`，`none` = 不限制。

**为什么不用 `Finset String`**：`String` 不是 `Fintype`，`.univ` 造不出来——「不限制」不能用集合表示。
**为什么不用「12/12」这样的分数**：分数不能表达「覆盖了哪 12 个中的哪几个」，
而两个都报 `11/12` 的 primitive 可能覆盖**不同的** 11 个，交集是 `10/12` 而不是 `11/12`。
**集合能表达，分数不能。**

## 3. 边界

- **`sound` 是字段**：没有它的 primitive **构造不出来**。§11.2 第 5 条的要求从文档纪律变成**类型纪律**。
- **`Strength.approx` 不带 `ε`**：带 `ε` 会让「取最小」没有全序。ε 属于具体 primitive 的 `post`。
- **本节不注册任何具体 primitive。** -/
import Mathlib

namespace Lattice.Compose

/-! ## 一、强度格 -/

/-- **强度**：一个 `Primitive` 对它的 `post` 承诺到什么程度。

次序（由弱到强）：`negative < existence < conditional < approx < exact`。

`negative` 是**否证性**结果，不是「更弱的正面结论」。`rank` 把它排在最低只是为了 `min` 有全序。 -/
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

/-- **取最小确实不大于左边**——「不允许把 `approx` 静默升级成 `exact`」的可证形式。

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

`none` 表示**不限制**（例如恒等），`some s` 表示**恰好**处理 `s` 里点名的情形。 -/
abbrev Coverage := Option (Finset String)

/-- **覆盖取交集**——§2.7 的「组合时覆盖取交集」。

`none` 是单位元：不限制 ∩ 任何 = 任何。 -/
def Coverage.inter : Coverage → Coverage → Coverage
  | none, b => b
  | a, none => a
  | some a, some b => some (a ∩ b)

/-- **覆盖取并**：`choice` 用。

`none`（不限制）吸收一切——与 `inter` 里 `none` 是单位元对偶。 -/
def Coverage.union : Coverage → Coverage → Coverage
  | none, _ => none
  | _, none => none
  | some a, some b => some (a ∪ b)

/-- **`none` 是 `inter` 的左单位。** -/
theorem Coverage.inter_none_left (b : Coverage) : Coverage.inter none b = b := by
  cases b <;> rfl

/-- **`none` 是 `inter` 的右单位。** -/
theorem Coverage.inter_none_right (a : Coverage) : Coverage.inter a none = a := by
  cases a <;> rfl

/-- **`none` 是 `union` 的左零元。** -/
theorem Coverage.union_none_left (b : Coverage) : Coverage.union none b = none := by
  cases b <;> rfl

/-! ## 三、契约本身（**参数版**） -/

/-- **基础调用的契约**（§4，第 232 轮改为**参数**）。

`I` 是输入类型，`O` 是输出类型。**它们是参数而不是字段**，所以：

- `Primitive I M` 接 `Primitive M O` 可以直接 `compose`，**不需要任何等式或 cast**；
- `choice` 取两个 `Primitive I O` 也是直接的。

`sound` 是**字段**：没有它，一个 `Primitive` **构造不出来**。 -/
structure Primitive (I O : Type) where
  /-- 前置条件。 -/
  pre : I → Prop
  /-- 后置条件。 -/
  post : I → O → Prop
  /-- 执行。失败用 `none` 传播。 -/
  run : I → Option O
  /-- **正确性**：前置成立则执行成功且后置成立。 -/
  sound : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  /-- 这个 primitive 承诺到什么程度。 -/
  strength : Strength
  /-- 它真正处理了哪些情形。 -/
  coverage : Coverage

/-- **收窄覆盖**：把一个 `Primitive` 的覆盖声明改成给定的集合。

`Coverage.inter` 只能变小，所以这不是「让它覆盖更多」。 -/
def Primitive.withCoverage {I O : Type} (p : Primitive I O) (c : Coverage) : Primitive I O :=
  { p with coverage := c }

/-- **收窄覆盖不改变正确性**：`sound` 与覆盖无关。 -/
theorem Primitive.withCoverage_sound {I O : Type} (p : Primitive I O) (c : Coverage) :
    (p.withCoverage c).sound = p.sound := rfl

end Lattice.Compose
