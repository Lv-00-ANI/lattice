import Mathlib
import Lattice.Compose.Primitive
import Lattice.Compose.Combinators

/-!
# 组合律：能证到哪一层，以及整结构为什么停在这里

## 已有的

`Compose/Combinators.lean:155` 已经有 **`compose_run_assoc`**——但它的陈述是
`(compose (compose f g h₁) k h₃).run x = (f.run x).bind (fun y => (g.run y).bind (fun z => k.run z))`，
即「嵌套组合的 `run` 等于扁平 bind 链」。**那是 `run` 层的结合律，已在。**

## 本文件补的四个

| 律 | 层 | 为什么它不是重言 |
|:--|:--|:--|
| `strength_min_assoc` | `strength` | `min` 是 `if a.rank ≤ b.rank then a else b`，结合性要穷举 |
| `coverage_inter_assoc` | `coverage` | `Coverage = Option (Finset String)`，`none` 是单位 |
| `compose_pre_assoc` | `pre` | 两边都是 `f.pre`，**这条是定义相等**（`rfl`） |
| **`compose_post_assoc_iff`** | `post` | 两边的 `∃` **嵌套顺序不同**，要交换见证 |

## ⚠ 一条对 `Combinators.lean` docstring 的更正

那里写着：

> `compose (compose f g) h = compose f (compose g h)` **不可证**（需要证明无关性）。

**结论对，理由错了。**

真正的原因**不是**「需要证明无关性」——恰恰相反，证明无关性（`Subsingleton.elim`）是**让**事情可证的工具。
障碍在别处：`Primitive.sound` 的**类型**是

    ∀ x, pre x → ∃ y, run x = some y ∧ post x y

**它依赖 `post`**。而 `post` 的两边只有**命题等价**（`compose_post_assoc_iff`），
**不是定义相等**。于是要把 `sound₁` 与 `sound₂` 相比较，必须**沿着 `post` 的等式搬运一个证明**——
而 `propext` 给出的那条等式是**变量**，`Eq.rec` 在依赖的 `sound` 字段上卡住。

**这与第 232 轮 `choice` 卡住的现象是同一个**（`hio.symm ▸ (hio ▸ z)` 不是 `rfl` 相等）。
**它不是一个可以靠更聪明的战术绕开的缺口，而是「字段类型依赖另一个字段」的固有代价。** -/

namespace Lattice.Compose

/-- **`Strength.min` 结合**：5 个元素穷举（`cases` × 3 = 125 支）。 -/
theorem strength_min_assoc (a b c : Strength) :
    Strength.min (Strength.min a b) c = Strength.min a (Strength.min b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **`Coverage.inter` 结合**：`none` 是单位，`some` 之间用 `Finset.inter_assoc`。 -/
theorem coverage_inter_assoc (a b c : Coverage) :
    Coverage.inter (Coverage.inter a b) c = Coverage.inter a (Coverage.inter b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Coverage.inter, Finset.inter_assoc]

/-- **`compose` 的 `pre` 层结合**：两边都就是 `f.pre`——**这是定义相等**，不需要证明。 -/
theorem compose_pre_assoc {I M N O : Type} (f : Primitive I M) (g : Primitive M N)
    (k : Primitive N O)
    (h₁ : ∀ x y, f.post x y → g.pre y)
    (h₂ : ∀ x z, (compose f g h₁).post x z → k.pre z) :
    (compose (compose f g h₁) k h₂).pre = f.pre := rfl

/-- ⭐ **`compose` 的 `post` 层结合**：两边的 `∃` **嵌套顺序不同**，逻辑等价。

**这是本文件唯一有内容的层律**：左边先取 `∃ y`（`g` 的输出）再取 `∃ m`（`f` 的输出），
右边反过来。交换见证即可。 -/
theorem compose_post_assoc_iff {I M N O : Type} (f : Primitive I M) (g : Primitive M N)
    (k : Primitive N O)
    (h₁ : ∀ x y, f.post x y → g.pre y)
    (h₂ : ∀ x z, (compose f g h₁).post x z → k.pre z)
    (h₃ : ∀ y z, g.post y z → k.pre z)
    (h₄ : ∀ x y, f.post x y → (compose g k h₃).pre y) (x : I) (z : O) :
    (compose (compose f g h₁) k h₂).post x z ↔ (compose f (compose g k h₃) h₄).post x z := by
  simp only [compose]
  constructor
  · rintro ⟨y, ⟨m, hfm, hgm⟩, hky⟩
    exact ⟨m, hfm, y, hgm, hky⟩
  · rintro ⟨m, hfm, y, hgm, hky⟩
    exact ⟨y, ⟨m, hfm, hgm⟩, hky⟩

/-! ⚠ **`frame` 层没有单独的定理，这是有意的。**

`frame` 的展开式与 `post` **同形**——都是「∃ 的嵌套换序」：

    post  (compose (compose f g h₁) k h₂) x z = ∃ y, (∃ m, f.post  x m ∧ g.post  m y) ∧ k.post  y z
    frame (compose (compose f g h₁) k h₂) x z = ∃ y, (∃ m, f.frame x m ∧ g.frame m y) ∧ k.frame y z

**所以 `compose_post_assoc_iff` 的证明原样适用于 `frame`**，只差把四个谓词名换掉。
第 39 轮先写了第二条定理，**别名普查把它判成 `copy`（同一份证明体）**——它是对的：
两份逐字相同的证明是重复，不是一个字段一条定理。

**决定**：只留 `post` 那条（结合律需要它），`frame` 由本段说明覆盖。
**若将来要 `frame` 的具名定理**，正确做法是先把 `∃`-换序抽成一条通用引理，再让两条都指向它——
那样两条都是 `forward`（指向同一个权威），而不是两份相同证明。 -/

/-- **`strength` 与 `coverage` 也结合**——于是整条组合在**除 `sound` 外的每个字段**上都结合。

**`sound` 是唯一的例外**，原因见文件头：它的类型依赖 `post`。 -/
theorem compose_strength_coverage_assoc {I M N O : Type} (f : Primitive I M)
    (g : Primitive M N) (k : Primitive N O)
    (h₁ : ∀ x y, f.post x y → g.pre y)
    (h₂ : ∀ x z, (compose f g h₁).post x z → k.pre z)
    (h₃ : ∀ y z, g.post y z → k.pre z)
    (h₄ : ∀ x y, f.post x y → (compose g k h₃).pre y) :
    (compose (compose f g h₁) k h₂).strength = (compose f (compose g k h₃) h₄).strength ∧
    (compose (compose f g h₁) k h₂).coverage = (compose f (compose g k h₃) h₄).coverage := by
  constructor
  · simp only [compose, strength_min_assoc]
  · simp only [compose, coverage_inter_assoc]

end Lattice.Compose
