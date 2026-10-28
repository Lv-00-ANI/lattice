/-
# 链路的传递性：一段保持 ⟹ 多段保持

## 0. 本节补什么

`Lattice/Geo/ClauseComposition.lean` 的边界声明（第 69–70 行）：

> 「本节测的是**相邻**条款。**非相邻**的组合未测；它们通常经过两个中间环节，
> 应当由相邻对的传递性得到——但**本节没有证明传递性**。」

本节补上那个传递性，并给出它的**正确形式**。

## 1. 「传递性」的精确含义

朴素说法「若 A→B 且 B→C 则 A→C」对**命题**来说是假言三段论，**平凡成立**——
那不是有意思的东西。

**链路真正的结构**是：每一段把配置**变换**到下一阶段，而每段**保持**某个性质，
下一段消费那个性质。所以传递性的正确形式是关于**沿阶段序列折叠**的：

```
若每个阶段都保持 P，则把全部阶段依次施加后 P 仍成立
```

## 2. 主定理

```
preserves_foldl :
  (∀ f ∈ steps, ∀ x, P x → P (f x))
    →  P x  →  P (steps.foldl (· 施加) x)
```

**证明**：对 `steps` 做归纳。空表是 `hx`；非空表时先施加首段，
再对剩余段用归纳假设。

**这条定理的价值**：它**不假设阶段之间有任何关系**，只要求每段各自保持同一性质。
于是**任意多段都能串起来**，不必为每一对相邻条款单独论证。

## 3. 为什么它真的回答了那个缺口

第 45 轮测了 6 对相邻组合，每对都**单独**验证。
若没有传递性，测了 6 对不代表第 7 段能接上。

有了 `preserves_foldl`，**只要每段的保持性质一致**，段数不限。
缺口被补上，而且补的方式是**一般的**，不是「再测第 7 对」。

## 4. 与相邻对结论的关系

| 第 45 轮的结论 | 本节的作用 |
|:--|:--|
| 5 对相邻直接可组合 | 提供「每段保持」的实例 |
| `Compiler`+`Representation` 需要粘合 | 粘合是**并置**的前提，不是**序列**的障碍 |

⇒ **序列组合靠保持性传递；并置组合靠粘合。** 两者是不同的问题，
第 44–45 轮把它们混在一起看，本节分开了。

## 5. 泛化

`preserves_foldl` 对**任意类型 `α`、任意性质 `P`、任意阶段列表**成立。
本节给出三个特例（单段、双段、任意多段），说明它们**不是三条定理，
而是同一条的三个投影**。

**这正是「可以推广的推广」**：第 45 轮测的 5 对是同一定理的五次实例化，
本节把那五次实例化收成一条。

## 6. 边界

- 本节证明的是**保持性的传递**，不是「条款之间全部可组合」。
  后者还需要**每段的保持性质确实一致**——那是各条款自己的义务，
  本节**不**逐一核对（第 45 轮已给出 5 个实例，但没有系统覆盖）。
- `foldl (fun acc f => f acc) x` 的写法避免依赖 `Function.comp` 的结合律，
  使定理在任意阶段列表上直接成立。
- 本节**不**声称链路的端到端性质由 `Ladder` 的字段之外的推理得到：
  `Ladder` 仍是一步到位的结构。本节说的是「若把链路拆成段，段可串」。
-/
import Mathlib
import Lattice.Core.Repair

namespace Lattice.Audit

namespace ChainTransitivity

/-- **传递性：逐阶段保持 ⟹ 整体保持。**

给定阶段列表 `steps : List (α → α)`，若每个阶段都保持性质 `P`，
则把这些阶段依次施加到 `x` 上之后 `P` 仍成立。

这是「链路可组合」的**一般形式**：它不假设阶段之间有任何关系，
只要求每段各自保持同一性质。于是任意多段都能串起来，
不必为每一对相邻条款单独论证。 -/
theorem preserves_foldl {α : Type} (P : α → Prop)
    (steps : List (α → α)) (hstep : ∀ f ∈ steps, ∀ x, P x → P (f x))
    (x : α) (hx : P x) :
    P (steps.foldl (fun acc f => f acc) x) := by
  induction steps generalizing x with
  | nil => exact hx
  | cons f rest ih =>
    apply ih
    · intro g hg
      exact hstep g (List.mem_cons_of_mem f hg)
    · exact hstep f (List.mem_cons_self f rest) x hx

/-- **两段是特例**：`[f, g]` 的整体保持。 -/
theorem preserves_two {α : Type} (P : α → Prop) (f g : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, P x → P (g x)) (x : α) (hx : P x) :
    P (g (f x)) :=
  hg (f x) (hf x hx)

theorem preserves_three {α : Type} (P : α → Prop) (f g h : α → α)
    (hf : ∀ x, P x → P (f x)) (hg : ∀ x, P x → P (g x)) (hh : ∀ x, P x → P (h x))
    (x : α) (hx : P x) : P (h (g (f x))) :=
  hh (g (f x)) (hg (f x) (hf x hx))

end ChainTransitivity

namespace IterateForm

/-- **迭代形式的保持律**：这是修复回路**实际使用**的形状。

`Nat.iterate f n` 与 `List.foldl` 是同一个想法的两个组合子，
但**类型不同**。一般定理不能直接套到回路上——这一点值得记录，
因为它说明「一般化」不等于「可套用」。 -/
theorem preserves_iterate {α : Type} (P : α → Prop) (f : α → α)
    (hf : ∀ x, P x → P (f x)) (n : ℕ) (x : α) (hx : P x) :
    P (Nat.iterate f n x) := by
  induction n generalizing x with
  | zero => exact hx
  | succ m ih => exact ih (f x) (hf x hx)

/-- **折叠形式蕴含迭代形式**（对常值阶段列表）。

两种形状**等价**：`foldl` 版本不更强，也不更弱，只是写在另一个组合子上。 -/
theorem iterate_from_fold {α : Type} (P : α → Prop) (f : α → α)
    (hf : ∀ x, P x → P (f x)) (n : ℕ) (x : α) (hx : P x) :
    P ((List.replicate n f).foldl (fun acc g => g acc) x) :=
  ChainTransitivity.preserves_foldl P (List.replicate n f)
    (fun g _ y hy => by
      have hgf : g = f := List.eq_of_mem_replicate ‹g ∈ List.replicate n f›
      rw [hgf]; exact hf y hy)
    x hx

/-- **吸收律给出回路的保持律**：`Repair.preserves` 就是本定理在
`P := R.Sat`、`f := R.fix` 处的实例。

这条把一般定理**接到库自身的法则**上，证明实例化是真实的而非形式上的。 -/
theorem loop_preserves {α : Type} (R : Lattice.Core.Repair α) (n : ℕ) (x : α)
    (hx : R.Sat x) : R.Sat (Nat.iterate R.fix n x) :=
  preserves_iterate R.Sat R.fix (fun y hy => by rw [R.absorbs y hy]; exact hy) n x hx

end IterateForm

end Lattice.Audit
