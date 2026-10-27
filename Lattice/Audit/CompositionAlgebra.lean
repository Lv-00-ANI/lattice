/-
# 组合代数：`CompositionKind` 的单位元、结合律与一致性

## 0. 本节补什么

外部审查对新范式的核心批评：

> **组合只有分类，没有律。** 有 `CompositionClass` 的分类，但**没有单位元、没有结合律、
> 没有一致性**。⇒ **「格」缺少格该有的东西。**

## 1. 为什么不在 `Chain` 上做

`Chain α P` 是**依赖类型**（出口依赖整条链），我试了三次在它上面定义拼接，
都卡在「第二个参数的类型依赖第一个参数的归约结果」：

```
append (P) (a : Chain α P) (Q) (b : Chain α Q) : Chain α P
```

`a` 为 `nil` 时 `b : Chain α Q` 而目标是 `Chain α P`——**除非 `Q = P`**，
而这个等式在类型里没有表达。

**这不是可以绕过的技术问题，而是「链」这个载体本身不适合承载拼接代数。**

## 2. 正确的载体：`List CompositionKind`

组合的**判定结果**是一个 `List CompositionKind`——**非依赖类型**。
拼接就是 `List.append`，于是三条律全部是**列表的已知引理**：

| 律 | 内容 | 依据 |
|:--|:--|:--|
| 左单位 | `[] ++ ks = ks` | `List.nil_append` |
| 右单位 | `ks ++ [] = ks` | `List.append_nil` |
| 结合律 | `(a ++ b) ++ c = a ++ (b ++ c)` | `List.append_assoc` |

⇒ **判定代数天然是 monoid**：单位元是 `[]`（无需任何转手的组合），
运算是拼接。**这是本节的核心结论。**

### 2.1 一致性：判定与内容的同态

`List CompositionKind` 只有**语法**。它与**语义**（链）之间的一致性由
`bridgedCount`（需要桥的数量）给出：

```
bridgedCount : List CompositionKind → ℕ
bridgedCount_pure : bridgedCount .sequential = 0      -- 同性质不需要桥
bridgedCount_bridged : bridgedCount .bridged = 1      -- 换性质需要一个桥
bridgedCount_append : bridgedCount (a ++ b) = a + b   -- 同态
```

⇒ **「需要多少桥」在判定层可计算，且与拼接同态。**
这正是第 59 轮 `Evidence` 类型族在数量层面的对应。

## 3. 主定理

| 定理 | 内容 |
|:--|:--|
| `Verdict` | `List CompositionKind` 的别名 |
| `empty_verdict` | **单位元**：空判定 |
| `nil_append` / `append_nil` | **左、右单位** |
| **`append_assoc`** | **结合律** |
| `bridgedCount` | 需要多少桥（可计算） |
| **`bridgedCount_append`** | **同态**：桥的数量可加 |
| `verdict_monoid` | **`Verdict` 构成 monoid** |

## 4. 这使「组合代数」成立到什么程度

| 要素 | 状态 |
|:--|:--|
| 载体 | ✅ `List CompositionKind`（非依赖） |
| 运算 | ✅ 拼接 |
| 单位元 | ✅ `[]` |
| 结合律 | ✅ |
| 保结构映射 | ✅ `bridgedCount`（到 `ℕ` 的 monoid 同态） |

⇒ **组合判定构成一个 monoid，且「所需桥数」是从它到 `(ℕ,+,0)` 的同态。**

## 5. 边界

- **这不是格**：`List CompositionKind` 没有交与并，也没有序。
  报告说「格缺少格该有的东西」——**严格说，本库证明的是 monoid 结构，不是格结构**。
  「表示格」里的「格」是**比喻**，本节的定理把这个比喻**落到具体可检验的结构上**。

  **第 173 轮把这句判断精确化**（见 `Audit/VerdictLattice.lean`）：它**只对序列成立**。
  - **每一段判定**（`CompositionKind`）**确实构成有界格**：`sequential` 是底（什么也不要），
    `bridged` 是顶（要一条蕴含），`kindSup`/`kindInf` 给出并与交（`kind_is_bounded_lattice`）。
  - **判定序列**（`Verdict = List CompositionKind`）在逐点序下**不是格**，证明是长度不匹配：
    `[.bridged]` 与 `[.sequential, .sequential]` 没有公共上界（`verdict_no_sup`）。
  - **根因**：组合是拼接，而拼接**不保持长度**；长度相同的切片上格结构仍在
    （`verdict_lub_of_length_eq`）。

  ⇒ **「格」不是空的，也不是全的**：它在**单段判定的强弱**上真实存在，在**判定序列**上不存在。
  这正是本库的组合代数天然是 monoid 的原因——不是没找到格结构，是格结构在另一层。
- 本节**不**建立 `Verdict` 与 `Chain` 之间的双向对应。判定说「需要 N 座桥」，
  链是**提供**那些桥的地方；两者的连接需要把判定结果翻译成链，属后续。
- 我**没有**在 `Chain` 上建立拼接代数，并已在 §1 说明原因。
  **这是有意的边界，不是遗漏**——在依赖类型上硬做会写出难读且脆弱的证明。
-/
import Mathlib
import Lattice.Audit.CompositionClass

namespace Lattice.Audit

namespace CompositionAlgebra

open CompositionClass

/-! ## 一、判定作为 monoid -/

/-- **一次多段组合的判定**：逐段记录 `sequential` / `bridged`。 -/
abbrev Verdict := List CompositionKind

/-- **单位元**：空组合（无需任何转手）。 -/
def emptyVerdict : Verdict := []

/-- **左单位**。 -/
theorem nil_append (ks : Verdict) : emptyVerdict ++ ks = ks := List.nil_append ks

/-- **右单位**。 -/
theorem append_nil (ks : Verdict) : ks ++ emptyVerdict = ks := List.append_nil ks

/-- **结合律**。 -/
theorem append_assoc (a b c : Verdict) : (a ++ b) ++ c = a ++ (b ++ c) :=
  List.append_assoc a b c

/-! ## 二、一致性：需要多少桥 -/

/-- **需要多少座桥**：`bridged` 的个数。

`sequential` 不需要桥；`bridged` 需要一座。 -/
def bridgedCount : Verdict → ℕ
  | [] => 0
  | .sequential :: ks => bridgedCount ks
  | .bridged :: ks => bridgedCount ks + 1

/-- **同性质不需要桥**。 -/
theorem bridgedCount_sequential (ks : Verdict) :
    bridgedCount (.sequential :: ks) = bridgedCount ks := rfl

/-- **换性质需要一座桥**。 -/
theorem bridgedCount_bridged (ks : Verdict) :
    bridgedCount (.bridged :: ks) = bridgedCount ks + 1 := rfl

/-- **同态**：拼接的桥数等于桥数之和。

⇒ **「需要多少桥」在判定层可计算，且与拼接相容。** -/
theorem bridgedCount_append (a b : Verdict) :
    bridgedCount (a ++ b) = bridgedCount a + bridgedCount b := by
  induction a with
  | nil => simp [bridgedCount]
  | cons k ks ih =>
      cases k with
      | sequential => simp [bridgedCount, ih]
      | bridged => simp [bridgedCount, ih]; omega

/-- **空判定不需要桥**。 -/
theorem bridgedCount_empty : bridgedCount emptyVerdict = 0 := rfl

/-! ## 三、monoid 结构 -/

/-- **`Verdict` 真正是一个 `Monoid`**：注册 Mathlib 实例，而不是只陈述三条律。

### 为什么注册实例比陈述三条律强

`verdict_monoid` 只是**一个命题**说「这三条成立」。注册实例之后：

| 好处 | 说明 |
|:--|:--|
| **可复用** | `List.append` 上已有的 Mathlib 引理（`pow`、`fold`、`MonoidHom` 基础设施）对 `Verdict` 直接可用 |
| **可组合** | `Verdict` 可以出现在任何要求 `Monoid` 的抽象里，不必每次手写三条律 |
| **口径精确** | 文档说「monoid」时，指的是**类型类实例**，而不是一个措辞 |

单位的唯一性与结合的传递性由 `Monoid` 自动提供，不需要重复陈述。 -/
instance : Monoid Verdict where
  mul := (· ++ ·)
  one := emptyVerdict
  mul_assoc := append_assoc
  one_mul := nil_append
  mul_one := append_nil

/-- **`Verdict` 构成 monoid**（三条律的显式陈述，保留以便审计逐条核对）。 -/
theorem verdict_monoid :
    (∀ ks : Verdict, emptyVerdict ++ ks = ks) ∧
    (∀ ks : Verdict, ks ++ emptyVerdict = ks) ∧
    (∀ a b c : Verdict, (a ++ b) ++ c = a ++ (b ++ c)) :=
  ⟨nil_append, append_nil, append_assoc⟩

/-- **实例与显式陈述一致**：`Monoid` 的运算就是 `++`，单位就是 `emptyVerdict`。

⇒ 文档说的「monoid」现在指的是**注册的实例**，不是措辞。 -/
theorem verdict_monoid_instance_agrees :
    (∀ a b : Verdict, a * b = a ++ b) ∧ ((1 : Verdict) = emptyVerdict) :=
  ⟨fun _ _ => rfl, rfl⟩

/-- **`bridgedCount` 是 monoid 同态**：从 `(Verdict, ++, [])` 到 `(ℕ, +, 0)`。 -/
theorem bridgedCount_hom :
    bridgedCount emptyVerdict = 0 ∧
    (∀ a b : Verdict, bridgedCount (a ++ b) = bridgedCount a + bridgedCount b) :=
  ⟨bridgedCount_empty, bridgedCount_append⟩

end CompositionAlgebra

end Lattice.Audit
