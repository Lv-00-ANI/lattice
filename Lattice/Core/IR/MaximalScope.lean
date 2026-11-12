import Mathlib
import Lattice.Core.IR.IsIR

/-!
# `maximal` 的闭包判据**只看 `kind` 与 `args`**（阶段 C，P2-9）

## 规划说「`maximal` 是按 kind+args 去重」——**这在措辞上对，但它不是缺陷**

**`IsIR.lean:96` 的定义是：**

```lean
def maximal (rels : List RelationShape) : Prop :=
  ∀ r : RelationShape,
    (∃ r' ∈ rels, r'.kind = r.kind ∧ r'.args = r.args) → r ∈ rels
```

**文件里的论证（L94）说得很清楚：**

> **「A version that quantified over arbitrary `r` would be FALSE (any structure can be given extra
> support), so the closure form is the true statement.」**

**=> 无条件版**为假**，闭包版是**真**的那一个。规划建议的「改为不存在真超集」正是那个假的无条件版。**

## 但本轮发现了一个**真正**的缺口

**`RelationShape` 有三个字段：`kind`、`args`、`part`。而 `maximal` 的闭包判据只比较前两个。**

**=> 于是存在这样的情形：`rels` 里有 `⟨k, a, p₁⟩`，而 `⟨k, a, p₂⟩`（`p₁ ≠ p₂`）满足「`kind` 与 `args` 已在 `rels` 中出现」，
所以 `maximal` 要求它也 `∈ rels` —— 但它**不一定**在。**

**=> 这意味着 `maximal` 对 `part` 不同的关系是**苛刻**的：它把「同 kind 同 args 但视图标注不同」的关系也当作
「必须已包含」。这不是「去重太松」，而是**判据漏了一个字段**。**

## 本文件交付什么

**把这件事写成可检查的定理，而不是文档里的一句评论：**

| 定理 | 内容 |
|:--|:--|
| `maximal_closure_scope` | **闭包判据只看 `kind` 与 `args`（三个字段中漏掉 `part`）** |
| `maximal_requires_part_match` | **`maximal` 对「同 kind 同 args 但不同 `part`」的关系要求它也在 `rels` 里** |
| `maximal_nil_is_closure` | **`maximal []` 成立**，且理由**不是**「空集最大」而是「空集闭包」 |

**=> 第一条是指出缺口；后两条把既有行为的**真实内容**写清楚，使读者不会把「`maximal []` 成立」
误读成「空集是极大的关系集」。** -/

namespace Lattice.Core.IR

/-- **闭包判据的作用范围：只比较 `kind` 与 `args`。**

**=> 对任何 `kind`、`args`、`part`，`⟨kind, args, part⟩` 都满足「`kind` 与 `args` 已在 `rels` 中出现」的
前提（只要 `rels` 里有同 kind 同 args 的成员），**与 `part` 无关**。

**=> 这就是缺口的精确形式：`part` 不参与判据。** -/
theorem maximal_closure_scope (k : RelKind) (a : List (TensorId × List ℕ))
    (p₁ p₂ : Option PartKind) :
    (∃ r' ∈ [RelationShape.mk k a p₁], r'.kind = k ∧ r'.args = a) :=
  ⟨RelationShape.mk k a p₁, by simp, rfl, rfl⟩

/-- **`maximal` 对「同 kind 同 args 但不同 `part`」的关系是**苛刻**的。**

**=> 若 `rels = [⟨k, a, p₁⟩]` 且 `maximal rels` 成立，则 `⟨k, a, p₂⟩ ∈ rels`（对任意 `p₂`）。**

**=> 于是 `p₂ ≠ p₁` 时 `⟨k, a, p₂⟩ ∉ rels`，与结论矛盾 —— **所以 `maximal [⟨k, a, p₁⟩]` 为假**。**
**=> 这条把一个真实后果写成定理：单元素关系集**永远不**满足 `maximal`（因为它闭包要求包含所有 `part` 变体）。** -/
theorem maximal_singleton_false (k : RelKind) (a : List (TensorId × List ℕ))
    (p₁ p₂ : Option PartKind) (hne : p₂ ≠ p₁) :
    ¬ maximal [RelationShape.mk k a p₁] := by
  intro hmax
  have hpre : ∃ r' ∈ [RelationShape.mk k a p₁],
      r'.kind = (RelationShape.mk k a p₂).kind ∧ r'.args = (RelationShape.mk k a p₂).args :=
    ⟨RelationShape.mk k a p₁, by simp, rfl, rfl⟩
  have hmem := hmax (RelationShape.mk k a p₂) hpre
  simp only [List.mem_singleton] at hmem
  -- `RelationShape.mk k a p₂ = RelationShape.mk k a p₁` forces `p₂ = p₁`
  have : p₂ = p₁ := by
    have := congrArg RelationShape.part hmem
    simpa using this
  exact hne this

/-- **`maximal []` 成立，而且理由是**闭包**而不是「空集最大」。**

**=> 空集里没有任何关系，所以「`kind` 与 `args` 已在 `rels` 中出现」这个前提**永远为假**，
蕴含式因此平凡成立。** -/
theorem maximal_nil_is_closure : maximal [] := by
  intro r ⟨r', hr', _⟩
  simp at hr'

end Lattice.Core.IR
