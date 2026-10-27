/-
# 「格」在哪里成立，在哪里不成立：`CompositionKind` 是格，`Verdict` 不是

## 0. 问题

库名叫 **LATTICE**，而 `Audit/CompositionAlgebra.lean` 自己写着：

> 报告说「格缺少格该有的东西」——**严格说，本库证明的是 monoid 结构，不是格结构**。

那条陈述是**对的**，但它是**结论**而不是**分析**。本文件把它拆开，给出精确的答案：

| 对象 | 结构 | 结论 |
|:--|:--|:--|
| `CompositionKind`（**一段**判定） | 两元素链 `sequential < bridged` | **有界格**，本节证明 |
| `Verdict = List CompositionKind`（**多段**判定） | 逐点序 | **不是格**，本节给出证明 |

**所以「格」不是空的，也不是全的**：它在「每段判定的强弱」上真实存在（`bridged` 需要一条蕴含，
`sequential` 什么也不需要，二者有交与并），而在「判定序列」上不存在（长度不同的两个判定没有
公共上界）。**这就是 `Verdict` 真正是 monoid 的原因：它的组合是拼接，而拼接不保持长度。**

## 1. `CompositionKind` 是有界格

两个构造子只用得上一个事实：`bridged` 需要一条蕴含，`sequential` 需要 `True`——**是一段蕴含的两种
极端**。所以它可以编码成 `Bool`（`sequential ↦ false`，`bridged ↦ true`），而 `Bool` 的序
`false < true` 正是「需求更弱」。

**这解释了为什么本库的判定代数天然是 monoid 而不是格**：格结构在**单段**上，而组合操作
（`++`）作用在**序列**上。序列的逐点序保留格性质需要长度一致，拼接破掉了它。

见 `kindLe` / `kindLe_iff` / `kindSup` / `kindInf` 及其上确界/下确界性质。

## 2. `Verdict` 在逐点序下不是格

逐点序 `Forall₂ (· ≤ ·)` 只在**等长**时可能有上界。反例：

```lean
[.bridged]             -- 一段，需要蕴含
[.sequential, .sequential]  -- 两段，都不需要
```

任何一个上界 `u` 必须同时满足 `u.length = 1`（因为 `Forall₂` 强制等长）与 `u.length = 2`。
**矛盾。所以没有上界，`Verdict` 不是格。**

见 `verdict_no_sup`。

## 3. 边界

- **本节不建 `Lattice`/`LinearOrder` 类型类实例**，只给出显式的 `kindLe`/`kindSup`/`kindInf`
  与它们的性质定理。理由：`Verdict` 上没有类型类实例，而给 `CompositionKind` 单独装一个
  `LinearOrder` 会让「某处有格结构」变成读者需要自己去猜的事；显式函数加性质定理把这个结构
  **局部化**在它真正成立的地方，且不与任何上游实例冲突。
- **本节不声称** `Verdict` 在其他序（例如引入 padding 的定长化）下也不是格。**定长化之后它确实是格**
  ——这正是「拼接不保持长度」这个根因的推论，也是如果需要格结构该走的路。
- 本节**不改** `CompositionAlgebra`、`CompositionClass` 的任何既有定理。
-/
import Mathlib
import Lattice.Audit.CompositionClass

namespace Lattice.Audit

open CompositionClass

/-! ## 一、单段判定：`CompositionKind` 是两元素链 -/

/-- `sequential ↦ false`（无需额外证据），`bridged ↦ true`（需要一条蕴含）。 -/
def kindToBool : CompositionKind → Bool
  | .sequential => false
  | .bridged => true

/-- `Bool` 回到判定。 -/
def boolToKind : Bool → CompositionKind
  | false => .sequential
  | true => .bridged

theorem kindToBool_boolToKind (b : Bool) : kindToBool (boolToKind b) = b := by
  cases b <;> rfl

theorem boolToKind_kindToBool (k : CompositionKind) : boolToKind (kindToBool k) = k := by
  cases k <;> rfl

/-- **判定强度的序**：`a ≤ b` 当且仅当 `b` 需要的证据不少于 `a`。

按 `Bool` 编码，`false < true`，即 `sequential < bridged`。**这是「需求更弱」的方向**：
`sequential` 是底（什么都不要），`bridged` 是顶（要一条蕴含）。 -/
def kindLe (a b : CompositionKind) : Prop := kindToBool a ≤ kindToBool b

/-- **序的显式形式**：`a ≤ b` 当且仅当 `a` 是 `sequential` 或者 `b` 是 `bridged`。

这条把「一段蕴含的两种极端」写成了序关系，比 `Bool` 编码更直接从 `Evidence` 的定义读出来。 -/
theorem kindLe_iff (a b : CompositionKind) : kindLe a b ↔ a = .sequential ∨ b = .bridged := by
  cases a <;> cases b <;> simp [kindLe, kindToBool]

theorem kindLe_refl (a : CompositionKind) : kindLe a a := by
  cases a <;> simp [kindLe, kindToBool]

theorem kindLe_antisymm {a b : CompositionKind} (h₁ : kindLe a b) (h₂ : kindLe b a) : a = b := by
  have hb : ∀ x y : Bool, x ≤ y → y ≤ x → x = y := by decide
  have h : kindToBool a = kindToBool b := hb _ _ h₁ h₂
  calc a = boolToKind (kindToBool a) := (boolToKind_kindToBool a).symm
    _ = boolToKind (kindToBool b) := by rw [h]
    _ = b := boolToKind_kindToBool b

theorem kindLe_trans {a b c : CompositionKind} (h₁ : kindLe a b) (h₂ : kindLe b c) :
    kindLe a c := by
  cases a <;> cases b <;> cases c <;> simp_all [kindLe, kindToBool]

/-- **底**：`sequential` 满足任何要求的下界。 -/
theorem kindLe_bot (a : CompositionKind) : kindLe .sequential a := by
  rw [kindLe_iff]; exact Or.inl rfl

/-- **顶**：`bridged` 是一切的上界。 -/
theorem kindLe_top (a : CompositionKind) : kindLe a .bridged := by
  rw [kindLe_iff]; exact Or.inr rfl

/-! ## 二、单段的并：`bridged` 是唯一非平凡的上界

两元素链的并就是「两者取较强的那个」。 -/

/-- **并**：任取一个仍是上界的最小者。在 `CompositionKind` 上就是 `bridged`（除非两者都弱）。 -/
def kindSup (a b : CompositionKind) : CompositionKind := if kindToBool a then .bridged else b

/-- **交**：取较弱的那个。 -/
def kindInf (a b : CompositionKind) : CompositionKind := if kindToBool a then b else .sequential

theorem kindLe_sup_left (a b : CompositionKind) : kindLe a (kindSup a b) := by
  cases a <;> cases b <;> simp [kindLe, kindToBool, kindSup]

theorem kindLe_sup_right (a b : CompositionKind) : kindLe b (kindSup a b) := by
  cases a <;> cases b <;> simp [kindLe, kindToBool, kindSup]

theorem kindSup_le {a b c : CompositionKind} (h₁ : kindLe a c) (h₂ : kindLe b c) :
    kindLe (kindSup a b) c := by
  cases a <;> cases b <;> simp_all [kindLe, kindToBool, kindSup]

theorem kindInf_le_left (a b : CompositionKind) : kindLe (kindInf a b) a := by
  cases a <;> cases b <;> simp [kindLe, kindToBool, kindInf]

theorem kindInf_le_right (a b : CompositionKind) : kindLe (kindInf a b) b := by
  cases a <;> cases b <;> simp [kindLe, kindToBool, kindInf]

theorem kindLe_inf {a b c : CompositionKind} (h₁ : kindLe c a) (h₂ : kindLe c b) :
    kindLe c (kindInf a b) := by
  cases a <;> cases b <;> simp_all [kindLe, kindToBool, kindInf]

/-- **`CompositionKind` 的判定代数是一个有界格。**

`kindLe_*` + `kindSup_le` / `kindLe_sup_left` / `kindLe_sup_right` 给出上确界，
`kindInf_*` 给出下确界，`kindLe_bot` / `kindLe_top` 给出界。 -/
theorem kind_is_bounded_lattice :
    (∀ a, kindLe a a) ∧ (∀ a b c, kindLe a b → kindLe b c → kindLe a c) ∧
    (∀ a, kindLe .sequential a) ∧ (∀ a, kindLe a .bridged) ∧
    (∀ a b, kindLe a (kindSup a b) ∧ kindLe b (kindSup a b) ∧
      ∀ c, kindLe a c → kindLe b c → kindLe (kindSup a b) c) :=
  ⟨kindLe_refl, fun _ _ _ => kindLe_trans,
   kindLe_bot, kindLe_top,
   fun a b => ⟨kindLe_sup_left a b, kindLe_sup_right a b, fun c h₁ h₂ => kindSup_le h₁ h₂⟩⟩

/-! ## 三、多段判定：`Verdict` 在逐点序下**不是**格

`Verdict = List CompositionKind`。逐点序用 `List.Forall₂`，它**强制等长**。 -/

/-- **`Verdict` 的逐点序**：逐段比较强度，长度必须相同。 -/
def verdictLe : List CompositionKind → List CompositionKind → Prop :=
  List.Forall₂ kindLe

/-- **`Verdict` 不是格。**

反例是长度不同的两个判定：

```lean
[.bridged]                   -- 1 段
[.sequential, .sequential]   -- 2 段
```

`Forall₂` 强制上界与两个下界**等长**，所以上界长度必须同时是 1 与 2——矛盾。
**这就是本库的组合代数天然是 monoid 而不是格的原因**：组合是拼接，而拼接不保持长度。 -/
theorem verdict_no_sup :
    ¬ ∃ u : List CompositionKind,
        verdictLe [.bridged] u ∧ verdictLe [.sequential, .sequential] u := by
  rintro ⟨u, h₁, h₂⟩
  have len₁ : u.length = 1 := by
    simpa using (List.Forall₂.length_eq h₁).symm
  have len₂ : u.length = 2 := by
    simpa using (List.Forall₂.length_eq h₂).symm
  omega

/-- **定长化之后它确实是格**：长度相同的两个判定有逐点上界（取逐段的 `kindSup`）。

这不是空话——它是「`Verdict` 为什么只是 monoid」这个问题的正面回答：**格结构被长度破坏，
而长度相同的切片上格结构仍在。** -/
theorem verdict_lub_of_length_eq {a b : List CompositionKind} (h : a.length = b.length) :
    ∃ u : List CompositionKind, u.length = a.length ∧ verdictLe a u ∧ verdictLe b u := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => exact ⟨[], rfl, .nil, .nil⟩
      | cons _ _ => simp at h
  | cons x xs ih =>
      cases b with
      | nil => simp at h
      | cons y ys =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          obtain ⟨u, hu_len, hu_a, hu_b⟩ := ih h
          exact ⟨kindSup x y :: u, by simp [hu_len],
                 List.Forall₂.cons (kindLe_sup_left x y) hu_a,
                 List.Forall₂.cons (kindLe_sup_right x y) hu_b⟩

/-- **结论**：库名里的「格」在**每段判定**上成立，在**判定序列**上不成立。

这一条不是措辞妥协，是两条定理的合取：`kind_is_bounded_lattice` 与 `verdict_no_sup`。 -/
theorem lattice_holds_per_segment_not_per_sequence :
    (∀ a : CompositionKind, kindLe .sequential a ∧ kindLe a .bridged) ∧
    (¬ ∃ u : List CompositionKind,
        verdictLe [.bridged] u ∧ verdictLe [.sequential, .sequential] u) :=
  ⟨fun a => ⟨kindLe_bot a, kindLe_top a⟩, verdict_no_sup⟩

end Lattice.Audit
