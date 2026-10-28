/-
# 语义信息主线 · 阶段 1：整合证书（`MergeRecord` / `MergeSound`）

## 0. 一段自我记录

这个文件**第 197 轮写过一个版本，被我自己删了**：那一版的 `MergeSound` 有一个字段
`conflict_free : R.conflicts = R.conflicts`。**那是重言**——它证明 `a = a`，什么都没说，
却让 `MergeSound` 看起来有了「冲突已裁决」这一项。

本节按之后的纪律重写：**每个字段都必须拒绝一个具体的反例**，且写完要过
`check_proof_strength.py` 与 `check_vacuous_hypotheses.py` 两道守卫。

## 1. 谁负责什么

`SEMANTICS-MAINLINE.md` §3.2 的分工是本节全部要点：

> `MergeRecord` 是**数据**；`MergeSound` 是**证明**。人只填数据，机器检查证明。

**这个分工只有在 `MergeSound` 有内容时才成立。** 本节让它有三个有内容的字段：

| 字段 | 内容 | 凭什么不是自动的 |
|:--|:--|:--|
| `global_holds` | 全局约束在 `pts` 上成立 | 要人给出，不是合并出来的 |
| `experts_hold` | 每个专家在自己的域上成立 | 同上 |
| **`conflicts_resolved`** | **每个登记的冲突，其「输」的一方确实被丢弃** | **可以不为真**（见 N 定理） |

## 2. 为什么「丢弃」用判定谓词而不是列表

`GeoConstraint` 没有 `DecidableEq`（`ConstraintSet.lean` 已记录 `DecidableEq ℝ` 不可得），
所以**不能**按值从列表里删。`MergeRecord.rejected : GeoConstraint n → Bool` 是**人做的决定**，
它是谓词而不是数据表——与 `Semantics/Annotations.lean` 的 `Edit.del` 同一个理由。

**人的决定变成谓词，机器的检查变成定理。** 这就是分工的实现形式。

## 3. 交付

| 声明 | 内容 |
|:--|:--|
| `Expert` / `ConflictPair` / `MergeRecord` | **数据** |
| `MergeRecord.allConstraints` | 全局 ++ 各专家 |
| `MergeRecord.merged` | 丢掉 `rejected` 的那些 |
| `holdsSet_of_sublist` | **通用引理**：`HoldsSet` 在子列表上仍成立 |
| `merged_sublist` | `merged` 是 `allConstraints` 的子列表 |
| `merge_parts` | 全局与各专家都成立 ⟹ `allConstraints` 成立 |
| **`merge_sound`** | **两者合起来 ⟹ `merged` 成立** |
| `MergeSound` | 三个有内容的字段 |
| **`conflict_loser_absent`** | **被裁决丢弃的约束确实不在 `merged` 里** |
| **`conflicts_not_automatic`** | **N：存在登记了冲突却没丢弃输方的记录** |

## 4. 边界

- **`merge_sound` 的前提是「每个专家在自己的域上成立」**，不是「对所有人成立」。
  一个专家只保证自己的域——**跨域一致性不是本节的事**。
- **本节不判断两个约束是否真的冲突**：`ConflictPair` 是**人登记**的。
  机器只能检查「登记的因果有没有被执行」，**检查不了「该不该登记」**——
  因为两个约束的联合可满足性在一般情形下不可判定。
- **`priority` 只记录，不参与证明**。按优先级自动裁决是另一个问题（优化/仲裁）。
- 本节**不改** `Geo/*` 与 `Semantics/Annotations.lean`。
-/
import Mathlib
import Lattice.Geo.ConstraintSet
import Lattice.Domains.Constraint

namespace Lattice.Semantics.Merge

open Lattice.Geo Lattice.Geo.ConstraintSet

variable {n : ℕ}

/-! ## 一、数据 -/

/-- **一个专家**：名字 + 它贡献的约束集。 -/
structure Expert (n : ℕ) where
  name : ℕ
  constraints : List (GeoConstraint n)

/-- **一个已被人工裁决的冲突**：两侧约束 + 保留哪一侧。 -/
structure ConflictPair (n : ℕ) where
  left : GeoConstraint n
  right : GeoConstraint n
  /-- `true` 表示保留左侧、丢弃右侧。 -/
  keepLeft : Bool

/-- **整合记录**——**纯数据**，人填。

`rejected` 是**人的决定**，不是推导出来的：`GeoConstraint` 没有 `DecidableEq`，
所以「丢哪些」只能由谓词给出（与 `Edit.del` 同一理由）。 -/
structure MergeRecord (n : ℕ) where
  experts : List (Expert n)
  global : List (GeoConstraint n)
  conflicts : List (ConflictPair n)
  /-- **人决定丢弃哪些约束。** -/
  rejected : GeoConstraint n → Bool
  /-- 优先级（记录用，**不参与证明**）。 -/
  priority : Expert n → ℕ

/-! ## 二、合并与两个基本事实 -/

/-- **合并前的全部约束**：全局的在前，各专家的依次在后。 -/
noncomputable def MergeRecord.allConstraints (R : MergeRecord n) : List (GeoConstraint n) :=
  R.global ++ R.experts.flatMap Expert.constraints

/-- **合并后的约束集**：丢掉人决定丢弃的那些。 -/
noncomputable def MergeRecord.merged (R : MergeRecord n) : List (GeoConstraint n) :=
  (R.allConstraints).filter (fun c => !R.rejected c)

/-- **通用引理：`HoldsSet` 在子列表上仍成立。**

**这条不是重言**：`HoldsSet` 是逐项合取，丢掉一些项仍然成立；
反之不成立（少项的合取更弱，推不出多项的合取）。 -/
theorem holdsSet_of_sublist {l l' : List (GeoConstraint n)} (pts : ℕ → Pt n)
    (h : HoldsSet l pts) (hs : List.Sublist l' l) : HoldsSet l' pts := by
  induction l generalizing l' with
  | nil => cases hs with
    | slnil => trivial
  | cons c rest ih =>
      cases hs with
      | cons _ htail => exact ih h.2 htail
      | cons₂ _ htail => exact ⟨h.1, ih h.2 htail⟩

/-- **`merged` 是 `allConstraints` 的子列表**（过滤只删不加）。 -/
theorem merged_sublist (R : MergeRecord n) :
    List.Sublist R.merged R.allConstraints := by
  unfold MergeRecord.merged
  exact List.filter_sublist R.allConstraints

/-- **`flatMap` 上的 `HoldsSet`**：若每个专家在自己的约束上成立，则全部拼起来也成立。

**这条需要归纳，不是 `flatMap` 定义的改写**——所以它单独成一条，
`merge_parts` 才能只做拼接。 -/
theorem holdsSet_flatMap_experts (es : List (Expert n)) (pts : ℕ → Pt n)
    (h : ∀ e ∈ es, HoldsSet e.constraints pts) :
    HoldsSet (es.flatMap Expert.constraints) pts := by
  induction es with
  | nil => trivial
  | cons e rest ih =>
      rw [List.flatMap_cons, holdsSet_append]
      exact ⟨h e (List.mem_cons_self e rest),
             ih (fun x hx => h x (List.mem_cons_of_mem e hx))⟩

/-- **各部分成立 ⟹ 合并前的全部约束成立。** -/
theorem merge_parts (R : MergeRecord n) (pts : ℕ → Pt n)
    (hg : HoldsSet R.global pts)
    (he : ∀ e ∈ R.experts, HoldsSet e.constraints pts) :
    HoldsSet R.allConstraints pts := by
  unfold MergeRecord.allConstraints
  rw [holdsSet_append]
  exact ⟨hg, holdsSet_flatMap_experts R.experts pts he⟩

/-! ## 三、整合证书 -/

/-- **整合证书**——**证明**，机器检查。三个字段，每个都拒绝一个具体的反例。

⚠ **第 197 轮的版本有一个字段是 `R.conflicts = R.conflicts`**（重言）。本节换成
`conflicts_resolved`，它有内容：**登记了冲突就必须真的丢弃输方**，而这件事可以不为真
（见 `conflicts_not_automatic`）。 -/
structure MergeSound (R : MergeRecord n) (pts : ℕ → Pt n) : Prop where
  /-- 全局约束在该配置上成立。 -/
  global_holds : HoldsSet R.global pts
  /-- 每个专家的约束在自己的域上成立。 -/
  experts_hold : ∀ e ∈ R.experts, HoldsSet e.constraints pts
  /-- **每个登记的冲突，其输方确实被丢弃。**

  `keepLeft = true` 时要求 `right` 被丢弃；反之要求 `left` 被丢弃。
  **这是「人的裁决被执行了」的唯一可检查形式。** -/
  conflicts_resolved :
    ∀ p ∈ R.conflicts,
      ((p.keepLeft = true) → R.rejected p.right = true) ∧
      ((p.keepLeft = false) → R.rejected p.left = true)

/-- **整合 sound**：证书存在 ⟹ 合并后的约束集在该配置上成立。 -/
theorem merge_sound (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts) :
    HoldsSet R.merged pts :=
  holdsSet_of_sublist pts (merge_parts R pts h.global_holds h.experts_hold)
    (merged_sublist R)

/-- **被丢弃的约束不在 `merged` 里。**

**这是 `rejected` 这个人的决定与合并结果之间的桥**：它让「丢弃」不是一个记录字段，
而是一条关于 `merged` 的定理。 -/
theorem rejected_absent (R : MergeRecord n) (c : GeoConstraint n)
    (h : R.rejected c = true) : c ∉ R.merged := by
  unfold MergeRecord.merged
  intro hmem
  have := (List.mem_filter.mp hmem).2
  simp [h] at this

/-- **裁决被执行 ⟹ 输方不在合并结果里。** -/
theorem conflict_loser_absent (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts)
    (p : ConflictPair n) (hp : p ∈ R.conflicts) :
    (p.keepLeft = true → p.right ∉ R.merged) ∧
      (p.keepLeft = false → p.left ∉ R.merged) := by
  have hr := h.conflicts_resolved p hp
  exact ⟨fun hk => rejected_absent R p.right (hr.1 hk),
         fun hk => rejected_absent R p.left (hr.2 hk)⟩

/-! ## 四、N：冲突检查不是自动的

**如果 `conflicts_resolved` 对任何记录都成立，它就不是字段而是一条定理**，
`MergeSound` 就退化成「只要各部分成立即可」——那正是第 197 轮那个重言版本的毛病。

下面给出反例：登记一个冲突、`keepLeft = true`，但 `rejected` 恒 `false`。
**输方没有被丢弃，而其他两个字段都成立。** 所以「冲突已裁决」是一个**真的要求**。 -/
theorem conflicts_not_automatic :
    ∃ (R : MergeRecord 0), ¬ MergeSound R (fun _ _ => 0) := by
  refine ⟨{ experts := [], global := [],
            conflicts := [{ left := .leZero (.const 0), right := .leZero (.const 1),
                            keepLeft := true }],
            rejected := fun _ => false,
            priority := fun _ => 0 }, ?_⟩
  intro h
  have hr := h.conflicts_resolved
    { left := .leZero (.const 0), right := .leZero (.const 1), keepLeft := true }
    (List.mem_cons_self _ _)
  exact absurd (hr.1 rfl) (by simp)

/-! ## 五、整合证书对专家是**可组合**的（S20 的可证部分）

### 先说清 S20 原文要求什么，以及为什么不能照做

`SEMANTICS-MAINLINE.md` 的 **S20 `vocab_align_merge_sound`** 说「多专家共享词表后 `MergeSound` 保持」。

**问题**：`MergeSound`（上一节）完全不涉及词表类型 `V`。所以「保持」只有两种可能：

1. **空的**：既然 `MergeSound` 不提 `V`，它对词表编辑自然不变——**那是重言**，
   正是本库反复出现的那种「看起来证明了什么」；
2. **需要一条桥**：把 `VocabModel.behavior : V → V → ℝ` 与 `GeoConstraint.Holds : (ℕ → Pt n) → Prop`
   连起来。**而这条桥在库里不存在**——`behavior` 返回标量 logit，`Holds` 谈配置，
   两者是不同的宇宙。**连接它们正是「符号⇄权重」那一跳，而那一跳没有通。**

**所以本节不做 S20 的词表部分，而是做它真正需要的那半：多专家整合的证书必须是可组合的。**
否则「多专家」只是一句话：一个专家的证书不能说明另一个专家。

### 交付

| 定理 | 内容 |
|:--|:--|
| **`merge_sound_cons`** | **追加一个在自身上成立的专家，证书保持** |
| **`merge_sound_append_experts`** | 追加**一列**这样的专家，证书保持 |
| **`merge_sound_add_global`** | 追加一条成立的全局约束，证书保持 |
| **`merge_sound_not_composable`** | **N：追加一个不成立的专家，证书破坏** |

**N 那条是关键**：若「追加专家总是保持证书」，可组合性就是重言。
反例证明**每个专家都必须自己满足自己的约束**——这才叫「多专家整合」。

### 边界

- **可组合性对专家数 `n`、约束表长度都没有限制**（`append` 归纳），
  但**每个新专家都要单独给出 `HoldsSet` 前提**：证书不会自己「传染」。
- **`rejected` 在整个过程中不变**：本节只讨论**追加**，不讨论**追加同时裁决冲突**。
  后者要改 `conflicts` 与 `rejected` 两个字段，是另一件事。
- **本节不碰词表**。理由见上。 -/

/-- **追加一个在自身上成立的专家，证书保持。**

三个字段逐个验证：`global_holds` 不变、`experts_hold` 对新专家用 `he`、对其余用原证书、
`conflicts_resolved` 不变（本节不改 `conflicts` 与 `rejected`）。 -/
theorem merge_sound_cons (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts)
    (e : Expert n) (he : HoldsSet e.constraints pts) :
    MergeSound { R with experts := e :: R.experts } pts where
  global_holds := h.global_holds
  experts_hold := by
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hmem
    · exact he
    · exact h.experts_hold e' hmem
  conflicts_resolved := h.conflicts_resolved

/-- **追加一列成立的专家，证书保持。** -/
theorem merge_sound_append_experts (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts)
    (es : List (Expert n)) (he : ∀ e ∈ es, HoldsSet e.constraints pts) :
    MergeSound { R with experts := R.experts ++ es } pts where
  global_holds := h.global_holds
  experts_hold := by
    intro e' he'
    rcases List.mem_append.mp he' with h1 | h2
    · exact h.experts_hold e' h1
    · exact he e' h2
  conflicts_resolved := h.conflicts_resolved

/-- **追加一条成立的全局约束，证书保持。** -/
theorem merge_sound_add_global (R : MergeRecord n) (pts : ℕ → Pt n) (h : MergeSound R pts)
    (c : GeoConstraint n) (hc : GeoConstraint.Holds c pts) :
    MergeSound { R with global := c :: R.global } pts where
  global_holds := by
    -- HoldsSet (c :: R.global) pts IS the conjunction Holds c pts ∧ HoldsSet R.global pts
    show HoldsSet (c :: R.global) pts
    exact ⟨hc, h.global_holds⟩
  experts_hold := h.experts_hold
  conflicts_resolved := h.conflicts_resolved

/-- **N：追加一个不成立的专家，证书破坏。**

取专家 `⟨0, [eqZero (const 1)]⟩`：它的约束要求 `1 = 0`，在任何配置上都不成立。

**若这条为假**（即追加任何专家都保持证书），可组合性就是重言，
`MergeSound` 也就退化成「只要全局约束成立即可」——那么「多专家」这个词没有任何内容。 -/
theorem merge_sound_not_composable :
    ∃ (R : MergeRecord 0) (pts : ℕ → Pt 0),
      MergeSound R pts ∧
        ∀ (e : Expert 0), ¬ HoldsSet e.constraints pts →
          ¬ MergeSound { R with experts := e :: R.experts } pts := by
  -- the empty record is sound at any configuration
  refine ⟨{ experts := [], global := [], conflicts := [], rejected := fun _ => false,
            priority := fun _ => 0 }, fun _ _ => 0, ?_, ?_⟩
  · exact ⟨trivial, (by intro e he; simp at he), (by intro p hp; simp at hp)⟩
  · intro e hne hs
    exact hne (by
      -- the certificate's `experts_hold` forces `HoldsSet e.constraints`
      simpa using hs.experts_hold e (List.mem_cons_self e []))

end Lattice.Semantics.Merge
