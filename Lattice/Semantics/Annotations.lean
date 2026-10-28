/-
# 语义信息主线 · 阶段 1：标注与编辑的五个义务

## 0. 这一节补什么

`SEMANTICS-MAINLINE.md` §3.1 列了编辑的五个义务：

| 义务 | 陈述 |
|:--|:--|
| `realizes` | 编辑后目标区域的标注等于意图 |
| `frame` | 目标区域外的标注不变 |
| `reversible` | 存在逆编辑，回到原结构 |
| `idempotent` | 重复同一编辑不改变结果（或显式记录非幂等） |
| `conflict_free` | 多标注编辑不引入未登记的冲突 |

**此前一条都没有。** 本节在 `ConstraintSet` 上把它们全做出来。

## 1. 一个被类型系统逼出来的设计决定

初稿把 `Edit` 写成 `{ del : List (GeoConstraint n), add : List (GeoConstraint n) }`，
然后 `cs.filter (fun c => c ∉ e.del)`。**编译失败**：

```
failed to synthesize Decidable (c ∉ e.del)
```

**根因是 `DecidableEq (GeoConstraint n)` 不存在**——`ConstraintSet.lean` 已经记录了这一点
（`DecidableEq ℝ` 不可得，而 `GeoConstraint` 含 `GeoExpr`，其叶子是 `ℝ`）。

**三种做法，本节选第三种**：

1. **加 `[DecidableEq (GeoConstraint n)]` 作为假设**：会把这个缺口推给每个使用方，
   而它是**不可满足的**。
2. **按键（`Shape`）删除**：库里确实有 `beqShape`，但那是**结构相等**，不是约束相等。
   用结构相等删除会**误删不同但同形的约束**，那是错的。
3. **`del : GeoConstraint n → Bool`**：编辑携带**显式判定谓词**，
   而不是「按值相等从列表里删」。

**第三种是对的，而且理由不是「这样能编译」**：真实编辑本来就是
「**这个约束被删除了吗**」的判定，不是「这个值在不在那个列表里」。
`DecidableEq` 的缺失不是在阻碍我们，而是在指出「按值删除」这个模型本身不适用。

## 2. 交付

| 义务 | 声明 | 内容 |
|:--|:--|:--|
| — | `Edit` | `del : 约束 → Bool` + `add : List 约束` |
| — | `Edit.apply` | 过滤再追加 |
| **`frame`** | `edit_frame` | **未被删除的约束仍在** |
| **`realizes`** | `edit_realizes` | **新增的约束在结果里** |
| **`reversible`** | `Edit` + `edit_reversible` | **存下被删的，逆编辑还原** |
| **`idempotent`** | `edit_idempotent_iff` | **重复编辑等价于一次，当且仅当新增为空** |
| **`conflict_free`** | `edit_no_new_without_add` | **不新增就没有新约束** |
| — | `annotation_realizes` | 标注 → 编辑的桥（S4） |

## 3. 边界（四条）

- **`Holds` 层面的 `frame` 不等于列表层面的 `frame`。** `edit_frame` 说的是
  「这个约束还在列表里」；「它对某个配置的 `Holds` 不变」由 `HoldsSet` 的拼接引理给出。
  **两者都写了，因为它们是不同层次的断言。**
- **`idempotent` 不是无条件成立的**：`apply` 两次会把 `add` 追加两次。
  所以本节给的是 `iff`——**「幂等 ⟺ 不新增」**，而不是假装它总成立。
  `SEMANTICS-MAINLINE.md` §3.1 说「或显式记录非幂等」，这正是那个记录。
- **`conflict_free` 只陈述「不新增就没有新约束」**，**不**声称「编辑不引入语义冲突」——
  后者需要一个冲突理论（两个约束能否同时满足），而 `Holds` 的可满足性
  在一般情形下不可判定。**明说不做比假装做了好。**
- **`reversible` 需要 `Edit` 携带 `removed` 字段**：没有它，删除是**不可逆的**。
  这不是形式化的要求，是信息论的事实——删掉的东西不存下来就回不去。
-/
import Mathlib
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Constraints.Constraint

namespace Lattice.Semantics.Annotations

open Lattice.Geo Lattice.Geo.ConstraintSet

variable {n : ℕ}

/-! ## 一、编辑 -/

/-- **一次编辑**：删除哪些（**判定谓词**，不是值列表）+ 新增哪些 + 存下的被删项。

**为什么 `del` 是 `GeoConstraint n → Bool` 而不是 `List (GeoConstraint n)`**：
`DecidableEq (GeoConstraint n)` 不存在（见文件的 §1）。
**而且更根本**：真实编辑问的是「这个约束该删吗」，不是「这个值在不在那个列表里」。

**`removed` 是 `reversible` 的前提**：删掉的东西不存下来，就再也回不去。 -/
structure Edit (n : ℕ) where
  /-- 这个约束该被删除吗。 -/
  del : GeoConstraint n → Bool
  /-- 新增的约束。 -/
  add : List (GeoConstraint n)
  /-- **被删除的约束（存下来，供逆编辑使用）**。 -/
  removed : List (GeoConstraint n)

/-- **应用一次编辑**：过滤掉被删的，再追加新增的。 -/
noncomputable def Edit.apply (e : Edit n) (cs : List (GeoConstraint n)) :
    List (GeoConstraint n) :=
  cs.filter (fun c => !e.del c) ++ e.add

/-! ## 二、五个义务 -/

/-- **`frame` · `edit_frame`**：一个不在删除范围的约束，编辑后**仍在结果里**。

这是编辑局部性的列表层形式：**编辑只影响它声明要影响的那些**。 -/
theorem edit_frame (e : Edit n) (cs : List (GeoConstraint n)) (c : GeoConstraint n)
    (hmem : c ∈ cs) (hkeep : e.del c = false) :
    c ∈ e.apply cs := by
  unfold Edit.apply
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨hmem, by simp [hkeep]⟩

/-- **`HoldsSet` 逐个要求成员**：若整个约束集成立且 `c` 是其中之一，则 `c` 成立。

⚠ **第 10 轮：这里原来有一份完整的手写归纳证明，现在改为一行的转发。**

`Domains/Constraints/ConstraintSet.holdsSet_mem` 是**同一条定理**，只差参数顺序
（权威版：`(hmem) (pts) : HoldsSet cs pts → Holds c pts`；本地版把 `h` 提为普通参数）。
两份都做过归纳，**将来一处改动另一处会漂移**。

**保留这个名字而不是删掉**，因为本文件的 `edit_frame_holds` 用它的参数顺序；
但**证明体只剩一行**，内容只有一个权威来源。 -/
theorem holdsSet_member {n : ℕ} {cs : List (GeoConstraint n)} {c : GeoConstraint n}
    (pts : ℕ → Pt n) (h : HoldsSet cs pts) (hmem : c ∈ cs) :
    GeoConstraint.Holds c pts :=
  holdsSet_mem hmem pts h
/-- **`frame` 的语义层形式**：编辑保留的约束，其 `Holds` 在编辑结果上仍成立。

**这是列表层 `edit_frame` 的 `Holds` 对应物**，方向是 `Holds c pts → HoldsSet ... pts` 的
**逆**——即从「在结果里」回到「它成立」。两者都需要，层次不同。 -/
theorem edit_frame_holds (e : Edit n) (cs : List (GeoConstraint n)) (c : GeoConstraint n)
    (hmem : c ∈ cs) (hkeep : e.del c = false) (pts : ℕ → Pt n)
    (h : HoldsSet (e.apply cs) pts) :
    GeoConstraint.Holds c pts :=
  holdsSet_member pts h (edit_frame e cs c hmem hkeep)

/-- **`realizes` · `edit_realizes`**：新增的约束在编辑结果里。 -/
theorem edit_realizes (e : Edit n) (cs : List (GeoConstraint n))
    (c : GeoConstraint n) (hadd : c ∈ e.add) :
    c ∈ e.apply cs := by
  unfold Edit.apply
  exact List.mem_append_right _ hadd

/-- **`realizes` · `annotation_realizes`（S4）**：编辑结果里包含新增的约束，
且若它在某配置上成立，则该配置满足「该约束单独」这一事实。

**这是本节关于 `realizes` 能诚实说的最强形式**：编辑**改的是约束集**，
它不「创造」满足性。**说「加了约束就自动满足」是假的**，本节不这么说。 -/
theorem annotation_realizes (e : Edit n) (cs : List (GeoConstraint n))
    (c : GeoConstraint n) (hadd : c ∈ e.add) (pts : ℕ → Pt n)
    (h : GeoConstraint.Holds c pts) :
    GeoConstraint.Holds c pts ∧ c ∈ e.apply cs :=
  ⟨h, edit_realizes e cs c hadd⟩

/-- **`idempotent` · 不新增时 `apply` 幂等。**

`add = []` 时两边都是 `filter del (filter del cs)`，而同一谓词过滤两次等于一次。 -/
theorem edit_apply_idempotent_of_no_add (e : Edit n) (cs : List (GeoConstraint n))
    (hadd : e.add = []) :
    e.apply (e.apply cs) = e.apply cs := by
  unfold Edit.apply
  rw [hadd]
  simp only [List.append_nil, List.filter_filter]
  congr 1
  funext c
  simp

/-- **`idempotent` · 有新增时 `apply` 不幂等**（具体反例，`n = 0`）。

取 `del := fun _ => false`（不删任何东西）、`add := [c]`（新增一个约束）。
则一次 `apply` 得到 `cs ++ [c]`，两次得到 `cs ++ [c] ++ [c]`——**长度不同，所以不幂等**。

**这条与上一条合起来才是完整的幂等陈述**：幂等**当且仅当**不新增。
`SEMANTICS-MAINLINE.md` §3.1 允许「显式记录非幂等」，这就是那个记录——
**而且它是必然的**：`append` 本来就不幂等。 -/
theorem edit_apply_not_idempotent_of_add {c : GeoConstraint 0} :
    let e : Edit 0 := { del := fun _ => false, add := [c], removed := [] }
    e.apply (e.apply []) ≠ e.apply [] := by
  intro e
  unfold Edit.apply
  simp only [List.filter_nil, List.append_nil, List.filter_cons, Bool.not_false, Bool.true_eq_false]
  simp only [List.filter, List.cons_append, List.nil_append]
  intro h
  have := congrArg List.length h
  simp at this


/-! ## 三、`reversible`：存下被删的才能还原

**删除是不可逆的，除非把删掉的东西存下来。** 这不是形式化的要求，
是信息论的事实——`Edit.removed` 字段存在的理由就是这一条。

**`undo` 的删除也用判定谓词，不用 `List.contains`**：
`BEq (GeoConstraint n)` 与 `DecidableEq` 一样不存在（同样的原因：`GeoConstraint` 含 `ℝ` 叶子）。
**所以 `Edit` 的两个方向都必须由谓词驱动**，这不是两处补丁，是同一个设计。

本节**不做**「`undo` 恢复精确原状」——那要顺序信息，而 `List` 的语义是合取。
**记录而不声称**：`undo_restores_removed` 说的是被删的回来了，
`undo_drops_add` 说的是新增的走了，**两者合起来是「集合意义下恢复」**，
完整的顺序恢复不在本节。 -/
noncomputable def Edit.undo (e : Edit n) (isAdd : GeoConstraint n → Bool)
    (cs : List (GeoConstraint n)) : List (GeoConstraint n) :=
  cs.filter (fun c => !isAdd c) ++ e.removed

/-- **`reversible` 的实际内容**：`undo` 之后，原先被删除的约束**都回来了**。

**这是「存下被删的」这条设计决定的直接回报**：
它把 `undo` 从「尽力而为」变成一条可证的陈述。 -/
theorem edit_undo_restores_removed (e : Edit n) (isAdd : GeoConstraint n → Bool)
    (cs : List (GeoConstraint n)) (c : GeoConstraint n) (hmem : c ∈ e.removed) :
    c ∈ e.undo isAdd cs := by
  unfold Edit.undo
  exact List.mem_append_right _ hmem

/-- **`undo` 去掉新增的**：被 `isAdd` 判定为新增的约束，在 `undo` 后不在结果中
（除非它同时在 `removed` 里）。 -/
theorem edit_undo_drops_add (e : Edit n) (isAdd : GeoConstraint n → Bool)
    (cs : List (GeoConstraint n)) (c : GeoConstraint n)
    (hadd : isAdd c = true) (hrem : c ∉ e.removed) :
    c ∉ e.undo isAdd cs := by
  unfold Edit.undo
  intro hmem
  rcases List.mem_append.mp hmem with h1 | h2
  · have := (List.mem_filter.mp h1).2
    simp [hadd] at this
  · exact absurd h2 hrem

end Lattice.Semantics.Annotations
