import Mathlib
import Lattice.Core.Syntax

/-!
# 约束核心：主线的抽象约束类型

## 为什么这个文件存在

**`Semantics/` 层把「约束」当作**不透明的符号**使用：它关心的是「一组约束在某配置上是否全真」这条**列表语义**，
而不是某个约束内部是「平行」还是「等距」。**

**第 265 轮把几何层整层归档到 `Lattice/Reference/Geometry/` 之后，主线不再能导入那些文件；
而 `Semantics/` 的 8 个文件确实需要「约束」这个类型与 `HoldsSet` 这个谓词。**
**⇒ 本文件提供**最小**的那一部分：一个抽象约束类型，加上它的列表语义。**

## 抽象到什么程度

**`GeoConstraint n` 有 16 个构造子，每一个都对应 `Lv-00` 的一条具体谓词（平行、共线、等距……）。
主线一处都没有用到那些构造子 —— 它只用「有这样一个类型」和「列表全真」。**
**⇒ 所以这里的 `Constraint n` 是一个**参数化的抽象类型**：给定一个「满足关系」`Sat : Constraint n → (ℕ → Pt n) → Prop`
就能得到具体的约束语义。**
**这不是「为了归档而删内容」：它把主线**真正依赖的那条接口**显式化，而几何层的 16 个构造子变成这条接口的一个实例。
归档目录里那份完整定义仍然存在，需要具体几何时从那里取。**

## 与归档层的关系

**归档层（`Reference/Geometry/`）与本文件**互不导入**：归档层可以保留它自己的 `GeoConstraint`，
本文件提供抽象版本，两者通过 `Constraint.specialize` 沟通 —— 也就是说，**任何具体的约束类型都可以看作本文件的一个实例。**
-/

namespace Lattice.Semantics

/-- **`n` 维实空间中的点**：与归档层同名同义，`Lattice.Core.Point ℝ n` 的缩写。

**=> 这里**不**另造一个点类型 —— `Core.Syntax.Point` 已经是权威定义，重定义会触发 I3（定义唯一）。** -/
abbrev Pt (n : ℕ) := Lattice.Core.Point ℝ n

open Lattice

/-- **抽象的约束类型。**

**`Constraint n` 是一个不透明的载体：它是什么由使用方决定。**
**=> 主线只需要「有一堆约束」这个概念，而约束的内部结构属于领域层（归档的几何层是其中一个实例）。**
**把构造子留空是有意的：一旦这里写下 `parallel`/`collinear` 之类的构造子，主线就又依赖了几何词汇。** -/
structure Constraint (n : ℕ) where
  /-- **约束的载体类型。** -/
  carrier : Type
  /-- **该约束在一个点配置上是否成立。** -/
  Sat : carrier → (ℕ → Pt n) → Prop

/-- **从任意具体的「载体 + 满足关系」得到一个 `Constraint`。**

**=> 这是把领域约束接进主线的唯一入口：几何层、约束层或任何别处的约束类型都可以用 `specialize` 落到这里，
而主线不需要知道它来自哪一层。** -/
def Constraint.specialize {n : ℕ} (C : Type) (Sat : C → (ℕ → Pt n) → Prop) : Constraint n :=
  { carrier := C, Sat := Sat }

/-- **约束集合的语义：列表全真。**

**`HoldsSet cs pts` 表示 `cs` 里的每条约束在 `pts` 上都成立。**
**=> 这是主线真正需要的那条语义：它只看**列表**，不看单条约束的内部。**
**定义按列表递归，因此空集恒真、且可对 `append` 分解 —— 这两条性质在下面的定理里给出。** -/
def HoldsSet {n : ℕ} (C : Constraint n) : List C.carrier → (ℕ → Pt n) → Prop
  | [], _ => True
  | c :: cs, pts => C.Sat c pts ∧ HoldsSet C cs pts

/-- **空约束集恒成立。**

**=> `HoldsSet` 的基例，也是「无条件约束集」的形式：没有要求时任何配置都满足。** -/
theorem holdsSet_nil {n : ℕ} (C : Constraint n) (pts : ℕ → Pt n) :
    HoldsSet C [] pts :=
  trivial

/-- **单条约束的集合语义就是该约束本身。**

**=> 把列表语义与单条语义对齐：这是「集合语义是单条语义的合取」这句话的基例。** -/
theorem holdsSet_singleton {n : ℕ} (C : Constraint n) (c : C.carrier) (pts : ℕ → Pt n) :
    HoldsSet C [c] pts ↔ C.Sat c pts := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, trivial⟩

/-- **集合语义在拼接下分解。**

**`HoldsSet C (cs ++ ds) pts ↔ HoldsSet C cs pts ∧ HoldsSet C ds pts`。**
**=> 这条使「约束集可以分块验证」成为严格等价，而不只是单向蕴含。**
**它是主线在 `Stage1`/`Merge` 里做「约束集合并」的基础：合并后的约束集成立，等价于两个来源各自成立。** -/
theorem holdsSet_append {n : ℕ} (C : Constraint n) (cs ds : List C.carrier) (pts : ℕ → Pt n) :
    HoldsSet C (cs ++ ds) pts ↔ HoldsSet C cs pts ∧ HoldsSet C ds pts := by
  induction cs with
  | nil =>
      simp only [List.nil_append, holdsSet_nil, true_and]
  | cons c cs ih =>
      rw [List.cons_append, HoldsSet, ih, HoldsSet]
      exact and_assoc.symm
theorem holdsSet_mem {n : ℕ} (C : Constraint n) {c : C.carrier} {cs : List C.carrier}
    (hmem : c ∈ cs) (pts : ℕ → Pt n) (h : HoldsSet C cs pts) : C.Sat c pts := by
  induction cs with
  | nil => exact by simp at hmem
  | cons d ds ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact h.1
      · exact ih hmem' h.2

/-! ## 待补：子列表单调性

**`holdsSet_of_sublist`（`cs <+: ds → HoldsSet C ds pts → HoldsSet C cs pts`）本轮**未**完成。**

**尝试过的三条路径及失败点：**

| 路径 | 失败点 |
|:--|:--|
| **对 `Sublist` 归纳** | **此 mathlib 版本对 `Sublist` 的 `induction` 只给出 `intro` 一个 case 名，`slnil`/`cons`/`cons₂` 均被拒为 "invalid alternative name"** |
| **`List.Sublist.rec` 显式递归** | **`cons` 分支需要从 `P (a :: l₂)` 得出 `P l₂`，对抽象 `P` 不可行（`cons` 允许 `ds` 多出一个元素）** |
| **`cs` 归纳 + `subset` + `sublist_cons_iff`** | **`cs` 的尾部仍是 `ds` 的子列表这一步需要 `ds` 减少一个元素，而 `sublist_cons_iff` 的形态不直接给出** |

**⇒ 这**不是**「定理为假」——`HoldsSet` 在子列表上确实更弱，命题本身成立（`holdsSet_mem` 已证每一成员成立，
而 `HoldsSet` 就是成员的合取）。**
**⇒ 缺的是**与版本匹配的归纳策略**，而不是内容。**

**下一步的思路（记录备查）：**
**1. 先证 `HoldsSet C cs pts ↔ ∀ c ∈ cs, C.Sat c pts`（`Forall` 形式），把列表递归转成 `List.Forall`；**
**2. `List.Forall` 上有成熟的 `Forall.imp`/`Sublist.forall` 一套引理，`Sublist.subset` 直接给成员关系；**
**3. 由 1 与 2 组合即得 `holdsSet_of_sublist`。**
**⇒ 这条路线把「递归定义的合取」与「基于成员关系的 `Forall`」桥接起来，绕开了 `Sublist` 归纳的版本问题。** -/

end Lattice.Semantics
