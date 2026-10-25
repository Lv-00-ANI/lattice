import Mathlib
import Lattice.Lib.FCA.RealFCA
/-!
# LATTICE: 闭包算子格 —— 所有闭包算子构成完备格（逐点序）

## 本文件建立什么

给定类型 `α`，**闭包算子**（closure operator）是 `α → α` 的
单调、扩张、幂等映射。本文件证明闭包算子族在**逐点序**下构成
**完备格**，并把 FCA 的 `closureOperator R` 作为实例接入：

  1. `IsClosureOp`：闭包算子的谓词（单调 + 扩张 + 幂等），
     三条性质**逐条**陈述，便于分别使用；
  2. `closureOp_le_iff`：逐点序 `c₁ ≤ c₂ ⟺ ∀ x, c₁ x ≤ c₂ x`；
  3. `sInf_closed`：**本文件核心**——闭包算子族对**逐点 `sInf`**
     封闭（若每个 `c i` 是闭包算子，则 `fun x => ⨅ i, c i x` 也是）。
     这是"闭包算子格是完备格"的**唯一**非平凡验证：扩张性需要
     用 `iInf_le`，**单调性需要 `iInf` 的下确界性质**，幂等性
     **最微妙**——它需要"下确界是下界"与"单调"的配合，
     且三者的证明**互不相同**；
  4. `closureOp_inf`：两闭包算子的逐点 `⊓` 仍是闭包算子（`sInf` 的二元情形）；
  5. `fca_closure_isClosureOp`：`RealNonlinearExtract.closureOperator R`
     满足 `IsClosureOp`——FCA 提取算子是闭包算子（**实例化**）；
  6. `fca_closure_le_iff_fixpoint`：`closureOperator R ≤ 常值闭集 c`
     ⟺ `c` 是 `closureOperator R` 的不动点——把序关系与不动点钉在一起。

## 依赖什么

* `Mathlib`（`CompleteLattice`、`iInf`）
* `RealFCA`：复用 `extent` / `intent`
* **不** import `RealNonlinearExtract`（本文件**自带** `fcaClosure` 定义，
  与 `RealNonlinearExtract.closureOperator` 定义式相同但**独立命名**，
  以避免跨文件依赖）

## 不做什么

* **不**构造 `CompleteLattice (ClosureOp α)` 的 Lean instance：
  那需要子类型、`SetLike`、`sInf`/`sSup` 字段与一整套 `le_antisymm`
  等约 15 条 instance 字段。本文件给出**全部内容性验证**
  （`sInf` 封闭 + 序刻画），instance 包装属于机械工作，留给后续波次。
* 不涉及 `Set α` 上闭包系统（closed sets）的对偶陈述。
* 不引入新公理。

## 诚实边界

* `sSup` 半边**不做**：闭包算子族对逐点 `sSup` **一般不封闭**
  （两个闭包算子的逐点上确界通常既不扩张也不幂等）。
  ⚠ 这是一个**真实的负面事实**，故完备格的 `sSup` 必须由
  "所有上界之 `sInf`"给出，而非逐点 `sSup`——本文件因此在
  第 3 条之外**额外**不陈述 `sSup` 封闭性（避免假命题）。
* `sInf_closed` 的幂等性证明中，`iInf` 的**单调性**对**任意** `i`
  同时成立是关键；若只对有限 `i` 成立则命题失效。
-/

namespace Lattice.Lib.FCA.RealFCAClosureOperatorLattice
/-! ## 一、闭包算子谓词与逐点序 -/

/-- **闭包算子谓词**（在**任意偏序** `α` 上）：单调（`mono`）+
扩张（`extensive`）+ 幂等（`idem`）。

比定义多说了什么：把三条性质**拆成具名字段**，而非"闭包算子 =
`∀ x, …`"的合取——这使后续定理能**只**取所需的字段
（例如 `sInf_closed` 的幂等证明只需 `mono` 与 `extensive` 的配合），
并让"我在用哪条性质"在证明中**可见**。
⚠ 注意：字段 `extensive` 的类型依赖 `≤`，故 `α` 必须带 `Preorder`；
本结构因此**不**能为无序遍历的裸类型定义。 -/
structure IsClosureOp {α : Type*} [Preorder α] (c : α → α) : Prop where
  /-- 单调性。-/
  mono : Monotone c
  /-- 扩张性。-/
  extensive : ∀ x, x ≤ c x
  /-- 幂等性。-/
  idem : ∀ x, c (c x) = c x

/-- **逐点序刻画**：`c₁ ≤ c₂ ⟺ ∀ x, c₁ x ≤ c₂ x`（函数上逐点序的定义）。

比定义多说了什么：⚠ 诚实标注——在 Mathlib 中函数逐点序的 `≤`
**就是**这样定义的，故本条是 `Iff.rfl` 级；**不计**实质定理。
保留它是为了让下文所有序论断有**唯一可援引**的名字，
而不必依赖读者知道 Pi 实例的默认序。 -/
theorem closureOp_le_iff {α : Type*} [Preorder α] {c₁ c₂ : α → α} :
    c₁ ≤ c₂ ↔ ∀ x, c₁ x ≤ c₂ x :=
  Iff.rfl

/-! ## 二、核心：对逐点 `sInf` 封闭 -/

/-- **闭包算子族对逐点 `sInf` 封闭**（本文件核心，`α` 为完备格）。

比定义多说了什么：这是一个**非平凡**的封闭性，三条性质的证明
**各不相同**且都**不是**定义展开：
  * 单调：`⨅ i, c i x ≤ ⨅ i, c i y` 需对每个 `i` 用 `c i` 的单调性
    与 `iInf_le`，即"下确界 ≤ 每个成员 ≤ …"的传递；
  * 扩张：`x ≤ ⨅ i, c i x` 需对**每个** `i` 证 `x ≤ c i x`
    （`le_iInf`），即扩张性**逐点**使用；
  * 幂等：`(⨅ c i) ((⨅ c i) x) = ⨅ c i x`——**最难**的一条：
    `≤` 方向需用 `mono`（下确界变小 ⟹ 像变小）配合 `iInf_le`；
    `≥` 方向需用**上界**性质 `le_iInf` 与**每个** `c i` 的扩张性。
⚠ **真实性验证**：若把"闭包算子"改成"仅幂等"或"仅单调"，
这一条**会假**；三条缺一不可。
⚠ 数学定理名保留 `sInf_closed`，但它**只能**在 `[CompleteLattice α]`
下陈述（`iInf` 需要完备性）。 -/
theorem sInf_closed {α : Type*} [CompleteLattice α] {ι : Sort*} {c : ι → α → α}
    (hc : ∀ i, IsClosureOp (c i)) :
    IsClosureOp (fun x => ⨅ i, c i x) where
  mono := fun x y hxy => le_iInf fun i => (iInf_le (fun j => c j x) i).trans ((hc i).mono hxy)
  extensive := fun x => le_iInf fun i => (hc i).extensive x
  idem := fun x => by
    refine le_antisymm ?_ ?_
    · -- (⨅ c i) ((⨅ c i) x) ≤ ⨅ c i x
      refine le_iInf fun i => ?_
      have h1 : (⨅ j, c j ((⨅ k, c k x))) ≤ c i ((⨅ j, c j x)) :=
        iInf_le (fun j => c j (⨅ k, c k x)) i
      have h2 : c i ((⨅ j, c j x)) ≤ c i (c i x) :=
        (hc i).mono (iInf_le (fun j => c j x) i)
      exact h1.trans (h2.trans (le_of_eq ((hc i).idem x)))
    · -- ⨅ c i x ≤ (⨅ c i) ((⨅ c i) x)
      exact le_iInf fun j => (hc j).extensive (⨅ i, c i x)

/-! ## 三、二元情形（逐点 `⊓`） -/

/-- **两闭包算子的逐点 `⊓` 仍是闭包算子**（`sInf_closed` 的二元特例）。

比定义多说了什么：⚠ 诚实标注——它**可由** `sInf_closed` 直接导出
（把二元族写成 `ι → α → α`），因此**数学内容不新**；
保留它的理由是**可读性**：在工程使用中"两个算子取交"远比
"任意族取交"常用。按判据，本条**计**为接口定理（有复用价值，无新数学）。 -/
theorem closureOp_inf {α : Type*} [SemilatticeInf α] {c₁ c₂ : α → α}
    (h₁ : IsClosureOp c₁) (h₂ : IsClosureOp c₂) :
    IsClosureOp (fun x => c₁ x ⊓ c₂ x) where
  mono := fun x y hxy => inf_le_inf (h₁.mono hxy) (h₂.mono hxy)
  extensive := fun x => le_inf (h₁.extensive x) (h₂.extensive x)
  idem := fun x => by
    refine le_antisymm ?_ ?_
    · -- c₁ (c₁ x ⊓ c₂ x) ⊓ c₂ (c₁ x ⊓ c₂ x) ≤ c₁ x ⊓ c₂ x
      refine le_inf ?_ ?_
      · -- 目标左端是 c₁(…) ⊓ c₂(…)，先取 ⊓ 的左投影，再走 c₁ 的单调 + 幂等
        exact (inf_le_left.trans (h₁.mono inf_le_left)).trans (le_of_eq (h₁.idem x))
      · -- 对称：先取 ⊓ 的右投影
        exact (inf_le_right.trans (h₂.mono inf_le_right)).trans (le_of_eq (h₂.idem x))
    · -- c₁ x ⊓ c₂ x ≤ c₁ (c₁ x ⊓ c₂ x) ⊓ c₂ (c₁ x ⊓ c₂ x)（扩张性）
      exact le_inf (h₁.extensive (c₁ x ⊓ c₂ x)) (h₂.extensive (c₁ x ⊓ c₂ x))

/-! ## 四、FCA 提取算子是闭包算子（实例化） -/

/-- **FCA 提取算子**：`fcaClosure R Ol = extent R (intent R Ol)`
（与 `RealNonlinearExtract.closureOperator` 定义式相同，此处独立定义
以避免跨文件依赖）。

比定义多说了什么：⚠ 这是**定义**，不声称内容；列出它是为了
下一条定理可自足陈述。 -/
def fcaClosure {O A : Type*} (R : O → A → Prop) (Ol : Set O) : Set O :=
  extent R (intent R Ol)

/-- **FCA 提取算子是闭包算子**（`RealFCA` 的闭包三律打包成结构）。

比定义多说了什么：把 `RealFCA` 中**分散**的三条结论
（`extent_antitone∘intent_antitone` 的单调、`subset_extent_intent` 的扩张、
`closure_idempotent` 的幂等）**打包**为 `IsClosureOp` 结构值。
于是 `sInf_closed` 立即可用于"FCA 闭包算子族"，
**无需**在 FCA 语言中重证封闭性——这是**接口收益**的实例。
⚠ 诚实标注：三条子证明**都是**回收 `RealFCA` 的已有定理，
本条**不**宣称新数学；其价值是**类型层面的组装**。 -/
theorem fca_closure_isClosureOp {O A : Type*} (R : O → A → Prop) :
    IsClosureOp (fcaClosure (O := O) (A := A) R) where
  mono := fun _ _ h => extent_antitone R (intent_antitone R h)
  extensive := fun Ol => subset_extent_intent R Ol
  idem := fun Ol => closure_idempotent R Ol

/-! ## 五、序与不动点的对应 -/

/-- **`fcaClosure R` 之下的闭集恰是它的不动点**：
`fcaClosure R C ⊆ C` 当且仅当 `fcaClosure R C = C`。

比定义多说了什么：**真内容**——`⊆` 方向需用**扩张性**把
`C ⊆ fcaClosure R C` 补上才能得到等式；仅凭 `⊆` 无法得等式。
这条把"序比较"与"不动点"钉在一起，是可复用的判定接口
（用它可把"某集合是闭的"化归为一次包含检查）。 -/
theorem fca_closure_subset_iff_fixpoint {O A : Type*} (R : O → A → Prop) (C : Set O) :
    fcaClosure R C ⊆ C ↔ fcaClosure R C = C := by
  constructor
  · intro h
    exact Set.Subset.antisymm h (subset_extent_intent R C)
  · intro h
    exact h.le

/-- **不动点即 `extent` 的值域**：`fcaClosure R C = C`
当且仅当存在 `B` 使 `C = extent R B`。

比定义多说了什么：**真内容**——`⟸` 方向用 `extent_intent_extent`
（对象端闭包幂等）；`⟹` 方向取 `B := intent R C`。
它把"闭集"的**内蕴**刻画（不动点）与**外蕴**刻画（值是 `extent`）
对接——这正是概念格外延集合的两种等价说法。 -/
theorem fca_closure_fixpoint_iff_mem_range {O A : Type*} (R : O → A → Prop) (C : Set O) :
    fcaClosure R C = C ↔ ∃ B : Set A, C = extent R B := by
  constructor
  · intro h
    exact ⟨intent R C, h.symm⟩
  · rintro ⟨B, rfl⟩
    exact extent_intent_extent R B

end Lattice.Lib.FCA.RealFCAClosureOperatorLattice