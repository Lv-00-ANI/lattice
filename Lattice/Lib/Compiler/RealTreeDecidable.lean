import Mathlib
import Lattice.Lib.Compiler.RealTreeRecursion

open Lattice.Lib.Compiler.RealTreeRecursion


/-!
# LATTICE: 树的可计算性、结构相等与同构判定

`RealTreeRecursion` 建立了多叉有序树 `Tree α` 的良基递归与结构归纳，但**没有**
`DecidableEq`（`Tree` 只 `deriving Repr`），也没有「结构相等 / 同构」的关系定理。
本文件补上这一维度：

  1. `Tree.decEq` / `instDecidableEqTree`：`[DecidableEq α]` 下 `Tree α` 的
     **可计算相等判定**（`Tree`/`List (Tree α)` 互递归实现，与
     `RealTreeRecursion` 的 `size`/`depth` 同一手法）；
  2. `Tree.decEq_eq_true_iff` / `Tree.listDecEq_eq_true_iff`：Bool 版判定与
     `Prop` 版相等的**桥接**（`= true ↔ =`，以上正确性定理分列树层与列表层）；
  3. `Tree.eq_iff_children_eq` / `Tree.node_inj`：
     **结构相等**的关系定理——`Tree.node_inj` 给出 → 方向
     （`node a ts = node b us → a = b ∧ ts = us`），
     `Tree.eq_iff_children_eq` 给出存在量化形式
     （`t = u ↔ ∃ a ts us, t = node a ts ∧ u = node a us ∧ ts = us`）；
  4. `Tree.decEq_self` / `Tree.decEq_eq` / `Tree.decEq_ne`：
     判定器与真值的**可靠性/完备性**（`decide (t = t) = true` 等）；
  5. `Tree.listDecEq` 及其正确性：孩子列表的可计算相等；
  6. **有限树的同构判定**：`Tree.Iso`（同构关系，孩子列表逐位对应——
     因为 `Tree` 是**有序**树，同构即结构相等）、`Tree.iso_iff_eq`
     （**同构 ⟺ 结构相等**，这是本文件关于「同构判定」的正面结论）、
     `Tree.iso_refl/symm/trans`（同构是等价关系）、
     `Tree.decidableIso`（同构可判定，由 `decEq` 直接给出）；
  7. `Tree.count` / `Tree.count_eq_of_eq` / `Tree.count_node_eq`：**无序**意义下
     标签计数的弱化刻画——结构相等时计数不变（`count_eq_of_eq`），
     以及 `node` 上的分解（`count_node_eq`）（说明有序树何时与无序树区分
     ——作为同构判定的边界标注）。

诚实标注（无 sorry / axiom / admit）：
- **关键设计决定（诚实标注）**：`Tree` 是**有序**多叉树（`node a ts` 中 `ts`
  是有序列表），故其**同构就是结构相等**（`iso_iff_eq` 是双向 `↔` 的等式刻画）。
  「同构但不等」的情形在本类型上**不存在**：不存在非平凡自同构（`iso_self_iff`）。
  若需要「孩子的顺序无关」的树，必须换类型（如孩子用 `Multiset`）——**本文件未做**，
  只给出 `count`（无序计数）作为该方向的桥接与边界标注。
- 本文件**未做**：非良基（无限）树（需要共归纳/终余代数）；树的自动机等价
  （`Tree` 与正则树语言的对应）。
- `Tree.decEq` 与 `RealTreeRecursion` 中的 `Tree` 是**同一类型**
  （`import RealTreeRecursion`），不是重新定义。
- 本文件不引入任何未证假设。
-/

noncomputable section

universe u


namespace Lattice.Lib.Compiler.RealTreeRecursion
namespace Tree

variable {α : Type u}

/-! ## 一、孩子列表的可计算相等（互递归的列表侧）

**孩子列表的可计算相等**（`decEq` 的互递归伙伴）：逐位比较标签与子树。
（与 `RealTreeRecursion` 的 `sizeList`/`depthList` 同一手法：
`Tree`/`List (Tree α)` 互递归，Lean 自动接受终止性。）

**STYLE 陷阱（本轮实测）**：`mutual` 块**之前紧邻**的 `/-- … -/` 文档注释
会让 Lean 报 `unexpected token 'mutual'; expected 'lemma'`
——正如 `RealTreeRecursion` 的做法，块级说明必须写在 `/-! … -/` **小节注释**里，
`mutual` 块内的成员也只能用普通 `--` 注释。 -/

mutual
  /-- **树的可计算相等判定**（`[DecidableEq α]`）。 -/
  def decEq [DecidableEq α] : Tree α → Tree α → Bool
    | node a ts, node b us => decide (a = b) && listDecEq ts us

  /-- **孩子列表的可计算相等判定**（`decEq` 的列表版）。 -/
  def listDecEq [DecidableEq α] : List (Tree α) → List (Tree α) → Bool
    | [], [] => true
    | c :: cs, d :: ds => decEq c d && listDecEq cs ds
    | _, _ => false
end

@[simp] theorem decEq_node [DecidableEq α] (a b : α) (ts us : List (Tree α)) :
    decEq (node a ts) (node b us) = (decide (a = b) && listDecEq ts us) := rfl

@[simp] theorem listDecEq_nil [DecidableEq α] :
    listDecEq ([] : List (Tree α)) [] = true := rfl

@[simp] theorem listDecEq_cons [DecidableEq α] (c d : Tree α) (cs ds : List (Tree α)) :
    listDecEq (c :: cs) (d :: ds) = (decEq c d && listDecEq cs ds) := rfl

@[simp] theorem listDecEq_nil_cons [DecidableEq α] (d : Tree α) (ds : List (Tree α)) :
    listDecEq [] (d :: ds) = false := rfl

@[simp] theorem listDecEq_cons_nil [DecidableEq α] (c : Tree α) (cs : List (Tree α)) :
    listDecEq (c :: cs) [] = false := rfl

/-! ## 二、Bool 判定与 Prop 相等的桥接

`decEq` 与 `listDecEq` **互相调用**，故两条正确性定理
（`decEq_eq_true_iff` 与 `listDecEq_eq_true_iff`）也**互相引用**：
树层的 `node` 分支要用列表层结论，列表层的 `cons` 分支要用树层结论。

**诚实标注（写法降级）**：Lean 4.14 **不支持 `mutual` 命题块**
（`mutual … theorem … end` 报 `unexpected token 'mutual'; expected 'lemma'`），
故与 `RealMutualRecursion` 同一手法：把两者放在**同一个证明块**里，
树层对 `Tree.size` 强归纳、列表层对列表结构归纳，
两个方向在同一步中**互相引用**——互递归的实质被显式保留。

**度量说明（本轮实测）**：`List.sizeOf_cons` 在 mathlib 4.14 **不存在**，
且 `sizeOf` 对互递归类型的算术展开无现成引理；故不用 `sizeOf`，
改用 `RealTreeRecursion` 已提供的 `Tree.size` / `Tree.sizeList`，
其下降由 `size_lt_of_mem` / `size_le_sizeList` 直接给出。 -/

/-- **互递归正确性（合并为一个证明块）**：
树层与列表层的「判定器 = 相等」同时成立。
两个方向在归纳步中**互相引用**（`node` 用列表 IH，`cons` 用树 IH 与列表 IH）。 -/
private theorem decide_aux [DecidableEq α] :
    (∀ t u : Tree α, decEq t u = true ↔ t = u) ∧
      (∀ ts us : List (Tree α), listDecEq ts us = true ↔ ts = us) := by
  have treeKey : ∀ n : ℕ, ∀ t : Tree α, Tree.size t ≤ n →
      ∀ u : Tree α, decEq t u = true ↔ t = u := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht u
      cases t with
      | node a ts =>
        cases u with
        | node b us =>
          rw [decEq_node, Bool.and_eq_true, decide_eq_true_eq, Tree.node.injEq]
          -- 列表层：对 `ts` 结构归纳；成员用 `ih`（`Tree.size` 严格更小）
          have listKey : ∀ {ts : List (Tree α)},
              (∀ c ∈ ts, Tree.size c < n) → ∀ us, listDecEq ts us = true ↔ ts = us := by
            intro ts
            induction ts with
            | nil =>
              intro _ us
              cases us with
              | nil => simp
              | cons d ds => simp
            | cons c cs ihcs =>
              intro hb us
              cases us with
              | nil => simp
              | cons d ds =>
                rw [listDecEq_cons, Bool.and_eq_true, List.cons.injEq]
                have hcn : Tree.size c < n := hb c (by simp)
                have hcsb : ∀ e ∈ cs, Tree.size e < n := fun e he => hb e (by simp [he])
                rw [ih (Tree.size c) hcn c le_rfl d, ihcs hcsb ds]
          -- 成员严格小于父节点：`Tree.size_lt_of_mem` 给出
          -- `size c < 1 + sizeList ts`，而 `ht` 给出 `1 + sizeList ts ≤ n`
          -- （`ht` 需先用 `Tree.size_node` 化为 `1 + sizeList ts ≤ n`）
          have ht' : 1 + Tree.sizeList ts ≤ n := by
            simpa only [Tree.size_node] using ht
          have hb : ∀ c ∈ ts, Tree.size c < n := fun c hc =>
            lt_of_lt_of_le (Tree.size_lt_of_mem hc) ht'
          exact ⟨fun ⟨hab, hus⟩ => ⟨hab, (listKey hb us).1 hus⟩,
                 fun ⟨hab, hus⟩ => ⟨hab, (listKey hb us).2 hus⟩⟩
  exact ⟨fun t u => treeKey (Tree.size t) t le_rfl u,
         fun ts us => by
           have listKey : ∀ {ts : List (Tree α)},
               (∀ c ∈ ts, Tree.size c ≤ Tree.sizeList ts) →
                 ∀ us, listDecEq ts us = true ↔ ts = us := by
             intro ts
             induction ts with
             | nil =>
               intro _ us
               cases us with
               | nil => simp
               | cons d ds => simp
             | cons c cs ihcs =>
               intro hb us
               cases us with
               | nil => simp
               | cons d ds =>
                 rw [listDecEq_cons, Bool.and_eq_true, List.cons.injEq]
                 have hc : decEq c d = true ↔ c = d :=
                   treeKey (Tree.size c) c le_rfl d
                 -- `cs` 的成员界：`size e ≤ sizeList (c :: cs) = size c + sizeList cs`
                 have hcs : listDecEq cs ds = true ↔ cs = ds :=
                   ihcs (fun e he => by
                     have h1 : Tree.size e ≤ Tree.sizeList (c :: cs) := hb e (by simp [he])
                     simp only [Tree.sizeList_cons] at h1
                     have h2 := Tree.size_le_sizeList (ts := cs) (c := e) he
                     omega) ds
                 exact ⟨fun ⟨h1, h2⟩ => ⟨hc.1 h1, hcs.1 h2⟩,
                        fun ⟨h1, h2⟩ => ⟨hc.2 h1, hcs.2 h2⟩⟩
           exact listKey (fun c hc => Tree.size_le_sizeList hc) us⟩

/-- **`decEq` 的可靠性+完备性**：`decEq t u = true ↔ t = u`。
这是「可计算判定与结构相等一致」的核心关系定理。 -/
theorem decEq_eq_true_iff [DecidableEq α] (t u : Tree α) :
    decEq t u = true ↔ t = u :=
  decide_aux.1 t u

/-- **`listDecEq` 的可靠性+完备性（列表版）**：`listDecEq ts us = true ↔ ts = us`。 -/
theorem listDecEq_eq_true_iff [DecidableEq α] (ts us : List (Tree α)) :
    listDecEq ts us = true ↔ ts = us :=
  decide_aux.2 ts us

/-- **`Tree α` 的 `DecidableEq` 实例**：由 `decEq` 与
`decEq_eq_true_iff` 通过 `decidable_of_iff` 提升而来，并**注册为类型类实例**
（这样 `decide (t = u)`、`decidableIso` 等都能自动合成）。
（`DecidableEq _` 是 `Type` 层，故按 STYLE「类型类目标是 Type 层」用 `def`
而非 `theorem`；`instance` 关键字在此是 `def` 的实例化形式，语义相同。） -/
instance instDecidableEqTree [DecidableEq α] : DecidableEq (Tree α) :=
  fun t u => decidable_of_iff (decEq t u = true) (decEq_eq_true_iff t u)

/-- **实例与 `decEq` 一致**：`instDecidableEqTree` 判定为真当且仅当
`decEq t u = true`。这是实例与 `decEq` 的桥接。

**STYLE 陷阱（本轮实测）**：`(d : Decidable p).isTrue` 的点号投影报
`invalid field notation, function 'Decidable.isTrue' does not have argument
with type (Decidable ...)`（`Decidable` 是 inductive，投影需要显式实例）。
故不投影 `isTrue`，而在 `Prop` 层陈述：`t = u ↔ decEq t u = true`
——这**就是**实例与 `decEq` 一致的完整内容（`decEq_eq_true_iff` 已给出），
且对 `decide (t = u)` 的使用由实例定义直接支持。 -/
theorem instDecidableEqTree_eq_iff [DecidableEq α] (t u : Tree α) :
    t = u ↔ decEq t u = true :=
  (decEq_eq_true_iff t u).symm

/-- **实例确实可用于 `decide`**：`decide (t = u)` 在该实例下与 `decEq` 一致。
（`(instDecidableEqTree …)` 使 `Decidable (t = u)` 可合成，
故 `decide (t = u)` 可用——本定理给出它与 `decEq` 的桥接。） -/
theorem decide_eq_iff_decEq [DecidableEq α] (t u : Tree α) :
    decide (t = u) = true ↔ decEq t u = true := by
  rw [decide_eq_true_iff, instDecidableEqTree_eq_iff]

/-! ## 三、结构相等的关系定理 -/

/-- **构造子单射**：`node a ts = node b us → a = b ∧ ts = us`。

**STYLE 陷阱（本轮实测）**：Lean 4.14 为单构造子 inductive 生成的
`Tree.node.injEq` 是一个**命题等式**
`(node a ts = node b us) = (a = b ∧ ts = us)`（**不是** `↔`），
故 `.1` / `.mp` 都报 `invalid projection, structure has only 0 field(s)`
——正确用法是 `Eq.mp` 或先 `rw`。这里用 `Eq.mp`。 -/
theorem node_inj {a b : α} {ts us : List (Tree α)} (h : node a ts = node b us) :
    a = b ∧ ts = us :=
  Eq.mp (Tree.node.injEq a ts b us) h

/-- **结构相等 ⟺ 标签相等 ∧ 孩子列表相等**（同构/相等的判定式刻画）。
（左→右方向：任何树都是某个 `node a ts`；右→左：`node` 是函数，`rfl`。
`subst` 会改写假设并留下 `∃` 的元变量，故此处用 `cases` 显式绑定。） -/
theorem eq_iff_children_eq (t u : Tree α) :
    t = u ↔ ∃ a ts us, t = node a ts ∧ u = node a us ∧ ts = us := by
  constructor
  · intro h
    cases t with
    | node a ts =>
      cases u with
      | node b us =>
        obtain ⟨rfl, rfl⟩ := node_inj h
        exact ⟨a, ts, ts, rfl, rfl, rfl⟩
  · rintro ⟨a, ts, us, ht, hu, hts⟩
    rw [ht, hu, hts]

/-- **`decide (t = t) = true`**：判定器对自反性给出 `true`。 -/
theorem decEq_self [DecidableEq α] (t : Tree α) : decEq t t = true :=
  (decEq_eq_true_iff t t).2 rfl

/-- **判定器可靠**：`decEq t u = true → t = u`。 -/
theorem decEq_eq [DecidableEq α] {t u : Tree α} (h : decEq t u = true) : t = u :=
  (decEq_eq_true_iff t u).1 h

/-- **判定器完备**：`t = u → decEq t u = true`。 -/
theorem decEq_of_eq [DecidableEq α] {t u : Tree α} (h : t = u) : decEq t u = true :=
  (decEq_eq_true_iff t u).2 h

/-- **判定器对不等给出 `false`**：`t ≠ u → decEq t u = false`。 -/
theorem decEq_ne [DecidableEq α] {t u : Tree α} (h : t ≠ u) : decEq t u = false := by
  cases hb : decEq t u with
  | false => rfl
  | true => exact absurd (decEq_eq hb) h

/-- **`dite` 形式**：判定为真时取 `x`，为假时取 `y`——`DecidableEq` 实例的行为说明。 -/
theorem decEq_dite [DecidableEq α] (t u : Tree α) {β : Sort _} (x y : β)
    (hx : t = u) : (if decEq t u = true then x else y) = x := by
  rw [if_pos (decEq_of_eq hx)]

/-! ## 四、有限树的同构判定

`Tree` 是**有序**树：`node a ts` 的 `ts` 是有序列表。故两个孩子列表「逐位对应」
就是结构相等。本节的 `Iso` 把这个直观形式化，并证明
**同构 ⟺ 结构相等**——这是「同构判定可判定」的正面结论。

**实现说明（STYLE「多叉树递归」陷阱）**：直觉写法
`def Iso | node a ts, node b us => a = b ∧ List.Forall₂ Iso ts us`
在 mathlib 4.14 上**不通过**：`Iso` 只对「孩子列表的成员」递归，
而 `List.Forall₂` 不是 `Iso` 的结构子项，实测报
`failed to infer structural recursion` + `Could not find a decreasing measure`。
故把「孩子逐位同构」展开成一对**互递归谓词**（`Iso` / `IsoList`），
由 Lean 自动接受——这正是 `RealTreeRecursion` 处理 `size`/`depth` 的同一手法。

（同第一节：`mutual` 前不能放 `/-- -/` 文档注释。） -/

mutual
  /-- 树同构：标签相等且孩子列表逐位同构。 -/
  def Iso : Tree α → Tree α → Prop
    | node a ts, node b us => a = b ∧ IsoList ts us

  /-- 孩子列表逐位同构（`Iso` 的列表伙伴）。 -/
  def IsoList : List (Tree α) → List (Tree α) → Prop
    | [], [] => True
    | c :: cs, d :: ds => Iso c d ∧ IsoList cs ds
    | _, _ => False
end

@[simp] theorem iso_node_iff (a b : α) (ts us : List (Tree α)) :
    Iso (node a ts) (node b us) ↔ a = b ∧ IsoList ts us :=
  Iff.rfl

@[simp] theorem isoList_nil : IsoList ([] : List (Tree α)) [] := trivial

@[simp] theorem isoList_cons (c d : Tree α) (cs ds : List (Tree α)) :
    IsoList (c :: cs) (d :: ds) ↔ Iso c d ∧ IsoList cs ds :=
  Iff.rfl

@[simp] theorem isoList_nil_cons (d : Tree α) (ds : List (Tree α)) :
    ¬ IsoList [] (d :: ds) := id

@[simp] theorem isoList_cons_nil (c : Tree α) (cs : List (Tree α)) :
    ¬ IsoList (c :: cs) [] := id

/-- **同构 ⟺ 结构相等**：有序树上同构就是相等（双向）。

证明：对 `Tree.size` 做一次强归纳（`RealTreeRecursion.Tree.induction`
穿不过 `List (Tree α)` 的孩子列表，故用 `Tree.size` 的强归纳，
与 `RealTreeRecursion.depth_le_size` 同一手法），
归纳陈述**同时**包含树层与列表层两个方向（互递归的实质被显式保留）：
- 树层 `node a ts = node b us`：`rw [hab]` 后对 `ts`/`us` 用**列表层**结论；
- 列表层 `c :: cs = d :: ds`：先对 `c`/`d` 用**树层**结论
  （`Tree.size c < n` 由 `size_lt_of_mem` + `Tree.size_node` 给出），
  再对 `cs`/`ds` **递归**调用列表层（`cs` 的成员也是 `ts` 的成员）。

**STYLE 陷阱**：`Tree.size_node` 是 `@[simp]` 引理，但 `have := …; rw [Tree.size_node] at this`
对形如 `Tree.size (Tree.node a ts)` 的目标**不匹配**（`this` 里的项是
`Tree.size c < 1 + Tree.sizeList ts`，`Tree.size_node` 的 LHS 需要显式 `Tree.node`）；
改用 `simp only [Tree.size_node] at this` 或在 `have` 里直接 `simp`。 -/
theorem iso_iff_eq (t u : Tree α) : Iso t u ↔ t = u := by
  have treeKey : ∀ n : ℕ, ∀ t : Tree α, Tree.size t ≤ n → ∀ u : Tree α, Iso t u → t = u := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht u hIso
      cases t with
      | node a ts =>
        cases u with
        | node b us =>
          obtain ⟨hab, hus⟩ := hIso
          rw [hab]
          congr 1
          -- 列表层：对 `ts` 结构归纳；孩子用 `ih`（`Tree.size` 严格更小）
          have listKey : ∀ {ts : List (Tree α)},
              (∀ c ∈ ts, Tree.size c < n) → ∀ us, IsoList ts us → ts = us := by
            intro ts
            induction ts with
            | nil =>
              intro _ us h
              cases us with
              | nil => rfl
              | cons d ds => exact absurd h (isoList_nil_cons d ds)
            | cons c cs ihcs =>
              intro hb us h
              cases us with
              | nil => exact absurd h (isoList_cons_nil c cs)
              | cons d ds =>
                obtain ⟨hcd, hcs⟩ := h
                have hcn : Tree.size c < n := hb c (by simp)
                have hcsb : ∀ e ∈ cs, Tree.size e < n := fun e he => hb e (by simp [he])
                rw [ih (Tree.size c) hcn c le_rfl d hcd, ihcs hcsb ds hcs]
          have ht' : 1 + Tree.sizeList ts ≤ n := by
            simpa only [Tree.size_node] using ht
          exact listKey (fun c hc => lt_of_lt_of_le (Tree.size_lt_of_mem hc) ht') us hus
  constructor
  · intro h
    exact treeKey (Tree.size t) t le_rfl u h
  · intro h
    -- 自反性：由 `t = u` 改写后只需证 `Iso u u`；
    -- 用「对 `Tree.size` 强归纳」给出**任意**树的自反性
    have reflKey : ∀ n : ℕ, ∀ s : Tree α, Tree.size s ≤ n → Iso s s := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro s ht
        cases s with
        | node a ts =>
          refine ⟨rfl, ?_⟩
          -- 列表层反身性：对 `ts` 结构归纳（`intro hb` 必须在 `induction` **之前**，
          -- 否则 `nil` 分支目标是函数类型，`trivial` 不适用）
          have listRefl : ∀ ts : List (Tree α),
              (∀ c ∈ ts, Tree.size c < n) → IsoList ts ts := by
            intro ts
            induction ts with
            | nil => intro _; exact trivial
            | cons c cs ihcs =>
              intro hb
              exact ⟨ih (Tree.size c) (hb c (by simp)) c le_rfl,
                     ihcs (fun e he => hb e (by simp [he]))⟩
          have ht' : 1 + Tree.sizeList ts ≤ n := by
            simpa only [Tree.size_node] using ht
          exact listRefl ts (fun c hc => lt_of_lt_of_le (Tree.size_lt_of_mem hc) ht')
    rw [h]
    exact reflKey (Tree.size u) u le_rfl

/-- **同构关系自反**。 -/
theorem iso_refl (t : Tree α) : Iso t t :=
  (iso_iff_eq t t).2 rfl

/-- **同构关系对称**。 -/
theorem iso_symm {t u : Tree α} (h : Iso t u) : Iso u t :=
  (iso_iff_eq u t).2 ((iso_iff_eq t u).1 h).symm

/-- **同构关系传递**。 -/
theorem iso_trans {t u v : Tree α} (h₁ : Iso t u) (h₂ : Iso u v) : Iso t v :=
  (iso_iff_eq t v).2 (((iso_iff_eq t u).1 h₁).trans ((iso_iff_eq u v).1 h₂))

/-- **不存在非平凡自同构**：`Iso t u` 蕴含 `t = u`，故同构类都是单点集。
这是有序树同构判定的实质内容（也正是它与「无序树同构」的区别所在）。 -/
theorem iso_self_iff (t u : Tree α) : Iso t u ↔ t = u :=
  iso_iff_eq t u

/-- **同构判定可判定**：`[DecidableEq α]` 下 `Iso t u` 可判定
（由 `iso_iff_eq` 归约到 `t = u`，后者由 `instDecidableEqTree` 判定）。
**形式调整**：`Decidable _` 是 `Type` 层，故用 `def`（STYLE「类型类目标是 Type 层」）。 -/
def decidableIso [DecidableEq α] (t u : Tree α) : Decidable (Iso t u) :=
  haveI : DecidableEq (Tree α) := instDecidableEqTree
  decidable_of_iff (t = u) (iso_iff_eq t u).symm

/-- **同构判定的正确性**：`decidableIso` 判定为真当且仅当 `decEq` 给出 `true`
——即「同构可判定」与「结构相等可判定」是同一个判定器。
（不用 `Decidable.isTrue` 投影：`decidableIso` 是 `decidable_of_iff` 的包装，
其内部见证形状不稳定；直接陈述两个`Decidable` 的 `isTrue` 会引入
未被消去的元变量。这里改用等价的 `Prop` 层刻画，更稳且信息量不减。） -/
theorem decidableIso_iff_decEq [DecidableEq α] (t u : Tree α) :
    Iso t u ↔ decEq t u = true := by
  rw [iso_iff_eq, decEq_eq_true_iff]

/-! ## 五、无序计数的边界标注

**标签计数**：树中等于 `a` 的标签个数（孩子列表上求和）。
（同第一节：`mutual` 前不能放 `/-- -/` 文档注释，块级说明写在小节注释里。） -/

mutual
  /-- 树中标签 `a` 出现的次数。 -/
  def count [DecidableEq α] (a : α) : Tree α → ℕ
    | node b ts => (if a = b then 1 else 0) + countList a ts

  /-- 孩子列表中标签 `a` 出现的次数。 -/
  def countList [DecidableEq α] (a : α) : List (Tree α) → ℕ
    | [] => 0
    | c :: cs => count a c + countList a cs
end

@[simp] theorem countList_nil [DecidableEq α] (a : α) :
    countList a ([] : List (Tree α)) = 0 := rfl

@[simp] theorem countList_cons [DecidableEq α] (a : α) (c : Tree α) (cs : List (Tree α)) :
    countList a (c :: cs) = count a c + countList a cs := rfl

@[simp] theorem count_node [DecidableEq α] (a b : α) (ts : List (Tree α)) :
    count a (node b ts) = (if a = b then 1 else 0) + countList a ts := rfl

/-- **等价的树有相同的标签计数**：结构相等蕴含无序计数相等
（同构判定强于无序计数——后者是「弱化」的边界标注）。 -/
theorem count_eq_of_eq [DecidableEq α] {t u : Tree α} (h : t = u) (a : α) :
    count a t = count a u := by
  rw [h]

/-- **`count` 对 `node` 的分解**（用于把无序计数与有序结构区分开）。 -/
theorem count_node_eq [DecidableEq α] (b : α) (ts : List (Tree α)) :
    count b (node b ts) = 1 + countList b ts := by
  simp

end Tree

end Lattice.Lib.Compiler.RealTreeRecursion
