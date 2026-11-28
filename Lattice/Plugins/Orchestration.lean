/-
# `Orchestration` —— 插件状态机（`PLUGIN-SYSTEM.md` §9.9 / Q7 的最小形式化）

**为什么只有状态机，没有排序键与依赖图（第 1199 轮，实测）**

规划 W3-3 要三个组件：`rankKey`（六分量排序键）、`dependencyGraph`（依赖无环）、`PluginState`（状态机）。
本轮先测了树里是否已有部分实现——**四个名字全部 0 次出现**——再读规格，发现：

* **排序键那节的 `rank_key_total : ∀ a b, a.rankKey ≠ b.rankKey` 按字面是**假的****（取 `a = b` 即断言 `k ≠ k`）。
  想说的必然是「序是全序」或「不同插件的键不同」，两者是不同的命题，被压成了一句。
  ⇒ **故不照抄**：照抄就只剩「把它改成恒真变体」这一种过法，而那正是本会话一直在治的病。
* **依赖图**那节同样有待核的表述（「7 条 `requires` 边悬空数当前 6」等），且它要能和 `plugin.yml` 对齐，
  而 `plugin.yml` 的解析目前没有 Lean 侧载体 ⇒ 暂不写。
* **状态机**这一节的**转移表是明确的**，且它的头两条定理 `error_is_terminal`、`no_skip_loaded` **只依赖那张表**
  ⇒ 可以**照规格**实现，不需要猜测规格的意图。

**⇒ 故本轮只做状态机，且只做那两条**——其余三条（`shadowed_retains_dispose`、`active_requires_satisfied`、
`implements_eq_offered`）需要 `dispose`/`satisfies`/`implements` 这些**尚未存在于树里**的概念，写出来会是空壳。
-/

import Mathlib

namespace Lattice.Plugins.Orchestration

/-- **插件在编排中的五个状态**（`PLUGIN-SYSTEM.md` §9.9）。

**⇒ `active` 是唯一「自有槽可被满足」的状态；`shadowed` 是「已登记而未被激活」——**
**⇒ 被遮蔽不等于被丢弃：它仍持有登记与逆。 -/
inductive PluginState where
  /-- 已解析清单，未登记。 -/
  | declared
  /-- 已登记，未激活。 -/
  | loaded
  /-- 是自有槽的胜者。 -/
  | active
  /-- 已登记而未被激活；保留登记。 -/
  | shadowed
  /-- 被拒。**终态。** -/
  | error
  deriving DecidableEq, Repr

/-- **转移关系：**逐行抄自规格的转移表**。

| 源态 | 可迁出到 |
|:--|:--|
| `declared` | `loaded`, `error` |
| `loaded` | `active`, `shadowed`, `error` |
| `active` | `shadowed`, `error` |
| `shadowed` | `active`, `error` |
| `error` | **无（终态）** |

**⇒ 写成归纳关系而不是函数：状态机允许**分叉**，而函数只能给一个后继。 -/
inductive transitions : PluginState → PluginState → Prop where
  | decl_loaded : transitions .declared .loaded
  | decl_error : transitions .declared .error
  | loaded_active : transitions .loaded .active
  | loaded_shadowed : transitions .loaded .shadowed
  | loaded_error : transitions .loaded .error
  | active_shadowed : transitions .active .shadowed
  | active_error : transitions .active .error
  | shadowed_active : transitions .shadowed .active
  | shadowed_error : transitions .shadowed .error

/-- **`error` 是终态**：没有任何状态可以从它迁出。

**⇒ 这是规格 §9.9 的第一条定理，**逐字**实现；它成立的原因是 `transitions` 没有一条以 `error` 为源的构造子。 -/
theorem error_is_terminal : ¬ ∃ s : PluginState, transitions .error s := by
  rintro ⟨s, h⟩
  cases h

/-- **不能跳过 `loaded`**：`declared` 不能直接到 `active`。

**⇒ 规格 §9.9 的第二条。⇒ 它成立的原因是转移表里没有 `declared → active` 这一行；**
**⇒ 故若有人日后「顺手」加一行，这条定理会立刻失败——这正是把它写成定理的意义。 -/
theorem no_skip_loaded : ¬ transitions .declared .active := by
  intro h
  cases h

/-- **终态是可达的**（不是空性质）：`declared → error` 真的存在。

**⇒ 加这一条是因为「`error` 是终态」与「`error` 不可达」是两件事；只有前者被规格要求，**
**⇒ 而若 `error` 根本到不了，那条终态定理就没有内容。⇒ 故显式给出一个到它的迁移。 -/
theorem error_reachable : ∃ s : PluginState, transitions .declared s :=
  ⟨.error, transitions.decl_error⟩

/-! ## 二、排序键（`PLUGIN-SYSTEM.md` §9.6 / Q4）：**修正后的真陈述** -/

/-- **部署层级**。**⇒ 它必须排在作者优先级**之前**；否则低层插件填满优先级就能盖掉高层。 -/
inductive DeployScope where
  | user
  | library
  | mainline
  deriving DecidableEq, Repr

/-- **层级的数值**：大者更高。 -/
def DeployScope.rank : DeployScope → ℕ
  | .user => 0
  | .library => 1
  | .mainline => 2

/-- **`DeployScope.rank` 是单射**：秩相等 ⇒ 层相等。

**⇒ 没有它，「六个分量均等 → 两个键相等」就断在第一个分量上（因为那一个是结构而非 ℕ）。**
**⇒ 而它只需三个构造子的穷举。 -/
theorem DeployScope.rank_injective {x y : DeployScope} (h : x.rank = y.rank) : x = y := by
  cases x <;> cases y <;> simp_all [DeployScope.rank]

/-- **六分量排序键**（§9.6）。

**→ 逐分量方向不同：**层级 / 优先级 / 协议版本**大者胜**；**
**→ 装载序号 / 登记序号 / 插件标识**小者胜**。 -/
structure RankKey where
  scope : DeployScope
  priority : ℕ
  protocol : ℕ
  loadSeq : ℕ
  regSeq : ℕ
  id : ℕ
  deriving DecidableEq, Repr

/-- **「a 胜过 b」**：按六分量字典序，每个分量按自己的方向。

**⇒ 这是**定义**，故下面两条定理是它的直接推论——而正是规范要求的两条。 -/
def Wins (a b : RankKey) : Prop :=
  a.scope.rank > b.scope.rank ∨
    (a.scope.rank = b.scope.rank ∧
      (a.priority > b.priority ∨
        (a.priority = b.priority ∧
          (a.protocol > b.protocol ∨
            (a.protocol = b.protocol ∧
              (a.loadSeq < b.loadSeq ∨
                (a.loadSeq = b.loadSeq ∧
                  (a.regSeq < b.regSeq ∨
                    (a.regSeq = b.regSeq ∧ a.id < b.id)))))))))

/-- **⭐ 部署层级**压倒**作者优先级**。

**⇒ 这是规范§9.6 的第一条守则：只要层级更高，**其余五个分量一概不看**。**
**⇒ 而它在定义下是**透明的**：就是那个析取式的第一个合取项。 -/
theorem scope_dominates_priority {a b : RankKey} (h : a.scope.rank > b.scope.rank) :
    Wins a b :=
  Or.inl h

/-- **⭐ 插件标识**打破完全并列**：标识不同 → 键不同。

**⇒ 故「两个不同插件拿到同一个键」**不可能发生**，而那正是排序键存在的理由。 -/
theorem rank_key_distinct_of_id {a b : RankKey} (h : a.id ≠ b.id) : a ≠ b :=
  fun hab => h (congrArg RankKey.id hab)

/-- **⭐ `Wins` 是**不可自反**的**：没有键胜过自己。

**⇒ 这条不是闲置的：若它不成立，「选胜者」这个动作就没有意义（一个插件会同时压倒自己）。**
**⇒ 而它证明起来只需一件事：每个分量上 `>` 与 `<` 都是**不可自反**的。 -/
theorem wins_irreflexive (a : RankKey) : ¬ Wins a a := by
  intro h
  unfold Wins at h
  omega

/-- **⭐ `Wins` 是**反对称**的**：两个键不可互相压倒。

**⇒ 这是「选一个胜者」能成为函数的**前提**：否则两个插件都可以是胜者。**
**⇒ 证明同样是纯线性算术：每个分量的 `>` 与 `<` 不可同时成立。 -/
theorem wins_asymm {a b : RankKey} (h : Wins a b) : ¬ Wins b a := by
  intro h'
  unfold Wins at h h'
  omega

/-- **⭐ **全序性：任两个键可比**。

**⇒ 这是排序键的**最后一块**：没有它，「选一个胜者」在某些键对上**无法决定**。**
**⇒ 证法：逐分量分情形。每一层三个分支——「大」（对大者胜分量）/ 「小」 / 「等」，**
**⇒ 等则下降一层；六层均等则两个键**结构上相等**。 -/
theorem wins_trichotomy (a b : RankKey) : Wins a b ∨ a = b ∨ Wins b a := by
  by_cases h1 : a.scope.rank > b.scope.rank
  · exact Or.inl (Or.inl h1)
  by_cases h1' : b.scope.rank > a.scope.rank
  · exact Or.inr (Or.inr (Or.inl h1'))
  have hr : a.scope.rank = b.scope.rank := by omega
  by_cases h2 : a.priority > b.priority
  · exact Or.inl (Or.inr ⟨hr, Or.inl h2⟩)
  by_cases h2' : b.priority > a.priority
  · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inl h2'⟩))
  have hp : a.priority = b.priority := by omega
  by_cases h3 : a.protocol > b.protocol
  · exact Or.inl (Or.inr ⟨hr, Or.inr ⟨hp, Or.inl h3⟩⟩)
  by_cases h3' : b.protocol > a.protocol
  · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inr ⟨hp.symm, Or.inl h3'⟩⟩))
  have hpr : a.protocol = b.protocol := by omega
  by_cases h4 : a.loadSeq < b.loadSeq
  · exact Or.inl (Or.inr ⟨hr, Or.inr ⟨hp, Or.inr ⟨hpr, Or.inl h4⟩⟩⟩)
  by_cases h4' : b.loadSeq < a.loadSeq
  · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inr ⟨hp.symm, Or.inr ⟨hpr.symm, Or.inl h4'⟩⟩⟩))
  have hl : a.loadSeq = b.loadSeq := by omega
  by_cases h5 : a.regSeq < b.regSeq
  · exact Or.inl (Or.inr ⟨hr, Or.inr ⟨hp, Or.inr ⟨hpr, Or.inr ⟨hl, Or.inl h5⟩⟩⟩⟩)
  by_cases h5' : b.regSeq < a.regSeq
  · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inr ⟨hp.symm, Or.inr ⟨hpr.symm, Or.inr ⟨hl.symm, Or.inl h5'⟩⟩⟩⟩))
  have hrg : a.regSeq = b.regSeq := by omega
  by_cases h6 : a.id < b.id
  · exact Or.inl (Or.inr ⟨hr, Or.inr ⟨hp, Or.inr ⟨hpr, Or.inr ⟨hl, Or.inr ⟨hrg, h6⟩⟩⟩⟩⟩)
  by_cases h6' : b.id < a.id
  · exact Or.inr (Or.inr (Or.inr ⟨hr.symm, Or.inr ⟨hp.symm, Or.inr ⟨hpr.symm, Or.inr ⟨hl.symm, Or.inr ⟨hrg.symm, h6'⟩⟩⟩⟩⟩))
  have hid : a.id = b.id := by omega
  right
  have hs : a.scope = b.scope := DeployScope.rank_injective hr
  cases a
  cases b
  simp_all

/-! ## 三、依赖图与无环性（`PLUGIN-SYSTEM.md` §9.7） -/

/-- **依赖图**：每个插件的**直接**依赖。

**⇒ 用 `P → List P` 而不是一个 `Map`：指数与顺序都不是语义的一部分，而列表的多重集恰好表达「这些依赖」。 -/
abbrev DepGraph (P : Type) : Type := P → List P

/-- **「有秩证人」**：存在一个秩函数，沿**每一条边**严格下降。

**⇒ 这就是「图无环」的**构造式**写法：有序就能排序，而排序就是无环。**
**⇒ 没有它，「无环」只能写成「不存在回路」——那是**否定式**，难以从中取出任何东西。 -/
def Ranked {P : Type} (g : DepGraph P) (r : P → ℕ) : Prop :=
  ∀ p q, q ∈ g p → r q < r p

/-- **自依赖**：一个插件直接依赖自己。 -/
def SelfDep {P : Type} (g : DepGraph P) (p : P) : Prop := p ∈ g p

/-- **⭐ `requires_acyclic`（一阶）：有秩证人 ⇒ 不存在自依赖。**

**⇒ 理由只有一句：自依赖会要求 `r p < r p`，而那是矛盾。**
**⇒ 故「依赖图必须无环」不是一句行规，而是**秩的存在性的直接推论**。 -/
theorem requires_acyclic {P : Type} (g : DepGraph P) (r : P → ℕ)
    (h : Ranked g r) (p : P) : ¬ SelfDep g p := by
  intro hs
  exact absurd (h p p hs) (Nat.lt_irrefl _)

/-- **⭐ 二边回路也不可能**（两个插件相互引用）。

**⇒ 它比一阶更强：一阶只说「自己不能引用自己」，而这里说**任何互引用都不行**，**
**⇒ 因为它会要求 `r q < r p` 与 `r p < r q` 同时成立。 -/
theorem no_two_cycle {P : Type} (g : DepGraph P) (r : P → ℕ)
    (h : Ranked g r) (p q : P) (hp : q ∈ g p) (hq : p ∈ g q) : False := by
  have h1 : r q < r p := h p q hp
  have h2 : r p < r q := h q p hq
  omega

/-- **⭐ 子图仍无环**：从有序图里**删边**，序仍然是证人。

**⇒ 这是**活动用的那一条**：插件失效、被禁用、或被屏蔽时，图只会**变小**；**
**⇒ 而「无环」必须在变小下**保持**，否则每次禁用都要重算一次排序。**
**⇒ 证明只需一句：新边集是原边集的子集。 -/
theorem ranked_of_subgraph {P : Type} {g g' : DepGraph P} {r : P → ℕ}
    (h : Ranked g r) (hsub : ∀ p q, q ∈ g' p → q ∈ g p) : Ranked g' r :=
  fun p q hq => h p q (hsub p q hq)

/-! ### 可达性：从「一阶」到「任意长度」 -/

/-- **可达性**：从 `p` 沿边走到 `q`。

**⇒ 不用 `Path` 这个名字：它会遮蔽同名的标准概念；而且这里要的不是拓扑路径，只是**可达**。**
**⇒ 两个构造子就够：一条边，或一条边接一条可达。 -/
inductive DepPath {P : Type} (g : DepGraph P) : P → P → Prop where
  | single {p q : P} (h : q ∈ g p) : DepPath g p q
  | tail {p q s : P} (h : q ∈ g p) (hp : DepPath g q s) : DepPath g p s

/-- **⭐ 秩沿**可达性**严格下降。

**⇒ 这是整个无环性论证的**引擎**：它把「有秩证人」从一条边推到**任意长度的路径**。**
**⇒ 证法只用归纳与 `Nat.lt_trans`：一条边时就是 `Ranked` 本身；加一条边就接一次传递。 -/
theorem path_rank_lt {P : Type} {g : DepGraph P} {r : P → ℕ} (h : Ranked g r)
    {p q : P} (hp : DepPath g p q) : r q < r p := by
  induction hp with
  | single hq => exact h _ _ hq
  | tail hq _ ih => exact Nat.lt_trans ih (h _ _ hq)

/-- **⭐⭐ `Ranked` ⇒ **没有任何长度的回路****。

**⇒ 这把前面两条（`requires_acyclic` 一阶、`no_two_cycle` 二边）从**两种形状**推到**全部形状**。**
**⇒ 而证法只有两行：回路会要求 `r p < r p`，而那是不可能的。 -/
theorem ranked_acyclic {P : Type} {g : DepGraph P} {r : P → ℕ} (h : Ranked g r)
    {p : P} : ¬ DepPath g p p := by
  intro hp
  exact absurd (path_rank_lt h hp) (Nat.lt_irrefl _)


/-! ### 逆向：无回路 ⇒ 存在秩证人（**有限图**） -/

/-- **可达关系是**传递**的。** -/
theorem DepPath.trans {P : Type} {g : DepGraph P} {p q s : P}
    (hpq : DepPath g p q) (hqs : DepPath g q s) : DepPath g p s := by
  induction hpq with
  | single h => exact DepPath.tail h hqs
  | tail h _ ih => exact DepPath.tail h (ih hqs)

/-- **可达集**：从 `p` 能走到的节点。

**⇒ `classical`：这个集合只用于**计数**（`card`），不用于计算，故不需要可判定性进入 API。** -/
noncomputable def reachSet {P : Type} [Fintype P] (g : DepGraph P) (p : P) : Finset P := by
  classical
  exact Finset.univ.filter (fun q => DepPath g p q)

/-- **可达集的戈尔得特征**（它把 `classical` 封在定义里，不让它泄到每一个使用处）。 -/
theorem mem_reachSet {P : Type} [Fintype P] {g : DepGraph P} {p q : P} :
    q ∈ reachSet g p ↔ DepPath g p q := by
  classical
  simp only [reachSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **可达数**：本轮的秩候选。 -/
noncomputable def reachCount {P : Type} [Fintype P] (g : DepGraph P) (p : P) : ℕ :=
  (reachSet g p).card

/-- **⭐⭐逆向：**无回路 ⇒ 存在秩证人**（有限图上）。

**⇒ 秩取「从 `p` 可达的节点数」。若 `q ∈ g p`：**
**⇒ (a) 从 `q` 可达的一切都从 `p` 可达（**传递**）⇒ 集合包含；**
**⇒ (b) `q` 自身从 `p` 可达（一条边）而**不能从 `q` 可达自己**（无回路）⇒ 集合**真包含**；**
**⇒ 故基数**严格变小**，即 `reachCount` 是合法的秩证人。**

**⇒ 这把「无环」从**否定式**换成了**构造式**；与 `ranked_acyclic` 合起来是一个**双向**刻画。 -/
theorem acyclic_ranked {P : Type} [Fintype P] (g : DepGraph P)
    (h : ∀ p : P, ¬ DepPath g p p) : Ranked g (reachCount g) := by
  classical
  intro p q hq
  have hsub : reachSet g q ⊆ reachSet g p := by
    intro s hs
    exact mem_reachSet.mpr
      (DepPath.trans (DepPath.single hq) (mem_reachSet.mp hs))
  have hmem : q ∈ reachSet g p := mem_reachSet.mpr (DepPath.single hq)
  have hnot : q ∉ reachSet g q := fun hc => h q (mem_reachSet.mp hc)
  have hssub : reachSet g q ⊂ reachSet g p :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq ▸ hmem)⟩
  simpa [reachCount] using Finset.card_lt_card hssub

/-! ## 四、槽的三态（`PLUGIN-SYSTEM.md` §7.3.4） -/

/-- **槽的内容**——就三种，而且没有第四种。

**⇒ 规范§7.3.4 的三行表直接就是这三个构造子；而「槽不得取字面真值」的含义正是**
**⇒ **不存在**一个「恒真」构造子。 -/
inductive SlotContent where
  /-- 有事项：逐个必须解析到真实声明。 -/
  | items (names : List String)
  /-- 不适用：**理由必须非空**，且计入统计。 -/
  | na (reason : String)
  /-- 待实现：**阻止通过**。 -/
  | todo (note : String)

/-- **是否通过**。

**⇒ `items` 非空才通过（`items []` 不通过：零个事项就是空槽），**
**⇒ `na` 理由非空才通过，`todo` **永不**通过。**
**⇒ 用 `decide` 而不是 `!isEmpty`：前者把「与空串相等」直接变成可算位，后者需要一条引理去翻译它。 -/
def SlotContent.passes : SlotContent → Bool
  | .items names => decide (names ≠ [])
  | .na reason => decide (reason ≠ "")
  | .todo _ => false

/-- **`todo` 永不通过**。 -/
theorem todo_never_passes (note : String) : (SlotContent.todo note).passes = false := rfl

/-- **`na` 通过 ↔ 理由非空**。 -/
theorem na_passes_iff (reason : String) : (SlotContent.na reason).passes = true ↔ reason ≠ "" := by
  simp [SlotContent.passes]

/-- **`items` 通过 ↔ 非空**。 -/
theorem items_passes_iff (names : List String) :
    (SlotContent.items names).passes = true ↔ names ≠ [] := by
  simp [SlotContent.passes]

/-- **⭐⭐「槽不得取字面真值」的定理形式**：**通过的槽一定携带内容**。

**⇒ 若一个槽通过，那么它要么有**至少一个事项**，要么有**非空的理由**。**
**⇒ **没有第三种可能**：不存在「什么都不写而通过」的槽。**
**⇒ 这把规范那句**禁令**变成了一条**可检查的命题**。 -/
theorem passes_carries_content {c : SlotContent} (h : c.passes = true) :
    (∃ ns : List String, c = .items ns ∧ ns ≠ []) ∨ (∃ r : String, c = .na r ∧ r ≠ "") := by
  cases c with
  | items ns => exact Or.inl ⟨ns, rfl, (items_passes_iff ns).mp h⟩
  | na reason => exact Or.inr ⟨reason, rfl, (na_passes_iff reason).mp h⟩
  | todo note => simp [SlotContent.passes] at h

end Lattice.Plugins.Orchestration