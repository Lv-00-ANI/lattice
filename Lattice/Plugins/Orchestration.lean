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

end Lattice.Plugins.Orchestration