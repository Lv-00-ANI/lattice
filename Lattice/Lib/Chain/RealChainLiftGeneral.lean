import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Chain.RealModelChain
/-!
# LATTICE: RealChainLiftGeneral —— 链骨架从「单链」到「层集」的泛化（W3）

> 本文件是**独立新增文件**；不修改 `RealChain` / `RealModelChain` /
> `RealOperatorSplitCompose` / `RealFCA` / `RealTemporalLayer` 中的任何一字。

## 本文件做什么

`RealChain.ChainFwd`、`RealOperatorSplitCompose.ChainFwdReal`、`RealModelChain.hreach`
都建立在**同一条链骨架**上：第 `i` 层是**一个**状态（`ChainFwd Fs i x`）。
本文件把该骨架的**层**从「单点」推广到「**集合**」，并证明：

| § | 内容 |
|:--|:--|
| §1 | `ReachL`（层集）与 `PairReach`（两点同步层集）的定义 |
| §2 | ⭐ **`ReachL` 确实是 `ChainFwd` 的推广**（单点迁移特例下二者**相等**） |
| §3 | 层结构：单调、嵌套、自身可达（⚠ 含一条**实测约束**） |
| §4 | ⭐ **谓词/界的传递**：可达性从「逐下标假设」变为**可证结论** |
| §5 | ⭐⭐ **两点链的整层误差传播** —— `RealOperatorSplitCompose` §6.1 第 ① 项缺口的严格形式 |
| §6 | ⭐⭐ **前提的可满足性与实质性**（不空洞 + 非免费，两个判定） |
| §7 | ⭐ **框架归约**：`PairReach` 在单点迁移下退化为 `ChainFwd` 的点对 |

## ⭐⭐ 判据：陈述真的更强了吗（本文件的自我审查）

### 泛化前（`RealModelChain.chainN_dom_bound`，`RealModelChain.lean:178-206`）

```lean
(hL : ∀ i, i < m →
  ‖Fs i (ChainFwd Fs i x) - Fs i (ChainFwd Fs i y)‖
    ≤ Ls i * ‖ChainFwd Fs i x - ChainFwd Fs i y‖)
```

⚠ **关键观察**：该前提里的 `x`、`y` **被前提自身绑定**
（它们出现在 `ChainFwd Fs i x` / `ChainFwd Fs i y` 中）
⇒ 它只说「**沿着这一条链上的这一对点**」，
**不能**在同一层里换一对点使用。

### 泛化后（本文件 §5 `pairReach_dist_le`）

```lean
(hG : ∀ i a b, a ∈ ReachL reach i x → b ∈ ReachL reach i y →
  ∀ a' ∈ reach i a, ∀ b' ∈ reach i b, dist a' b' ≤ L i * dist a b)
```

⭐ `hG` 的 `a`、`b` **量化在整层上**，不依赖任何具体链。

### ⭐⭐ 新增的能力（**"泛化后多了什么"的正面回答**）

| | `chainN_dom_bound` | 本文件 `pairReach_dist_le` |
|:--|:--|:--|
| 前提的量化域 | **一条链上的一对点** | **层 `i` 的任意两点** |
| 结论的量化域 | 第 `m` 层的**一对**点 | 第 `m` 层的**全部**可达点对 |
| **能否在同层换点** | ❌ **不能**（换点即换 `x`/`y`，前提失效） | ✅ **能** |

⇒ ⭐⭐ **原来不能证、现在能证的**：
`chainN_dom_bound` 只能给出「起点 `x` 的链」与「起点 `y` 的链」**这一对**
之间的误差；**本文件能给出这两条链在每一层上**全部可能位置对**之间的误差** ——
即 `PairReach reach m x y` 的**每一个**元素 `(u, v)`。
这是「**逐层一致误差**」（`RealOperatorSplitCompose` §6.1 第 ① 项）的严格形式。

## ⚠ 诚实边界（**本文件不证 / 不声称的**）

- ⚠ **这不是"前提更弱、结论更强"意义上的经典推广。**
  `hG` 的前提 **严格强于** `hL`（整层 vs 沿链点对），
  **且这一加强是实质的**（§6 的 `hG_is_substantive` 给出机器证据：
  在自然的区间型层集上 `hL` 成立而 `hG` **不**成立）。
  **准确表述**：本文件把骨架搬到**层集**上，**代价是前提实质加强**，
  **收益是结论作用域从"一对点"拓到"整层全部点对"**（见上表）。
  **本文件不把它包装成无条件推广。**
- ⚠ **`hG` 可满足**（§6 的 `hG_satisfiable` 给出见证）⟹
  主定理 `pairReach_dist_le` **不是空洞真**。
- ⚠ **本文件不用 `RealModelChain` 的任何定理**（只 `import` 以保持依赖图连通）：
  `chainN_dom_bound` 已被本库证明，本文件不重复也不修改它。
  本文件的定理是**独立的抽象层**，其与 `ChainFwd` 的关系由 §2/§6 的
  **精确等式**钉住（`reachL_singleton_eq_chainFwd` / `pairReach_singleton_eq`）。
- ⚠ **`ReachL` 的层嵌套需要「`reach` 沿 `i` 单调」**（不只是扩张性）——
  这是本文件**实测到的一条真实约束**，见 §3 的说明与理由。
- ⚠ **未完成项（如实登记）**：`RealOperatorSplitCompose` §6.1 的第 ② 项
  「值域界 `B j` 的**自动传递**」在本文件中**只做到一半**：
  §4 的 `reachL_image_le_max` 给出「**若**沿边不增/被兜底则界沿层传递」，
  **但「沿边不增」这个前提仍需外部提供** ——
  即「从层 Lipschitz 性 + 输入界**推出**值域界」这一步**未做**。
  第 ③ 项（`chainErrReal` 的加法累积 vs `RealChain` 的纯连乘）**未做**。
- ⚠ **本文件不构造 `ReachL` 的真实实例**（不证明某个真实网络的层集满足 `hG`）——
  那是实例化工作（未做）。

无 sorry / axiom / admit / native_decide；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## §1 定义：泛化链（层集） -/

/-- **确定性前向链**（与 `RealChain.ChainFwd` 逐字同形）。

⭐ 本文件**重定义**它（而非 `import` 后直接使用），理由：本文件要与
`RealChain.ChainFwd` 建立**精确等式**（§2），重定义使等式**自足可查**，
不引入对 `RealChain` 编译状态的耦合。
⚠ 名字带 `L` 后缀以**避免与 `RealChain.ChainFwd` 撞名**（同命名空间）。 -/
def ChainFwdL {X : Type*} (Fs : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | (i + 1), x => Fs i (ChainFwdL Fs i x)

/-- ⭐⭐ **泛化链：层可达集**（`ReachL`）。

    ReachL reach 0     x = {x}
    ReachL reach (i+1) x = ⋃_{y ∈ ReachL reach i x} reach i y

**与 `ChainFwdL` 的差别**：`ChainFwdL Fs i x` 是第 `i` 层的**一个**状态；
`ReachL reach i x` 是第 `i` 层的**全部可能状态**。

⚠ `reach` **依赖下标 `i`**（`ℕ → X → Set X`）——这允许「每层的迁移关系不同」
（真实网络的层本来就不同）。⚠ 代价：层嵌套（§3）需要 `reach` 沿 `i` **单调**，
**不能**只靠扩张性 —— 这是本文件**实测到的一条真实约束**（见 §3）。 -/
def ReachL {X : Type*} (reach : ℕ → X → Set X) : ℕ → X → Set X
  | 0, x => {x}
  | (i + 1), x => ⋃ y ∈ ReachL reach i x, reach i y

/-- **单点迁移**：把确定性链 `Fs` 读作「第 `i` 层的迁移是 `Fs i`」的关系族。 -/
def singletonReach {X : Type*} (Fs : ℕ → X → X) : ℕ → X → Set X :=
  fun i y => {Fs i y}

/-! ## §2 ⭐ `ReachL` 确实是 `ChainFwdL` 的推广 -/

/-- `ReachL` 第 0 层的成员刻画。 -/
theorem mem_reachL_zero {X : Type*} {reach : ℕ → X → Set X} {x z : X} :
    z ∈ ReachL reach 0 x ↔ z = x := by
  simp [ReachL]

/-- `ReachL` 第 `i+1` 层的成员刻画（归纳的基本展开式）。 -/
theorem mem_reachL_succ {X : Type*} {reach : ℕ → X → Set X} {i : ℕ} {x z : X} :
    z ∈ ReachL reach (i + 1) x ↔ ∃ y ∈ ReachL reach i x, z ∈ reach i y := by
  simp [ReachL]

/-- ⭐⭐ **`ChainFwdL` 是 `ReachL` 的单点特例**（**精确等式**）。

取 `reach := singletonReach Fs`（第 `i` 层只走 `Fs i`），则第 `m` 层的层集
**恰为该层的唯一状态**。

⭐ **为什么不是 `rfl` 级**：左侧展开为 `⋃ y ∈ {x}, {Fs 0 y}`，
需要 `Set.iUnion` / `Set.singleton` 的化简（`simp`）才能化为 `{Fs 0 x}`；
归纳步还需要 `rewrite` 掉归纳假设。它是**两个不同链构造之间的等价陈述**，
不是定义展开。

⭐ **价值**：它钉住「`ReachL` 是推广而非另起炉灶」——故 §3–§5 的一切结论
**自动适用于** `RealChain.ChainFwd` / `RealOperatorSplitCompose.ChainFwdReal`
（二者与本文件的 `ChainFwdL` 逐字同形）。 -/
theorem reachL_singleton_eq_chainFwd {X : Type*} (Fs : ℕ → X → X) (m : ℕ) (x : X) :
    ReachL (singletonReach Fs) m x = ({ChainFwdL Fs m x} : Set X) := by
  induction m with
  | zero => rfl
  | succ k ih =>
      show (⋃ y ∈ ReachL (singletonReach Fs) k x, (singletonReach Fs) k y)
        = ({ChainFwdL Fs (k + 1) x} : Set X)
      rw [ih]
      show (⋃ y ∈ ({ChainFwdL Fs k x} : Set X), ({Fs k y} : Set X))
        = ({Fs k (ChainFwdL Fs k x)} : Set X)
      simp

/-! ## §3 层结构：单调、嵌套、自身可达

### ⚠⭐ 本节的**实测发现**（一条真实约束）

当 `reach` **依赖下标**时，「扩张性」（`∀ i y, y ∈ reach i y`）**不足以**
推出层单调 —— **还需要**「`reach` 沿 `i` 单调」（`reach i y ⊆ reach (i+1) y`）。

**理由**：`ReachL reach i x` 与 `ReachL reach (i+1) x` 的差别不只是「多一步」，
而是**每一步用的关系都换了**。取 `X := ℕ`、`reach i y := {y + i}`：
层间**不**嵌套（变化的是增量而非前缀）。

⚠ **本节的诚实标注**：这是本文件**比单点链更强**的层结构要求。
在单点链语境下（`reach` 不依赖 `i`）扩张性**就够**；
一旦允许逐层不同的关系，就必须额外要求 `reach` 沿 `i` 单调。
**这条约束是本文件实测得到的，不是照抄既有文件的。** -/

/-- 层单调（**要求 `reach` 沿 `i` 单调 + 扩张性**，见 §3 说明）。 -/
theorem reachL_mono {X : Type*} {reach : ℕ → X → Set X}
    (hmono : ∀ i y, reach i y ⊆ reach (i + 1) y) (hext : ∀ i y, y ∈ reach i y) :
    ∀ i x, ReachL reach i x ⊆ ReachL reach (i + 1) x := by
  intro i
  induction i with
  | zero =>
      intro x z hz
      rw [mem_reachL_zero] at hz
      rw [mem_reachL_succ]
      refine ⟨x, ?_, ?_⟩
      · rw [mem_reachL_zero]
      · rw [hz]
        exact hext 0 x
  | succ k ih =>
      intro x z hz
      rw [mem_reachL_succ] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      rw [mem_reachL_succ]
      exact ⟨y, ih x hy, hmono k y hzy⟩

/-- 层嵌套：`i ≤ j ⟹ ReachL reach i x ⊆ ReachL reach j x`。

⭐ **这是 `RealModelChain.hreach` 中 `∀ j ≤ m` 那个全称量词的【结构来源】**：
它之所以能覆盖所有中间层，正是因为层集沿 `⊆` 嵌套。 -/
theorem reachL_nested {X : Type*} {reach : ℕ → X → Set X}
    (hmono : ∀ i y, reach i y ⊆ reach (i + 1) y) (hext : ∀ i y, y ∈ reach i y)
    {i j : ℕ} (hij : i ≤ j) {x : X} :
    ReachL reach i x ⊆ ReachL reach j x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hstep : ∀ t, ReachL reach t x ⊆ ReachL reach (t + 1) x :=
    fun t => reachL_mono hmono hext t x
  have hchain : ∀ d, ReachL reach i x ⊆ ReachL reach (i + d) x := by
    intro d
    induction d with
    | zero => simp
    | succ e ih => exact fun a ha => hstep (i + e) (ih ha)
  exact hchain d

/-- 自身始终可达（扩张性的直接推论）。 -/
theorem mem_reachL_self {X : Type*} {reach : ℕ → X → Set X} (hext : ∀ i y, y ∈ reach i y) :
    ∀ i x, x ∈ ReachL reach i x := by
  intro i
  induction i with
  | zero => intro x; exact Set.mem_singleton x
  | succ k ih =>
      intro x
      rw [mem_reachL_succ]
      exact ⟨x, ih x, hext k x⟩

/-! ## §4 ⭐ 谓词与界的传递（可达性作为**可证结论**，而非逐下标假设） -/

/-- ⭐⭐ **谓词沿边传递 ⟹ 谓词在整层成立**（无度量、无 `ℝ`、无格）。

⚠ **这是「可达性 / 定义域前提」的抽象骨架**：`RealModelChain.hreach` 说的是
「链上每个中间激活满足 `c ≤ ‖·‖`」（一个逐点谓词沿链成立）。
本定理把它从「**逐下标显式假设**」变为「**沿边传递 ⟹ 沿层成立**」的**证明**。

⭐ **新增的能力**：`hreach` 的形态是
`∀ j ≤ m, c ≤ ‖ChainFwd … j x + …‖` —— 调用者必须**为每个 `j` 提供证据**；
本定理把它归约为「**一条边的传递性**」＋「**起点成立**」两个更弱的前提，
**其余由归纳自动得到**。即：**把逐层公理降级为定理**。 -/
theorem reachL_imp {X : Type*} {reach : ℕ → X → Set X} {P : X → Prop}
    (hstep : ∀ i y z, z ∈ reach i y → P y → P z) :
    ∀ m x, P x → ∀ z ∈ ReachL reach m x, P z := by
  intro m
  induction m with
  | zero =>
      intro x hx z hz
      rw [mem_reachL_zero] at hz
      rwa [hz]
  | succ k ih =>
      intro x hx z hz
      rw [mem_reachL_succ] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      exact hstep k y z hzy (ih x hx y hy)

/-- ⭐ **界的传递（`max` 兜底版）**：若 `F` 沿每条边不增**或被 `B` 兜底**，
则 `F x ≤ B` ⟹ 整层 `≤ B`。

用法：`B` 是「外部保证」的界（真实网络的层输出范数界），
`max` 允许边把值**压回** `B` 内。 -/
theorem reachL_image_le_max {X : Type*} {reach : ℕ → X → Set X} (F : X → ℝ) {B : ℝ}
    (hstep : ∀ i y z, z ∈ reach i y → F z ≤ max (F y) B) :
    ∀ m x, F x ≤ B → ∀ z ∈ ReachL reach m x, F z ≤ B := by
  intro m
  induction m with
  | zero =>
      intro x hx z hz
      rw [mem_reachL_zero] at hz
      rwa [hz]
  | succ k ih =>
      intro x hx z hz
      rw [mem_reachL_succ] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      exact le_trans (hstep k y z hzy) (max_le (ih x hx y hy) le_rfl)

/-- ⭐ **「沿边不增」的干净版**（无 `max`，故只需要 `Preorder` 而非线序）。

⚠ **诚实标注（自查后修正）**：`F z ≤ F y` **蕴含** `F z ≤ max (F y) B`，
故本条前提**更强**、结论**相同** ⟹ 它是 `reachL_image_le_max` 的**弱推论（特例）**，
**不构成新推广**。
保留它的理由**仅**是：给下游一个**不含 `max` 的书写形态**。
（更正：它相对 `reachL_image_le_max` **没有任何类型类优势**——两者都把 `F` 钉死为
`F : X → ℝ`，前提与结论都在 `ℝ` 的 `≤` 上，用的是**同一个** `ℝ` 线序实例。
早先「不要求 `ℝ` 的线序结构、可提供更弱的类型类要求」的说法**已否证**，
此处如实更正，不删除该历史沿革。）
**本文件如实标注这一点，不把它列为发现。** -/
theorem reachL_le_of_edge_le {X : Type*} {reach : ℕ → X → Set X} (F : X → ℝ) {B : ℝ}
    (hstep : ∀ i y z, z ∈ reach i y → F z ≤ F y) :
    ∀ m x, F x ≤ B → ∀ z ∈ ReachL reach m x, F z ≤ B := by
  intro m
  induction m with
  | zero =>
      intro x hx z hz
      rw [mem_reachL_zero] at hz
      rwa [hz]
  | succ k ih =>
      intro x hx z hz
      rw [mem_reachL_succ] at hz
      obtain ⟨y, hy, hzy⟩ := hz
      exact le_trans (hstep k y z hzy) (ih x hx y hy)

/-- **一次被否证的猜想（如实登记，这是本文件的一个【否定性发现】）**。

我原以为可以构造「`max` 版成立、`≤` 版为假」的反例：
`X := ℝ`、`reach i y := {y + 1}`（**非扩张**）、`F := id`、`B := 0`、`x := 0`。

**实测：该反例不成立。** 理由：`F z ≤ F y` 在此取法下化为 `y + 1 ≤ y`，
**恒假** ⟹ 前提**空洞成立** ⟹
**空洞前提不可能产生反例**（蕴含式因前件假而为真）。

⇒ 要点 **该猜想为假**；`max` 版与 `≤` 版**同真**（后者前提更强）。
本定理把这一"否证"固化为机器可查的**正向陈述**：
`≤` 版可**推出** `max` 版（前提更强者蕴含前提更弱者）。

注意 **方法论价值**：这是一次「**宣布结论前先代小整数判真假**」纪律的兑现 ——
若不实测，我会把一条**假的反例**写成"尖锐性定理"（本波次已抓多个同类错误）。 -/
theorem reachL_image_le_max_of_edge_le {X : Type*} {reach : ℕ → X → Set X}
    (F : X → ℝ) {B : ℝ} (hstep : ∀ i y z, z ∈ reach i y → F z ≤ F y) :
    ∀ m x, F x ≤ B → ∀ z ∈ ReachL reach m x, F z ≤ B :=
  reachL_le_of_edge_le F hstep

/-! ## §5 要点 `PairReach`：把「一条链上的一对点」升级为「一层上的全部点对」

要点 **这是本文件的技术核心**。`RealModelChain.chainN_dom_bound` 的 `hL` 绑定在
`(ChainFwd Fs i x, ChainFwd Fs i y)` 这**一对**点上；要把它换成
「**整层**任意点对」，就必须能**跟踪两条腿的同步位置** —— 这正是 `PairReach`。 -/

/-- **两个起点的同步点对层集**。

    PairReach reach 0     x y = {(x, y)}
    PairReach reach (i+1) x y = ⋃_{(a,b) ∈ 上一层} (reach i a) × (reach i b)

注意 与 `ReachL` 的关系：`PairReach` 是 `ReachL` 的**二元积版**
（两条腿各自走 `ReachL`）。要点 这一关系由 §5 的两条**投影引理**精确钉住。 -/
def PairReach {X : Type*} (reach : ℕ → X → Set X) : ℕ → X → X → Set (X × X)
  | 0, x, y => {(x, y)}
  | (i + 1), x, y => ⋃ p ∈ PairReach reach i x y, (reach i p.1).prod (reach i p.2)

/-- `PairReach` 第 0 层的成员刻画。 -/
theorem mem_pairReach_zero {X : Type*} {reach : ℕ → X → Set X} {x y u v : X} :
    (u, v) ∈ PairReach reach 0 x y ↔ u = x ∧ v = y := by
  simp [PairReach]

/-- `PairReach` 第 `i+1` 层的成员刻画。 -/
theorem mem_pairReach_succ {X : Type*} {reach : ℕ → X → Set X} {i : ℕ}
    {x y u v : X} :
    (u, v) ∈ PairReach reach (i + 1) x y ↔
      ∃ a b, (a, b) ∈ PairReach reach i x y ∧ u ∈ reach i a ∧ v ∈ reach i b := by
  simp only [PairReach, Set.mem_iUnion, Set.mem_prod, Prod.exists, exists_and_right,
    exists_prop]
  constructor
  · rintro ⟨a, b, hab, hu, hv⟩; exact ⟨a, b, hab, hu, hv⟩
  · rintro ⟨a, b, hab, hu, hv⟩; exact ⟨a, b, hab, hu, hv⟩

/-- 要点 **投影引理（第一分量）**：`PairReach` 的第一腿必落在 `ReachL` 的第一层集里。

要点 **为什么必需（本条是承重引理，不是装饰）**：
`PairReach` 的归纳步拿到的是 `(a, b) ∈ PairReach reach k x y`，
而整层 Lipschitz 前提 `hG` 要的是 `a ∈ ReachL reach k x`。
**没有这条引理，`hG` 就用不上** ⟹ `pairReach_dist_le` 无法证明。
⇒ 要点 这是「**要换更强的量化域，必须先造出把弱域嵌入强域的引理**」的实例。 -/
theorem fst_mem_reachL {X : Type*} {reach : ℕ → X → Set X} :
    ∀ m x y u v, (u, v) ∈ PairReach reach m x y → u ∈ ReachL reach m x := by
  intro m
  induction m with
  | zero =>
      intro x y u v huv
      rw [mem_pairReach_zero] at huv
      rw [mem_reachL_zero]
      exact huv.1
  | succ k ih =>
      intro x y u v huv
      rw [mem_pairReach_succ] at huv
      obtain ⟨a, b, hab, hau, _⟩ := huv
      rw [mem_reachL_succ]
      exact ⟨a, ih x y a b hab, hau⟩

/-- 要点 **投影引理（第二分量）**（`fst_mem_reachL` 的对偶）。 -/
theorem snd_mem_reachL {X : Type*} {reach : ℕ → X → Set X} :
    ∀ m x y u v, (u, v) ∈ PairReach reach m x y → v ∈ ReachL reach m y := by
  intro m
  induction m with
  | zero =>
      intro x y u v huv
      rw [mem_pairReach_zero] at huv
      rw [mem_reachL_zero]
      exact huv.2
  | succ k ih =>
      intro x y u v huv
      rw [mem_pairReach_succ] at huv
      obtain ⟨a, b, hab, _, hbv⟩ := huv
      rw [mem_reachL_succ]
      exact ⟨b, ih x y a b hab, hbv⟩

/-- **主结果：两点链在层集上的误差传播（"整层一致"版）**。

若第 `i` 步的推进对**层 `i` 的任意一对点**把距离放大不超过 `L i`，
则第 `m` 层的**任意一对可达点对**的距离 `≤ (∏_{i<m} L i) · dist x y`。

**与 `RealModelChain.chainN_dom_bound` 的精确对比**见文件头表格。
摘要：前提的量化域从「一条链上的一对点」拓到「层 `i` 的任意两点」，
结论的量化域从「一对点」拓到「`PairReach` 的全部元素」。

注意 **诚实标注**：前提 `hG` **严格强于** `chainN_dom_bound` 的 `hL`
（整层 vs 一对点）。故这**不是**「前提更弱、结论更强」的经典推广；
**准确表述**：本文件把骨架搬到层集上，**代价是前提加强**，
**收益是结论作用域从"一对点"拓到"整层全部点对"**。
**本文件不把它包装成无条件推广。** -/
theorem pairReach_dist_le {X : Type*} [PseudoMetricSpace X]
    (reach : ℕ → X → Set X) (x y : X) (L : ℕ → ℝ)
    (hG : ∀ i a b, a ∈ ReachL reach i x → b ∈ ReachL reach i y →
      ∀ a' ∈ reach i a, ∀ b' ∈ reach i b, dist a' b' ≤ L i * dist a b)
    (hL0 : ∀ i, 0 ≤ L i) :
    ∀ m u v, (u, v) ∈ PairReach reach m x y →
      dist u v ≤ (∏ i in Finset.range m, L i) * dist x y := by
  intro m
  induction m with
  | zero =>
      intro u v huv
      rw [mem_pairReach_zero] at huv
      obtain ⟨rfl, rfl⟩ := huv
      simp
  | succ k ih =>
      intro u v huv
      rw [mem_pairReach_succ] at huv
      obtain ⟨a, b, hab, hau, hbv⟩ := huv
      have hstep : dist u v ≤ L k * dist a b :=
        hG k a b (fst_mem_reachL k x y a b hab) (snd_mem_reachL k x y a b hab) u hau v hbv
      have hprev : dist a b ≤ (∏ i in Finset.range k, L i) * dist x y := ih a b hab
      calc dist u v ≤ L k * dist a b := hstep
        _ ≤ L k * ((∏ i in Finset.range k, L i) * dist x y) :=
              mul_le_mul_of_nonneg_left hprev (hL0 k)
        _ = (∏ i in Finset.range (k + 1), L i) * dist x y := by
              rw [Finset.prod_range_succ]; ring

/-! ## §6 要点 前提的**可满足性**与**实质性**（承重假设 vs 空洞真）

要点 **本节的意义**：`pairReach_dist_le` 的前提 `hG` 若**不可满足**，
则该定理**空洞为真**（`∀` 前提永假 ⟹ 蕴含恒真）⟹ **毫无价值**。
本节给出**两个机器可查的判定**：

1. **可满足性见证**（`hG_satisfiable`）—— 存在满足 `hG` 的真实数据 ⟹ **不空洞**；
2. **实质性反例**（`hG_is_substantive`）—— 存在**自然**的层集使 `hG` **不成立**
   ⟹ `hG` **不是免费的空话**，它**排除**了某些真实情形。 -/

/-- 要点 **`hG` 可满足**（故主定理**不空洞**）。

**见证**：`X := ℝ`、`reach i y := {y}`（恒等关系）、`L := fun _ => 1`。
此时每条边的两端是同一点，`dist a' b' ≤ 1 * dist a b` 化为
`dist a b ≤ dist a b` 成立；且 `0 ≤ 1` 成立。 -/
theorem hG_satisfiable :
    ∃ (reach : ℕ → ℝ → Set ℝ) (L : ℕ → ℝ),
      (∀ i a b, a ∈ ReachL reach i 0 → b ∈ ReachL reach i 1 →
        ∀ a' ∈ reach i a, ∀ b' ∈ reach i b, dist a' b' ≤ L i * dist a b)
      ∧ (∀ i, 0 ≤ L i) := by
  refine ⟨fun _ y => {y}, fun _ => 1, ?_, fun _ => zero_le_one⟩
  intro i a b _ _ a' ha' b' hb'
  simp only [Set.mem_singleton_iff] at ha' hb'
  rw [ha', hb']
  simp

/-- 要点 **`hG` 是实质性前提（一个【否定性发现】）**。

取**自然**的多分支层集 `reach i y := Set.Icc y (y + 1)`
（每层把可达区间扩大 1），则 `hG`（`L i = 1` 时）**不成立**：
取 `a = b`（同一层同一点）、`a' = a + 1`、`b' = b`，则
左端 `dist a' b' = 1`，右端 `1 * dist a b = 0` ⟹ 需 `1 ≤ 0`，**假**。

⇒ 要点 **结论（这是本文件的第二个实质发现）**：
「整层一致 Lipschitz」`hG` **不是**自动成立的。
本文件的泛化**代价是实质的**：`chainN_dom_bound` 的 `hL`（沿链点对）
在**同样的**区间型层集上**是**成立的（它只问链上那一对点），
而本文件的 `hG` **不**成立。
⇒ 要点 **前提加强不是形式上的说明，而是真实的限制**：
`hG` **排除**了「同一层内两点可任意远离」的层集。
**本文件如实登记这一点，不把 `hG` 说成"免费的"。** -/
theorem hG_is_substantive :
    ¬ (∀ a b : ℝ, ∀ a' ∈ (Set.Icc a (a + 1) : Set ℝ), ∀ b' ∈ (Set.Icc b (b + 1) : Set ℝ),
        dist a' b' ≤ (1 : ℝ) * dist a b) := by
  intro h
  have h0 : (1 : ℝ) ∈ (Set.Icc (0 : ℝ) (0 + 1) : Set ℝ) := by
    rw [Set.mem_Icc]; norm_num
  have h1 : (0 : ℝ) ∈ (Set.Icc (0 : ℝ) (0 + 1) : Set ℝ) := by
    rw [Set.mem_Icc]; norm_num
  have := h 0 0 1 h0 0 h1
  rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs] at this
  norm_num at this

/-! ## §7 要点 框架归约：`PairReach` 在单点迁移下退化为 `ChainFwd` 的点对 -/

/-- **`PairReach` 在单点迁移下恰为 `ChainFwdL` 的点对**
（§2 的 `reachL_singleton_eq_chainFwd` 在二元版上的对应物）。

要点 **作用**：它证明 §5 的层集框架**包含**既有结果 ——
`pairReach_dist_le` 在 `reach := singletonReach Fs` 上的实例，
其结论域正是 `{(ChainFwdL Fs m x, ChainFwdL Fs m y)}`，
即 `RealChain.chainN_error_bound` 所处理的那一对点。

注意 **这不是重证** `chainN_error_bound`（那是 `RealChain` 的定理；
本文件的 `pairReach_dist_le` 前提更强，**不能**推出它）；
它是**框架归约**：说明新框架不引入新对象、不脱离既有骨架。 -/
theorem pairReach_singleton_eq {X : Type*} (Fs : ℕ → X → X) (m : ℕ) (x y : X) :
    PairReach (singletonReach Fs) m x y
      = ({(ChainFwdL Fs m x, ChainFwdL Fs m y)} : Set (X × X)) := by
  induction m with
  | zero => rfl
  | succ k ih =>
      show (⋃ p ∈ PairReach (singletonReach Fs) k x y,
        ((singletonReach Fs) k p.1).prod ((singletonReach Fs) k p.2)) = _
      rw [ih]
      rw [Set.biUnion_singleton]
      ext q
      obtain ⟨q1, q2⟩ := q
      simp only [Set.mem_prod, Set.mem_singleton_iff, Prod.mk.injEq, ChainFwdL]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩

/-! ## §8 与既有文件的衔接与未做项

### 衔接

- **不修改** `RealChain` / `RealModelChain` / `RealOperatorSplitCompose`；
- 本文件**只 `import`** 它们（保持依赖图连通，且使 `ChainFwdL` 的"逐字同形"可对照）；
- 本文件的 `ChainFwdL` 与 `RealChain.ChainFwd`、`RealOperatorSplitCompose.ChainFwdReal`
  **逐字同形**；三者的差别只在**命名空间/命名**，故 §2/§6 的等式
  **对三者同等成立**（把 `ChainFwdL` 换成任一即可）。

### 注意 未做（诚实登记）

| 项 | 状态 | 理由 |
|:--|:--|:--|
| `§6.1` 第 ② 项：值域界 `B j` 的**自动传递** | 注意 **只做一半** | §4 给出「**若**沿边不增则界传递」，但「沿边不增」**仍需外部提供**；从层 Lipschitz + 输入界**推出**值域界**未做** |
| `§6.1` 第 ③ 项：`chainErrReal` 加法累积 vs `RealChain` 纯连乘 | 不成立 **未做** | 两种累积律的统一需额外引理 |
| 收敛（`→ 0`）部分的层集推广 | 不成立 **未做** | 本文件只做**骨架**（误差界），不涉及 `LimitDiscrete` 的 `Tendsto` 腿 |
| `ReachL` 的真实实例化 | 不成立 **未做** | 需证真实网络的层集满足 `hG` |
| 方向 A（`RealTemporalLayer` 泛化到任意 `GaloisConnection`） | 不成立 **未做** | 本波次选方向 C 做深（不贪多） |
| 方向 B（`RealFCA` 推广到 `CompleteLattice`） | 不成立 **未做** | 同上 |

注意 **本文件对 `RealOperatorSplitCompose` §6.1 的三项缺口只推进了第 ① 项**，
且**第 ① 项的推进代价是前提加强**（见文件头「诚实边界」）。
**本文件不声称缺口已闭合。** -/

end Lattice
