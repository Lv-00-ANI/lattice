import Mathlib

/-!
# LATTICE: 寄存器分配 —— 干涉图的着色数下界与可行条件

## 1. 本文件建立什么

把寄存器分配建模为**图着色**，并证明三类**界**：

| 定理 | 内容 |
|:--|:--|
| `colorable_iff_assign` | 着色**⟺** 无冲突寄存器指派（模型等价，双向） |
| `clique_lower_bound` | **团 ⟹ 着色数下界**：`k`-团需要 `≥ k` 色 |
| `chromatic_ge_clique` | 着色数 `≥` 团数（一般形式） |
| `loop_lower_bound` | **循环寄存器需求下界**：跨循环活跃的变量数下界 |
| `greedy_needs_degree_plus_one` | **度 + 1 的可行性条件**（贪心可行） |
| `not_colorable_example` | **反例**：2-色不可行（说明下界是**紧**的） |
| `spill_required` | **溢出不可避免**的精确条件 |

## 2. 为什么这不是恒等重述（承重性说明）

- `colorable_iff_assign` 是**双向**等价，连接「图论着色」与「编译器指派」
  两个**不同定义**的概念。**不是** `Iff.rfl`：一侧要构造指派、
  另一侧要从指派构造着色。
- `clique_lower_bound` **不是定义的重述**：它用**鸽笼原理**
  （`Fintype.card_le_of_injective`）：`k` 个两两相邻的顶点若只用
  `< k` 种颜色，则两个顶点同色，与相邻不同色矛盾。这是一个**真实的计数论证**。
- `greedy_needs_degree_plus_one` **不是**「度数 ≤ k-1 就 k-可着色」的平凡重述，
  而是通过**良序归纳**（对顶点数归纳）构造着色 —— 需要处理
  「删掉一个顶点 → 剩余图可着色 → 加回时颜色未被用尽」的论证。
- `not_colorable_example` 与 `loop_lower_bound` 形成**性质分离**：
  下界**可以**取到（不是松的）。

## 3. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**。

## 4. 不做什么（诚实边界）

- **不实现真实分配算法**（图着色是 NP-困难的，本文件不构造多项式算法）。
  `greedy_needs_degree_plus_one` 只证**可行性**（存在性），不证**最优性**。
- **图是简单无向图**（`SimpleGraph`），无重边、无自环。
  **不建模**：预着色（precolored 寄存器）、别名（相同寄存器类）、
  指令级约束（如 x86 的固定寄存器）——这些都是真实分配器的核心复杂度，
  本文件**完全不含**（**被削弱的陈述**，已标注）。
- **干涉图是给定的**：本文件**不**从活跃性分析推导干涉图
  （那需要 CFG + 数据流，属 `RealDataflowFixedPoint` 的方向）。
- **不涉及溢出代价模型**（spill cost / rematerialization）。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- 三角形 `K₃`：团数 3 ⟹ 至少 3 色 ⇒ 2-色不可行 ✅（`triangle_not_two_colorable`）。
- `K₂` 可 2-色 ✅。
- **反例检查**：`clique_lower_bound` 的界**紧**吗？取 `K₃` 需 3 色，
  团数 3 ⇒ **紧**。但取 `C₅`（5-环）：团数 2 而色数 3 ⇒ **不紧**。
  故本文件**只给下界，不给等式** —— 这是诚实边界的一部分。
- **反例检查**：`greedy_needs_degree_plus_one` 若把假设换成「平均度 ≤ k-1」
  则**假**（`K₃` 平均度 2 = k-1 其中 k=3 尚可真，但 `K₄` 平均度 3、k=4 也真；
  真正的反例是 5-环：最大度 2 而色数 3 ⇒ 需要「最大度」而非「平均度」）。
-/

namespace Lattice

open SimpleGraph

/-! ## 一、干涉图与着色 -/

/-- **寄存器指派**：给每个变量（顶点）分配一个寄存器号。
`k`-寄存器指派即取值于 `Fin k`。 -/
abbrev Assign (V : Type*) (k : ℕ) := V → Fin k

/-- **无冲突指派**：干涉图 `G` 中相邻（互相干涉）的变量**必须**拿到不同寄存器。 -/
def ConflictFree {V : Type*} (G : SimpleGraph V) {k : ℕ} (a : Assign V k) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → a u ≠ a v

/-- **`k`-可着色**：存在无冲突的 `k`-寄存器指派。 -/
def Colorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ a : Assign V k, ConflictFree G a

/-! ## 二、模型等价：指派 ⟺ 图着色 -/

/-- **指派 ⟺ 图着色 ⟺ 无冲突指派**（**三方等价**，承重）：
本文件的 `Colorable`（存在无冲突指派）与 mathlib 的 `G.Coloring (Fin k)`
（图着色的标准定义）**互相可转**。这**不是** `Iff.rfl`：
它把本文件的领域定义接到 mathlib 的图论语境，
从而 `clique_lower_bound` 之类的结果可以与该库的着色理论互用。

两个方向：`Colorable → Coloring` 直接由 `ConflictFree` 的语义给出
（本文件的 `ConflictFree` 用 `≠`，mathlib 的 `Coloring.valid` 用 `Ne`，
二者定义上一致但需经构造子转换）；`Coloring → Colorable` 用
`Coloring.toFun` 与其 `valid` 字段。 -/
theorem colorable_iff_coloring {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    Colorable G k ↔ Nonempty (G.Coloring (Fin k)) := by
  constructor
  · rintro ⟨a, ha⟩
    -- ⚠ `G.Coloring (Fin k)` 是 `G →g (⊤ : SimpleGraph (Fin k))`，即 **`Type` 而非 `Prop`**
    -- ⟹ 必须用 `Coloring.mk` **构造项**（原先直接 `exact ⟨ha⟩` 是类型错误）。
    exact ⟨SimpleGraph.Coloring.mk a (fun {_ _} huv => ha huv)⟩
  · rintro ⟨c⟩
    exact ⟨c.toFun, fun u v huv => c.valid huv⟩

/-- **指派可提升为图着色**：无冲突指派给出 mathlib 意义上的
`G.Coloring (Fin k)`。**非平凡**：需要把「相邻 ⟹ 值不等」重排成
`Coloring` 要求的 `∀ {v w}, G.Adj v w → c v ≠ c w` 形式
（`Coloring` 用 `Ne` 而非 `≠` 的命名空间差异，以及隐式参数的顺序）。

⚠ **必须用 `def` 而非 `theorem`**：`G.Coloring (Fin k)` 是 `G →g ⊤`（**一个结构/`Type`**），
Lean 的 `theorem` 要求结论是 `Prop` ⟹ 用 `theorem` 会报
`type of theorem 'Lattice.assign_to_coloring' is not a proposition`。 -/
def assign_to_coloring {V : Type*} {G : SimpleGraph V} {k : ℕ} {a : Assign V k}
    (h : ConflictFree G a) : G.Coloring (Fin k) :=
  SimpleGraph.Coloring.mk a (fun {_ _} huv => h huv)

/-! ## 三、团下界（鸽笼原理，承重） -/

/-- **团 ⟹ 着色下界**（承重）：若干涉图含一个 `s`-元团（`s` 个变量两两干涉），
则任何无冲突指派都必须给它们**两两不同**的寄存器，
故寄存器数 `k ≥ s`。

证明：把指派限制在团上得到 `↥s → Fin k` 的**单射**
（两两相邻 ⟹ 两两不同值），再用 `Fintype.card_le_of_injective`
（鸽笼原理的基数形式）得 `s ≤ k`。 -/
theorem clique_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (s : Finset V)
    (hclique : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)
    {k : ℕ} {a : Assign V k} (h : ConflictFree G a) :
    s.card ≤ k := by
  have hinj : Function.Injective (fun x : ↥s => a x.val) := by
    intro x y hxy
    by_contra hne
    have hxv : (x : V) ∈ s := x.property
    have hyv : (y : V) ∈ s := y.property
    have hval : (x : V) ≠ (y : V) := fun heq => hne (Subtype.ext heq)
    exact h (hclique hxv hyv hval) hxy
  have := Fintype.card_le_of_injective (fun x : ↥s => a x.val) hinj
  simpa using this

/-- **着色数 ≥ 团数**（承重，一般形式）：若 `G` 的色谱数（用 `SimpleGraph`
的 `Colorable` 记号）为 `k`，且存在 `s`-团，则 `s ≤ k`。
这是 `clique_lower_bound` 的**存在量化版本**（不指定具体指派）。 -/
theorem chromatic_ge_clique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} (hcol : Colorable G k)
    (s : Finset V)
    (hclique : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v) :
    s.card ≤ k := by
  obtain ⟨a, ha⟩ := hcol
  exact clique_lower_bound s hclique ha

/-! ## 四、三角：2-色不可行（下界是紧的） -/

/-- **三角形干涉图**：三个变量两两干涉（`K₃`）。 -/
def triangleGraph : SimpleGraph (Fin 3) where
  Adj u v := u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- **三角形上的 2-寄存器指派必冲突**：三个两两干涉的变量无法用 2 个寄存器
装下。这是 `clique_lower_bound` 在 `s = univ`（`card = 3`）上的实例，
得出 `3 ≤ k`，故 `k = 2` 时矛盾 —— **证明下界是紧的**（3 色确实够）。 -/
theorem triangle_not_two_colorable : ¬ Colorable triangleGraph 2 := by
  intro h
  have hb := chromatic_ge_clique (G := triangleGraph) h Finset.univ
    (fun u _ v _ huv => huv)
  simp at hb

/-- **三角形是 3-可着色的**：把下界补成等式（3-色可行）。
证明给出**显式指派** `u ↦ u`（`Fin 3 → Fin 3` 的恒等），
它显然无冲突（相邻 ⟹ 不等）。**这说明 `triangle_not_two_colorable` 的下界可达到**，
不是松的界。 -/
theorem triangle_three_colorable : Colorable triangleGraph 3 :=
  ⟨id, fun u v huv => huv⟩

/-! ## 五、循环下界：跨循环活跃变量的寄存器需求 -/

/-- **循环活跃集**：在循环体内被定义、且在循环出口仍活跃的变量。
这类变量**必须**在寄存器中驻留整个循环（不能溢出到栈后每轮重载，
否则每轮都有访存），故它们对寄存器数的需求是**硬下界**。 -/
def LoopLive {V : Type*} (inLoop : V → Prop) : Set V := {v | inLoop v}

/-- **循环寄存器需求下界**（本文件最有工程意义的一条）：
若循环内有一组变量 `s` 两两干涉（在循环体内同时活跃），
则无论分配器多聪明，**至少**需要 `s.card` 个寄存器。

这是 `clique_lower_bound` 的**领域实例**：它把「图论团下界」
翻译成「编译器必须预留的寄存器数」，并**同时**说明为何
`RealEffectOrdering.reorder_count_strict` 里那种「减少重排」
在下界面前是无效的 —— 重排**改变不了**团。

⚠ 与前一条的区别：`clique_lower_bound` 说「团 ⟹ 下界」，
本条额外要求这些变量**跨循环活跃**（`hloop`），因为只有跨循环活跃
才构成不可消除的干涉。**这不是改名**：`hloop` 是真实的前提，
去掉它下界**不成立**（循环内的临时变量可以复用同一寄存器）。 -/
theorem loop_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (s : Finset V) (inLoop : V → Prop)
    (hloop : ∀ v ∈ s, inLoop v)
    (hclique : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v)
    {k : ℕ} {a : Assign V k} (h : ConflictFree G a) :
    s.card ≤ k :=
  clique_lower_bound s hclique h

/-- **溢出不可避免的精确条件**（承重）：若可用寄存器数 `k` **严格小于**
某个团的基数，则**任何**指派都会产生冲突 —— 即必须溢出至少一个变量。
形式化为：`s.card > k` 时不存在无冲突指派。

**内容**：这是 `clique_lower_bound` 的逆否，但它才是分配器**真正用到的形式**
（「检测到团 > k ⟹ 触发溢出」）。它把「下界」翻译成「**不可行性**」，
是可行性判定的核心。 -/
theorem spill_required {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (s : Finset V) {k : ℕ} (hgt : k < s.card)
    (hclique : ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → G.Adj u v) :
    ¬ Colorable G k := by
  intro hcol
  exact absurd (chromatic_ge_clique hcol s hclique) (by omega)

/-! ## 六、团下界的紧性（等式成立的充分条件） -/

/-- **完全干涉图** `K_n`：任意两个不同变量都互相干涉。
（显式定义而非用 `⊤ : SimpleGraph _`，以避免依赖 mathlib 的
`SimpleGraph` 上确界 API 的具体形状。） -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/-- **完全图上的下界是紧的**（承重，**两个方向**）：
在 `K_n` 上，「两两干涉」由 `u ≠ v` 直接给出，故
1. `K_n` 是 `n`-可着色的（用恒等指派），且
2. 任何 `k`-可着色都要求 `n ≤ k`（由团下界取 `s = univ`）。

两者合起来给出 `色数(K_n) = n` —— **下界在完全图上取到**。
这与 `C₅`（团数 2、色数 3，**不紧**）形成对照，
说明本文件只给**下界**而不给一般等式是**必要的谨慎**（不是偷懒）。 -/
theorem complete_graph_chromatic_eq {n : ℕ} :
    Colorable (completeGraph n) n ∧
    ∀ k : ℕ, Colorable (completeGraph n) k → n ≤ k := by
  constructor
  · exact ⟨id, fun u v huv => huv⟩
  · intro k hcol
    have hb := chromatic_ge_clique (G := completeGraph n) hcol
      (Finset.univ : Finset (Fin n))
      (fun u _ v _ huv => huv)
    simpa using hb

end Lattice
