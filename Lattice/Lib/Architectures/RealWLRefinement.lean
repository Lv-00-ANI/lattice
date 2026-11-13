import Mathlib
import Lattice.Lib.Architectures.RealGNN
import Lattice.Plugins.Architectures.GNN.Proofs
/-!
# LATTICE: 1-WL 颜色精化的完整等价定理——GNN 表达力的上界与可达性

`RealGNN` 给出消息传递的数值界，`RealGNNEquivariance` 给出置换等变性，
`RealGraphExpressivity` 给出**首轮**失明与过平滑。本文件补上**核心一环**：
**完整的 1-WL 迭代颜色精化**，并证明它**恰好刻画**求和聚合 GNN 的区分能力。

## 一、1-WL 颜色精化的形式化（避免 `Multiset` 商类型）

经典 1-WL 迭代为

    color_0 v = ℓ v,
    color_{k+1} v = (color_k v, {{ color_k u : u ∈ N(v) }}).

直接形式化需要「颜色的多重集」与有限颜色类型的迭代（颜色空间的基数每轮膨胀）。
本文件改用**等价的检验函数刻画**（多重集相等的对偶）：两个节点有相同的
「邻居深度-`k` 颜色的多重集」当且仅当**所有在深度-`k` 颜色类上取常值的检验函数
`φ` 的邻居求和相等**：

    wlEq 0 x y     := ℓ x = ℓ y,
    wlEq (k+1) x y := wlEq k x y ∧
        ∀ φ, (∀ u v, wlEq k u v → φ u = φ v) → ∑_{u∈N(x)} φ u = ∑_{u∈N(y)} φ u.

这一改写有**三重好处**：
(i) 不必构造「颜色多重集」的商类型，也不必为膨胀的颜色空间做有限性编码；
(ii) 检验函数 `φ` 正是 GNN 的**特征**——于是「GNN 输出相同」可以**直接**读出；
(iii) 该刻画与多重集刻画**等价**（取 `φ` 为颜色类的指示函数即得计数相等）。

## 二、主定理：1-WL 不可区分 ⟹ 任意定深求和 GNN 输出相同

设 `N(x)` 为节点 `x` 的邻居集（由边集 `E : Finset (ι × ι)` 诱导），
`ℓ : ι → ℝ` 为初始标签，`φ : ι → ℝ` 为任意特征。

1. `gnnFeat_eq_of_wlEq`（**GNN ⊆ WL**，核心，任意定深 `k`，无条件）：
   若 `wlEq k x y`，则**任意**深度 `k` 的求和聚合 GNN 在 `x`、`y` 上给出**相同**输出。
   即 1-WL 的区分能力是 GNN 的**上界**（Morris et al. 2019 的 "GNN ≤ 1-WL" 方向）；
2. `wlEq_zero_iff_gnnFeat_eq`：`k = 0` 的**完整双向**等价；
3. **一般 `k` 的方向二（WL ⊆ GNN）：未做（诚实降级）**。
   它需要把「邻居颜色的多重集」无损编码为实数的算术引理
   `exists_injective_multiset_sum`（Grohe Lemma VIII.5，`m` 进制表示唯一性），
   经项目负责人批准**暂不投入**，见 §六 的完整说明。
   本文件**不声称**一般 `k` 的「⟺」。

## 三、检验函数刻画的直接推论

- `wlEq_refl` / `wlEq_symm` / `wlEq_trans`：`wlEq` 是等价关系（对 `k` 归纳）；
- `wlEq_succ_le` / `wlEq_mono`：颜色精化是**单调细分**（`wlEq (k+1) ⟹ wlEq k`）；
- `wlEq_one_iff`：`wlEq 1` 的完整展开——即标准 1-WL 的**第一轮**；
- `oneWL_degree_of_wlEq`：无标签时第一轮**只能看到度数**。

## 诚实边界（中文标注）

- **未做（降级）—— 一般 `k` 的方向二（WL ⊆ GNN）**：需要把「邻居颜色的多重集」
  无损编码为实数的算术引理 `exists_injective_multiset_sum`（Grohe Lemma VIII.5，
  `m` 进制表示唯一性）。这是**独立的纯算术里程碑**，经项目负责人批准**暂不投入**。
  故本文件**只证方向一（任意 `k`）+ `k = 0` 的完整双向**，
  **不声称**已证一般 `k` 的「1-WL 不可区分 ⟺ GNN 输出相同」；
- **未做 —— 非线性激活的一般版本**：本文件的 GNN 模型为**求和聚合 + 线性读出**
  （`RealGNN.gnnLayer` 的标量权重特例）。含一般 `σ` 的版本需要 `σ` 的**单射性**
  参与（否则 `σ` 可能把不同特征映为同值——这与 1-WL 上界不矛盾，
  但陈述需改为「`σ` 单射时」），**未做**；
- **降级 —— 边集为无权、无自环的有限边集**：本文件用 `E : Finset (ι × ι)` 表示边集；
  带边权 `w : ι → ι → ℝ`（`sparseMsgPass` 已在 `RealGNNEquivariance` §七 给出）
  与**完整边特征**（`e_{ij}` 参与聚合）的版本**未做**；
- **已做 —— `C6Edges` / `TwoK3Edges` 的 2-正则性**：`RealGraphExpressivity` 已形式化
  两个边集与 `C6Edges_two_regular` / `TwoK3Edges_two_regular`（`decide` 核验），
  并在其上实例化 `twoRegular_oneWL_blind` 得到 `C6_twoK3_1WL_blind`；
- **标注 —— `k` 为有限深度**：主定理对**每个**固定深度 `k` 成立（`∀ k`），
  但**不**声称 `k → ∞` 的极限等价（那需要颜色在有限步后稳定，即
  「WL 稳定化引理」，**未做**）；
- **未做 —— 3-WL / 高阶 WL 与 k-WL 层级**：只做 1-WL；
- **未做 —— 多重集刻画的显式桥接**：本文件直接用检验函数刻画（按 R4 调研建议，
  刻意**避免** `Multiset` 商类型），故**未**给出与 `Multiset` 版本的显式双向引理
  ——(iii) 中「取指示函数即得计数相等」只是**说明**，未形式化为定理。

无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 一、邻域结构与 1-WL 迭代定义 -/

/-- **邻居集**：由边集 `E : Finset (ι × ι)` 诱导的 `x` 的出邻居集
`N(x) = { u | (x, u) ∈ E }`。

标注：用 `Finset` 而非 `Set`，因为后续所有求和都在有限集上进行；
`Fintype ι` 已给定，故 `E` 必然是有限的。 -/
def nbhdSet (E : Finset (ι × ι)) (x : ι) : Finset ι :=
  Finset.univ.filter (fun u => (x, u) ∈ E)

/-- **邻域求和**：`∑_{u ∈ N(x)} f u`——GNN 一跳聚合的**无量纲化**形式。 -/
def nbhdSum (E : Finset (ι × ι)) (x : ι) (f : ι → ℝ) : ℝ :=
  ∑ u in nbhdSet E x, f u

/-- **邻域基的性质**：`u ∈ N(x) ↔ (x, u) ∈ E`。 -/
@[simp] theorem mem_nbhdSet {E : Finset (ι × ι)} {x u : ι} :
    u ∈ nbhdSet E x ↔ (x, u) ∈ E := by
  simp [nbhdSet]

/-- **1-WL 颜色的等价关系（检验函数刻画）**。

`wlEq E k x y` 读作「`x` 与 `y` 在第 `k` 轮 1-WL 精化后**同色**」：

- `k = 0`：初始标签相同（此处以「所有标签可读函数取值相同」形式给出，
  见 `wlEq_zero_iff` 与 `wlEq_zero_of_label_eq`）；
- `k+1`：`k` 轮同色，**且**所有在 `k` 轮颜色类上取常值的检验函数 `φ`
  在两者的邻域上求和相等。

**为什么用检验函数而非多重集**：多重集相等 `{{f u : u ∈ N x}} = {{f u : u ∈ N y}}`
在 `Multiset` 商类型上需要 `DecidableEq` 与可计算性负担；而「对所有 `φ` 求和相等」
是它的**对偶刻画**（取 `φ` 为指示函数即得计数相等），且 `φ` 恰好就是 GNN 特征，
使主定理的证明变成**直接读出**。 -/
def wlEq (E : Finset (ι × ι)) (ℓ : ι → ℝ) : ℕ → ι → ι → Prop
  | 0, x, y => ℓ x = ℓ y
  | k + 1, x, y =>
      wlEq E ℓ k x y ∧
        ∀ φ : ι → ℝ, (∀ u v : ι, wlEq E ℓ k u v → φ u = φ v) →
          nbhdSum E x φ = nbhdSum E y φ

@[simp] theorem wlEq_zero (E : Finset (ι × ι)) (ℓ : ι → ℝ) (x y : ι) :
    wlEq E ℓ 0 x y ↔ ℓ x = ℓ y := Iff.rfl

theorem wlEq_succ (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k : ℕ) (x y : ι) :
    wlEq E ℓ (k + 1) x y ↔
      wlEq E ℓ k x y ∧
        ∀ φ : ι → ℝ, (∀ u v : ι, wlEq E ℓ k u v → φ u = φ v) →
          nbhdSum E x φ = nbhdSum E y φ := Iff.rfl

/-! ## 二、`wlEq` 的基本结构：自反、对称、传递 -/

/-- **自反性**：每个节点与自己同色（对 `k` 归纳）。

`k+1` 步：`k` 步由归纳假设；检验函数部分两边**逐字相同**，故 `rfl`。 -/
theorem wlEq_refl (E : Finset (ι × ι)) (ℓ : ι → ℝ) :
    ∀ k x, wlEq E ℓ k x x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ⟨ih x, fun _ _ => rfl⟩

/-- **对称性**：`wlEq k x y → wlEq k y x`（对 `k` 归纳，检验函数部分用 `Eq.symm`）。 -/
theorem wlEq_symm (E : Finset (ι × ι)) (ℓ : ι → ℝ) :
    ∀ k x y, wlEq E ℓ k x y → wlEq E ℓ k y x := by
  intro k
  induction k with
  | zero => intro x y h; exact h.symm
  | succ n ih =>
      intro x y h
      exact ⟨ih x y h.1, fun φ hφ => (h.2 φ hφ).symm⟩

/-- **传递性**：`wlEq` 是等价关系（对 `k` 归纳）。

`k+1` 步：第一分量由归纳假设传递；检验函数部分把两条等式**串接**
（`hxy.2 φ hφ` 与 `hyz.2 φ hφ`）。 -/
theorem wlEq_trans (E : Finset (ι × ι)) (ℓ : ι → ℝ) :
    ∀ k x y z, wlEq E ℓ k x y → wlEq E ℓ k y z → wlEq E ℓ k x z := by
  intro k
  induction k with
  | zero => intro x y z h1 h2; exact h1.trans h2
  | succ n ih =>
      intro x y z h1 h2
      exact ⟨ih x y z h1.1 h2.1,
        fun φ hφ => (h1.2 φ hφ).trans (h2.2 φ hφ)⟩

/-! ## 三、检验函数刻画的直接推论 -/

/-- **颜色类上常值的检验函数**：这就是 `wlEq` 递归里的那个前提，
单独命名为 `ConstOn` 便于阅读与复用。 -/
def ConstOn (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k : ℕ) (φ : ι → ℝ) : Prop :=
  ∀ u v : ι, wlEq E ℓ k u v → φ u = φ v

/-- **`wlEq (k+1)` 展开为邻域求和相等**（把 `ConstOn` 命名后的重述）。 -/
theorem wlEq_succ_iff (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k : ℕ) (x y : ι) :
    wlEq E ℓ (k + 1) x y ↔
      wlEq E ℓ k x y ∧
        ∀ φ : ι → ℝ, ConstOn E ℓ k φ → nbhdSum E x φ = nbhdSum E y φ :=
  Iff.rfl

/-- **每次下降一轮**：`wlEq (k+1) x y → wlEq k x y`（精化只**细分**颜色类）。

即颜色精化是**单调细分**的：同色关系随 `k` 递减。
这是 `wlEq_mono` 的基本步（`wlEq_mono` 由它迭代得到）。 -/
theorem wlEq_succ_le (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k : ℕ) {x y : ι}
    (h : wlEq E ℓ (k + 1) x y) : wlEq E ℓ k x y := h.1

/-- **下降 `d` 轮**：`wlEq (j + d) x y → wlEq j x y`（对 `d` 归纳）。

这是 `wlEq_mono` 的**正确归纳形状**：对**差值 `d`** 归纳（而非对 `j` 或 `k`），
于是归纳步是把「`j + (d+1)`」经 `wlEq_succ_le` 化为「`j + d`」，
再用归纳假设——**motive 里 `j` 保持为参数**，不会出现 `y✝` 式的作用域错位。 -/
theorem wlEq_mono_aux (E : Finset (ι × ι)) (ℓ : ι → ℝ) (d : ℕ) :
    ∀ (j : ℕ) (x y : ι), wlEq E ℓ (j + d) x y → wlEq E ℓ j x y := by
  induction d with
  | zero =>
      intro j x y h
      simpa using h
  | succ e ih =>
      intro j x y h
      -- `j + (e+1) = (j + e) + 1`：先下降一轮，再用 `ih`（对 `j + e` 到 `j`）
      have h1 : wlEq E ℓ (j + e) x y := wlEq_succ_le E ℓ (j + e) (by simpa [Nat.add_assoc] using h)
      exact ih j x y h1

/-- **单调性的向下闭包**：`wlEq E ℓ k x y` 蕴含**所有更浅**轮次 `j ≤ k` 同色。

即颜色精化是**单调细分**的：同色关系随 `k` 递减；
等价地「1-WL 能区分的节点对，在更深轮次仍能区分」。

证明：把 `k` 写成 `j + (k - j)`，对差值 `k - j` 用 `wlEq_mono_aux`。 -/
theorem wlEq_mono (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k j : ℕ) (hj : j ≤ k)
    {x y : ι} (h : wlEq E ℓ k x y) : wlEq E ℓ j x y := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  exact wlEq_mono_aux E ℓ d j x y h
/-! ## 四、深度 `k` 求和聚合 GNN 的特征 -/

/-- **深度 `k` 求和 GNN 的特征族**。

`gnnFeat E ℓ k` 是**所有**深度 `k`、以 `ℓ` 为初始标签、以邻域求和为聚合、
以线性函数为读出的 GNN 在节点 `x` 处的**输出向量**——用「对每个检验函数 `φ`
的读出值」编码为函数 `ι → ℝ`。

定义（对 `k` 递归）：

    gnnFeat 0        x = (fun φ => φ x)                -- 直接用原始标签/特征
    gnnFeat (k+1)    x = (fun φ => ∑_{u ∈ N(x)} gnnFeat k u φ)   -- 邻居处的 `k` 层特征求和

即第 `k+1` 层就是「对邻居的深度-`k` 特征做**求和聚合**」，这正是求和型消息传递
（GIN 的 sum 变体）的**代数骨架**：不含权重的逐点线性变换可以吸收进 `φ` 的选取。

**为什么用「函数 `ι → ℝ`」而非数值向量**：这样 `gnnFeat` 对**所有**检验函数同时成立，
于是「GNN 输出相同」的量化是 `gnnFeat E ℓ k x = gnnFeat E ℓ k y`（函数外延相等），
无需为特征维数引入额外的有限类型。 -/
def gnnFeat (E : Finset (ι × ι)) : ℕ → ι → (ι → ℝ) → ℝ
  | 0, x, φ => φ x
  | k + 1, x, φ => ∑ u in nbhdSet E x, gnnFeat E k u φ

@[simp] theorem gnnFeat_zero (E : Finset (ι × ι)) (x : ι) (φ : ι → ℝ) :
    gnnFeat E 0 x φ = φ x := rfl

theorem gnnFeat_succ (E : Finset (ι × ι)) (k : ℕ) (x : ι) (φ : ι → ℝ) :
    gnnFeat E (k + 1) x φ = ∑ u in nbhdSet E x, gnnFeat E k u φ := rfl

/-- **`gnnFeat 1` 就是邻域求和**：`gnnFeat E 1 x φ = ∑_{u ∈ N(x)} φ u = nbhdSum E x φ`。

这条把 `gnnFeat` 与 §1 的 `nbhdSum` 对接：**一层 GNN 就是一次邻域求和**。 -/
theorem gnnFeat_one (E : Finset (ι × ι)) (x : ι) (φ : ι → ℝ) :
    gnnFeat E 1 x φ = nbhdSum E x φ := rfl

/-! ## 五、主定理方向一：GNN ⊆ WL（1-WL 是 GNN 区分能力的上界） -/

/-- **关键引理（核心）**：若 `wlEq E ℓ k x y`，则**任意**深度 `k` 求和 GNN 特征相同。

精确陈述：对 `wlEq E ℓ k` 的任何**常值检验函数** `φ`（即 `φ` 在 `k` 轮颜色类上常值），
`gnnFeat E k x φ = gnnFeat E k y φ`。

证明（对 `k` 归纳）：
- `k = 0`：`wlEq 0 x y` 即 `ℓ x = ℓ y`；而 `ConstOn … 0 φ` 要求
  `∀ u v, ℓ u = ℓ v → φ u = φ v`，取 `u = x`、`v = y` 即得 `φ x = φ y`，
  也就是 `gnnFeat E 0 x φ = gnnFeat E 0 y φ`；
- `k+1`：`wlEq (k+1) x y` 给出 `wlEq k x y` **与** 「所有 `k`-常值检验函数
  `ψ` 的邻域求和相等」。取 `ψ := fun u => gnnFeat E k u φ`——
  关键在于 `ψ` **恰是归纳假设可证其 `k`-常值的**：归纳假设的陈述对**任意**
  `ψ`（只要 `ConstOn E ℓ 0 ψ`）给出 `wlEq k u v → gnnFeat k u ψ = gnnFeat k v ψ`，
  而此处 `ψ = gnnFeat k · φ` 本身**就是** `gnnFeat k` 的取值，
  故归纳假设以 `φ` 为参数**直接**给出 `ConstOn E ℓ k ψ`。
  于是 `wlEq (k+1) x y` 的第二分量（取 `ψ` 为检验函数）给出所求等式。

**这正是 R4 提示的关键技巧**：把归纳假设保持在**最弱前提** `ConstOn 0 φ` 上
（而非 `ConstOn k φ`），则归纳步无需任何「颜色类单调性」引理即可闭合。

**这条定理正是「GNN 的表达力不超过 1-WL」**：1-WL 同色的节点对，
任何深度 `k` 的求和 GNN 都**无法**区分。 -/
theorem gnnFeat_eq_of_wlEq (E : Finset (ι × ι)) (ℓ : ι → ℝ) :
    ∀ k x y, wlEq E ℓ k x y → ∀ φ : ι → ℝ, ConstOn E ℓ 0 φ →
      gnnFeat E k x φ = gnnFeat E k y φ := by
  intro k
  induction k with
  | zero =>
      intro x y hxy φ hφ
      exact hφ x y hxy
  | succ n ih =>
      intro x y hxy φ hφ
      rw [gnnFeat_succ, gnnFeat_succ]
      -- 关键：`ψ := fun u => gnnFeat E n u φ` 是 `n`-常值的，
      -- 而这**正是归纳假设**（同一 `hφ : ConstOn 0 φ`）给出的
      exact hxy.2 (fun u => gnnFeat E n u φ) (fun u v huv => ih u v huv φ hφ)

/-- **GNN ⊆ WL（GNN 可达特征的逐点形式）**：`wlEq E ℓ k x y` 蕴含

    ∀ φ, ConstOn E ℓ 0 φ → gnnFeat E k x φ = gnnFeat E k y φ,

即**任何**以 `ℓ` 的常值函数为输入的深度 `k` GNN 都无法区分 `x`、`y`。

**这条才是「GNN 表达力 ≤ 1-WL」的正确形式**：`gnnFeat` 的输入 `φ` 必须
**在初始颜色类上常值**（否则 `φ` 本身就是一个「外部神谕」，可以用它直接读出
任意节点的原始特征，从而绕过 WL——这不是 GNN 的区分力，而是输入特征的区分力）。

`φ` 常值于初始颜色类（`ConstOn E ℓ 0 φ`）蕴含 `φ` 可写成 `ℓ` 的**函数**形式
（`∃ g, φ = g ∘ ℓ`），见 `constOn_zero_of_comp`——该引理只证**充分方向**
（`∃ g, φ = g ∘ ℓ` ⟹ `ConstOn E ℓ 0 φ`），反向需选择公理下的 `ℓ` 的截面，**未做**
（详见下文 `ConstOn … 0` 处的 docstring）。这是图机器学习里
「节点特征由初始标签决定」的标准约定。 -/
theorem gnnFeat_eq_of_wlEq_of_constOn_zero (E : Finset (ι × ι)) (ℓ : ι → ℝ) (k : ℕ)
    {x y : ι} (hxy : wlEq E ℓ k x y) (φ : ι → ℝ) (hφ : ConstOn E ℓ 0 φ) :
    gnnFeat E k x φ = gnnFeat E k y φ :=
  gnnFeat_eq_of_wlEq E ℓ k x y hxy φ hφ

/-- **`gnnFeat 0` 的形式**：`gnnFeat E 0 x φ = φ x`（定义即得）。 -/
theorem gnnFeat_zero_apply (E : Finset (ι × ι)) (x : ι) (φ : ι → ℝ) :
    gnnFeat E 0 x φ = φ x := rfl

/-- **`ConstOn … 0` 就是「`φ` 是 `ℓ` 的函数」**：
`(∃ g : ℝ → ℝ, φ = g ∘ ℓ) ↔ ConstOn E ℓ 0 φ`。

正向（`←`）：若 `φ` 在 `ℓ` 的等值类上常值，则 `φ` 的取值只依赖 `ℓ` 的值。
此处只证**易用的充分方向**（`∃ g` ⟹ `ConstOn`）与**第一轮同色的读出**，
完整双向需要选择公理下的 `ℓ` 的截面，**未做**（不影响主定理）。 -/
theorem constOn_zero_of_comp (E : Finset (ι × ι)) (ℓ : ι → ℝ) {g : ℝ → ℝ} :
    ConstOn E ℓ 0 (fun u => g (ℓ u)) := by
  intro u v huv
  show g (ℓ u) = g (ℓ v)
  rw [huv]

/-- **`gnnFeat` 对 `ℓ` 的复合特征在首轮即相等**：
`wlEq E ℓ 0 x y` ⟹ `gnnFeat E 0 x (g ∘ ℓ) = gnnFeat E 0 y (g ∘ ℓ)`。 -/
theorem gnnFeat_zero_comp_eq (E : Finset (ι × ι)) (ℓ : ι → ℝ) {g : ℝ → ℝ} {x y : ι}
    (hxy : wlEq E ℓ 0 x y) :
    gnnFeat E 0 x (fun u => g (ℓ u)) = gnnFeat E 0 y (fun u => g (ℓ u)) :=
  gnnFeat_eq_of_wlEq_of_constOn_zero E ℓ 0 hxy _ (constOn_zero_of_comp E ℓ)

/-- **`gnnFeat` 对常值函数退化**：若 `φ` 在所有节点上常值 `c`，则
`gnnFeat E 1 x φ = c · |N(x)|`——即**常值特征不会产生区分力**，
这与 `RealGraphExpressivity` 的「均匀聚合失明」一致。
此处以 `k = 1` 的显式形式给出（一般 `k` 需多重邻域计数，**未做**）。 -/
theorem gnnFeat_const_one (E : Finset (ι × ι)) (c : ℝ) (x : ι) :
    gnnFeat E 1 x (fun _ => c) = c * (nbhdSet E x).card := by
  rw [gnnFeat_one, nbhdSum, Finset.sum_const, nsmul_eq_mul]
  ring
/-! ## 六、主定理方向二：WL ⊆ GNN（1-WL 上界的可达性——**部分完成**）

方向一（`gnnFeat_eq_of_wlEq`）说「WL 同色 ⟹ GNN 不可分」。方向二是它的**逆**：
「WL 不同色 ⟹ **存在**一个求和 GNN 可分」。这才是「上界**可达**」。

本文件**只对 `k = 0` 给出完整双向**（`wlEq_zero_iff_gnnFeat_eq`），一般 `k` 的
方向二**诚实降级**，理由如下（这也是本文件唯一的实质性诚实边界）。

### 为什么 `k = 0` 容易而一般 `k` 难

`wlEq` 用**检验函数刻画**定义：
`wlEq (k+1) x y := wlEq k x y ∧ ∀ φ, ConstOn E ℓ k φ → nbhdSum E x φ = nbhdSum E y φ`。

- **方向一（易，已证）**：`wlEq k x y` 蕴含所有 `ConstOn 0 φ` 的 `k` 层读出相等。
  归纳步取 `ψ := gnnFeat E n · φ`，而 `ConstOn n ψ` **恰好就是归纳假设本身**
  （前提保持最弱的 `ConstOn 0 φ`）——**无需任何单调性引理**即可闭合。
  这正是 R4 提示的技巧，也是本文件在探针诊断中发现的关键修正：
  若把前提写成 `ConstOn k φ`，归纳步需要「`wlEq n ⟹ wlEq (n+1)`」，
  而该蕴含**为假**（精化是**向下**单调：`wlEq (n+1) ⟹ wlEq n`），故不可闭合。

- **方向二（难，未做）**：要从「所有 `ConstOn k φ` 的读出都相等」**反推** `wlEq k x y`，
  归纳步必须把 `gnnFeat E (n+1)` 的相等**解码**为「`wlEq n x y`」**与**
  「所有 `ConstOn n φ` 的邻域求和相等」两部分。前者要求 `gnnFeat` 的读出族
  在颜色类上**单射**——即存在把「邻居颜色的多重集」**无损编码**为实数的构造

      `exists_injective_multiset_sum`（Grohe, Lemma VIII.5：`m` 进制表示的唯一性）

  这是一条**独立的纯算术里程碑**（多重集 → `∑ m ^ (code c)` 的单射性），
  本文件**未做**（经项目负责人批准暂不投入，可后续单独立项）。
  它**与 `wlEq` 的定义无关**，是「WL 颜色的算法侧实数实现」问题。

### 因此本文件实际给出

- **方向一（任意 `k`，无条件）**：`gnnFeat_eq_of_wlEq`——**GNN 表达力 ≤ 1-WL**；
- **完整双向（`k = 0`）**：`wlEq_zero_iff_gnnFeat_eq`；
- **方向二（一般 `k`）**：**未做**，依赖上述算术引理，**明确标注为降级**。

诚实标注：`RealGraphExpressivity` 侧的 `C₆ vs 2K₃` 见证与本节方向一共同把
「1-WL 上界」从首轮特例推进到**任意固定深度**；但「上界**可达**」的完整证明
仍缺失，本文件**不声称**已证完整的「⟺」。 -/

/-- **WL ⊆ GNN（方向二，`k = 0` 完整版）**：若**所有**在初始颜色类 `wlEq E ℓ 0`
（即 `ℓ` 的等值类）上常值的检验函数 `φ` 都被深度 `0` 的读出在 `x`、`y` 上
给出相同输出，则 `ℓ x = ℓ y`（即 `wlEq E ℓ 0 x y`）。

**证明思路**：取指示函数 `φ u = if ℓ u = ℓ x then 1 else 0`（它是 `ℓ` 的复合，
故由 `constOn_zero_of_comp` 是 `ConstOn 0`）。由假设
`gnnFeat E 0 x φ = gnnFeat E 0 y φ` 得 `φ x = φ y`，即 `1 = [ℓ y = ℓ x]`，
故 `ℓ y = ℓ x`。

**诚实标注**：这是**唯一**给出完整双向的轮次。一般 `k` 的方向二需要
Grohe Lemma VIII.5（`m` 进制单射编码），**未做**——见本节说明。 -/
theorem wlEq_zero_of_gnnFeat_eq (E : Finset (ι × ι)) (ℓ : ι → ℝ) {x y : ι}
    (h : ∀ φ : ι → ℝ, ConstOn E ℓ 0 φ → gnnFeat E 0 x φ = gnnFeat E 0 y φ) :
    wlEq E ℓ 0 x y := by
  -- 取指示函数 `φ u = if ℓ u = ℓ x then 1 else 0`（它是 `ℓ` 的复合，故 `ConstOn … 0`）
  set φ : ι → ℝ := fun u => if ℓ u = ℓ x then 1 else 0 with hφdef
  have hφ : ConstOn E ℓ 0 φ := by
    intro u v huv
    -- `huv : wlEq E ℓ 0 u v` 即 `ℓ u = ℓ v`（定义即得）
    show (if ℓ u = ℓ x then (1 : ℝ) else 0) = (if ℓ v = ℓ x then (1 : ℝ) else 0)
    rw [show ℓ u = ℓ v from huv]
  have hx := h φ hφ
  -- 展开 `gnnFeat 0 x φ = φ x` 与 `gnnFeat 0 y φ = φ y`，并把恒真条件 `ℓ x = ℓ x` 化简掉
  simp only [gnnFeat_zero_apply, hφdef, if_true] at hx
  -- 此时 `hx : 1 = (if ℓ y = ℓ x then 1 else 0)`
  show ℓ x = ℓ y
  by_contra hne
  rw [if_neg (fun hc => hne hc.symm)] at hx
  -- `hx : 1 = 0`
  exact one_ne_zero hx

/-- **双向等价（`k = 0` 完整版）**：`wlEq E ℓ 0 x y` **当且仅当**
所有 `0`-常值检验函数的 GNN 读出相同。

两条方向都用同一套检验函数族，故这是**完整的等价**而非单向蕴含。 -/
theorem wlEq_zero_iff_gnnFeat_eq (E : Finset (ι × ι)) (ℓ : ι → ℝ) (x y : ι) :
    wlEq E ℓ 0 x y ↔
      ∀ φ : ι → ℝ, ConstOn E ℓ 0 φ → gnnFeat E 0 x φ = gnnFeat E 0 y φ := by
  constructor
  · intro hxy φ hφ
    exact gnnFeat_eq_of_wlEq E ℓ 0 x y hxy φ hφ
  · intro h
    exact wlEq_zero_of_gnnFeat_eq E ℓ h

/-- **`k = 1` 的显式 `wlEq`**：把 `wlEq 1` 完全展开为
「初始标签相同 **且** 所有 `ℓ`-常值函数的邻域求和相等」。

这是**完整 1-WL 第一轮**（即 `RealGraphExpressivity` 中只做了「正则图失明」那一半）
的精确刻画：`wlEq 1` 就是标准 1-WL 的**第一轮颜色精化**。 -/
theorem wlEq_one_iff (E : Finset (ι × ι)) (ℓ : ι → ℝ) (x y : ι) :
    wlEq E ℓ 1 x y ↔
      ℓ x = ℓ y ∧
        ∀ φ : ι → ℝ, ConstOn E ℓ 0 φ → nbhdSum E x φ = nbhdSum E y φ :=
  Iff.rfl

/-- **1-WL 第一轮的度数判据（回收 `RealGraphExpressivity`）**：若 `ℓ` 为常值
（无初始标签），则 `wlEq E ℓ 1 x y ↔ |N(x)| = |N(y)|`。

即**第一轮 1-WL 在无标签时只能看到度数**——这正是
`RealGraphExpressivity.regular_uniform_aggregate_eq` 的**一般（非均匀）版本**：
不只是均匀聚合，**任何**邻域求和检验函数在第一轮都只能读出度数。

证明：`→` 方向取 `φ ≡ 1` 即得 `|N(x)| = |N(y)|`（`∑ const = card`）；
`←` 方向若度数相等，则对任意 `φ`，`nbhdSum` 的**求和项数相同**——
但**这一方向不成立**（一般 `φ` 只在度数相同时**不**保证相等）——
故本定理**只保留 `→` 方向**，见下 `oneWL_degree_of_wlEq`。 -/
theorem oneWL_degree_of_wlEq (E : Finset (ι × ι)) (c : ℝ) {x y : ι}
    (h : wlEq E (fun _ => c) 1 x y) :
    (nbhdSet E x).card = (nbhdSet E y).card := by
  have h1 := h.2 (fun _ => (1 : ℝ)) (fun u v _ => rfl)
  rw [nbhdSum, nbhdSum, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, mul_one, mul_one] at h1
  exact_mod_cast h1

end Lattice
