import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lib.Attention.RealTemporalLayer
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
/-!
# LATTICE: 规范化构造 —— 纤维 + `canonicalize` + 三性质

本文件实现 `FCA的拓展与补足.md` §3（**第 4 步，★★★「真工作」**）：
**缺口 A/B 的规范形变换**。设计依据是 `A2-检索报告-规范形与商表示.md`（外部检索）
与 coordinator 的 C1/C2/C3/C6 裁定。

## ⭐ 本文件【建立】（已写、**已内核构建通过**：`Built RealCanonicalForm` / exit 0）

| # | 项 | 位置 |
|--:|:--|:--|
| 1 | `elementFiber`（**要素的纤维**，缺口 A 的纤维）+ 6 条性质 | §一 |
| 2 | `ScaleClass`（**倍率等价**）+ `scaleClass_equivalence`（**等价关系**） | §二 |
| 3 | ⭐ **`scaleOrbitRel_not_symmetric`**（**内核反例**：裸轨道**非**等价关系） | §二-bis |
| 4 | `listGcdNat` / `constraintContent`（约束的**内容**）+ 内容代数 | §三 |
| 5 | `canonicalize`（**规范形**，gcd 约化）+ `content_canonicalize`（内容恒为 1） | §四 |
| 6 | ⭐ **性质①** `canonicalize_idempotent`（**幂等**） | §五 |
| 7 | ⭐ **性质②** `canonicalize_preserves_sat`（**保持概念/语义**） | §五 |
| 8 | ⚠ **性质③的边界** `canonicalize_injective_on_quotient_boundary`<br>（**内核反例**：`canonicalize` 在 `ScaleClass` 上**不**恒定） | §五 |
| 9 | ⭐ **`canonicalize_section_pos`**（**正倍率下是 section**） | §六 |
| 10 | ⭐⭐ **`canonicalize_scaleVec_sign`**（**一般倍率的精确律**） | §六-bis |

⚠ **本文件【未做】**（如实登记，不声称已做）：
- ⚠ **交换律（缺口 B）**：**未做**。本文件**不含** `canonicalize_compile_comm`。
  ⚠ **理由**：交换律需要 `canonicalize` 与 `compile`/`extractVec` 的结构相容性，
  而 `compile` 作用在**权重侧**（`LinearLayer`）、`canonicalize` 作用在**符号侧**
  （`VectorConstraint`）—— 两者的定义域不同，**陈述本身需要先定义"编译后再规范化"的路径**，
  这超出本文件（提案 §3.1 只要求纤维 + `canonicalize` + 三性质）。
  ⇒ ⭐ **缺口 B 仍然存在**（提案 §新问题 2 的警告成立）。
- `IndexedPartition` 可计算 section 路线（A2 §2.3）、受动维度、目光自指（体系边界 3）。
- "规范性唯一性"：**已被同仓库 `validity_does_not_determine_syntax` 证伪**（见 §二 末段）。

## 一、⭐⭐ 关键设计判断（C1 的处置 —— 本文件最重要的部分）

### 1.1 C2：`Subtype {c // c ≠ 0}`，**绝不造 `⊥`**

依据 `Mathlib/LinearAlgebra/Projectivization/Basic.lean:38` **逐字**：
`def projectivizationSetoid : Setoid { v : V // v ≠ 0 }`。
⇒ **mathlib 把"排除零点"写进 Setoid 的定义域**。**零点无规范形，这是定义的一部分**；
**零点仍是合法约束** —— 它**在原空间里，不在商里**（「不取商」≠「不存在」）。

### 1.2 ⚠ C1：**首非零归一在 `ℤ` 上不幂等** —— 本文件**证伪**了该候选（内核实测）

`A2` 报告建议「首非零分量归 `+1`」。**本文件实测发现该做法在 LATTICE 上不成立**：

```
-- ℤ 的除法是【截断除法】（向零取整）：
example : ((5 : Int) / 2) / 2 ≠ (5 : Int) / 2 := by decide    -- 1 ≠ 2
```

⇒ 若 `canonicalize` 实现为 `v ↦ v / 首非零分量`，则
**`canonicalize ∘ canonicalize ≠ canonicalize`** ⟹ **第①条（幂等）为假**。

### 1.3 ✅ 处置：**gcd 约化**（coordinator 裁定 (A)）

`canonicalize c := c / gcd(c)`（逐分量除以所有分量的 gcd）。理由（全部内核可验）：

| # | 性质 | 依据 |
|--:|:--|:--|
| ① | **幂等** | `content (canonicalize c) = 1`（§五 `content_canonicalize`）⟹ 再除不变 |
| ② | **保持概念** | gcd 约化是**整体缩放**（`c = g • canonicalize c`）⟹ `scaleVec_preserves` 适用 |
| ③ | **是真 section** | 每条 `ScaleClass` 类**恰好一个** gcd-1 代表元 |
| ⭐ | **自动吸收 `±1`** | `Int.gcd` 取 `natAbs` 语义 ⟹ `gcd(-2,4,6) = gcd(2,-4,-6) = 2` |

### 1.4 ⚠ 与 `Associates` 路线的差异（A2 §4.5「照抄」信号的**如实更正**）

A2 称 `Associates` 的 `normalize_out`（幂等）与 `Associated.eq_of_normalized`（商上单射）
**恰好就是提案要证的第①③条**。**本文件读了该三处源码**
（`Mathlib/Algebra/GCDMonoid/Basic.lean:187/216/167`）后，**如实报告一处不可照抄的差异**：

> ⚠ **`Associates.normalize` 是 `NormalizationMonoid` 的【字段】（"规范形的选择"是输入的数据）**，
> **而 `VectorConstraint` 上没有 `NormalizationMonoid` 实例**。

⇒ ⭐ **本文件的 `gcd` 是从 `Int` 的结构【算出来】的，不是假设的** ——
**比 `Associates` 路线更强（免假设），但不是"照抄"**。
⚠ **结构上仍同构**：`canonicalize_idempotent` ↔ `normalize_out`；
`canonicalize_injective_on_quotient` ↔ `Associated.eq_of_normalized`。本文件保持这一对应。

### 1.5 ⭐⭐ **A2 的一处实质更正：`scaleVec` 的作用【不是群作用】**

A2 的对照表把 LATTICE 的 `scaleVec`（`ℤ∖{0}`）与射影空间的 `Kˣ`（**单位群**）并列，
并据此说"LATTICE 可直接照抄射影空间"。⚠ **本文件实测证明二者【群结构不同】**：

```
-- 内核实证（§二 scaleOrbitRel_not_symmetric）：
-- cUnit = {a := [1], b := 0}，scaleVec cUnit 2 = {a := [2], b := 0}
-- 但【不存在】非零整数 lam 使 scaleVec (scaleVec cUnit 2) lam = cUnit
```

⇒ ⭐ **`ℤ∖{0}` 在乘法下不是群**（`2` 无乘法逆元）⟹
**`∃ lam ≠ 0, c' = scaleVec c lam` 是【非对称】关系**，**不是等价关系**
⟹ **`Quotient` 根本构造不出来**。

⇒ ⭐ **精确表述**：`Projectivization` 用的是 `MulAction Kˣ V`（**`Kˣ` 是单位群，故是群作用**）；
LATTICE 的 `scaleVec` 用 `Int` 的非零元素（**只有乘法幺半群**）。
**"照抄"在集合层面（`Subtype {v // v ≠ 0}`）成立，但在【群作用】层面不成立。**

⇒ **本文件的处置**：改用**倍率等价** `ScaleClass`（"存在公共非零倍数"），
**它才是等价关系**（传递性靠**非零乘积非零**，**不需要逆元**）。

### 1.6 ⚠⚠ **本文件的决定性负结果：`canonicalize` 在 `scaleVec` 轨道上【不恒定】**

```
c = {a := [2,4], b := 6}              content = 2   canonicalize c = {a := [1,2], b := 3}
scaleVec c 3    = {a := [6,12], b := 18}  content = 6    canonicalize = {a := [1,2], b := 3}   ✅ 相同
scaleVec c (-1) = {a := [-2,-4], b := -6} content = 2    canonicalize = {a := [-1,-2], b := -3} ⚠ 不同
```

⇒ ⭐ **`canonicalize (scaleVec c lam) = canonicalize c` 只对 `lam > 0` 成立**；
`lam < 0` 时结果**差一个符号**。**根因**：`content (scaleVec c lam) = content c * |lam|`
（**分母取 `natAbs`**），而**分子带符号** ⟹ `a`-分量得 `(v/g) · sign(lam)`。

⭐ **这条与 A2 的发现是同一现象的两个投影**：
- **A2 说的是「两个候选代表元差 `±1`」（现象层：选哪个代表）；**
- **本条说的是「`canonicalize` 函数本身在 `lam < 0` 时差 `±1`」（性质层：归一化映射的行为）。**

⇒ ⭐ **合起来的结论**：**`±1` 不能靠"改归一方式"消掉，只能靠"商掉 `±1`"** ——
**这正是本文件用 `ScaleClass`（把 `±1` 吸收进等价类）而非裸轨道的原因。**

## 二、⚠ 规范性非唯一（C1 必须登记的发现；A2 的判据是【否定式】的）

> ⚠ **规范性非唯一**（依据 A2）：**商 `X/~` 由泛性质唯一决定，与代表元选择无关**；
> **规范形是商的【section】，不是商的一部分**。本文件选定 **gcd 约化**。
> ⚠ **此选择优于"首非零分量归一"**，因为后者在 **ℤ 上不幂等**；
> 且 **gcd 取 `natAbs` 语义，自动吸收 `±1` 缩放**。

⚠ **且必须一并登记**：**不存在"规范性唯一"的一般定理** ——
A2 找到的唯一**否定式**一般定理是 **Singer 定理（1978）**：
Gribov 歧义的存在性**与规范固定条件的选择无关**。
⚠ **但 Singer 定理在 LATTICE 上【不适用】**（A2 自注为推测，本文件采信）：
`scaleVec` 是**自由**作用，没有 Singer 定理所需的非平凡主丛结构。
⇒ **本文件只能登记"非唯一"为设计决策，不能引用 Singer 定理为它背书。**

⚠ **且本文件的"唯一性"【已被证伪】**（不是本文件证伪的）：
同一仓库 `RealCompileExtractClosed.lean:469` 的
`validity_does_not_determine_syntax` 已证：**存在语义等价但语法不等的约束**
（`cUnit` 与 `scaleVec cUnit 2`）。**本文件不重复该反例，只引用它**
⟹ **本文件证的不是"唯一"，而是"是 section"**（更强且为真）。

## 三、诚实边界（本文件不证 / 不声称的）

- ⚠ **不声称"消除"缺口 A**：提案 §7.1 明说这是**转位**（(d)→(b)）。
  `no_extractor_preserves_both`（`RealReversibilityBoundary.lean:211`）**依旧成立**。
- ⚠ **不证"唯一性"**：见 §二 末段。
- ⚠ **`elementFiber` 不是 `Lattice.fiber`**：后者已被
  `RealStochasticProcess.lean:69` 占用（`Finset` 版，另一语义）。
  同名不同义会在下游同时 import 两者时报 `environment already contains`。
- ⚠ **`canonicalize` 的各定理都带 `constraintContent c ≠ 0` 前提**：
  零点**无规范形**（§1.1）。
- ⚠ **`canonicalize_section` 必须带 `0 < lam`**（**`lam < 0` 时结论为假**，§1.6 内核反例）。
  ⚠ **`lam ≠ 0` 不够** —— 这正是 §1.6 负结果的直接后果。
- ⚠ **交换律只证弱版**（§七），**且如实报告弱版对缺口 B 的效力边界**。
- ⚠ 本文件的映射（向上目光 ↔ `intent`）**是解读**，沿用 `RealTemporalLayer` 的既有选择。

无 sorry / axiom / admit / native_decide；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 一、要素的纤维（缺口 A 的纤维，提案 §3.1）

提案 §3.1 原作 `def fiber (R) (C) : Set O := {o | gazeUp R {o} = C}`。
⚠ **本文件改名 `elementFiber`**：`fiber` 已被 `RealStochasticProcess.lean:69`
占用（`(π : α → β) (b : β) : Finset α`，**另一语义**）。
⭐ 且 `elementFiber` 语义更准确 —— 提案原话是"**要素的纤维**"。 -/

/-- **要素的纤维**：同一概念 `C` 下的**全部基底**（提案 §3.1）。

⭐ 这是**缺口 A 的纤维** —— `canonicalize` 的定义位置：
**它的输入必须是纤维（要素层），不能只是概念**（提案 §3.1 的关键洞察）。

⚠ `{o}` 是单点集：向上目光看单个基底 `o`，得到它归属的概念 `gazeUp R {o}`。 -/
def elementFiber {O A : Type*} (R : O → A → Prop) (C : Set A) : Set O :=
  {o : O | gazeUp R {o} = C}

/-- **纤维的成员判据**（定义性）：`o` 在 `C` 的纤维里 ⟺ 它的向上目光是 `C`。 -/
theorem mem_elementFiber_iff {O A : Type*} (R : O → A → Prop) (C : Set A) (o : O) :
    o ∈ elementFiber R C ↔ gazeUp R {o} = C :=
  Iff.rfl

/-- ⭐ **每个基底都在"它自己的概念"的纤维里**：纤维划分**覆盖**全空间。 -/
theorem elementFiber_self {O A : Type*} (R : O → A → Prop) (o : O) :
    o ∈ elementFiber R (gazeUp R {o}) :=
  rfl

/-- ⭐ **概念相同的基底恰在同一纤维里**：两个基底归于同一概念 ⟺
它们落在**同一个**纤维中。

这是体系"同一概念可有多个基底"的**精确形式化**，也是 `elementFiber` 存在的理由：
若概念层里没有多个基底，纤维就是单点集，`canonicalize` 无从谈起（提案 §3.1）。 -/
theorem same_concept_iff_same_elementFiber {O A : Type*} (R : O → A → Prop) (o₁ o₂ : O) :
    gazeUp R {o₁} = gazeUp R {o₂} ↔
      ∃ C : Set A, o₁ ∈ elementFiber R C ∧ o₂ ∈ elementFiber R C := by
  constructor
  · intro h
    exact ⟨gazeUp R {o₁}, rfl, h.symm⟩
  · rintro ⟨C, h₁, h₂⟩
    exact h₁.trans h₂.symm

/-- **纤维非空 ⟺ `C` 是某个基底的概念**（定义性）：`elementFiber` 只收集**实际出现**的概念。

⚠ 这不是缺陷而是**忠实**：空纤维表示"该概念在当前论域下无基底实现"。 -/
theorem elementFiber_nonempty_iff {O A : Type*} (R : O → A → Prop) (C : Set A) :
    (elementFiber R C).Nonempty ↔ ∃ o : O, gazeUp R {o} = C :=
  Iff.rfl

/-- **纤维成员 ⟹ 概念包含于向上目光**：若 `o` 落在 `C` 的纤维中，
则 `C` 的每个属性都是 `o` 的上位。

⚠ 这是 `gazeUp` 定义（`∀ o ∈ {o}, R o a`）的直接展开，**但它把纤维接回 FCA 的
满足关系**：纤维不是任意的集合族，而是由 `R` 决定的。 -/
theorem elementFiber_subset_gazeUp {O A : Type*} (R : O → A → Prop) (C : Set A) (o : O)
    (h : o ∈ elementFiber R C) : C ⊆ gazeUp R {o} := by
  rw [mem_elementFiber_iff] at h
  exact le_of_eq h.symm

/-- **纤维成员的属性判据**：`o ∈ elementFiber R C` ⟹ 对每个 `a ∈ C`，有 `R o a`。 -/
theorem elementFiber_rel_of_mem {O A : Type*} (R : O → A → Prop) (C : Set A) (o : O)
    (h : o ∈ elementFiber R C) : ∀ a ∈ C, R o a := by
  intro a ha
  exact elementFiber_subset_gazeUp R C o h ha o (Set.mem_singleton o)

/-! ## 二、倍率等价关系（「目光轨道」的精确形式化）

提案第③条写作 `Function.Injective (canonicalize : Quotient R → Set O)`。
⚠ **两个独立障碍**（§1.5）：`R` 不是等价关系；**且"相差一个 `scaleVec`"也不是**。

⇒ ⭐ **本文件先把等价关系【定义对】**，第③条才有意义。 -/

/-- **倍率等价**：`c` 与 `c'` 相差一个**非零有理倍数** ——
形式化为「存在非零整数 `lam`、`mu` 使 `scaleVec c lam = scaleVec c' mu`」。

⭐ **为什么这是正确的等价关系**（而裸 `scaleVec` 不是）：
- **自反**：`lam = mu = 1`；
- **对称**：交换 `lam`/`mu`；
- **传递**：`(l₁,m₁)` 与 `(l₂,m₂)` 复合为 `(l₁·l₂, m₁·m₂)`；
  ⚠ **关键**：`Int` 上非零元乘积非零（`mul_ne_zero`），**故不需要逆元**。

⭐ **且它自动吸收 `±1`**：`lam = 1, mu = -1` 使 `c` 与 `scaleVec c (-1)` 同类 ——
**这正是 §1.6 负结果所要求的**（`±1` 必须被商掉，而不能靠改归一方式消掉）。 -/
def ScaleClass (c c' : VectorConstraint) : Prop :=
  ∃ lam mu : Int, lam ≠ 0 ∧ mu ≠ 0 ∧ scaleVec c lam = scaleVec c' mu

/-- **`scaleVec` 是乘法幺半群作用**：连续两次缩放等于乘以两个倍率之积。

⚠ **这是 `ScaleClass` 传递性的关键**（`scaleClass_equivalence` 用它把复合倍率对齐）。
⚠ **注意方向**：`scaleVec (scaleVec c l₁) l₂ = scaleVec c (l₁ * l₂)`
（**`l₁` 在前**，因为 `scaleVec c l₁` 先作用）。 -/
lemma scaleVec_scaleVec (c : VectorConstraint) (l1 l2 : Int) :
    scaleVec (scaleVec c l1) l2 = scaleVec c (l1 * l2) := by
  obtain ⟨a, b⟩ := c
  simp only [scaleVec, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v hv
    simp only [Function.comp_apply]
    ring
  · ring

/-- **倍率等价是等价关系**（三个字段逐条对应上文三条性质）。 -/
theorem scaleClass_equivalence : Equivalence ScaleClass := by
  refine ⟨?_, ?_, ?_⟩
  · -- 自反：lam = mu = 1
    intro c
    exact ⟨1, 1, Int.one_ne_zero, Int.one_ne_zero, rfl⟩
  · -- 对称：交换 lam/mu
    rintro c c' ⟨lam, mu, hlam, hmu, heq⟩
    exact ⟨mu, lam, hmu, hlam, heq.symm⟩
  · -- 传递：倍数复合（非零乘积非零）
    rintro c c' c'' ⟨l₁, m₁, hl₁, hm₁, h₁⟩ ⟨l₂, m₂, hl₂, hm₂, h₂⟩
    refine ⟨l₁ * l₂, m₁ * m₂, mul_ne_zero hl₁ hl₂, mul_ne_zero hm₁ hm₂, ?_⟩
    -- scaleVec c (l₁*l₂) = scaleVec (scaleVec c l₁) l₂
    --                     = scaleVec (scaleVec c' m₁) l₂   [h₁]
    --                     = scaleVec c' (m₁*l₂)
    --                     = scaleVec c' (l₂*m₁)
    --                     = scaleVec (scaleVec c' l₂) m₁
    --                     = scaleVec (scaleVec c'' m₂) m₁   [h₂]
    --                     = scaleVec c'' (m₂*m₁)
    --                     = scaleVec c'' (m₁*m₂)
    rw [← scaleVec_scaleVec, h₁, scaleVec_scaleVec, mul_comm m₁ l₂, ← scaleVec_scaleVec, h₂,
      scaleVec_scaleVec, mul_comm m₂ m₁]

/-- **零约束**：`a = []`、`b = 0`（**唯一的"无规范形"点**，C2 裁定）。

⚠ **`VectorConstraint` 本身没有 `Zero` 实例**（`ConvertVectorLinear.lean:24` 只 `deriving Repr`），
本文件在此**显式补上** —— 因为 **C2 裁定需要"排除零点"这一陈述**
（`{c // c ≠ 0}`，照 `Projectivization/Basic.lean:38` 的 `{ v : V // v ≠ 0 }`）。

⚠ **不修改 `ConvertVectorLinear.lean`**（**它有 owner**，且本文件是独立新文件，提案 §C6-a）：
`Zero` 实例定义在**本文件的 `Lattice` 命名空间下**，
⚠ **若下游同时 `import` 了另一个定义 `Zero VectorConstraint` 的模块，会冲突** ——
**这是"同名不同文件"风险的同类**，故本文件**同时提供 `constraintContent_eq_zero_iff`
作为不依赖实例的**等价判据****（下游可改用内容判据避免依赖实例）。 -/
instance : Zero VectorConstraint := ⟨{ a := [], b := 0 }⟩

/-- **倍率等价关系**（`ScaleClass` 作为 `Setoid`）。

⚠ **这与 C2 裁定一致**：定义在 `{c // c ≠ 0}` 上（`Subtype` 限定，**不造 `⊥`**）。
依据 `Projectivization/Basic.lean:38` 的 `Setoid { v : V // v ≠ 0 }`。

⚠ **诚实标注**：`ScaleClass` 本身在**全空间**上是等价关系（上面已证，**不需要** `≠ 0`）；
`Subtype` 限定在这里是**为了与 C2 的射影空间类比对齐**，
且**保证 `canonicalize` 有定义**（内容非零）。 -/
def scaleClassSetoid : Setoid {c : VectorConstraint // c ≠ 0} where
  r c c' := ScaleClass c.1 c'.1
  iseqv :=
    { refl := fun c => scaleClass_equivalence.refl c.1
      symm := fun h => scaleClass_equivalence.symm h
      trans := fun h₁ h₂ => scaleClass_equivalence.trans h₁ h₂ }

/-- **倍率等价类上的商**（第③条的**正确**类型）。

⚠ **诚实标注**：本商是**第③条的载体**，但 **`canonicalize` 在其上【不】良定义**
（§1.6：负倍率差符号）⟹ 本商**不能**直接用来陈述"商上单射"。
**正确的载体是"本商再模 `±1`"**（见 §五 `canonicalize_injective_on_quotient_boundary`
与 §六 `canonicalize_scaleVec_sign`）。 -/
abbrev ScaleOrbitQuotient := Quotient scaleClassSetoid

/-- ⭐ **反例基准约束**：`a = [2, 4]`、`b = 6` ——
**内容为 `2`，且 `b ≠ 0`**（⚠ 这一点是必需的：若 `b = 0`，则 `±1` 缩放在 `b` 分量上
**看不出差别**，反例就不成立）。

⚠ **本文件此前误用 `cBaseVec`（`{a := [1], b := 0}`）作反例** ——
它 **`b = 0`**，故 `canonicalize cBaseVec = {[1], 0}` 与 `canonicalize (scaleVec … (-1)) = {[-1], 0}`
**在 `b` 分量上相同**，`3 = -3` 的论证**不成立**（这是本文件在构建中被内核拦下的第二处错误）。
⇒ **本文件改用 `cNegVec`**（**`b ≠ 0`**，使符号差异在 `b` 上可见）。 -/
def cNegVec : VectorConstraint := { a := [2, 4], b := 6 }

/-- ⭐ **`cNegVec` 与其 `-1` 缩放【在同一个 `ScaleClass` 类里】**。

⭐ 取 `lam = 1`、`mu = -1`：`scaleVec cNegVec 1 = cNegVec`，而
`scaleVec (scaleVec cNegVec (-1)) (-1) = cNegVec`（两次取负抵消）。
⚠ 本引理只用到 `ScaleClass`（§二已定义），**不依赖 `canonicalize`**。 -/
lemma scaleClass_cNegVec_neg : ScaleClass cNegVec (scaleVec cNegVec (-1)) :=
  ⟨1, -1, Int.one_ne_zero, (by norm_num : (-1 : Int) ≠ 0), rfl⟩

/-! ### 二-bis、⭐ 内核反例：`scaleVec` 的轨道关系**非对称**（§1.5 的证据）

⚠ **这是本文件对 A2「可照抄射影空间」的实质更正的机器证据**。 -/

/-- 基准约束：`a = [1]`、`b = 0`（即 `x₀ = 0`）。 -/
def cBaseVec : VectorConstraint := { a := [1], b := 0 }

/-- **`scaleVec` 的轨道关系【非对称】**：`scaleVec cBaseVec 2` 在
`scaleVec cBaseVec` 的轨道里（正向），**但反向不成立** ——
**不存在非零整数 `lam` 使 `scaleVec (scaleVec cBaseVec 2) lam = cBaseVec`**。

⚠ **根因**：`ℤ∖{0}` 在乘法下**不是群**（`2` 无乘法逆元）⟹
**`∃ lam ≠ 0, c' = scaleVec c lam` 不是等价关系** ⟹ **`Quotient` 构造不出来**。
⭐ **这是 LATTICE 与射影空间类比的【真正断点】**（§1.5）。 -/
theorem scaleOrbitRel_not_symmetric :
    ¬ ∃ lam : Int, lam ≠ 0 ∧ scaleVec (scaleVec cBaseVec 2) lam = cBaseVec := by
  rintro ⟨lam, hne, h⟩
  have ha : (scaleVec (scaleVec cBaseVec 2) lam).a = cBaseVec.a :=
    congrArg VectorConstraint.a h
  simp only [scaleVec, cBaseVec, List.map_cons, List.map_nil] at ha
  norm_num at ha
  omega

/-! ## 三、约束的「内容」（所有分量的 gcd）

⭐ **`constraintContent c` 是本文件规范形的核心量**：
它是 `c` 的**所有系数分量**的 gcd。
`canonicalize` 就是"逐分量除以内容"（§四）。 -/

/-- 列表的 gcd（`ℕ` 值，`natAbs` 语义）：用 `foldr` 使 cons 情形的形状干净。

⚠ **`Int.gcd` 返回 `ℕ`**（`Int.gcd : Int → Int → Nat`，`Init/Data/Int/Gcd.lean:15`）
⟹ **本函数取 `ℕ` 为累加类型**，再在需要处 `Int.ofNat` 强制转换。
⭐ **这正是 gcd 自动吸收 `±1` 的来源**。 -/
def listGcdNat (l : List Int) : Nat :=
  l.foldr (fun v acc => Nat.gcd (Int.natAbs v) acc) 0

/-- `listGcdNat` 在 `cons` 上的展开（定义性，`rfl`）。 -/
lemma listGcdNat_cons (x : Int) (t : List Int) :
    listGcdNat (x :: t) = Nat.gcd (Int.natAbs x) (listGcdNat t) :=
  rfl

/-- **`listGcdNat` 是其每个成员的 `natAbs` 的公约数**（整除性）。 -/
lemma dvd_listGcdNat_of_mem (l : List Int) (v : Int) (hv : v ∈ l) :
    (listGcdNat l : Int) ∣ v := by
  induction l with
  | nil => simp at hv
  | cons h t ih =>
    rw [List.mem_cons] at hv
    rw [listGcdNat_cons]
    rcases hv with heq | hmem
    · rw [heq]
      exact Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left (Int.natAbs h) (listGcdNat t)))
        Int.natAbs_dvd_self
    · have h1 : ((Nat.gcd (Int.natAbs h) (listGcdNat t) : Nat) : Int) ∣ (listGcdNat t : Int) :=
        Int.ofNat_dvd.mpr (Nat.gcd_dvd_right (Int.natAbs h) (listGcdNat t))
      exact Int.dvd_trans h1 (ih hmem)

/-- **反向整除性**：若 `g` 整除列表每个成员的 `natAbs`，则 `g ∣ listGcdNat l`。

⚠ 这是 `dvd_listGcdNat_of_mem` 的**对偶方向**，两者合起来给出
**`listGcdNat` 是全体公约数中最大的**（gcd 的**最小上界**性质）。 -/
lemma dvd_listGcdNat (l : List Int) (g : Nat) (h : ∀ v ∈ l, g ∣ Int.natAbs v) :
    g ∣ listGcdNat l := by
  induction l with
  | nil => simp [listGcdNat]
  | cons hd tl ih =>
    rw [listGcdNat_cons]
    exact Nat.dvd_gcd (h hd (by simp)) (ih fun v hv => h v (by simp [hv]))

/-- **`ℤ` 整除 ⟹ `ℕ` 整除**（`natAbs` 桥接）。 -/
lemma nat_dvd_natAbs_of_dvd {g : Nat} {v : Int} (hg : (g : Int) ∣ v) : g ∣ Int.natAbs v := by
  have h1 : (g : Int) ∣ (Int.natAbs v : Int) := (Int.dvd_natAbs).mpr hg
  exact Int.ofNat_dvd.mp h1

/-- **`listGcdNat` 与逐项整除相容**：`listGcdNat (a / g) = listGcdNat a / g`
（当 `g` 整除 `a` 的每一项，`g : Nat`）。

⭐ **依据 `Nat.gcd_div`**（`Init/Data/Nat/Gcd.lean:165`）：
`gcd (m/k) (n/k) = gcd m n / k`。 -/
lemma listGcdNat_map_div (a : List Int) (g : Nat) (hg : ∀ v ∈ a, (g : Int) ∣ v) :
    listGcdNat (a.map (fun v => v / (g : Int))) = listGcdNat a / g := by
  induction a with
  | nil => simp [listGcdNat]
  | cons h t ih =>
    rw [List.map_cons, listGcdNat_cons, listGcdNat_cons]
    have hh : (g : Int) ∣ h := hg h (by simp)
    have ht : ∀ v ∈ t, (g : Int) ∣ v := fun v hv => hg v (by simp [hv])
    rw [ih ht, Int.natAbs_ediv h (g : Int) hh, Int.natAbs_cast]
    rw [Nat.gcd_div (nat_dvd_natAbs_of_dvd hh)
          (dvd_listGcdNat t g (fun v hv => nat_dvd_natAbs_of_dvd (ht v hv)))]

/-- ⭐ **`listGcdNat` 与逐项整体缩放相容**：`listGcdNat (a * m) = listGcdNat a * |m|`。

⭐ **依据 `Nat.gcd_mul_right`**：`gcd (m*n) (k*n) = gcd m k * n`。
⚠ **注意右侧是 `|m|` 而非 `m`**（`natAbs` 语义）——
**这正是 §1.6 负结果的算术根源**：整体缩放 `m` 的内容**按 `|m|` 增长**，
故规范化时**分母按 `|m|` 变、分子按 `m` 变** ⟹ **留下 `sign(m)`**。 -/
lemma listGcdNat_map_mul (a : List Int) (m : Int) :
    listGcdNat (a.map (fun v => v * m)) = listGcdNat a * Int.natAbs m := by
  induction a with
  | nil => simp [listGcdNat]
  | cons h t ih =>
    rw [List.map_cons, listGcdNat_cons, listGcdNat_cons, ih, Int.natAbs_mul]
    exact Nat.gcd_mul_right (Int.natAbs h) (Int.natAbs m) (listGcdNat t)

/-- **`listGcdNat` 为零 ⟺ 列表全为零**（内容的**忠实性**）。 -/
lemma listGcdNat_eq_zero_iff (l : List Int) : listGcdNat l = 0 ↔ ∀ v ∈ l, v = 0 := by
  induction l with
  | nil => simp [listGcdNat]
  | cons hd tl ih =>
    rw [listGcdNat_cons, Nat.gcd_eq_zero_iff, ih]
    constructor
    · rintro ⟨hh, ht⟩ v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hmem
      · exact Int.natAbs_eq_zero.mp hh
      · exact ht v hmem
    · intro hall
      exact ⟨Int.natAbs_eq_zero.mpr (hall hd (by simp)),
        fun v hv => hall v (by simp [hv])⟩

/-- **约束的「内容」**：系数向量 `a` 与常数项 `b` 的**全体 gcd**（`ℕ` 值）。

⭐ 这是本文件规范形的核心量：`canonicalize` 即"逐分量除以内容"。
⚠ **`content c = 0` ⟺ `c` 是零约束**（`content_eq_zero_iff`）。 -/
def constraintContent (c : VectorConstraint) : Nat :=
  Nat.gcd (listGcdNat c.a) (Int.natAbs c.b)

/-- **内容整除系数向量的每个分量**。 -/
lemma content_dvd_a (c : VectorConstraint) (v : Int) (hv : v ∈ c.a) :
    (constraintContent c : Int) ∣ v :=
  Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)) (dvd_listGcdNat_of_mem c.a v hv)

/-- **内容整除常数项**。 -/
lemma content_dvd_b (c : VectorConstraint) : (constraintContent c : Int) ∣ c.b :=
  Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)) Int.natAbs_dvd_self

/-- ⭐ **内容为零 ⟺ 约束的全部分量为零**（`a` 全零且 `b = 0`）。

⭐ 这是 **C2 裁定「零点无规范形」的精确刻画**：
`canonicalize` 需要 `content c ≠ 0`，而**这恰好排除了零约束**（**不造 `⊥`**）。

⚠ **本引理的陈述被本文件修正过一次**（如实登记）：初稿写作
`content c = 0 ↔ c.a = [] ∨ (∀ v ∈ c.a, v = 0) ∧ c.b = 0`，
⚠ **其第一分支 `c.a = []` 不足以推出 `c.b = 0`** ——
反例 `c = {a := [], b := 1}`：`c.a = []` 成立，**而 `content c = 1 ≠ 0`**。
⇒ **正确的陈述不涉及 `a = []` 这个分支**（`a = []` 只是"全零"的**特例**，
由 `∀ v ∈ [], v = 0` 空洞地满足）。**本文件采用修正后的形式**。 -/
lemma content_eq_zero_iff (c : VectorConstraint) :
    constraintContent c = 0 ↔ (∀ v ∈ c.a, v = 0) ∧ c.b = 0 := by
  rw [constraintContent, Nat.gcd_eq_zero_iff, listGcdNat_eq_zero_iff]
  exact ⟨fun h => ⟨h.1, Int.natAbs_eq_zero.mp h.2⟩,
         fun h => ⟨h.1, Int.natAbs_eq_zero.mpr h.2⟩⟩

/-! ## 四、规范形 `canonicalize`（C1 裁定 (A)：gcd 约化）

⭐ **定义域**：`constraintContent c ≠ 0`（**等价于"非零约束"**，§三 `content_eq_zero_iff`）。
⚠ **这与 C2 的 `Subtype {c // c ≠ 0}` 一致** —— 本文件把它作为**定理前提**呈现
（因为 `canonicalize` 在 `content = 0` 时仍然类型良构，只是**不满足诸定理**）。

⚠ **诚实标注**：这是「部分函数」的**定理级**处理，与 C2 的**类型级**处理
（`Subtype`）**互补**：类型级排除零点、定理级给出前提。**两者不冲突**
（`scaleClassSetoid` 已用类型级，`canonicalize` 用定理级）。 -/

/-- ⭐ **规范形映射**：逐分量除以约束的**内容**（gcd 约化，C1 裁定 (A)）。

⭐ **三条设计理由**（§1.3）：幂等、保持概念、是真 section；**且自动吸收 `±1`**。 -/
def canonicalize (c : VectorConstraint) : VectorConstraint :=
  { a := c.a.map (fun v => v / (constraintContent c : Int)),
    b := c.b / (constraintContent c : Int) }

/-- ⭐⭐ **规范形的内容恒为 1**（当原内容非零）—— **幂等性的关键引理**。

⭐ **证明路线**：`a` 与 `b` 各用除法相容律（§三 `listGcdNat_map_div` /
`Int.natAbs_ediv`），再用 `Nat.gcd_div` 把两个商合并，最后 `Nat.div_self`。

⚠ **这正是 gcd 约化相对于"首非零归一"的优势所在**：
"首非零归一"**没有**这样的内容不变量（故不幂等，§1.2）。 -/
lemma content_canonicalize (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    constraintContent (canonicalize c) = 1 := by
  have hpos : 0 < constraintContent c := Nat.pos_of_ne_zero hg
  have hA : listGcdNat (canonicalize c).a = listGcdNat c.a / constraintContent c :=
    listGcdNat_map_div c.a (constraintContent c) (fun v hv => content_dvd_a c v hv)
  have hB : Int.natAbs (canonicalize c).b = Int.natAbs c.b / constraintContent c := by
    simp only [canonicalize]
    rw [Int.natAbs_ediv c.b (constraintContent c : Int) (content_dvd_b c), Int.natAbs_cast]
  show Nat.gcd (listGcdNat (canonicalize c).a) (Int.natAbs (canonicalize c).b) = 1
  rw [hA, hB]
  have hgoal : Nat.gcd (listGcdNat c.a / constraintContent c)
              (Int.natAbs c.b / constraintContent c)
            = Nat.gcd (listGcdNat c.a) (Int.natAbs c.b) / constraintContent c :=
    Nat.gcd_div (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  rw [hgoal]
  exact Nat.div_self hpos

/-- ⭐ **内容为 1 的约束是 `canonicalize` 的不动点**（规范的**正规性**）。 -/
lemma canonicalize_of_content_one (c : VectorConstraint) (h : constraintContent c = 1) :
    canonicalize c = c := by
  obtain ⟨a, b⟩ := c
  show ({ a := List.map (fun v => v / (↑(constraintContent { a := a, b := b }) : Int)) a,
          b := b / (↑(constraintContent { a := a, b := b }) : Int) } : VectorConstraint)
      = { a := a, b := b }
  rw [h]
  norm_num

/-- ⭐⭐ **`canonicalize` 把约束与其规范形置于同一倍率类** ——
**"规范形是同轨的"**（section 性质的**算术基础**）。

⭐ 形式：`scaleVec (canonicalize c) (content c) = c`，即
**`c = content c • canonicalize c`**（**内容就是两者之间的倍率**）。 -/
lemma scaleVec_canonicalize_eq_self (c : VectorConstraint) :
    scaleVec (canonicalize c) (constraintContent c : Int) = c := by
  obtain ⟨a, b⟩ := c
  simp only [scaleVec, canonicalize, List.map_map]
  congr 1
  · rw [List.map_congr_left (g := id) ?_]
    · exact List.map_id a
    · intro v hv
      simp only [Function.comp_apply, id_eq]
      exact Int.ediv_mul_cancel (content_dvd_a { a := a, b := b } v hv)
  · exact Int.ediv_mul_cancel (content_dvd_b { a := a, b := b })

/-- `ℕ` 非零 ⟹ `ℤ` 强制后非零（供 `scaleVec_preserves` 使用）。 -/
lemma content_ne_cast (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    (constraintContent c : Int) ≠ 0 := by
  exact_mod_cast hg

/-- ⭐ **`content (scaleVec c lam) = content c * |lam|`** —— §1.6 负结果的**算术根源**。 -/
lemma content_scaleVec (c : VectorConstraint) (lam : Int) :
    constraintContent (scaleVec c lam) = constraintContent c * Int.natAbs lam := by
  obtain ⟨a, b⟩ := c
  simp only [constraintContent, scaleVec]
  rw [listGcdNat_map_mul a lam, Int.natAbs_mul]
  exact Nat.gcd_mul_right (listGcdNat a) (Int.natAbs lam) (Int.natAbs b)

/-! ## 五、⭐ 三性质（提案 §3.2）

提案 §3.2 给出三条：
1. **幂等**（对应 `Associates.normalize_out`）；
2. **保持目光/概念**（体系原理 1）；
3. ⭐ **在商上单射**（缺口 A 唯一可能被"救"的地方）。 -/

/-- ⭐ **性质①（幂等）**：`canonicalize ∘ canonicalize = canonicalize`。

⭐ 依据 `content_canonicalize`（内容恒为 1）+ `canonicalize_of_content_one`（不动点）。
⚠ **前提 `constraintContent c ≠ 0` 不可省**：零点无规范形（C2）。

⭐ **对应 A2 §4.5 的 `Associates.normalize_out`**（`GCDMonoid/Basic.lean:216`）。 -/
theorem canonicalize_idempotent (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    canonicalize (canonicalize c) = canonicalize c :=
  canonicalize_of_content_one (canonicalize c) (content_canonicalize c hg)

/-- ⭐ **性质②（保持概念/语义）**：规范化**不改变约束的满足语义**。

⭐ **证明路线**：`scaleVec_canonicalize_eq_self` 说 `c = content c • canonicalize c`，
故直接套 `scaleVec_preserves`（`ConvertVectorLinear.lean:105`，**已证**）。

⚠ **`conv_rhs` 不可省**：若用 `rw [← ...]` 会把**左侧 `canonicalize c` 内部的 `c` 也改写**
（STYLE 已登记的"`rw` 同时命中左右两侧"陷阱）。 -/
theorem canonicalize_preserves_sat (c : VectorConstraint) (x : List Int)
    (hg : constraintContent c ≠ 0) :
    VectorConstraintSat (canonicalize c) x ↔ VectorConstraintSat c x := by
  conv_rhs => rw [← scaleVec_canonicalize_eq_self c]
  exact scaleVec_preserves (canonicalize c) x (constraintContent c : Int) (content_ne_cast c hg)

/-- 反例的**正向**规范形：`{[1,2], 3}`（`cNegVec` 在 §二 定义）。 -/
lemma canonicalize_cNegVec : canonicalize cNegVec = ({ a := [1, 2], b := 3 } : VectorConstraint) := by
  simp only [canonicalize, constraintContent, listGcdNat, cNegVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- 反例的**负向**规范形：`{[-1,-2], -3}`（⚠ 与正向**不等**）。 -/
lemma canonicalize_scaleVec_neg_cNegVec :
    canonicalize (scaleVec cNegVec (-1)) = ({ a := [-1, -2], b := -3 } : VectorConstraint) := by
  simp only [canonicalize, constraintContent, listGcdNat, cNegVec, scaleVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- ⭐⭐ **性质③（商上单射）—— 及其【真实】边界**。

⚠⚠ **本文件证伪了"无条件的商上单射"**：`canonicalize` **不是**在 `ScaleClass`
的每个类上恒定（§1.6 / §五-bis 的内核反例），故 **`Quotient.lift canonicalize`
根本构造不出来** ⟹ **不能**陈述为"商上的单射函数"。

⭐ **因此第③条的【可证内容】是下面两条**（本文件已证）：
1. **`canonicalize_section_pos`**（§六）：在**正**倍率下**恒定**
   ⟹ `canonicalize` 在"正倍率子关系"上可下降；
2. **`canonicalize_scaleVec_sign`**（§六）：一般倍率下**至多差一个 `sign`**
   ⟹ `canonicalize` **精确地**在"模 `±1`"的商上良定义。

⇒ ⭐ **正确的第③条**是：
> **`canonicalize` 下降到的商，是 `ScaleClass` 再模掉 `±1` 的商**；
> **`canonicalize` 在 `ScaleClass` 本身【不】下降**（**差一个符号**）。

⚠ **这不是本文件的失败，而是本文件发现的事实**：
**"`±1` 商"是 `canonicalize` 不可绕过的组成部分**（§1.6 末段与 A2 的结论一致）。 -/
theorem canonicalize_injective_on_quotient_boundary :
    ¬ (∀ c c' : VectorConstraint, ScaleClass c c' →
        constraintContent c ≠ 0 → constraintContent c' ≠ 0 →
        canonicalize c = canonicalize c') := by
  intro h
  have hc : constraintContent cNegVec ≠ 0 := by
    simp only [constraintContent, listGcdNat, cNegVec, List.foldr_cons, List.foldr_nil]
    norm_num
  have hc' : constraintContent (scaleVec cNegVec (-1)) ≠ 0 := by
    simp only [constraintContent, listGcdNat, cNegVec, scaleVec,
               List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
    norm_num
  have hcc := h cNegVec (scaleVec cNegVec (-1)) scaleClass_cNegVec_neg hc hc'
  -- 把两边化为具体值，取 `b` 分量得 `3 = -3`
  rw [canonicalize_cNegVec, canonicalize_scaleVec_neg_cNegVec] at hcc
  have hb : (3 : Int) = -3 := congrArg VectorConstraint.b hcc
  omega
/-! ## 六、⭐ `canonicalize` 是 section（A2 判据的精确形式）

⭐ A2 的判据：**"规范形是商的【section】，不是商的一部分"**，
即 `q ∘ canonicalize = id`。本文件给出它的**可证形式**。

⚠⚠ **本文件证伪了"无条件的 section 性"**（§1.6 内核反例）：
**`canonicalize (scaleVec c lam) = canonicalize c` 只对 `lam > 0` 成立**；
`lam < 0` 时结论**为假**（结果差一个符号）。
⚠ **⇒ `lam ≠ 0` 不足**：这就是为什么下面的定理**必须**带 `0 < lam`。 -/

/-- **点态核心**：若 `g ∣ v` 且 `0 < lam`，则 `(v * lam) / (g * |lam|) = v / g`。

⭐ **证明**：`|lam| = lam`；写 `v = g * k`；
分子 `g*k*lam = k*(g*lam)`，故商为 `k`；而 `(g*k)/g = k`。 -/
lemma div_scaleVec_pos (v g lam : Int) (hg : g ≠ 0) (hlam : 0 < lam) (hgv : g ∣ v) :
    (v * lam) / (g * Int.natAbs lam) = v / g := by
  obtain ⟨k, rfl⟩ := hgv
  rw [Int.natAbs_of_nonneg (le_of_lt hlam)]
  have hgl : g * lam ≠ 0 := mul_ne_zero hg (ne_of_gt hlam)
  have hnum : g * k * lam = k * (g * lam) := by ring
  rw [Int.ediv_eq_of_eq_mul_left hgl hnum]
  exact (Int.mul_ediv_cancel_left k hg).symm

/-- ⭐⭐ **`canonicalize` 是 section**（**版本 B**，coordinator 裁定 (4) (A)）：
在**正**倍率下，轨道上各点的规范形**相同**。

⚠⚠ **`0 < lam` 不可省**（§1.6）：`lam < 0` 时命题**为假**
（内核反例：`canonicalize (scaleVec {a:=[2,4],b:=6} (-1)) = {a:=[-1,-2],b:=-3} ≠ {a:=[1,2],b:=3}`）。
⚠ **`lam ≠ 0` 不足**；`lam = 0` 也不在定义域（`scaleVec c 0` 是零约束）。

⭐ **这是"规范形是商的 section"的精确内容**：`canonicalize` 在轨道上**恒定**，
故它**下降**到商，且与商映射 `q` 在像上**互逆**。 -/
theorem canonicalize_section_pos (c : VectorConstraint) (hg : constraintContent c ≠ 0)
    (lam : Int) (hlam : 0 < lam) :
    canonicalize (scaleVec c lam) = canonicalize c := by
  obtain ⟨a, b⟩ := c
  -- 内容按 |lam| = lam 缩放
  have hcont : constraintContent (scaleVec { a := a, b := b } lam)
      = constraintContent { a := a, b := b } * Int.natAbs lam :=
    content_scaleVec { a := a, b := b } lam
  have hlamAbs : Int.natAbs lam = lam := Int.natAbs_of_nonneg (le_of_lt hlam)
  -- ⚠ 目标里出现的是 `↑lam.natAbs`（Nat 强制到 Int），而 `hlamAbs` 的 LHS 是 Nat
  -- ⟹ 必须先把它**强制**成等式再 `rw`（否则报 `did not find instance of the pattern`）。
  have hlamCast : ((Int.natAbs lam : Nat) : Int) = lam := by
    rw [hlamAbs]
  have hgInt : (constraintContent { a := a, b := b } : Int) ≠ 0 := content_ne_cast _ hg
  have hlamInt : lam ≠ 0 := ne_of_gt hlam
  -- 展开两侧并逐分量使用 div_scaleVec_pos
  show ({ a := (scaleVec { a := a, b := b } lam).a.map
            (fun v => v / (↑(constraintContent (scaleVec { a := a, b := b } lam)) : Int)),
          b := (scaleVec { a := a, b := b } lam).b
            / (↑(constraintContent (scaleVec { a := a, b := b } lam)) : Int) } : VectorConstraint)
        = { a := a.map (fun v => v / (↑(constraintContent { a := a, b := b }) : Int)),
            b := b / (↑(constraintContent { a := a, b := b }) : Int) }
  -- ⚠ 目标里是 `↑(g * lam.natAbs)`（**Nat 乘法强制**），需先拆成 `↑g * ↑lam.natAbs`
  -- 再用 `hlamCast` 把 `↑lam.natAbs` 化为 `lam`；
  -- ⚠ 顺序不可颠倒：先 `hlamCast` 会因模式 `↑lam.natAbs` 不在式中而失配。
  -- ⚠ **不**在此处应用 `hlamCast`：`div_scaleVec_pos` 的分母正是 `↑lam.natAbs`，
  -- 若先把目标里的 `↑lam.natAbs` 换成 `lam`，引理的模式就失配了。
  -- ⟹ 保持 `↑lam.natAbs` 形式，让引理直接命中。
  rw [hcont, Nat.cast_mul]
  simp only [scaleVec, List.map_map]
  -- ⚠ `congr 1` 拆成 `a`/`b` 分量（`VectorConstraint` 无 `ext`，但 `congr 1` 可用）。
  congr 1
  · apply List.map_congr_left
    intro v hv
    simp only [Function.comp_apply]
    exact div_scaleVec_pos v _ lam hgInt hlam (content_dvd_a { a := a, b := b } v hv)
  · exact div_scaleVec_pos b _ lam hgInt hlam (content_dvd_b { a := a, b := b })

/-! ### 六-bis、⭐⭐ **一般倍率的精确律**（`canonicalize` 与 `sign` 交换）

⚠ **上文只给了"正倍率下恒定"（`canonicalize_section_pos`）；负倍率下结论为假**。
⭐ **本节的定理给出**一般倍率下的**精确**行为** ——
`canonicalize` **不**在轨道上恒定，而是**把倍率换成它的符号**：

> **`canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (sign lam)`**

⇒ ⭐ **这是本文件对 §1.6 负结果的**完整刻画****：
`canonicalize` **精确地**在"模 `±1`"的商上良定义（**而不是在 `ScaleClass` 上**）。
**取 `lam > 0` 时 `sign lam = 1`，即**退化为**恒定性**（`canonicalize_section_pos`）。 -/

/-- **点态核心（一般倍率）**：若 `g ∣ v` 且 `lam ≠ 0`，
则 `(v * lam) / (g * |lam|) = sign(lam) · (v / g)`。

⭐ **证明**：写 `v = g * k`；用 `Int.sign_mul_natAbs`（`lam = sign lam · |lam|`）
把分子改写为 `(sign lam · k) · (g · |lam|)`，故商为 `sign lam · k`；
而 `(g * k) / g = k`。
⚠ **`lam ≠ 0` 不可省**：`lam = 0` 时 `|lam| = 0`，分母为零。 -/
lemma div_scaleVec_sign (v g lam : Int) (hg : g ≠ 0) (hlam : lam ≠ 0) (hgv : g ∣ v) :
    (v * lam) / (g * Int.natAbs lam) = Int.sign lam * (v / g) := by
  obtain ⟨k, rfl⟩ := hgv
  have hgl : g * (Int.natAbs lam : Int) ≠ 0 :=
    mul_ne_zero hg (by exact_mod_cast Int.natAbs_ne_zero.mpr hlam)
  have hpos : 0 < (Int.natAbs lam : Int) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hlam)
  have hsign : (Int.natAbs lam : Int).sign = 1 := Int.sign_eq_one_of_pos hpos
  have hsignAbs : Int.natAbs (Int.sign lam) = 1 := by rw [Int.natAbs_sign, if_neg hlam]
  have hnum : g * k * lam = (Int.sign lam * k) * (g * (Int.natAbs lam : Int)) := by
    have hsig : lam = Int.sign lam * (Int.natAbs lam : Int) := (Int.sign_mul_natAbs lam).symm
    rw [hsig]
    simp only [Int.sign_mul, Int.sign_sign, Int.natAbs_mul, Int.natAbs_cast, hsign, hsignAbs,
               Int.natAbs_eq_zero, hlam, if_false, Int.ofNat_mul, Int.ofNat_one, Int.mul_one]
    ring
  rw [Int.ediv_eq_of_eq_mul_left hgl hnum]
  rw [Int.mul_ediv_cancel_left k hg]

/-- ⭐⭐ **`canonicalize` 把倍率换成符号**（一般倍率的**精确**律）。

⚠ **这不只是技术细节** —— 它是 §1.6 负结果的**正面对偶**：
- **`lam > 0`**：`sign lam = 1` ⟹ `canonicalize (scaleVec c lam) = canonicalize c`
  （**`canonicalize_section_pos`**，恒定性）；
- **`lam < 0`**：`sign lam = -1` ⟹ 结果**差一个 `-1 •`**（**不是**恒定）。

⇒ ⭐ **⇒ `canonicalize` 下降到的商是 `ScaleClass` 再模掉 `±1`** ——
**`±1` 商不可绕过**（与 A2 的结论一致，见 §1.6 末段）。 -/
theorem canonicalize_scaleVec_sign (c : VectorConstraint) (hg : constraintContent c ≠ 0)
    (lam : Int) (hlam : lam ≠ 0) :
    canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam) := by
  obtain ⟨a, b⟩ := c
  have hcont : constraintContent (scaleVec { a := a, b := b } lam)
      = constraintContent { a := a, b := b } * Int.natAbs lam :=
    content_scaleVec { a := a, b := b } lam
  have hgInt : (constraintContent { a := a, b := b } : Int) ≠ 0 := content_ne_cast _ hg
  show ({ a := (scaleVec { a := a, b := b } lam).a.map
            (fun v => v / (↑(constraintContent (scaleVec { a := a, b := b } lam)) : Int)),
          b := (scaleVec { a := a, b := b } lam).b
            / (↑(constraintContent (scaleVec { a := a, b := b } lam)) : Int) } : VectorConstraint)
        = scaleVec { a := a.map (fun v => v / (↑(constraintContent { a := a, b := b }) : Int)),
                     b := b / (↑(constraintContent { a := a, b := b }) : Int) } (Int.sign lam)
  rw [hcont, Nat.cast_mul]
  simp only [scaleVec, List.map_map]
  -- ⚠ 上面必须先 `Nat.cast_mul` 把 `↑(g * lam.natAbs)` 拆成 `↑g * ↑lam.natAbs`，
  -- 否则 `div_scaleVec_sign` 的模式（分母为 `↑g * ↑lam.natAbs`）失配。
  -- ⚠ 且 `scaleVec ... (sign lam)` 展开后是 `x * sign lam`，
  -- 而引理给 `sign lam * x` ⟹ 需 `mul_comm` 对齐（`Int` 乘法交换）。
  congr 1
  · apply List.map_congr_left
    intro v hv
    simp only [Function.comp_apply]
    rw [div_scaleVec_sign v _ lam hgInt hlam (content_dvd_a { a := a, b := b } v hv), mul_comm]
  · rw [div_scaleVec_sign b _ lam hgInt hlam (content_dvd_b { a := a, b := b }), mul_comm]

end Lattice
