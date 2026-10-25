import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealCanonicalForm
/-!
# LATTICE R-02：抽取的「规范代表」 —— ⚠ **目标已被既有文件覆盖，且字面陈述为假**

## 0. 任务书原话（**逐字抄录**）

> **ID**：R-02
> **标题**：抽取的**规范代表**
> **任务**：证明：任意 Layer W 的符号原像集合中，存在唯一**规范代表**（如 gcd 约化后的）。
> 给出 `canonical : Layer → Option ConstraintSet` 及其正确性。

⚠⚠ **任务书文件 `_proof_out\_prompt_R-02.txt` 在本机【不存在】**（`read` 报 not found，
`glob` 全工作区无结果）。本文件的标题与任务**不是**从该文件读到的，而是从
**批次生成器的定义文件**逐字抄录的：
`_w30_11.json`（`{"id": "R-02", "title": "抽取的**规范代表**", "task": ...}`），
并与 `_w30_list.json`、`_mk30.py:22` 两处**独立交叉核对一致**。
⇒ **任务书正文（纪律条款、报告格式）取自同批次的 `_tmp_E09_prompt.txt` / `_e02_prompt_tmp.txt`（88 行，已读）。**

## 1. ⚠⚠ 结论先行：三件事，按重要性排序

| # | 结论 | 性质 | 位置 |
|:--|:--|:--|:--|
| **甲** | 任务书的核心（「原像集合中存在**唯一**规范代表」+ gcd 约化 + 正确性）**已由既有 `RealCanonicalForm.lean` 完成**，且比任务书要求的更强 | ⚠ **重复劳动 / 已被覆盖** | §一 |
| **乙** | 任务书要求的**接口类型** `canonical : Layer → Option ConstraintSet` 在整仓中**不存在**；既有的是 **`VectorConstraint → VectorConstraint`**（`canonicalize`）与 **`Layer → ConstraintSet`**（`extractLayer`）。**两者的类型都对不上任务书** | **真实缺口（类型级）** | §二 |
| **丙** | ⭐⭐ 把任务书**按字面**升级到 `Layer` 后，命题「存在**唯一**规范代表」**为假** —— 因为 `Layer` 是**列表**，而列表**没有**商掉「重排」与「系数为 0 的冗余位置」的自由度。**本文件给出机器反例** | ⭐ **主定理（否定结果）** | §三 |

⭐ **本文件因此不是「再证一遍 gcd 约化」**，而是：
**(i)** 如实登记甲（既有文件已覆盖，附逐字行号）；
**(ii)** 补上乙（真正缺失的 `Layer → Option ConstraintSet` 接口）；
**(iii)** 证明丙（字面命题为假，给出反例与结构性原因）。

⚠ **若甲、乙、丙与真实任务书的意图有偏差，请 coordinator 以甲为准** ——
因为**任务书文件不存在，我无法核对它的真实措辞**（见 §五 风险表第 1 项）。

## 2. 逐字核对过的既有签名（**不靠记忆**，全部用 `read` 抄录）

```lean
-- ConvertVectorLinear.lean:24-27
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项
deriving Repr                       -- ⚠ 只有 Repr：无 DecidableEq、无 BEq、无 LawfulBEq

-- ConvertVectorLinear.lean:39-42
structure LinearLayer where
  w : List Int      -- 权重向量
  b : Int           -- 偏置
deriving Repr                       -- ⚠ 同上

-- ConvertVectorLinear.lean:49-50
def convertVec (c : VectorConstraint) : LinearLayer :=
  { w := c.a, b := c.b }

-- ConvertVectorLinear.lean:69-70
def scaleVec (c : VectorConstraint) (lam : Int) : VectorConstraint :=
  { a := c.a.map (fun v => v * lam), b := c.b * lam }

-- ConvertVectorLinear.lean:105
theorem scaleVec_preserves (c : VectorConstraint) (x : List Int) (lam : Int) (hlam : lam ≠ 0) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x

-- SymbolToWeightCorrectness.lean:27
abbrev ConstraintSet := List VectorConstraint

-- SymbolToWeightCorrectness.lean:31
abbrev Layer := List LinearLayer

-- WeightToSymbolEquivalence.lean:55-56
def extractVec (l : LinearLayer) : VectorConstraint :=
  { a := l.w, b := l.b }

-- RealCompileExtractClosed.lean:99
def extractLayer (ls : Layer) : ConstraintSet := ...

-- RealCompileExtractClosed.lean:111
theorem extractLayer_compileToLayer (cs : ConstraintSet) : ...
```

**`RealCanonicalForm.lean`（⚠ 这是 R-02 已完成的证据）：**
```lean
-- :250
def ScaleClass (c c' : VectorConstraint) : Prop :=
  ∃ lam mu : Int, lam ≠ 0 ∧ mu ≠ 0 ∧ scaleVec c lam = scaleVec c' mu

-- :336
def cNegVec : VectorConstraint := { a := [2, 4], b := 6 }

-- :472
def constraintContent (c : VectorConstraint) : Nat :=
  Nat.gcd (listGcdNat c.a) (Int.natAbs c.b)

-- :514
def canonicalize (c : VectorConstraint) : VectorConstraint :=
  { a := c.a.map (fun v => v / (constraintContent c : Int)),
    b := c.b / (constraintContent c : Int) }

-- :595   ⭐ 幂等（=「唯一性」的可证内容）
theorem canonicalize_idempotent (c : VectorConstraint) (hg : constraintContent c ≠ 0) :
    canonicalize (canonicalize c) = canonicalize c

-- :606   ⭐ 正确性（保持语义）
theorem canonicalize_preserves_sat (c : VectorConstraint) (x : List Int)
    (hg : constraintContent c ≠ 0) :
    VectorConstraintSat (canonicalize c) x ↔ VectorConstraintSat c x

-- :692   ⭐ 正倍率下轨道上恒定（section 性）
theorem canonicalize_section_pos (c : VectorConstraint) (hg : constraintContent c ≠ 0)
    (lam : Int) (hlam : 0 < lam) :
    canonicalize (scaleVec c lam) = canonicalize c

-- :776   ⭐ 一般倍率的精确律：负倍率【差一个符号】
theorem canonicalize_scaleVec_sign (c : VectorConstraint) (hg : constraintContent c ≠ 0)
    (lam : Int) (hlam : lam ≠ 0) :
    canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam)
```

⭐ **关键读数**：`canonicalize` 的类型是 **`VectorConstraint → VectorConstraint`**，
**不是**任务书要的 **`Layer → Option ConstraintSet`**。
⚠ **这不是笔误**：`VectorConstraint` 是**单条约束**，`Layer` 是**层的列表**，
两者**不是同一个类型**（`_R-01.lean` §二 已就同类混淆登记过「类型错误【甲】」）。

## 3. ⚠ 诚实边界（**不许省**）

- 注意 本文件**未整体经内核编译**（任务书严禁 `lake` / `lake build` / `lake env lean`）。
  注意 **但边界不是「完全未经内核检查」**：文件内多处以 `#check` 探针核对过内核判定，
  并在 §二 的 `canonical_isSome_of_contentOk` / `canonical_eq_none_of_not_contentOk`
  以及 §三 的三条否定定理（`R02_layer_canonical_not_unique_perm` /
  `R02_layer_canonical_not_unique_scale` / `R02_layer_canonical_not_unique_dup`）
  的 `rw [canonical, dif_pos …]` / `dif_neg …` 分支收尾处引用了探针结果
  （`probe.ps1` **exit 0**）。⇒ 这些条目是**经探针核对**的，**不是**「未经检查」。
  注意 **仍未经内核检查的范围**：§一/§二/§五 中**未逐条过探针**的其余证明项
  （含 §五 `R02_canonical_well_defined_on_image` / `R02_canonical_single_valued`）。
  注意 **另有文件内自陈的独立不确定性**见下一条；既有签名已**逐字抄录**核对（§2）。
- 注意 **只读引用**：本文件**不修改**任何既有文件。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
- 注意 §一 的「已完成」判定是**我读源码得到的**，**不是**从既有文件的构建日志得到的
  （`RealCanonicalForm.lean:15` 自称 `Built RealCanonicalForm` / exit 0，**我没有独立验证**）。
-/

noncomputable section

-- 注意 `canonical` below is defined with `if h : LayerContentOk ls then ... else ...`,
-- i.e. `dite` on a **Prop**-valued predicate over `Layer = List LinearLayer`.
-- `LinearLayer` only derives `Repr` (no `DecidableEq`), so the branch condition is not
-- decidable by computation. `open scoped Classical` installs `Classical.propDecidable`
-- (the repo-wide idiom), which is what makes the definition elaborate.
open scoped Classical

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、甲：任务书的核心已由 `RealCanonicalForm` 完成（**如实登记，不重复劳动**）

要点 **本节不写新定理** —— 它把「任务书要的东西**已经存在**」做成**可核对的清单**，
并**只读引用**既有定理，避免与 `RealCanonicalForm.lean`（**有 owner 的既有文件**）重复。

注意 **为什么必须登记这件事**：如果我在不知情的情况下重写一遍 `canonicalize`，
就会产生**第二份 gcd 规范形实现**（`S9 重复收敛` 所禁止的模式）。
⇒ **本文件的正确做法是引用 + 补缺口**，而不是复制。 -/

/-- 要点 **甲-①：任务书要的「gcd 约化规范代表」已存在**（只读引用）。

任务书说「（如 gcd 约化后的）」；`RealCanonicalForm.canonicalize` **正是** gcd 约化。
要点 本定理把这条引用**机器化**，使「已存在」不是一句叙述而是一个**可核对的项**。 -/
theorem R02_canonicalize_already_exists :
    canonicalize cNegVec = ({ a := [1, 2], b := 3 } : VectorConstraint) :=
  canonicalize_cNegVec

/-- 要点 **甲-②：任务书要的「正确性」已存在**（只读引用 `canonicalize_preserves_sat`）。

注意 任务书说 `canonical ... 及其正确性` —— **正确性**在这里的含义是
「规范代表与原约束**语义相同**」，由既有定理给出。 -/
theorem R02_correctness_already_exists (c : VectorConstraint) (x : List Int)
    (hg : constraintContent c ≠ 0) :
    VectorConstraintSat (canonicalize c) x ↔ VectorConstraintSat c x :=
  canonicalize_preserves_sat c x hg

/-- 要点 **甲-③：任务书要的「唯一性」的可证内容已存在**（只读引用 `canonicalize_section_pos`）。

注意 **注意本定理的精确含义**：`canonicalize` 在**正倍率**轨道上**恒定** ⟹
同一 `ScaleClass` 类里的元素**有同一个**规范代表。
要点 **这就是「唯一规范代表」在 `VectorConstraint` 上的【真命题】**。 -/
theorem R02_uniqueness_already_exists (c : VectorConstraint) (hg : constraintContent c ≠ 0)
    (lam : Int) (hlam : 0 < lam) :
    canonicalize (scaleVec c lam) = canonicalize c :=
  canonicalize_section_pos c hg lam hlam

/-! ### 1.1 注意 但「唯一性」在 `VectorConstraint` 上**也不是无条件的**（既有负结果）

注意 **不许把甲-③ 读成「唯一性无条件成立」**。既有 `RealCanonicalForm` **自己证伪了**无条件的版本：

```lean
-- RealCanonicalForm.lean:776（逐字）
theorem canonicalize_scaleVec_sign ... :
    canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam)
```

⇒ `lam < 0` 时 `canonicalize (scaleVec c lam) ≠ canonicalize c`（**差一个符号**）。
要点 **本文件把这条负结果【从约束级提升到层级】**（§三），因为**层级的后果更严重**：
在层级，它使「唯一规范代表」**直接为假**，而不只是「差一个符号」。 -/

/-- 要点 **甲-④（负结果，只读引用）**：`±1` 缩放**改变**规范代表
⟹ `canonicalize` 在 `ScaleClass` 上**不恒定**。

注意 **本定理的用途**：它是 §三 层级否定的**约束级根源**。
要点 **逐字引用 `RealCanonicalForm.lean:619-623`**（`canonicalize_scaleVec_neg_cNegVec`）。 -/
theorem R02_sign_obstruction_already_exists :
    canonicalize (scaleVec cNegVec (-1)) = ({ a := [-1, -2], b := -3 } : VectorConstraint) :=
  canonicalize_scaleVec_neg_cNegVec

/-! ## 二、乙：注意 任务书要的**接口** `canonical : Layer → Option ConstraintSet` **不存在**

注意 **这是本文件的第一个真实缺口**（甲之外）。

任务书要求：`canonical : Layer → Option ConstraintSet`。**整仓 grep 结果**：
- `RealCanonicalForm.canonicalize : VectorConstraint → VectorConstraint`（**符号侧、非列表、非 Option**）；
- `RealCompileExtractClosed.extractLayer : Layer → ConstraintSet`（**是 `Layer`，但不是 `Option`，且不做规范化**）；
- `RealTokenSymbolLink.decode : List SymToken → Option ConstraintSet`（**是 `Option ConstraintSet`，但输入是 `SymToken` 列表，不是 `Layer`**）。

⇒ 注意 **三者都【不】是任务书要的 `Layer → Option ConstraintSet`**。
要点 **本节补上这个接口**（这是任务书的**正面要求**，属于真缺口，不是重复劳动）。

### 2.1 注意 为什么返回 `Option`（而不是 `ConstraintSet`）

要点 **`Option` 不是装饰**：`RealCanonicalForm` 的 `canonicalize` **需要** `constraintContent c ≠ 0`
（零点无规范形 —— 这是 C2 裁定「不造 `⊥`」的后果，见 `RealCanonicalForm.lean:495` 的
`content_eq_zero_iff`）。
⇒ **「某些层没有规范代表」是必须被编码进类型的事实** ⟹ `Option` **恰好**承载它。
注意 若返回裸 `ConstraintSet`，就必须在零约束上返回**某个假的**代表 ⟹ **该函数将是错的**。 -/

/-- 要点 **层级的「内容非零」谓词**：`ls` 的**每个**神经元都对应非零约束。

要点 **为什么逐元素**：`Layer := List LinearLayer`，而规范代表的**存在性**是**逐元素**的性质
（一条零约束就足以使整个列表没有规范代表 —— 因为无法给零约束指定代表）。 -/
def LayerContentOk (ls : Layer) : Prop :=
  ∀ l ∈ ls, constraintContent (extractVec l) ≠ 0

/-- 要点 **任务书要的接口**：`canonical : Layer → Option ConstraintSet`。

- `none` ⟺ `ls` 含**至少一条零约束**（**无规范代表**）；
- `some cs` ⟺ 逐元素 `canonicalize`，且**每条都非零**。

注意 **诚实标注**：本函数**只做逐元素 gcd 约化**；它**不**对列表做重排或去冗余 ——
注意 **而正是这个「不」，使 §三 的否定定理成立**（层级的唯一性**不能**靠逐元素得到）。 -/
def canonical (ls : Layer) : Option ConstraintSet :=
  if h : LayerContentOk ls then
    some (ls.map (fun l => canonicalize (extractVec l)))
  else
    none

/-- 要点 **`canonical` 在「内容全非零」的层上确实给出 `some`**（正确性的第一半：**存在性**）。 -/
theorem canonical_isSome_of_contentOk (ls : Layer) (h : LayerContentOk ls) :
    (canonical ls).isSome = true := by
  unfold canonical
  rw [dif_pos h]
  -- 注意 走到这里目标是 `(some …).isSome = true`，`dif_pos` 只负责选分支，
  -- **不会**顺带关掉 `Option.isSome`；原稿缺这一步收尾。
  rfl

/-- 要点 **`canonical` 在含零约束的层上给出 `none`**（**诚实性**：不造假的代表）。

注意 **本定理不是技术细节**：它说明 `canonical` **不会**在无代表时返回一个假代表 ——
这是 `Option` 返回值**唯一**的意义所在。 -/
theorem canonical_eq_none_of_not_contentOk (ls : Layer) (h : ¬ LayerContentOk ls) :
    canonical ls = none := by
  unfold canonical
  rw [dif_neg h]

/-- 要点 **`canonical` 非 `none` ⟹ 内容全非零**（上条的逆否，用于**判定**）。

注意 **方向不可颠倒**：`canonical ls ≠ none` 与 `LayerContentOk ls` 在此**互为充要**
（因为 `canonical` 的分支由 `LayerContentOk` **决定**）。 -/
theorem contentOk_of_canonical_ne_none (ls : Layer) (h : canonical ls ≠ none) :
    LayerContentOk ls := by
  by_contra hc
  exact h (canonical_eq_none_of_not_contentOk ls hc)

/-! ## 三、要点 丙：**层级**的「唯一规范代表」命题 —— **为假**（本文件主定理）

注意 **本节是本文件的核心否定结果。** 任务书说「任意 `Layer W` 的符号原像集合中，
存在**唯一**规范代表」。**按字面把它升级到 `Layer` 后，该命题为假**，有两个**独立**的原因。

### 3.1 原因刻划（一句话）

`Layer := List LinearLayer` 是**列表**，而「符号原像」在层级**不知道两条**列表何时是
「同一个符号表示」：

| # | 层的自由度 | 后果 | 本文件的定理 |
|:--|:--|:--|:--|
| **I** | **重排**：`[l₁, l₂]` 与 `[l₂, l₁]` 是**同一个**约束集合 | 逐元素 `canonical` 给出**两个不同列表** | §3.2 |
| **II** | **`±1` 缩放**：`l` 与 `-1 • l` 是**同一条**约束 | 逐元素 `canonical` 给出**两个不同**代表 | §3.3 |
| **III** | **冗余位置**：`[l, l]` 与 `[l]` 是**同一个**集合 | 逐元素 `canonical` **保留重复** | §3.4 |

要点 **三条都是「层的自由度在逐元素规范化下【不被吸收】」** ⟹
**「唯一规范代表」不可能由逐元素定义得到**，**必须**先把层**取商**（排序 + 去重 + 模 `±1`）。

注意 **诚实标注**：III 与 I 的「集合语义」是**我引入的约定**（任务书**没有定义**层级原像）。
注意 **但 I 与 II 不需要任何额外约定**：它们直接来自 `canonical` 的**定义体**（`List.map` 保持长度与顺序），
**是纯结构事实**。⇒ 要点 **§3.2 与 §3.3 是最强的部分**（前提最少）。

### 3.2 要点 原因 I：**重排** —— 逐元素 `canonical` 不吸收顺序（**主反例**）

要点 **构造**：取两条**不同**的层，它们在**同一个符号原像集合**里（条数相同、集合相同），
但 `canonical` 给出**不同的列表**。

注意 **本反例只用 `List.map` 的结构性质**（长度保持 + 顺序保持），**不需要任何层级语义约定**。 -/

/-- 反例用的第一条层：`[{[1,2],3}, {[1],1}]`（**两条都已规范**，内容均为 1）。
注意 显式写 `LinearLayer` 记录（**不依赖任何 `OfNat`/`Coe` 实例**）。 -/
def layerAB : Layer :=
  [{ w := [1, 2], b := 3 }, { w := [1], b := 1 }]

/-- 反例用的第二条层：**同两条、顺序对调** `[{[1],1}, {[1,2],3}]`。 -/
def layerBA : Layer :=
  [{ w := [1], b := 1 }, { w := [1, 2], b := 3 }]

/-- 要点 **两条层的内容都非零**（故 `canonical` 在两者上都不返回 `none`）。

注意 **必须显式证**：否则 `canonical` 落进 `none` 分支，反例就**退化**成「两者都是 none」——
那样结论**平凡**（`none = none`），**不是**我要的反例。 -/
theorem layerContentOk_layerAB : LayerContentOk layerAB := by
  intro l hl
  simp only [layerAB, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · -- { w := [1,2], b := 3 }：content = gcd (gcd 1 2) 3 = 1
    simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num
  · -- { w := [1], b := 1 }：content = gcd 1 1 = 1
    simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num

/-- 要点 **第二条层的内容也非零**（同上，顺序对调不改变逐元素内容）。 -/
theorem layerContentOk_layerBA : LayerContentOk layerBA := by
  intro l hl
  simp only [layerBA, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num
  · simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num

/-- 要点 **主反例（原因 I）**：**存在两条不同的层**，其符号约束集合**相同**（顺序对调），
但 `canonical` 给出**不同的**规范代表。

要点 **`hsame` 的含义**：两条层的**约束多重集**相同（此处逐字是「同一对元素的两种排列」）——
注意 这是**任何**合理的「层 ≙ 符号原像」约定都必须承认的同一性
（约束集合**与顺序无关**）。
注意 **而结论是「规范代表不等」** ⟹ 要点 **层级的「唯一规范代表」为假**。

注意 **证明不依赖任何语义约定**：只用 `List.map` 的顺序保持（`List.map_cons`）——
若两个列表**首元素不同**，则 `map` 之后的列表**首元素也不同**（故不等）。 -/
theorem R02_layer_canonical_not_unique_perm :
    ∃ ls ls' : Layer,
      (∀ c, c ∈ ls ↔ c ∈ ls') ∧
      canonical ls ≠ canonical ls' := by
  refine ⟨layerAB, layerBA, ?_, ?_⟩
  · -- 集合相同：两条层的元素集合都是那两条（重排不改变成员的「属于关系」）
    intro c
    simp only [layerAB, layerBA, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl) <;> (try { exact Or.inl rfl }) <;> exact Or.inr rfl
    · rintro (rfl | rfl) <;> (try { exact Or.inr rfl }) <;> exact Or.inl rfl
  · -- 规范化后不等：逐元素 canonicalize 后首元素不同（[1,2] ≠ [1]）
    intro h
    have hsome : some (layerAB.map (fun l => canonicalize (extractVec l)))
        = some (layerBA.map (fun l => canonicalize (extractVec l))) := by
      rw [canonical, dif_pos layerContentOk_layerAB, canonical,
        dif_pos layerContentOk_layerBA] at h
      exact h
    have hlist : layerAB.map (fun l => canonicalize (extractVec l))
        = layerBA.map (fun l => canonicalize (extractVec l)) := Option.some.inj hsome
    -- 两侧都非空（长度 2），取首元素比对 `w`
    have hw := congrArg (fun (t : List VectorConstraint) => (t.head?).map VectorConstraint.a) hlist
    simp only [layerAB, layerBA, List.map_cons, List.map_nil, extractVec, canonicalize,
      constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil] at hw
    norm_num at hw

/-! ### 3.3 要点 原因 II：**`±1` 缩放**在层级的后果（比约束级更严重）

注意 **`RealCanonicalForm` 已在约束级登记**：`canonicalize (scaleVec c lam) ≠ canonicalize c`
当 `lam < 0`（§1.1 / `canonicalize_scaleVec_sign`）。
要点 **本节说明层级为什么【更严重】**：

- 在**约束级**，后果是「同一 `ScaleClass` 类里的两个点**规范形差一个符号**」——
  注意 这**仍然**可以救：把商**再模掉 `±1`**（`RealCanonicalForm` §六-bis 的建议）；
- 在**层级**，后果是「**同一个层的两个符号原像**给出**两个不同的规范代表**」——
  注意 **这直接使「唯一规范代表」为假**，因为**层本身**（不是约束的轨道）就有两个原像。

要点 **本节的定理把这条从约束级【提升】到层级的类型层面**。 -/

/-- **把约束级反例搬进层**：`cNegVec` 作为**单元素层**。
注意 用 `extractVec` 的逆 `convertVec`（**同一记录的字段改名**，`Change`）构造。 -/
def layerNeg : Layer := [convertVec cNegVec]

/-- **`-1` 缩放后的同一条约束**，同样作为单元素层。
注意 `scaleVec cNegVec (-1)` 与 `cNegVec` **同属一个 `ScaleClass`**
（`RealCanonicalForm.lean:343` 的 `scaleClass_cNegVec_neg`，只读引用）。 -/
def layerNegScaled : Layer := [convertVec (scaleVec cNegVec (-1))]

/-- 要点 **两个单元素层的内容都非零**。 -/
theorem layerContentOk_layerNeg : LayerContentOk layerNeg := by
  intro l hl
  simp only [layerNeg, List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  simp only [extractVec, convertVec, constraintContent, listGcdNat, cNegVec,
    List.foldr_cons, List.foldr_nil]
  norm_num

/-- 要点 **缩放后的层内容也非零**（`content` 按 `|lam| = 1` 不变）。 -/
theorem layerContentOk_layerNegScaled : LayerContentOk layerNegScaled := by
  intro l hl
  simp only [layerNegScaled, List.mem_cons, List.not_mem_nil, or_false] at hl
  subst hl
  simp only [extractVec, convertVec, constraintContent, listGcdNat, cNegVec, scaleVec,
    List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  norm_num

/-- 要点 **原因 II（层级）**：**两条层的符号约束【仅相差 `±1` 倍率】**（故是**同一个**符号对象），
但 `canonical` 给出**不同的**规范代表。

注意 **`hsame` 的形式**：两条层**逐点**在 `ScaleClass` 里（这里只有一个元素，故是单点条件）。
要点 **`ScaleClass` 是 `RealCanonicalForm` 定义的等价关系**（`scaleClass_equivalence`），
**不是我临时造的** ⟹ 反例**不依赖我的约定**。

注意 **与 §3.2 的关键差别**：§3.2 用的是「重排」（需要「集合语义」的约定），
**本条用的是既有等价关系 `ScaleClass`** ⟹ 要点 **本条反例的假设最弱、最不可反驳**。 -/
theorem R02_layer_canonical_not_unique_scale :
    ∃ ls ls' : Layer,
      (∀ l ∈ ls, ∃ l' ∈ ls', ScaleClass (extractVec l) (extractVec l')) ∧
      canonical ls ≠ canonical ls' := by
  refine ⟨layerNeg, layerNegScaled, ?_, ?_⟩
  · -- 唯一的元素对：`cNegVec` 与 `scaleVec cNegVec (-1)` 同属一个 `ScaleClass`
    intro l hl
    simp only [layerNeg, List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    exact ⟨convertVec (scaleVec cNegVec (-1)), by simp [layerNegScaled],
      scaleClass_cNegVec_neg⟩
  · -- 规范化后不等：`{[1,2],3}` 与 `{[-1,-2],-3}`
    intro h
    have hsome : some (layerNeg.map (fun l => canonicalize (extractVec l)))
        = some (layerNegScaled.map (fun l => canonicalize (extractVec l))) := by
      rw [canonical, dif_pos layerContentOk_layerNeg, canonical,
        dif_pos layerContentOk_layerNegScaled] at h
      exact h
    have hlist : layerNeg.map (fun l => canonicalize (extractVec l))
        = layerNegScaled.map (fun l => canonicalize (extractVec l)) := Option.some.inj hsome
    have hw := congrArg (fun (t : List VectorConstraint) => (t.head?).map VectorConstraint.a) hlist
    simp only [layerNeg, layerNegScaled, List.map_cons, List.map_nil, extractVec, convertVec,
      canonicalize, constraintContent, listGcdNat, cNegVec, scaleVec,
      List.foldr_cons, List.foldr_nil] at hw
    norm_num at hw

/-! ### 3.4 注意 原因 III：**冗余位置**（**假设最强的一条，如实降级**）

注意 **诚实标注**：本条**需要**「层等价于其约束**集合**」这个约定
（即 `[l, l]` 与 `[l]` 表示同一符号对象）。
注意 **任务书没有定义层级等价**，故**本条的假设比 I / II 强**。
要点 **我把它列出并【显式降级】**，而不是让它混在 I / II 里冒充同等的强度 ——
**因为「重复约束是不是同一个集合」本身是可争的**（多重集 vs 集合）。

要点 **它的价值**：即使把 I 的重排、II 的缩放都**用商消掉**，
III 仍说明**「去重」是第三件必须做的事** ⇒
要点 **「层级的唯一规范代表」至少需要三个商操作**（排序、去重、模 `±1`），
**逐元素 `canonicalize` 一个都不做**。 -/

/-- 要点 **原因 III**：`[l, l]` 与 `[l]` 的 `canonical` **不等**（长度不同）。

注意 **前提**：两条层表示**同一个约束集合**（重复不影响集合）——
注意 **这是本定理唯一的、也是最强的约定**，故 §3.4 的结论**弱于** §3.2 / §3.3。 -/
theorem R02_layer_canonical_not_unique_dup :
    ∃ ls ls' : Layer,
      (∀ c, c ∈ ls ↔ c ∈ ls') ∧
      canonical ls ≠ canonical ls' := by
  -- `[{[1],1}]` 与 `[{[1],1}, {[1],1}]`：集合成员的「属于关系」相同
  refine ⟨[{ w := [1], b := 1 }], [{ w := [1], b := 1 }, { w := [1], b := 1 }], ?_, ?_⟩
  · intro c
    -- 注意 两侧都化简成 `c = {w:=[1],b:=1} ∨ c = {w:=[1],b:=1}`，还需 `or_self` 才能
    -- 把右式折回左式（原稿只 `simp only [...]` 就收尾，故留下 `A ↔ A ∨ A` 未解）。
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
  · -- 长度不同（1 vs 2）⟹ 规范化结果必不同
    intro h
    have hok1 : LayerContentOk ([{ w := [1], b := 1 }] : Layer) := by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
      norm_num
    have hok2 : LayerContentOk ([{ w := [1], b := 1 }, { w := [1], b := 1 }] : Layer) := by
      intro l hl
      -- 注意 这里没有 `∈ []` 分支，故 `hl` 仍是 **二元析取** `l = X ∨ l = X`（`or_false` 不适用）
      -- ⟹ 必须 `rcases` 两次；`subst hl` 只对「单等式」有效。
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;>
        · simp only [extractVec, constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
          norm_num
    have hsome : some (( [{ w := [1], b := 1 }] : Layer).map
          (fun l => canonicalize (extractVec l)))
        = some (( [{ w := [1], b := 1 }, { w := [1], b := 1 }] : Layer).map
          (fun l => canonicalize (extractVec l))) := by
      rw [canonical, dif_pos hok1, canonical, dif_pos hok2] at h
      exact h
    have hlist := Option.some.inj hsome
    have hlen := congrArg List.length hlist
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hlen
    omega

/-! ## 四、要点 真实缺口（任务书末句要求的登记）

要点 任务书说：「若目标本质平凡，直说『平凡』并指出真实缺口 —— **这同样是合格交付**」。

### 4.1 注意 判定：任务书的**目标不是平凡，而是【已被完成】+【字面为假】**

注意 **不许含糊**。三句话：

1. **任务书的符号侧核心**（「原像里有唯一 gcd 规范代表」+ 正确性）
   注意 **不是平凡** —— 它是 `RealCanonicalForm.lean`（803 行，**有 owner**）的**真内容**
   （幂等靠 `content_canonicalize`，正确性靠 `scaleVec_preserves`，
   还附带 kernel 反例）。**它不是 `rfl` 级空壳。**
2. 注意 **但它【已经存在】** ⟹ **R-02 若只做这件事，就是重复劳动**（§一）。
3. 要点 **任务书把对象写成 `Layer` 后，命题【为假】**（§三）⟹
   **不是「平凡」，是「假」** —— 而**这正是本文件的正面交付**。

要点 **⇒ 我的判定**：R-02 的**字面目标**（`Layer → Option ConstraintSet` + 唯一代表）
**不可满足**；**真实缺口**是下面 §4.2 的两条。

### 4.2 要点 真实缺口（**两条，按重要性**）

| # | 真实缺口 | 为什么它是**真**缺口 | 本文件做了什么 |
|:--|:--|:--|:--|
| **缺口 1** | 要点 **「层级的符号原像」从未被定义** | 任务书说「`Layer W` 的**符号原像集合**」，注意 但整仓**没有**这个概念的载体：`canonicalize` 作用于 `VectorConstraint`，`extractLayer` 是**反向**（层→约束）。**「层的原像集合」没有定义** ⟹ 任务书的命题**连陈述都写不出来** | §五 给出**两个候选定义**并证明二者**不等价**（故「选哪个」是**真决定**，不是记法） |
| **缺口 2** | 要点 **层级规范化必须【先取商】** | §三 的三个反例（重排 / `±1` / 冗余）说明：逐元素 `canonicalize` **必然**不是唯一的。⇒ 唯一代表**只能**定义在**商**上：`(List LinearLayer) / (排序 + 去重 + 模 ±1)` | §五 给出该商**正确性所依赖**的**必要条件**，并**如实登记未构造该商** |

### 4.3 注意 缺口 1 的形式化：两个候选原像定义**不等价**（**这是真决定，不是记法**）

要点 **候选 A（逐条）**：`c` 是 `ls` 的原像 ⟺ `compileToLayer c` 与 `ls` **逐条相同**（含顺序）。
要点 **候选 B（集合）**：`c` 是 `ls` 的原像 ⟺ 两者**约束集合相同**（**忽略顺序与重复**）。

注意 **两者不等价** —— 而 §3.2/§3.4 的反例**恰好**落在二者**分歧**处。 -/

/-- **候选 A：逐条原像**（`compileToLayer` 与 `ls` **精确相等**，含顺序与重复）。 -/
def PreimageStrict (ls : Layer) (c : ConstraintSet) : Prop :=
  compileToLayer c = ls

/-- **候选 B：集合原像**（忽略顺序与重复，只看**成员集合**）。 -/
def PreimageSet (ls : Layer) (c : ConstraintSet) : Prop :=
  ∀ v : VectorConstraint, v ∈ c ↔ convertVec v ∈ ls

/-- 要点 **两个候选【不等价】**（缺口 1 的机器证据）。

要点 **构造**：取 `c := [{[1,2],3}, {[1],1}]` 与 `ls := layerBA`（**对调后的层**）。
- **候选 B 成立**：两者的成员集合相同（§3.2 的 `hsame` 已证）；
- **候选 A 不成立**：`compileToLayer c = layerAB ≠ layerBA = ls`（首元素不同）。

⇒ 要点 **「层的符号原像」这个说法【歧义】**，
注意 而**任务书没有消歧** ⟹ **任务书的命题在陈述层面就不确定**。
注意 **这是缺口 1 的精确含义**，不是文字挑剔：**选 A 还是选 B 会改变命题的真假**
（选 A → §三 的反例不成立，因为 A 把顺序算进原像；选 B → §三 的反例成立）。 -/
theorem R02_preimage_definitions_not_equivalent :
    ∃ (ls : Layer) (c : ConstraintSet), PreimageSet ls c ∧ ¬ PreimageStrict ls c := by
  -- 注意 原稿写 `[convertVec cNegVec, { a := [1], b := 1 }]`，有两处错：
  --   (i) `convertVec : VectorConstraint → LinearLayer`，而 `ConstraintSet = List VectorConstraint`
  --       ⟹ 方向反了（应直接用 `VectorConstraint`，**不是** `convertVec` 它）；
  --   (ii) 取值也不符本文档 `:544` 的声明 `c := [{[1,2],3}, {[1],1}]`（原稿用的是 `cNegVec = {[2,4],6}`）。
  -- 按 §4.3 的**声明意图**取 `c := [{a:=[1,2],b:=3}, {a:=[1],b:=1}]`：
  -- `compileToLayer c = [{w:=[1,2],b:=3}, {w:=[1],b:=1}] = layerAB ≠ layerBA` ⟹ 候选 A 假；
  -- 而两者的成员集合相同 ⟹ 候选 B 真。
  refine ⟨layerBA, [{ a := [1, 2], b := 3 }, { a := [1], b := 1 }], ?_, ?_⟩
  · -- 候选 B：成员集合相同（`{[1,2],3} ↦ {[1,2],3}`，`{[1],1} ↦ {[1],1}`）
    --
    -- 注意 真正的障碍是**类型**，不是化简：`v ∈ c` 化简后是 **`VectorConstraint`** 的等式
    --   （`v = {a := …, b := …}`），而 `convertVec v ∈ layerBA` 化简后是 **`LinearLayer`**
    --   的等式（`{w := v.a, b := v.b} = {w := …, b := …}`）。二者**不同一类型**，
    --   故 `rfl` 接不上，`cases v` 也救不了（`cases` 后 `v` 成字面记录，
    --   右式仍是 `LinearLayer`，还是两个类型）。
    -- 要点 出路：先证一条**桥引理** `convertVec v = l ↔ v = extractVec l`
    --   （纯字段改名，两侧都写 `cases` 即可），再用它把右式整体换成左式的形状。
    intro v
    have hbridge : ∀ l : LinearLayer, (convertVec v = l ↔ v = extractVec l) := by
      intro l
      -- 注意 两侧 `cases` 之后，目标是**两个不同结构类型**上的等式之等价：
      --     `{w := va, b := vb} = {w := lw, b := lb}  ↔  {a := va, b := vb} = {a := lw, b := lb}`
      --   `simp only` **关不掉**它（它不是同类型化简，而是"字段改名"的往返）。
      --   要点 正确做法：两个方向都对**等式假设**做 `cases`，让字段被替换掉。
      constructor
      · intro h
        cases h
        rfl
      · intro h
        cases h
        rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false, layerBA]
    rw [hbridge { w := [1], b := 1 }, hbridge { w := [1, 2], b := 3 }]
    simp only [extractVec]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h
  · -- 候选 A 不成立：`compileToLayer c` 的首元素是 `{[1,2],3}`，而 `layerBA` 的首元素是 `{[1],1}`
    intro h
    have hw := congrArg (fun (t : Layer) => (t.head?).map LinearLayer.w) h
    simp only [PreimageStrict, compileToLayer, List.map_cons, List.map_nil, layerBA,
      convertVec, List.head?_cons] at hw
    norm_num at hw

/-! ## 五、要点 正面结论：**逐元素规范化在「严格原像」下确实是良定义的**

注意 **不许只交否定结果**。§三 说明**层级唯一性为假**，
要点 **但**在 §4.3 的**候选 A（严格原像）**下，`canonical` **确实**满足一个**真**性质：

> **同一条符号约束 `c` 的两次编译，规范化后相同。**

要点 **这不是废话**：它说明 `canonical` 在 `compileToLayer` 的**像**上是**良定义的函数**
（而非依赖于「怎么编译」），注意 **这正是任务书「规范化是良定义的」那一半的【真内容】**。 -/

/-- 要点 **正面定理**：`canonical` 在 `compileToLayer` 的**像**上**单值** ——
即 `canonical (compileToLayer c)` **只依赖** `c` 的**规范形**（逐元素）。

要点 **证明**：`compileToLayer c = c.map convertVec`（定义），
而 `extractVec (convertVec v) = v`（`roundtrip_extractVec`，**定义相等**，`_R-01` §二已登记）
⟹ 两侧化为同一个 `List.map canonicalize`。 -/
-- 注意 参数类型必须写 `LayerContentOk (c.map convertVec)`：`.`-记法（`c.map convertVec`）
-- 绑定**紧于**函数应用，故原稿的 `LayerContentOk c.map convertVec` 会被解析成
-- `(LayerContentOk c.map) convertVec` ⟹ 「`(VectorConstraint → ?m) → List ?m` 不是 `Layer`」。
theorem R02_canonical_well_defined_on_image (c : ConstraintSet)
    (h : LayerContentOk (c.map convertVec)) :
    canonical (compileToLayer c) = some (c.map canonicalize) := by
  -- 注意 必须先 `rw [compileToLayer]` 把 `compileToLayer c` **化成** `c.map convertVec`：
  -- `dif_pos h` 的 `h` 是关于 `LayerContentOk (c.map convertVec)` 的，
  -- 而 `unfold canonical` 后判据里写的是 `LayerContentOk (compileToLayer c)`
  -- ⟹ 两者**不同一**，`rw [dif_pos h]` 找不到模式（原稿正是卡在这里）。
  rw [compileToLayer]
  unfold canonical
  rw [dif_pos h]
  -- 此时两侧化为同一个 `List.map canonicalize`
  have hmap : (c.map convertVec).map (fun l => canonicalize (extractVec l))
      = c.map canonicalize := by
    rw [List.map_map]
    exact List.map_congr_left (fun v _ => by
      simp only [Function.comp_apply]
      rw [roundtrip_extractVec])
  rw [hmap]

/-- 要点 **上条的「唯一性」读数**：**同一个** `c` 经 `compileToLayer` 后，
`canonical` 给出**唯一确定**的结果（不依赖任何选择）。

注意 **与 §三 的关系**：§三 说「**不同的** `c`, `c'` 可以有**相同**的层却给出**不同**的 `canonical`」；
要点 本条说「**同一个** `c` 给出**唯一**结果」。注意 **两条【不矛盾】** ——
⇒ 要点 **层级唯一性的失败【不在】`canonical` 的函数性，而在层的商没取**（缺口 2）。 -/
theorem R02_canonical_single_valued (c c' : ConstraintSet)
    (h : LayerContentOk (c.map convertVec)) (h' : LayerContentOk (c'.map convertVec))
    (hc : c.map convertVec = c'.map convertVec) :
    c.map canonicalize = c'.map canonicalize := by
  have h1 := R02_canonical_well_defined_on_image c h
  have h2 := R02_canonical_well_defined_on_image c' h'
  -- 注意 原稿 `rw [← h1, ← h2, hc]` 与我在上一轮试的 `calc … := h1.symm` **都是类型错**：
  -- `h1/h2` 的左右两端都被 `some` **包裹**，而目标是**裸列表**等式
  -- （`some (c.map canonicalize) = canonical (compileToLayer c)`，不是 `c.map canonicalize = …`）。
  -- 正确路线：先用 `hc`（经 `compileToLayer`）把两个 `canonical` 对齐到同一个值，
  -- 再用 `Option.some.inj` **脱掉 `some`**。
  have hsame : canonical (compileToLayer c) = canonical (compileToLayer c') := by
    rw [compileToLayer, compileToLayer, hc]
  have : some (c.map canonicalize) = some (c'.map canonicalize) := by
    rw [← h1, ← h2]
    exact hsame
  exact Option.some.inj this

/-! ## 六、要点 承重性总结（**哪条定理是本文件的内容，哪条是接口**）

注意 **本文件的纪律要求**：明确区分**承重**与**装饰**。

| 定理 | 承重？ | 理由 |
|:--|:--|:--|
| `R02_layer_canonical_not_unique_perm` | 要点 **强承重** | **否定**任务书的字面命题；只用 `List.map` 结构性质（**假设最少**） |
| `R02_layer_canonical_not_unique_scale` | 要点 **强承重** | 同上，且用**既有的** `ScaleClass`（**不是我的约定**）|
| `R02_preimage_definitions_not_equivalent` | 要点 **承重** | 证明任务书**陈述歧义**（缺口 1 的核心） |
| `R02_layer_canonical_not_unique_dup` | 注意 **弱承重** | 依赖「集合语义」约定（§3.4 **已显式降级**） |
| `R02_canonical_well_defined_on_image` | 要点 **中等** | 正面补充；注意 但它是 `List.map_map` + `rfl` 级（**如实标注**）|
| `R02_canonical_single_valued` | 注意 **接口** | 是上条的直接推论，**不独立承重** |
| `canonical_isSome_of_contentOk` / `canonical_eq_none_of_not_contentOk` | 注意 **接口** | 展开 `canonical` 的定义分支（`dif_pos` / `dif_neg`），**无数学内容** |
| `R02_canonicalize_already_exists` 等甲组 | 注意 **登记** | **只读引用**既有定理，用于**登记重复劳动**（§一），**不是我的内容** |

要点 **一句话总结**：
**本文件的内容 = §三 的两个否定定理（重排 + `±1`）+ §4.3 的歧义定理。**
注意 **删掉这三条，本文件就退化为「引用 `RealCanonicalForm` + 展开 `canonical` 的定义」，
即平凡。** 注意 **我在文件头也明写了这一点**（§1 的表格）。 -/

end Lattice
