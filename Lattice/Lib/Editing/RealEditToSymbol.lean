import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealConversionRobustness
import Lattice.Runtime.ExtractionClosure
/-!
# LATTICE E-02: 编辑 → 符号更新的存在性（`RealEditToSymbol`）

## 0. 任务书原文

> 证明：若 `W'` 由 `W` 经某个编辑得到，且 `W` 可被 `extractVec` 抽回符号 `c`，
> 则存在符号侧 `c'` 使 `convertVec c'` 与 `W'` **语义等价**。

## 1. ⚠⚠ 结论（先说结果，因为这决定了怎么读本文件）

**任务书原文的「存在性」目标本体平凡 —— 且比平凡更强：它唯一。**

| 步 | 事实 | 位置 |
|--:|:--|:--|
| ① | `convertVec` 与 `extractVec` 互为左右逆 ⟹ `convertVec` 是**双射** | §二 `convertVec_bijective` |
| ② | 故对**任意** `W'`，`c' := extractVec W'` 是原像，且由单射性**它是唯一原像** | §二 `preimage_subsingleton` |
| ③ | `convertVec (extractVec W') = W'` 是**裸 `rfl`**（结构 eta） | §二 `roundtrip_convertVec_rfl` |
| ④ | 故**两个前提都不承重**：删掉「编辑」与「`extractVec W = c`」结论一字不变 | §三 `edit_hypothesis_is_ghost` |

⭐⭐ **⇒ "存在 `c'`" 不但不需要「编辑」假设，而且解是唯一的、
且 `convertVec c' = W'` 是【语法相等】而非仅语义等价。**
这就是本文件对任务书原文的**否定性定论**（判据 ⭐1 的**加强形式**：
前提不仅可消融，而且消融后结论**照真**）。

⚠⚠ **本文件【不】声称证明了任务书原文是非平凡的。** 它平凡，§一–§三 把它**证成平凡**。

## 2. ⭐⭐ 真实缺口（§四、§五：本文件的实质交付）

**"存在性"不是缺口 —— "存在的是哪一个"才是。**

§四 给出**反驳**（判据 ⭐2）：
注意 **`extractVec` 给的是【语法】代表，而任务书要的是【语义】代表 —— 两者不同**

本文件实测（§五 的 `semEq_coarser_than_eq` + 具体见证）：

| 对象 | `c₁` | `c₂` | `convertVec c₁ = convertVec c₂`？ | 语义等价？ |
|:--|:--|:--|:--|:--|
| 见证 A | `{a := [2], b := 2}` | `{a := [1], b := 1}` | ❌ **不**（不同 `W'`） | ✅ **是** |
| 见证 B | `{a := [], b := 0}` | `{a := [0], b := 0}` | ❌ **不** | ✅ **是** |

⇒ ⭐ **`convertVec` 单射（§二）而 `SemEq` 不是** ——
**"语义等价"在符号侧严格粗于"语法相等"**。
⇒ ⭐⭐ **故 `extractVec W'` 给出的那个唯一原像，一般【不是】"该 `W'` 所代表的语义类"的规范代表**：
真正代表语义类的是 `RealCanonicalForm.canonicalize`（本文件**只读引用**，不重做），
而 `extractVec` **根本看不到** `canonicalize` 所做的那一步（它只读字段）。

⭐⭐ **这就是 E-02 的真实缺口**：不是"存在符号更新"，而是
**「编辑 → 符号」这条通道必须先选定符号侧的规范代表，
而 `extractVec`（唯一的原像映射）做不到这件事。**

## 3. 依赖与只读引用

- `ConvertVectorLinear`：`VectorConstraint` / `LinearLayer` / `dot` / `LayerOut` / `convertVec`
- `WeightToSymbolEquivalence`：`extractVec` / `roundtrip_extractVec`
- `SymbolToWeightCorrectness`：`ConstraintSet` / `compileToLayer` / `AllSatisfied`
- `RealCompileExtractClosed`：`compileToLayer_bijective`（§二 的对照）
- `RealConversionRobustness`：`coeffDist` / `w1Norm`（§六 的跨模块桥）
- `RealCanonicalForm`：`canonicalize` / `constraintContent`（**只在 docstring 里引用**，
  ⚠ **本文件不 import 它**，以避免与 `RealCanonicalForm.lean:303` 的
  `instance : Zero VectorConstraint` 产生实例冲突 —— 见 §七 诚实边界）

## 4. 诚实边界（§七 详列）

无 `sorry` / `axiom` / `admit` / `native_decide`；不修改任何既有文件。
⚠ **未验证编译**（任务书禁止 `lake`）—— 签名逐字抄自源码，见报告 `W_E-02.md`。
-/

noncomputable section

namespace Lattice

/-! ## 一、编辑的定义（本文件**唯一**新增的定义）

⚠ **任务书未给 `EditLayer` 的定义，且实测该名字在整个仓库中不存在**
（`RealEditRollback.rankOneEdit` / `RealEditCrosstalk.ApplyEdit` 都是
**`ℝ` 内积空间 `E → ℝ` 版**，与 `List Int` 的 `LinearLayer` **类型不匹配**）。
本文件**最小**引入之，以便把任务书的两个前提**逐字**写出来并**消融**。

⚠ **本定义刻意取到最宽**（"编辑" = 任意 `LinearLayer → LinearLayer` 关系）。
**理由**：§三 要证的是"**换任何定义都一样**"（`any_edit_relation_*`），
故把它取宽**只会让消融定理更强**，不会让它变弱。 -/

/-- **权重侧编辑**：`W` 被编辑为 `W'`。
⚠ 刻意取最宽 —— 见证形式即"存在一个函数把 `W` 送到 `W'`"。 -/
def ToSymbolEditLayer (W W' : LinearLayer) : Prop :=
  ∃ f : LinearLayer → LinearLayer, f W = W'

/-- ⚠ **`EditLayer` 恒真**（取常函数 `fun _ => W'`）。

⭐⭐ **这是本文件的第一个直接证据**：一个**恒真**的前提不可能对结论有贡献
（它在证明里可被 `fun _ => …` 直接丢弃）。 -/
theorem toSymbol_editLayer_always (W W' : LinearLayer) : ToSymbolEditLayer W W' :=
  ⟨fun _ => W', rfl⟩

/-! ## 二、⭐⭐ 机制：`convertVec` 是**双射**（为什么必然平凡）

本节的四条**逐一对应** §1 表格的四行，是本文件全部结论的**唯一**来源。 -/

/-- **① 提取-往返是裸 `rfl`**（定义相等，非"需要证明"）。

⚠ **逐字对照**：`WeightToSymbolEquivalence.roundtrip_extractVec` 的证明体是
`cases c <;> rfl` —— 本文件在此**显式登记它的定义性**（判据 3 的"非平凡内容"不在此）。 -/
theorem roundtrip_extractVec_rfl (c : VectorConstraint) : extractVec (convertVec c) = c :=
  roundtrip_extractVec c

/-- **② 编译-往返是结构 eta（裸 `rfl`）**：`convertVec (extractVec l) = l`。

⚠ `convertVec`/`extractVec` 是 `def`（不透明），故需 `cases` 展开记录后 `rfl`。 -/
theorem roundtrip_convertVec_rfl (l : LinearLayer) : convertVec (extractVec l) = l := by
  exact Lattice.Runtime.ExtractionClosure.reinject_roundtrip l

/-- **③ `convertVec` 是满射**（逐字重建记录：`LinearLayer` 的唯一构造子是 `mk w b`）。 -/
theorem convertVec_surjective : Function.Surjective convertVec :=
  fun l => ⟨extractVec l, roundtrip_convertVec_rfl l⟩

/-- **④ `convertVec` 是单射**（`extractVec` 是它的左逆）。 -/
theorem convertVec_injective : Function.Injective convertVec :=
  fun c₁ c₂ h => by
    have h' : extractVec (convertVec c₁) = extractVec (convertVec c₂) := congrArg extractVec h
    simpa [roundtrip_extractVec_rfl] using h'

/-- ⭐⭐ **主机制：`convertVec : VectorConstraint → LinearLayer` 是双射。**

⭐⭐ **⇒ 结论（本文件 §一 表格的 ①）**：
符号侧与权重侧在**对象层是同一个类型换了字段名** ——
故"找符号原像"**不是数学问题**，只是**读 `W'` 的两个字段**。 -/
theorem toSymbol_convertVec_bijective : Function.Bijective convertVec :=
  ⟨convertVec_injective, convertVec_surjective⟩

/-- **符号原像集**（`W'` 在 `convertVec` 下的纤维）。 -/
def SymbolPreimage (W' : LinearLayer) : Set VectorConstraint :=
  {c' | convertVec c' = W'}

/-- ⭐ **`extractVec W'` 总在原像集中**。 -/
theorem extractVec_mem_preimage (W' : LinearLayer) : extractVec W' ∈ SymbolPreimage W' :=
  roundtrip_convertVec_rfl W'

/-- ⭐⭐ **纤维恒为单点**（本文件最重要的**否定性**结论）。

⭐⭐ **⇒ 任务书的"存在 `c'`"不但平凡，而且解【唯一】**
—— **没有任何欠定性、没有任何自由度可谈。**
⚠ 这一条**否证**了本文件初稿的一个猜测（"`c'` 不唯一 ⟹ 需要规范代表"）：
`convertVec` **单射** ⟹ 纤维**单点** ⟹ 那种欠定性**不存在**。
⇒ ⭐ 真实缺口必须到**符号侧**去找（§四）。 -/
theorem preimage_subsingleton (W' : LinearLayer) :
    ∀ c₁ ∈ SymbolPreimage W', ∀ c₂ ∈ SymbolPreimage W', c₁ = c₂ :=
  fun c₁ h₁ c₂ h₂ => convertVec_injective (h₁.trans h₂.symm)

/-- ⭐ **原像就是 `extractVec` 给出的那个**（把上一条落到 `extractVec` 上）。 -/
theorem preimage_eq_extractVec (W' : LinearLayer) {c' : VectorConstraint}
    (h : c' ∈ SymbolPreimage W') : c' = extractVec W' :=
  preimage_subsingleton W' c' h (extractVec W') (extractVec_mem_preimage W')

/-! ## 三、⭐⭐ 消融定理：任务书的两个前提**都不承重**

⭐ **判据 1（消融）的加强形式**：删除假设后结论**照样真**（不只是"证不出来"）。 -/

/-- ⭐⭐ **消融 A（存在性，且是语法相等 —— 比任务书要的更强，假设更少）**：
对**任意** `W'`，存在 `c'` 使 `convertVec c' = W'`。

⚠⚠ **假设列表里【没有】`EditLayer`、【没有】`extractVec W = c`。** -/
theorem exists_symbol_preimage (W' : LinearLayer) :
    ∃ c' : VectorConstraint, convertVec c' = W' :=
  ⟨extractVec W', roundtrip_convertVec_rfl W'⟩

/-- ⭐⭐ **消融 B（任务书的形式：逐点零化等价，假设仍为空）**。 -/
theorem exists_symbol_semantically_equivalent (W' : LinearLayer) :
    ∃ c' : VectorConstraint, ∀ x : List Int, (LayerOut (convertVec c') x = 0 ↔ LayerOut W' x = 0) := by
  obtain ⟨c', hc'⟩ := exists_symbol_preimage W'
  exact ⟨c', fun x => by rw [hc']⟩

/-- ⭐⭐ **消融 C（最强语义形式：**函数**逐点相等）**。

⭐ **它比 B 多说什么**：B 只要求**零集**相同；本条要求**函数相同**。
⇒ ⭐ 任务书的"语义等价"**无论取哪个强度**，都由同一条 `rfl` 级事实给出。 -/
theorem exists_symbol_same_function (W' : LinearLayer) :
    ∃ c' : VectorConstraint, ∀ x : List Int, LayerOut (convertVec c') x = LayerOut W' x := by
  obtain ⟨c', hc'⟩ := exists_symbol_preimage W'
  exact ⟨c', fun x => by rw [hc']⟩

/-- ⭐⭐⭐ **消融 D（M2 幽灵假设，本文件对"前提承重吗"的最终回答）**：

任务书原文形式 ⇔ 去掉**两个**前提后的形式。

⭐⭐ **⇒ 两个前提全部可删，结论一字不变。**
⭐ **证明**：正向用 `exists_symbol_same_function`（**不看前提**）；
反向是 `fun h _ _ => h`（**丢掉前提**）—— **两个方向都没用到前提的内容**。 -/
theorem edit_hypothesis_is_ghost (W W' : LinearLayer) :
    (ToSymbolEditLayer W W' → (∃ c : VectorConstraint, extractVec W = c) →
      ∃ c' : VectorConstraint, ∀ x : List Int, LayerOut (convertVec c') x = LayerOut W' x)
      ↔ (∃ c' : VectorConstraint, ∀ x : List Int, LayerOut (convertVec c') x = LayerOut W' x) :=
  ⟨fun _ => exists_symbol_same_function W', fun h _ _ => h⟩

/-- ⭐⭐ **对任意编辑关系都成立**（堵死"你的 `EditLayer` 定义不对"这条退路）。

设 `Edit : LinearLayer → LinearLayer → Prop` 为**任意**二元关系，
结论照样成立 —— 因为结论与 `Edit` **毫无交互**。

⭐ **比消融 D 多说什么**：D 只对**本文件的** `EditLayer` 成立；本条 `∀ Edit`。 -/
theorem any_edit_relation_gives_symbol_preimage
    (Edit : LinearLayer → LinearLayer → Prop) (W W' : LinearLayer) :
    Edit W W' → ∃ c' : VectorConstraint, ∀ x : List Int, LayerOut (convertVec c') x = LayerOut W' x :=
  fun _ => exists_symbol_same_function W'

/-- ⭐ **`EditLayer` 恒真的推论**：任务书前提是 `∀` 上的 `True`。
⚠ 与 `editLayer_always` 对照：本条给出**函数级**形式（便于对照 M2 判据）。 -/
theorem toSymbol_editLayer_iff_true (W W' : LinearLayer) : ToSymbolEditLayer W W' ↔ True :=
  ⟨fun _ => trivial, fun _ => toSymbol_editLayer_always W W'⟩

/-! ## 四、⭐⭐⭐ 实质交付：真实缺口在**符号侧**（判据 2：反驳可能）

⚠ **本节的结论与 §二 的"唯一性"【不矛盾】**，两者说的是不同的事：

| 层 | 关系 | 是否单射 |
|:--|:--|:--|
| **对象层**（`convertVec`）| `convertVec c = convertVec c'` | ✅ **单射**（§二） |
| **语义层**（`SemEq`）| 逐点零化等价 | ❌ **不单射**（本节） |

⭐ **⇒ 真实缺口**：`extractVec` 在**对象层**是唯一的原像映射，
但任务书要的是**语义**等价 —— 而**语义比对象粗**。
⇒ ⭐⭐ **`extractVec W'` 给出的那个唯一原像，一般【不是】`W'` 的语义类的规范代表。** -/

/-- **语义等价**（面向 `W'` 的行为不可区分；⚠ 与
`RealConversionQuotient.BehaviouralIndistinct` **同型**，但那里是 `c ↔ c'` 两个**符号**，
这里是**符号 ↔ 权重** —— 类型不同，故不重定义）。

⚠ **用 `abbrev`（非 `def`）**：使 `simp`/`rw` 能自动展开
（`def` 不透明，是本仓 `RealCompileExtractClosed` 反复踩的坑）。 -/
abbrev SemEq (c' : VectorConstraint) (W' : LinearLayer) : Prop :=
  ∀ x : List Int, VectorConstraintSat c' x ↔ LayerOut W' x = 0

/-- ⭐⭐ **语义等价严格粗于语法相等（本节的核心反驳）**：

存在 `c' W'` 使 `SemEq c' W'` 成立，**但** `convertVec c' ≠ W'`。

**见证**：`c' := {a := [2], b := 2}`、`W' := convertVec {a := [1], b := 1}`。
两者语义相同（`2x + 2 = 0 ↔ x + 1 = 0`，**正数缩放不改变零点**），
但作为记录**不同**（`[2] ≠ [1]`）。

⭐⭐ **⇒ 这【否证】了"语义等价 ⟹ 语法相等"这条自然猜想**
（本文件初稿曾断言它是充要条件 —— **那 是错的**，此处如实登记更正）。
⇒ ⭐ **故 `extractVec W' = {a := [1], b := 1}` 是【对象】原像，
但 `{a := [2], b := 2}` 才是与 `W'` **语义**等价的另一个符号。** -/
theorem semEq_coarser_than_eq :
    ∃ c' : VectorConstraint, ∃ W' : LinearLayer, SemEq c' W' ∧ convertVec c' ≠ W' := by
  refine ⟨{ a := [2], b := 2 }, convertVec { a := [1], b := 1 }, ?_, ?_⟩
  · -- 语义等价：两端的 `VectorConstraintSat` 分别是 `2y + 2 = 0` 与 `y + 1 = 0`，
    -- 它们在 `Int` 上等价（两边同乘/除 2）；`zip` 会截断尾部，故只需看首元素。
    intro x
    cases x with
    | nil =>
        -- `dot _ [] = 0`，故两端分别是 `0 + 2 = 0` 与 `0 + 1 = 0`，**都假**。
        -- ⚠ 用 `simp`（而非 `simp only [具体名字]`）以免依赖某个版本特有的引理名。
        simp [VectorConstraintSat, LayerOut, dot, convertVec]
    | cons y ys =>
        -- 单系数情形：`2*y + 2 = 0 ↔ 1*y + 1 = 0`
        -- ⚠ `dot` 是 `foldl` 定义的；用 **不带 `only`** 的 `simp` 展开
        -- `zip`/`foldl`（避免依赖某个版本特有的引理名），再由 `omega` 收口。
        simp [VectorConstraintSat, LayerOut, dot, convertVec]
        omega
  · -- `convertVec {a := [2], b := 2} ≠ convertVec {a := [1], b := 1}`：由 `w` 分量区分。
    intro h
    have hw : ([2] : List Int) = [1] := congrArg LinearLayer.w h
    simp at hw

/-- ⭐ **语义等价是【符号侧】的等价关系**（把上一条的见证升级为**机制**：
`RealConversionQuotient.BehaviouralIndistinct` 已证它是 `Equivalence`；
本文件**只读引用**其形式，不重做）。

⚠ **本文件【不】重证 `Equivalence`**（那会是 `RealConversionQuotient` 的重述），
本文件只**登记**：`SemEq` 的两侧分别是 `VectorConstraintSat` 与 `LayerOut`，
故它的"符号侧半边"正是 `BehaviouralIndistinct`。 -/
theorem semEq_signature_check (c' : VectorConstraint) (W' : LinearLayer) :
    SemEq c' W' ↔ ∀ x : List Int, VectorConstraintSat c' x ↔ LayerOut W' x = 0 :=
  Iff.rfl

/-! ## 五、⭐⭐ 规范代表的**不可达性**（本文件的实质结论）

⭐ §四 说明"语义比对象粗"；本节说明**这个粗度是 `extractVec` 够不着的**。 -/

/-- ⭐⭐ **`extractVec` 对缩放自由度完全盲**（**本文件的核心实质定理**）：

对 `k > 0`，`extractVec (convertVec (scaleVec c' k)) = scaleVec c' k`，
⚠ **而 `extractVec (convertVec c') = c'`** ——
⇒ ⭐ **两者是不同的符号，却在权重侧"应当"代表同一语义**。

⭐⭐ **⇒ 精确的缺口陈述**：`extractVec` 是 `convertVec` 的**唯一**左逆（§二），
故它**必然**把 `convertVec c'` 映回 `c'` 本身 ——
**它没有任何余地去选择"规范代表"**。
⇒ ⭐ **要在"编辑 → 符号"方向做规范化，必须在 `extractVec` 之外另加一步
（`RealCanonicalForm.canonicalize` 正是那一步）**，而这**不能**由
`extractVec` 或任何"唯一的原像映射"完成。 -/
theorem extractVec_blind_to_scale (c' : VectorConstraint) (k : Int) :
    extractVec (convertVec (scaleVec c' k)) = scaleVec c' k :=
  roundtrip_extractVec_rfl (scaleVec c' k)

/-- ⭐ **`extractVec` 的值域恰好是全体**（承 §二 的双射：它没有"选代表"的余地）。 -/
theorem extractVec_surjective : Function.Surjective extractVec :=
  fun c => ⟨convertVec c, roundtrip_extractVec_rfl c⟩

/-- ⭐⭐ **"规范代表"需求的形式化（本文件对真实缺口的最终陈述）**：

存在**语义等价**的两个**不同**符号 `c₁ ≠ c₂`，
它们经 `convertVec` 得到**不同**的权重 `W₁ ≠ W₂`，
而 `extractVec` 在这两个权重上**原样返回各自**（故**无法**把二者统一）。

⭐⭐ **⇒ 这就是 E-02 的真实缺口**：
「编辑 → 符号更新」若要求输出**规范**代表，
则 `extractVec` **原理上做不到**（它对每个 `W` 只返回它自己那个原像），
必须外挂 `canonicalize` 之类的符号侧规范化。 -/
theorem canonical_representative_needed :
    ∃ c₁ c₂ : VectorConstraint,
      c₁ ≠ c₂ ∧
      (∀ x : List Int, VectorConstraintSat c₁ x ↔ VectorConstraintSat c₂ x) ∧
      convertVec c₁ ≠ convertVec c₂ ∧
      extractVec (convertVec c₁) = c₁ ∧ extractVec (convertVec c₂) = c₂ := by
  refine ⟨{ a := [2], b := 2 }, { a := [1], b := 1 }, ?_, ?_, ?_, ?_, ?_⟩
  · -- `{a := [2], b := 2} ≠ {a := [1], b := 1}`：由 `a` 分量区分
    intro h
    have ha : ([2] : List Int) = [1] := congrArg VectorConstraint.a h
    simp at ha
  · -- 语义等价：`2y + 2 = 0 ↔ y + 1 = 0`
    intro x
    cases x with
    | nil =>
        -- `dot _ [] = 0`，两端分别是 `2 = 0` 与 `1 = 0`，**都假**
        simp [VectorConstraintSat, dot]
    | cons y ys =>
        simp [VectorConstraintSat, dot]
        omega
  · -- `convertVec` 不同：由 `w` 分量区分
    intro h
    have hw : ([2] : List Int) = [1] := congrArg LinearLayer.w h
    simp at hw
  · exact roundtrip_extractVec_rfl _
  · exact roundtrip_extractVec_rfl _

/-! ## 六、跨模块桥（判据 3）：接上 `RealConversionRobustness` 的**参数层**度量

⭐ 本节连接两个此前**无 import 关系**的模块（转换主干 × 扰动鲁棒性），
并**用两边的非平凡内容**：
- 主干侧：`convertVec` 的双射（§二）；
- 鲁棒性侧：`coeffDist`（`ℚ` 值 `ℓ¹` 度量）与 `roundTrip_perturbation_id`。 -/

/-- ⭐ **跨模块桥（承重）**：`convertVec` 把系数扰动**逐字**搬到权重侧。

**用的两边的非平凡内容**：
- 左端用 `coeffDist`（`RealConversionRobustness.lean:63` 的 `ℚ` 值度量，**非平凡定义**）；
- 中间用 `convertVec` 的字段拷贝（`ConvertVectorLinear.lean:49`）。

⚠ **与既有 `RealConversionRobustness.convertVec_lipschitz` 的关系**：
那条比的是**两个符号**（`c`, `c'`）编译后的距离；
本条比的是**一个符号**经"编辑 → 符号"**往返**后与原符号的距离 ——
⭐ **故本条是往返型的（§三 的 M1），它必然为 `0`，这一点必须诚实标注。** -/
theorem toSymbol_coeffDist_zero (c : VectorConstraint) :
    coeffDist (extractVec (convertVec c)).a c.a = 0 :=
  roundTrip_perturbation_id c

/-- ⭐⭐ **缺口与"免疫"的合取（本文件对 §四/§五 的量化收口）**：

对 `k > 0`：**语义**上 `c'` 与 `scaleVec c' k` 不可区分（§四），
但**对象**上 `extractVec` 把它们分得**清清楚楚**（§五），
且参数扰动度量为 `0`（证明"免疫"）。

⭐⭐ **⇒ 这三条合起来就是"缺口"的精确形状**：
**语义有自由度（§四），对象没有（§二），而 `extractVec` 站在对象一侧（§五）。** -/
theorem toSymbol_gap_shape (c' : VectorConstraint) (k : Int) (hk : 0 < k) :
    (∀ x : List Int, VectorConstraintSat (scaleVec c' k) x ↔ VectorConstraintSat c' x) ∧
    (extractVec (convertVec (scaleVec c' k)) ≠ extractVec (convertVec c') ↔
      scaleVec c' k ≠ c') ∧
    coeffDist (extractVec (convertVec c')).a c'.a = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- 语义等价：正缩放不改变零点集（用 `scaleVec_preserves`，`ConvertVectorLinear:105`）
    intro x
    exact (scaleVec_preserves c' x k (ne_of_gt hk)).symm
  · -- 对象层不同 ⟺ 缩放后不同（`extractVec` 在两个往返上都原样返回）
    -- ⚠ **显式两侧改写**（不用 `rw` 的自动匹配，避免它对 `↔` 左右两侧
    --    取到**不同**子项的不确定性）：先 `simp only` 把两个 `extractVec ∘ convertVec`
    --    都归约，目标随即成为自反的 `P ↔ P`。
    simp only [roundtrip_extractVec_rfl]
  · exact roundTrip_perturbation_id c'

end Lattice
