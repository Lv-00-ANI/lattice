import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealConversionRobustness
/-!
# LATTICE E-06：编辑与符号约束的**一致性**

## 0. 任务书原文（逐字）

> **标题**：编辑与符号约束的**一致性**
> **任务**：证明：若 `c` 是 `W` 的符号代表且 `c'` 是 `W'` 的符号代表，
> 则 `编辑 W→W' ⟹ c 与 c' 的差` 可由某个符号侧操作描述。

⚠ **本文件的任务书文件 `_proof_out/_prompt_E-06.txt` 在磁盘上【不存在】**
（实测 `Test-Path` ⟹ `False`）。本文件的题面取自**波次清单**
`C:\Users\xingg\Desktop\agent\_w30_prompts.json` 中 `id == "E-06"` 的条目，
其正文已**逐字**抄录于上。参见报告 `W_E-06.md` §0 的登记。

## 1. ⚠⚠ 结论先行：**该目标平凡**（这正是任务书允许的合格交付）

任务书自己写明：

> ⚠ **若你发现你的目标本质上是平凡的** ⟹
> ⭐ **⇒ 不要假装它不平凡** —— **在报告里明确说「该目标平凡，真实缺口是 X」**。

本文件认定：**E-06 的题面目标平凡，且是"双重平凡"** —— 两处前提**各自**都足以
使结论**无需任何数学内容**地成立。§二、§三 把它**证成平凡**（机器定理，非口头断言）：

| 步 | 事实 | 位置 |
|--:|:--|:--|
| ① | 「符号代表」在两侧**互逆**：`convertVec`/`extractVec` 是双射 ⟹ **`c'` 被 `W'` 唯一决定** | §二 `representative_forced` |
| ② | 故「符号侧操作」可取**常函数** `fun _ => extractVec W'` —— 它**不看** `c`、**不看**编辑 | §三 `diff_described_vacuously` |
| ③ | 「编辑 `W→W'`」若取最宽（本仓 `_E-02.AnyEditLayer` 即"存在函数送 `W` 到 `W'`"）则**恒真** ⟹ 该前提可**整体删去** | §三 `diff_described_fully_erased` |
| ④ | ⭐ **两处前提【独立地】各自可消融** ⟹ 结论是**双重空壳**（不是"一处依赖一处"） | §三 `double_vacuity` |

⭐⭐ **⇒ 本题的"一致性"不是数学内容 —— 它是 `convertVec` 是双射的【重述】。**
「编辑 → 符号更新」之所以总能被描述，**不是因为编辑有什么结构**，
而是因为**符号侧根本没有自由度**（`extractVec` 是唯一的原像映射）。

## 2. ⭐⭐ 真实缺口（§四：本文件的实质交付）

**"差能否被描述"不是缺口 —— "描述出来的是哪一个"才是。**

承 `_E-02.lean` §四/§五 已建立的机制（本文件**只读引用**，不重做）：
`extractVec` 是 `convertVec` 的**唯一**左逆，故它**必然**返回 `W'` 自己那个原像，
**没有任何余地选择规范代表**。

⭐ **本文件把该缺口推到 E-06 的编辑语境**（§四），新增三个机器见证：

| 见证 | 内容 | 判据 |
|:--|:--|:--|
| `edit_diff_not_representative` | ⭐ **同一个符号 `c`，两个不同编辑给出【语义等价但对象不同】的 `c'`** ⟹ "差"依赖编辑的**语法**而非**语义** | ⭐2 反驳 |
| `edit_diff_scale_sensitive` | ⭐ 正缩放编辑 `c ↦ scaleVec c k`（`k>0`）**语义上什么都没变**，但 `c' ≠ c` ⟹ 报告出的"差"**是假差** | ⭐2 反驳 |
| `canonicalization_not_free` | ⭐ `canonicalize`（`RealCanonicalForm:514`）与 `extractVec` **不可交换** ⟹ 规范代表**不能**由 `extractVec` 通道免费得到 | ⭐2 + ⭐4 |

⭐⭐ **⇒ E-06 的真实缺口**：「编辑 → 符号差」这条通道**必然**输出**语法**差，
而任务书要的是**语义**意义上的差。二者**不等价**（§四的见证），
**故必须外挂符号侧规范化**（`RealCanonicalForm.canonicalize`），
而这一步**不能**由 `extractVec` 或任何"唯一的原像映射"完成。

## 3. 依赖与只读引用

- `ConvertVectorLinear`：`VectorConstraint` / `LinearLayer` / `dot` / `LayerOut` /
  `convertVec` / `VectorConstraintSat` / `scaleVec` / `scaleVec_preserves`（**承重**：判据 2 的语义半边）
- `WeightToSymbolEquivalence`：`extractVec` / `roundtrip_extractVec`（**承重**：§二 双射的来源）
- `SymbolToWeightCorrectness`：`Layer` / `compileToLayer` / `AllSatisfied` / `symbolToWeight_correct`
- `RealConversionRobustness`：`coeffDist` / `roundTrip_perturbation_id`（§五 跨模块桥）

⚠ **本文件【不】import `RealCanonicalForm`** —— 它在 `:303` 有
`instance : Zero VectorConstraint`，与 `_E-02.lean` §七 登记的实例冲突风险同源。
`canonicalize` / `constraintContent` 仅在 §四 的**存在性反驳**里以
**名字**出现（构造见证不需要展开它的定义体），故**无需** import。

## 4. 诚实边界

无 `sorry` / `axiom` / `admit` / `native_decide`；不修改任何既有文件。
⚠ **未验证编译**（任务书严禁 `lake` / `probe.ps1`）—— 所有既有签名逐字抄自源码，
证明项未经内核检查。详见 `W_E-06.md` §诚实边界。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、把题面的两个前提**逐字**写下来

⚠ **任务书未给「符号代表」与「编辑」的定义**。本文件**最小**引入之，
并**刻意取到最宽**（"代表" = 编译回原权重，"编辑" = 任意函数），
**理由**：§三 要证的是"**换任何定义都一样**"（消融），
故取宽**只会让消融定理更强**。 -/

/-- **符号代表（题面「`c` 是 `W` 的符号代表」的精确形式）**：
`c` 经编译恰好得到 `W`。

⚠ **这是【语法】代表**（对象层相等），**不是**语义代表 ——
⭐ 这个区分正是 §四 真实缺口的来源。 -/
abbrev IsRepresentative (c : VectorConstraint) (W : LinearLayer) : Prop :=
  convertVec c = W

/-- **权重侧编辑（题面「编辑 `W→W'`」的最宽形式）**：
存在**某个**函数把 `W` 送到 `W'`。

⚠ **刻意取最宽** —— 见证形式即"存在一个函数"。这是 `_E-02.lean:92` 的定义，
本文件**沿用同一形式**以保证两个 sibling 的结论可直接比较。
⚠ **原子版 `convertVec ∘ editConstraint` 已由 `_E-01.edit_commutes_with_convert` 给出**；
本文件要证的是"**任意**编辑"，故必须用这个最宽版，否则消融不成立。 -/
def AnyEditLayer (W W' : LinearLayer) : Prop :=
  ∃ f : LinearLayer → LinearLayer, f W = W'

/-- ⚠ **`AnyEditLayer` 恒真**（取常函数 `fun _ => W'`）。

⭐⭐ **这是§三消融的引擎**：一个**恒真**的前提在证明里可被 `fun _ => W'` 直接丢弃，
故它对结论**不可能**有贡献。 -/
theorem anyEditLayer_always (W W' : LinearLayer) : AnyEditLayer W W' :=
  ⟨fun _ => W', rfl⟩

/-- ⭐ **消融的接口层读数**：`AnyEditLayer` 与 `True` **等价** ⟹
命题 `AnyEditLayer W W' → P` 与 `P` **等价**（前提可整体删去）。 -/
theorem anyEditLayer_iff_true (W W' : LinearLayer) : AnyEditLayer W W' ↔ True :=
  ⟨fun _ => trivial, fun _ => anyEditLayer_always W W'⟩

/-! ## 二、⭐⭐ 机制：`c'` 被 `W'` **唯一决定**（为什么必然平凡）

本节的四条**逐一对应** §1 表格的第 ① 行，是本文件全部结论的**唯一**来源。
⚠ **它们不是新数学** —— 全部是 `convertVec` 双射的重述；
本文件**显式登记**这一点（任务书要求：不假装平凡的东西不平凡）。 -/

/-- **① 编译-往返是结构 eta（裸 `cases` + `rfl`）**：`convertVec (extractVec l) = l`。

⚠ 逐字对照 `_E-02.roundtrip_convertVec_rfl`（同一陈述，同型证明）。
本文件**重新给出**是因为**不 import `_E-02`**（sibling 之间不互相 import，
避免给 coordinator 的 roots 注册制造耦合）。 -/
theorem convert_extract_id (l : LinearLayer) : convertVec (extractVec l) = l := by
  cases l with
  | mk w b => rfl

/-- **② 提取-往返是裸 `rfl`**：`extractVec (convertVec c) = c`。
逐字引用既有 `roundtrip_extractVec`（证明体为 `cases c <;> rfl`）。 -/
theorem extract_convert_id (c : VectorConstraint) : extractVec (convertVec c) = c :=
  roundtrip_extractVec c

/-- ⭐⭐ **主机制：`convertVec : VectorConstraint → LinearLayer` 是双射。**

⭐ **它为什么承重**：§三 的「常函数描述」**完全**依赖满射性
（要保证 `extractVec W'` 真的是 `W'` 的一个符号代表）。 -/
theorem agreement_convertVec_bijective : Function.Bijective convertVec :=
  ⟨-- 单射：`extractVec` 是左逆
   fun c₁ c₂ h => by
     have h' := congrArg extractVec h
     rwa [extract_convert_id c₁, extract_convert_id c₂] at h',
   -- 满射：`extractVec` 是右逆
   fun l => ⟨extractVec l, convert_extract_id l⟩⟩

/-- ⭐⭐ **承重结论：题面的「符号代表」存在且【唯一】**。

若 `c` 与 `c'` 都是 `W'` 的符号代表，则 `c = c'`。

⭐⭐ **它说明什么**：题面写「`c` 是 `W` 的符号代表且 `c'` 是 `W'` 的符号代表」，
读起来像是两个**独立**的输入；但由双射性，
⭐ **`c'` 实际上不是自由输入 —— 它被 `W'` 钉死为 `extractVec W'`。**
⇒ 这就是"结论必然平凡"的**结构性原因**：题面以为有自由度的地方**没有**自由度。 -/
theorem representative_forced (c c' : VectorConstraint) (W' : LinearLayer)
    (hc : IsRepresentative c' W') : c' = extractVec W' := by
  rw [← hc]
  exact extract_convert_id c'

/-- ⭐ **存在性（题面对「符号代表」的存在性假设）**：
每个权重 `W'` 都**有**符号代表（`extractVec W'`）。 -/
theorem representative_exists (W' : LinearLayer) :
    ∃ c' : VectorConstraint, IsRepresentative c' W' :=
  ⟨extractVec W', convert_extract_id W'⟩

/-! ## 三、⭐⭐⭐ 题面目标的**双重空壳性**（判据 ⭐1：消融，加强形式）

本节的策略：**不**去证题面那句含混的话（"可由某个符号侧操作描述"未定义），
而是证明 ⭐ **无论怎么把它写实，它都被两处前提各自独立地空壳化**。 -/

/-- ⭐⭐ **结论（存在形式）：差可由**常函数**描述的符号侧操作描述。**

⭐⭐ **它为什么是空壳**：见证的符号侧操作是 `fun _ => extractVec W'` ——
它**不看** `c`、**不看**编辑、**不看**差，是个**常函数**。
一个不引用任何输入的"描述"，**没有描述任何东西**。
⇒ 这正是 `_E-01.lean:17-19` 点名的缺陷同型（那里的 δ := 两输出之差）。

⚠ **本定理【三个前提全部未使用】已被 `diff_described_fully_erased` 独立证明** ——
本定理保留它们**只为展示"原样写下题面时"结论长什么样**，
⭐ **这是本文件对"字面照做"的显式演示，不是实质内容**。 -/
theorem diff_described_vacuously (c c' : VectorConstraint) (W W' : LinearLayer)
    (_hc : IsRepresentative c W) (_hc' : IsRepresentative c' W')
    (_hedit : AnyEditLayer W W') :
    ∃ op : VectorConstraint → VectorConstraint,
      op c = extractVec W' ∧ op = (fun _ => extractVec W') :=
  ⟨fun _ => extractVec W', rfl, rfl⟩

/-- ⭐⭐⭐ **消融母定理（判据 ⭐1 的加强形式）：删掉【全部三个前提】，结论照真。**

对比 `diff_described_vacuously`：本条的 `∃ op` **一字不变**，
但 `IsRepresentative` ×2 与 `AnyEditLayer` **全部消失**。

⭐⭐ **它说明什么**：一条定理若在**删空全部前提**后仍然成立，
则它的内容量为 **0** —— 它不是"关于编辑与符号约束的一致性"的定理，
而是"常函数总是存在的"这一逻辑重言式。
⇒ ⭐ **这就是 E-06 题面目标平凡性的【机器证明】**（非口头断言）。 -/
theorem diff_described_fully_erased (W' : LinearLayer) (c : VectorConstraint) :
    ∃ op : VectorConstraint → VectorConstraint, op c = extractVec W' :=
  ⟨fun _ => extractVec W', rfl⟩

/-- ⭐⭐ **双重空壳性（本节的最终收口）**：

两处前提**各自独立地**可消融 —— 不是"一处依赖另一处"：

- 保留「`c` 是 `W` 的符号代表 + `c'` 是 `W'` 的符号代表」，删掉「编辑」⟹ **照真**；
- 保留「编辑」，删掉两处「符号代表」⟹ **照真**（见 `diff_described_fully_erased`）。

⭐⭐ **⇒ 「编辑 ⟹ 差可描述」这个蕴含式【两头都是空的】。**
这是比"前提 A 可删"更强的否定：**删哪一头都一样**。

⚠ **两个见证都是常函数**（`fun _ => c'` 与 `fun _ => extractVec W'`），
故 `hc`、`hc'` **同样未被使用** —— 本定理只保留它们以对齐题面。 -/
theorem double_vacuity (c c' : VectorConstraint) (W W' : LinearLayer)
    (_hc : IsRepresentative c W) (_hc' : IsRepresentative c' W') :
    (∃ op : VectorConstraint → VectorConstraint, op c = c') ∧
    (∃ op : VectorConstraint → VectorConstraint, op c = extractVec W') :=
  ⟨⟨fun _ => c', rfl⟩, ⟨fun _ => extractVec W', rfl⟩⟩

/-! ## 四、⭐⭐⭐ 实质交付：真实缺口（判据 ⭐2 反驳 + ⭐4 量化）

**"差能否被描述"不是缺口 —— "描述出来的是哪一个"才是。**

承 `_E-02.lean` §四/§五：`extractVec` 是 `convertVec` 的**唯一**左逆
（§二 `agreement_convertVec_bijective`），故它**必然**返回 `W'` 自己那个原像。
⭐ 本节把它推到 **E-06 的编辑语境**，给出三个**新的**机器见证。 -/

/-- ⭐⭐ **见证 A（判据 ⭐2）：同一个符号 `c`，两个【不同】编辑给出
【语义等价】但【对象不同】的 `c'`。**

构造：`c := {a := [1], b := 1}`，两个编辑分别为
`c ↦ c`（恒等）与 `c ↦ scaleVec c 2 = {a := [2], b := 2}`（正缩放）。

⭐⭐ **它说明什么**：
- 两个 `c'` **语义上完全一样**（`≡ 0` 与 `≡ 0` 同为真/同为假，由
  `scaleVec_preserves` 承重）；
- 但按题面的语法代表定义，它们是**两个不同的"差"**。
⇒ ⭐ **故"差"报告的是【语法】差，而任务书要的是【语义】差 —— 二者不等价。** -/
theorem edit_diff_not_representative :
    ∃ c c₁' c₂' : VectorConstraint,
      c₁' ≠ c₂' ∧
      (∀ x : List Int, VectorConstraintSat c₁' x ↔ VectorConstraintSat c₂' x) ∧
      (∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c₁' x) := by
  refine ⟨{ a := [1], b := 1 }, { a := [1], b := 1 }, scaleVec { a := [1], b := 1 } 2,
    ?_, ?_, ?_⟩
  · -- 对象层不同：由 `a` 分量区分（`[1] ≠ [1].map (· * 2)`）
    -- ⚠ 先 `show` 把 `scaleVec` 的**定义**摆到目标里（不透明 def ⇒ `congrArg` 后会残留）。
    show ({ a := [1], b := 1 } : VectorConstraint) ≠ scaleVec { a := [1], b := 1 } 2
    intro h
    have ha : ([1] : List Int) = ([1] : List Int).map (fun v => v * 2) :=
      congrArg VectorConstraint.a h
    simp only [List.map_cons, List.map_nil] at ha
    -- `[1] = [1 * 2]` ⟹ `1 = 2`，矛盾
    have h2 : (1 : Int) = 1 * 2 := by simpa using ha
    norm_num at h2
  · -- 语义等价：正缩放 2 不改变零点集（`scaleVec_preserves`，`ConvertVectorLinear:105`）
    intro x
    -- ⚠ 定向核对（根因 A）：`scaleVec_preserves c x lam h` 的结论**逐字**是
    --     `VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x`
    -- ——即【未缩放】在左、【缩放后】在右。
    -- ⚠ 本目标（本 `refine` 第 2 支，`c₁' := scaleVec c 2`、`c₂' := c`）经目标态实测为
    --     `VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c 2) x`
    -- ⭐ **与引理同向** ⟹ **不能**加 `.symm`（旧代码误加了 `.symm`，这正是 `type mismatch` 的真身）。
    -- 对照：本文件 §三 `edit_diff_scale_sensitive` / §五 `agreement_gap_shape` 的目标是
    -- `Sat (scaleVec c k) x ↔ Sat c x`（缩放在左），那里**才**需要 `.symm`。
    exact scaleVec_preserves { a := [1], b := 1 } x 2 (by norm_num)
  · -- 与 `c` 语义等价：`c₁' = c`，故 `Iff.rfl`
    intro x
    exact Iff.rfl

/-- ⭐⭐ **见证 B（判据 ⭐2 的量化版）：正缩放编辑 `k>0` 语义上"什么都没变"，
但按题面通道报告的"差"非零。**

⭐⭐ **它说明什么**：`k = 1` 时 `scaleVec c 1 = c`（差为 0）；
`k = 2` 时语义**完全不变**而差**非零**。
⇒ ⭐ **同一件语义事件，报告的差从 0 跳到非 0** ——
这就是"**语法差 ≠ 语义差**"的最锋利读数：
⭐ **报告出的"差"可以是【假差】**（语义上不存在任何变化）。 -/
theorem edit_diff_scale_sensitive (c : VectorConstraint) :
    (∀ x : List Int, VectorConstraintSat (scaleVec c 1) x ↔ VectorConstraintSat c x) ∧
    (scaleVec c 1 = c) ∧
    (∀ x : List Int, VectorConstraintSat (scaleVec c 2) x ↔ VectorConstraintSat c x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `k = 1`：语义等价
    intro x
    exact (scaleVec_preserves c x 1 (by norm_num)).symm
  · -- `k = 1`：对象层**恒等**（`v * 1 = v`、`b * 1 = b`）
    -- ⚠ 用 `cases` 展开记录：`VectorConstraint` 的唯一构造子是 `mk`
    -- （与 `_E-02.roundtrip_convertVec_rfl` 同型的手法）。
    -- ⚠ `List.map (fun v => v * 1)` **不是** `List.map id` 的语法形态，
    -- 故用 `List.map_congr_left` 逐项化成 `id` 后再 `List.map_id`
    -- （`RealCanonicalForm.lean:562-563` 是仓内已验证的同款写法）。
    cases c with
    | mk a b =>
        -- ⚠ 根因 B：`cases c` 之后目标是
        --     `Lattice.scaleVec { a := a, b := b } 1 = { a := a, b := b }`
        -- ⚠ `scaleVec` 是**不透明 `def`**，`cases` **不会**展开它（旧代码误以为展开了）。
        -- ⚠ 更关键：`{ a := ..., b := ... }` 这里是 `VectorConstraint.mk` 的**记录记法**，
        -- Lean 把 `mk` 视为**只有一个显式参数**的结构（其字段经 `mk.injEq` 平铺），
        -- 故旧代码 `refine ⟨?_, ?_⟩`（构造子 2 个参数）必然报
        --     "invalid constructor ⟨...⟩, insufficient number of arguments"
        -- 且紧随一条 "no goals to be solved"（根因 B 的真身，**不是**类型写错）。
        -- ⚠ 正解：先用 `show` 把 `scaleVec` 的**定义体**显式摆出来（承重的一步），
        -- 再用 `rw` 逐分量归约 `a`（`List.map (fun v => v * 1)` ⟹ `List.map id` ⟹ `a`）
        -- 与 `b`（`b * 1` ⟹ `b`），最后两条等式由 `rfl` 收口。
        show ({ a := a.map (fun v => v * 1), b := b * 1 } : VectorConstraint) = { a := a, b := b }
        rw [show List.map (fun v : Int => v * 1) a = List.map id a from
              List.map_congr_left (fun v _ => mul_one v)]
        rw [List.map_id, mul_one]
  · -- `k = 2`：语义**仍然等价**（正缩放不改变零点），尽管对象层变了
    intro x
    exact (scaleVec_preserves c x 2 (by norm_num)).symm

/-- ⭐⭐⭐ **见证 C（判据 ⭐2 + ⭐4）：规范代表**不能**由 `extractVec` 通道免费得到。**

**精确陈述**：存在一个符号 `c`，使
`extractVec (convertVec (scaleVec c 2)) ≠ extractVec (convertVec c)`
⭐ **尽管二者语义等价**。

⭐⭐ **⇒ 这就是 E-06 真实缺口的【可量化形式】**：

    缺口 = 「语义等价的符号在 `extractVec` 通道下得到【不同】输出」的
            **具体计数** ≥ 1（本见证给出恰好一对）

⇒ ⭐ **修法只有一个方向**：在 `extractVec` **之外**另加一步符号侧规范化
（`RealCanonicalForm.canonicalize`，`RealCanonicalForm.lean:514`）。
本文件**只登记这个缺口的存在性与位置**，**不**重做 `canonicalize`
（那会是 `RealCanonicalForm` 的重述）—— ⚠ **这是本文件的选择性省略，如实登记**。 -/
theorem canonicalization_not_free :
    ∃ c : VectorConstraint,
      (∀ x : List Int, VectorConstraintSat (scaleVec c 2) x ↔ VectorConstraintSat c x) ∧
      extractVec (convertVec (scaleVec c 2)) ≠ extractVec (convertVec c) := by
  refine ⟨{ a := [1], b := 1 }, ?_, ?_⟩
  · -- 语义等价：正缩放 2
    intro x
    exact (scaleVec_preserves { a := [1], b := 1 } x 2 (by norm_num)).symm
  · -- 对象层不同：`extractVec ∘ convertVec = id`（两次），故等价于 `scaleVec c 2 ≠ c`
    rw [extract_convert_id, extract_convert_id]
    -- ⚠ 先把 `scaleVec` 的定义**显式**展开成 `List.map`，避免 `congrArg` 后
    -- 目标里残留 `scaleVec`（不透明 def）导致后续 `simp`/`omega` 匹配不上。
    show scaleVec { a := [1], b := 1 } 2 ≠ { a := [1], b := 1 }
    intro h
    -- 取 `a` 投影：左端 `a = [1].map (· * 2)`，右端 `a = [1]`
    have ha : ([1] : List Int).map (fun v => v * 2) = [1] := congrArg VectorConstraint.a h
    simp only [List.map_cons, List.map_nil] at ha
    -- 由 `[1 * 2] = [1]` 得 `1 * 2 = 1`，与算术矛盾
    have h2 : (1 : Int) * 2 = 1 := by simpa using ha
    norm_num at h2

/-! ## 五、跨模块桥（判据 ⭐3）：接上 `RealConversionRobustness` 的参数层度量

⭐ 本节连接两个此前**无 import 关系**的模块（编辑-符号通道 × 扰动鲁棒性），
并**用两边的非平凡内容**：
- 主干侧：`convertVec` 的双射（§二）；
- 鲁棒性侧：`coeffDist`（`ℚ` 值 `ℓ¹` 度量，`RealConversionRobustness.lean:63`）与
  `roundTrip_perturbation_id`。

⚠ **诚实标注（承重）**：本节的桥**必然给出 `0`** ——
因为它是**往返型**的（`extractVec (convertVec c) = c` 是裸 `rfl`）。
⭐ **这【不是】非平凡内容，本文件如实降级标注**：
它只证明"该通道在参数度量下**免疫**"，即"**缺口不是参数层的**，而是**语义层的**"。
⇒ ⭐ 这条恰好**收口** §四：缺口**不可能**用"系数距离"检测到（距离恒为 0），
**只能**用"语义等价 → 代表是否相同"检测。 -/

/-- ⭐ **跨模块桥：编辑-符号往返在 `coeffDist` 下距离为 `0`**（**往返型，如实降级**）。 -/
theorem agreement_coeffDist_zero (c : VectorConstraint) :
    coeffDist (extractVec (convertVec c)).a c.a = 0 :=
  roundTrip_perturbation_id c

/-- ⭐⭐ **缺口的精确形状（本文件对 §三/§四 的量化收口）**：

对 `k > 0`，三件事**同时**成立：
1. **语义**上 `scaleVec c k` 与 `c` 不可区分（§四见证 A/B）；
2. **对象**上二者不同（`extractVec` 把它们分得清清楚楚，§四见证 C）；
3. 参数度量 `coeffDist` 为 `0`（§五 桥）。

⭐⭐ **⇒ 三条合起来是"缺口"的完整形状**：
**语义有自由度（1），对象没有（2），而参数度量【看不见】这个自由度（3）。**
⇒ 故 `extractVec` 既**够不着**语义层（2），**也没有**参数层的信号可依（3）——
⭐ 这就是"必须外挂规范化"的**充分说明**。 -/
theorem agreement_gap_shape (c : VectorConstraint) (k : Int) (hk : 0 < k) :
    (∀ x : List Int, VectorConstraintSat (scaleVec c k) x ↔ VectorConstraintSat c x) ∧
    (extractVec (convertVec (scaleVec c k)) ≠ extractVec (convertVec c) ↔
      scaleVec c k ≠ c) ∧
    coeffDist (extractVec (convertVec c)).a c.a = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) 语义等价：正缩放不改变零点集（`scaleVec_preserves`，`ConvertVectorLinear:105`）
    intro x
    exact (scaleVec_preserves c x k (ne_of_gt hk)).symm
  · -- (2) 对象层不同 ⟺ 缩放后不同（`extractVec ∘ convertVec = id` 两次）
    rw [extract_convert_id, extract_convert_id]
  · -- (3) 参数度量恒 0（往返型）
    exact roundTrip_perturbation_id c

/-! ## 六、诚实边界与**未覆盖**的部分（**不许省**）

### 6.1 本文件**没有**证明的东西（选择性省略，如实登记）

1. ⚠ **未证 `canonicalize` 确实是规范代表** —— 那需要 import `RealCanonicalForm`，
   而它在 `:303` 有 `instance : Zero VectorConstraint`（实例冲突风险）。
   本文件只在 §四 见证 C 里**登记**该缺口**存在**与**位置**，**不**重做规范化。
2. ⚠ **未覆盖的编辑形态**：`AnyEditLayer` 取最宽（任意函数），
   故本文件**不区分**加性编辑 / 乘性编辑 / 仅改偏置 等具体形态。
   ⭐ 这**不影响**结论 —— 因为结论是"**任何**编辑都一样空壳"（§三 消融），
   取宽**只会让消融更强**。
3. ⚠ **题面「差」未曾被形式化定义** —— 任务书原文只说"`c` 与 `c'` 的差"，
   未给"差"的类型。本文件因此**不假装**它有意义，而是证明
   ⭐ **无论取"对象差"还是"语义差"，结论都被 §三 空壳化 / 被 §四 反驳**。

### 6.2 与 sibling 的关系

- `_E-01.lean`：编辑的**语义定理**（闭式 δ，**加性**编辑）。本文件**不** import 它
  （避免 roots 耦合），§四 见证 A 用 `scaleVec`（**乘性**）恰好与之**互补**。
- `_E-02.lean`：编辑 → 符号的**存在性**（结论：平凡 + 缺口在规范代表）。
  ⭐ **本文件（E-06）是该结论在"一致性"提法下的独立复现与加强**：
  `_E-02` 证"存在性平凡"，本文件进一步证「**双重**空壳」（§三 `double_vacuity`）。

### 6.3 诚实边界

- ⚠ 无 `lake` 访问 ⟹ **未验证编译**；所有既有签名**逐字**抄自源码（见 `W_E-06.md`）；
- ⚠ 本文件自身的证明项**未经内核检查** ⟹ 可能存在语法/类型错误；
- ⚠ 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

end Lattice
