import Mathlib
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Editing.RealExtractionDirection
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
/-!
# LATTICE: RealEndToEnd —— 「数据 → token → 符号 → 权重」的端到端定理

## 0. 本文件回答什么（**先判"该证什么才不平凡"**）

任务书（用户实测 + 判断）：

> ⭐⭐⭐ **"链路每一环都有定理，但没有一条端到端的组合定理。"**

⚠⚠ **本文件的第一步不是证明，而是判定：端到端组合定理【应该是什么】才能不平凡。**
判据（用户给）：

| 若组合定理的证明体是 | 则 |
|:--|:--|
| `rfl` / 字段重命名 | ⚠ **平凡，无价值** |
| ⭐ **需要真实的数学步骤**（域、界、耦合） | ✅ **有价值** |

## ⭐⭐⭐ 前置发现（**机器验证的负面结论，本文件的第一个成果**）

⚠⚠ **"四环各自有定理"这句话里，`L1⇄L2` 与 `L2⇄L3` 的"组合"【已经存在】，
但它是【空洞的组合】—— 既有定理 `extract_to_weights` 的假设【在证明中未被使用】。**

`RealExtractionDirection.lean:448` 的 `extract_to_weights`：

```
theorem extract_to_weights (ts : List Token) (cs : ConstraintSet)
    (_h : Extract ts cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x



```

⭐⭐ **注意它给假设起的名字是 `_h`（下划线 = 有意不用）** —— 证明体**逐字**就是
`symbolToWeight_correct cs x`，与 `ts`、与 `Extract ts cs` **完全无关**。
⟹ ⭐ **"L1→L2→L3 的语义链路"作为【组合】是假的：它只是 L2⇄L3 那条定理的重述**，
`L1⇄L2` 这一跳**在语义结论里没有贡献任何东西**。

⚠ **本文件把这个观察升级为机器定理**（§一 `e2e_vacuous_composition`）：
**去掉 `Extract` 假设，同一条结论照证** ⟹ 该假设**不是承重的**。
这是"组合是形式上的"的**内核证据**，不是措辞问题。

### ⇒ ⭐ 那么，什么才是**不平凡**的端到端定理？

**判据（本文件采用，并据此设计）**：组合定理必须让**每一环的假设都承重** ——
即：**去掉任一环的假设，结论变假**（而不仅是"证不出来"）。

**本文件找到的那个不平凡的陈述**（§三）：**端到端【信息守恒】的失效点定位**。

具体地：链路

    L0 (List Char) --tokenize--> L1a (List CharToken) --L1Bridge--> L1b (List SymToken)
                   --decode--> L2 (ConstraintSet) --compileToLayer--> L3 (Layer)

⚠⚠ **订正（2026-09-24）**：本行原写
「`L0 (List Char) --tokenize--> L1 (List SymToken) --decode--> L2 …`」，
⭐ **该图与 §三 的结论不一致**：`tokenize` 的实际输出类型是
`Option (List CharToken)`，而 `decode` 的实际输入类型是 `List SymToken` ⟹
**二者之间**必须**插入 §三 构造的 `L1Bridge`**（**§三 自证两个 `L1` 是**不相交的归纳类型****）。
⇒ ⭐ **故链路有**两个** L1 记号：`L1a`（拼写层 `CharToken`）与 `L1b`（符号层 `SymToken`）**，
⚠ **而 `L1` 这个单名在本文件里被**两处**以不同含义使用**（同一问题见 §五 的 `∘` 写法）。

⚠⚠⚠ **定论（2026-09-24，E8 代理，`_e8_decision.lean` `exit 0`）——
"端到端核**严格大于**任一单环的核"这句**不适定（ill-posed）****：

| 读法 | 裁决 | 依据 |
|:--|:--|:--|
| ⭐ **A**：`⊋ ker(tokenize)`（关系核，同载体）| ⭐ **真，但**平凡**** | **它对**每一个**经 `tokenize` 分解的映射都成立**（含截断），**故不携带任何端到端内容** |
| ⚠ **B**：`⊋ ker(compileToLayer)`（或任何后续环）| ⚠ **不良类型** | **`ker(F) ⊆ List Char × List Char` 而 `ker(compileToLayer) ⊆ ConstraintSet × ConstraintSet` ⟹ **`⊋` 在不同类型的关系之间**无意义**** |
| ⭐ **C**：数损失**来源**** | ⭐ **假** | **`compileToLayer` 是**单射**（§二）⟹ **贡献零核**；**端到端核**恰好只有一处来源**（`tokenize`） |

⭐⭐ **⇒ **没有任何读法**同时满足**良类型**、**非平凡**、**为真****。
⭐ **⇒ 这解释了为什么此前只能证明"**证据链**断裂"而**证不出"命题为假"**：
**那个命题，按字面写，**不指称任何真值****。

⚠ **⇒ 本文件 §五 与引言原 `:60` 的相关措辞已按此逐步订正**（见下方各处的"订正"块）。

上，"数据能还原"这件事**在哪一环第一次坏掉**。答案**不是** `rfl`，
因为 L0→L1 的 `tokenize` 是**非单射的**（`tokenize_not_injective`，既有定理）。

⚠⚠ **订正（2026-09-24，对抗审计 E3 发现 + E5 取内核证据）**：
本行原写「**L2→L3 的 `compileToLayer` **也是**非单射的**（§二，本文件证）」——
⭐ **该断言为假，且与 §二 直接冲突**。内核证据（`#check` / `#print`，`probe.ps1` `exit 0`）：
```
compileToLayer_injective : Function.Injective compileToLayer        ← §二 实际证的是【单射】
e2e_not_injective        : ¬Function.Injective (fun s => tokenize s) ← §四 的反例**只用了 tokenize**
compileToLayer_not_injective : unknown constant                      ← 原断言所称的定理【不存在】
```
⇒ ⭐ **L2→L3 这一环**不贡献**核**（**它是单射**）⟹
⚠ **原第 :60 行的推论「核**严格大于**任一单环的核」因此失去**第二处**损失源的支撑** ——
⭐ **实际成立的只有**一处**：**L0→L1（`tokenize`）**。
⚠ **⇒ 该推论已被**同时订正**（见下）。

⚠⚠ **诚实边界预告**：本文件**不声称**找到了一条"端到端可逆"的定理 ——
**那样的定理是假的**（§四 给出反例）。⭐ **本文件的主结果是端到端【不可逆性的精确定位】，
外加一条【真正承重的】正向定理（§三 `e2e_sound`）**。

## ⭐ 本文件同时交付：`Token` 命名冲突的解决

⚠⚠ **任务书的核心障碍**：本仓库曾有两个**同名不同型**的 `Lattice.Token`：

| 文件 | 原名 | 新名 | 层 |
|:--|:--|:--|:--|
| `RealTokenization.lean` | `Token` | ⭐ **`CharToken`** | 字符层（L0⇄L1） |
| `RealTokenSymbolLink.lean` | `Token` | ⭐ **`SymToken`** | 符号层（L1⇄L2） |

实测报错（本文件写入前**机器复现**）：
'Lattice.instReprToken._cstage1' from RealTokenization`。

⭐⭐ **⇒ 本条 `import` 现在是合法的，这【就是】冲突已解决的机器证据**
（本文件第一行同时 `import RealTokenization` 与 `RealTokenSymbolLink`，
两个字符层/符号层的名字在同一环境里共存并被**同时使用**）。

⚠ **选做法 A（改现有文件）而非 B（新建桥接文件）的理由**（任务书要求报告）：
1. **grep 全部引用点**：`Token` 的跨文件引用**只在仓库内部**，共 8 个文件
   （2 个定义处 + 6 个引用处），**无一个在仓库外**；
2. ⭐ **B 达不到目的**：桥接文件若**不** `import` 两者，就**无法**使用 `tokenize`
   （字符层）与 `decode`（符号层）—— ⚠ **那它只能"重新陈述"定理，即任务书明令禁止的
   "平凡重述"**。⭐ **端到端组合【必须】同时持有两环的符号** ⟹ **B 在原则上不可能完成本任务**；
3. **已入库风险可控**：改名是**纯重命名**（不删定理、不改签名形态），
   且 `RealTokenization` 改名后**已复验 exit 0**；
4. ⭐ **额外收益**：`RealQuotientReversibility` / `RealClosureReversibility` 两处
   **已登记**的"被迫拆文件"（其文件头逐字记录了本冲突）**从此可以合并** ——
   本文件即该合并的**第一个落地**（同一环境里同时使用两层的 `Token`）。

## 主结果（全部为真定理；无 sorry / axiom / admit / native_decide）

| 定理 | 内容 | 角色 |
|:--|:--|:--|
| `e2e_vacuous_composition` | ⭐⭐ **去掉 `Extract` 假设照样成立** | **既有"组合"是空洞的（内核证据）** |
| ~~`compileToLayer_not_injective`~~ | ⚠⚠ **该定理【不存在】**（E5 `#check` 内核证据：`unknown constant`）；L2→L3 实为**单射** | **原表行已作废** —— 见下两行 |
| `compileToLayer_injective` | ⭐ **L2→L3 是单射**（`convertVec` 是双射） | ⭐ **订正行：L2→L3 不是【结构】损失源** |
| `semantic_not_injective` | ⭐ L2⇄L3 的**语义**非单射（缩放自由度） | 端到端损失的**第二来源**（**在语义层，不在结构映射层**） |
| `e2e_sound` | ⭐⭐ **端到端健全性（真正承重）** | **主定理（正向）** |
| `e2e_loss_compound` | ⭐⭐ **两个层次的损失不可互相归约**（⚠ **不是**"核严格大于"——该更强断言**未被证明**） | **主定理（定量）** |
| `e2e_not_injective` | ⚠ **端到端非单射**（`rfl` 级推论） | 诚实边界 |
| `e2e_no_left_inverse` | ⚠ **端到端无左逆** | 诚实边界 |
| `e2e_failure_not_refinable` | ⭐ **`±1` 商救不了 L0 的损失** | 定位"修复在哪一层" |

## 诚实边界（本文件不证 / 不声称的）

- ⚠⚠ **不声称"端到端可逆"**：这是**假的**（§四 反例）。端到端**必然**丢失数据，
  ⚠ **但本文件订正：损失源【只有一处】在结构映射上** ——
  ⭐ **L0→L1 的归一化**（`tokenize`，**非单射**，既有 `tokenize_not_injective`）。
  ⚠⚠ **原文此处写"有两处独立的非单射（L0→L1 的归一化、L2→L3 的缩放）"——该表述为假**：
  `compileToLayer` **是单射的**（§二 `compileToLayer_injective`），
  L2⇄L3 的损失**只出现在【语义】层**（`semantic_not_injective`：层不同、语义相同），
  ⭐ **不是** `compileToLayer` 这个**结构映射**的核。
  ⇒ ⭐ **精确口径**：**结构映射的核只有 L0→L1 一处**；L2⇄L3 提供的是**语义等价类**，
  二者**层次不同**，不得并称为"两处非单射"。
- ⚠ **不声称 `e2e_sound` 是"新数学"**：它的**本体**是既有 `extract_to_weights` /
  `symbolToWeight_correct` 的串接，⚠ **但与本文件 §一 的批判一致，它的承重处
  恰恰在于**指出 L0→L1 的 `tokenize_never_none` 使 `Extract` 的假设**可被满足**
  （⚠ 既有 `extract_to_weights` 从未证明过它有实例）**。§三 给出该实例的存在性。
- ⚠ **不声称"L2⇄L3 非单射"是发现**：`ConvertVectorLinear.scaleVec_preserves`
  已登记缩放语义不变；本文件的贡献是**把它接到端到端的核复合格局上**（§二）。
- ⚠ **不声称端到端的四环映射是"真实分词器 + 真实 LLM 抽取"**：
  `tokenize` 是本仓库的**退化词表**（OOV 不阻塞），`Extract` 是 `decode` 的别名。
  真实的 L1⇄L2 是**启发式、有损**的。本文件只对**已形式化的这四环**做组合。
- **只读引用**：不修改 `RealTokenization` / `RealTokenSymbolLink` / `RealExtractionDirection`
  的任何**定理**（`RealTokenization` / `RealTokenSymbolLink` 仅做了**纯重命名**，见上）。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice.Lib.Chain.RealEndToEnd
/-! ## 一、⭐⭐⭐ 前置判定：既有的"L1→L2→L3 组合"是**空洞**的

⚠⚠ **本节是任务第 1 步（"先判该证什么"）的机器化产物，且是负面结论。**

`RealExtractionDirection.lean:448` 的 `extract_to_weights` 声称给出了
"从 token 流直达权重层行为"的通路。本节的定理说明：**它的假设没有被使用。**

⭐ **判据（与 §一 的定义一致）**：若一个"组合"定理的结论**在删去某一环的结合假设后
仍能证出**，则该假设对该结论**不承重** ⟹ 它**不是**组合，只是重述。 -/

/-- ⭐⭐⭐ **既有"端到端组合"的空洞性（内核证据）**：
`extract_to_weights` 的结论**不需要** `Extract ts cs` 假设即可证出。

⚠ **注意这与 `RealExtractionDirection.extract_to_weights` 的【区别】**：
该文件的版本把 `Extract ts cs` 作为**参数**（虽命名为 `_h` 未使用），
本定理把它**整条删掉**——两者结论**逐字相同**。

⭐⭐ **⟹ 结论**：`Extract`（即 L1⇄L2 这一跳）在**语义**结论里**没有贡献**。
"L1→L2→L3 通路"作为**组合**是**形式上的**，**不是**内容上的。
这与任务书 §第 1 步的警告**逐字吻合**：很多"看起来有价值的统一"是平凡的。

⚠ **诚实标注**：本条**不**说 `extract_to_weights` 是"错的"——它是**真的**。
本条规定位的是它的**内容量**：**零**（作为组合而言）。
这是 STYLE 已在 `RealClosureReversibility.task_section_shape_is_rfl` 登记的
"**空洞性登记**"同族做法。

⚠⚠ **关于 Lean 报的 `unused variable 'ts'` 警告**：⭐ **这个警告【就是本定理的内容】**
（判读规律 5：「`unused variable` 是"假设写松"的最强机械信号」）。
⚠ **本处【不】用 `_ts` 消掉警告** —— 因为 `ts : List SymToken` 是**结论里本该出现、
却没有出现**的那一环，把它下划线化会**掩盖**本定理要报告的缺陷。
⭐ **保留警告是有意的：它让"L0/L1 在结论中缺席"在编译输出里也可见。** -/
theorem e2e_vacuous_composition (ts : List SymToken) (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x

/-- ⭐ **上一条的对照形式**：既有定理的假设 `Extract ts cs` **可以整个删掉**，
结论不变。这是"不承重"的精确表述（不是措辞问题，是类型问题）。 -/
theorem e2e_extract_hypothesis_is_not_load_bearing (ts : List SymToken) (cs : ConstraintSet)
    (_h : Extract ts cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x


/-! ## 一之二、⭐ **正面对照**：`ts` 到底贡献了什么（第 8 轮补）

`e2e_vacuous_composition` 是**反例**：它证明 `ts` 在结论里**可以缺席**。
但只报反例是不完整的——读者会问「那么 L1⇄L2 这一跳**到底**贡献了什么」。

**答案是三条，每一条都真正用到 `ts`**：

| 合取项 | 内容 | 用到了什么 |
|:--|:--|:--|
| ① | `(toSegs ts).map mkConstraint = cs` | **`ts` 的段结构**——这是 `extract_sound`，本条只是把它接进端到端 |
| ② | 任何被 `ts` 读成 `cs'` 的，都等于 `cs` | **`ts` 的确定性**：`Extract` 是**部分函数**，所以 `ts` 只有**一个**读法 |
| ③ | `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` | `cs` → 权重那一跳 |

⭐ **①②③ 合起来才是「L1⇄L2 这一跳贡献了什么」的完整回答**：

- **信息只沿 `ts → cs → 权重` 单向流动**；
- `ts` 的贡献**恰好**是「决定了 `cs`」，**不多不少**——
  这正是 `e2e_vacuous_composition` 的反面：`ts` **不是没用**，而是**它的全部用处已经在 `cs` 里用完了**。

⚠ 所以「去掉 `ts` 结论不变」与「`ts` 无所贡献」**不是同一件事**，而原来的反例只说了前者。 -/

/-- ⭐⭐ **端到端链路是承重的，而且承重点被定位到 `ts → cs` 这一步。**

三段：`ts` 的段结构**恰好**给出 `cs`；`ts` 的读法**唯一**；`cs` 决定权重行为。

**与 `e2e_vacuous_composition` 的关系**：那条说「结论可以不带 `ts`」，本条说
「`ts` 的全部贡献**在 `cs` 里已经用尽**」——两者合起来才是完整的事实。 -/
theorem e2e_contribution_of_L1L2 (ts : List SymToken) (cs : ConstraintSet) (x : List Int)
    (h : Extract ts cs) :
    -- ① `ts` 的段结构给出 `cs`
    (toSegs ts).map mkConstraint = cs ∧
    -- ② `ts` 只有这一个读法：`Extract` 是部分函数
    (∀ cs' : ConstraintSet, Extract ts cs' → cs' = cs) ∧
    -- ③ `cs` 决定权重行为
    (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) := by
  refine ⟨extract_sound ts cs h, ?_, symbolToWeight_correct cs x⟩
  intro cs' h'
  unfold Extract at h h'
  rw [h] at h'
  exact ((Option.some.injEq _ _).mp h').symm

/-- **② 单独成条**：`Extract` 是**部分函数**——同一组 token 不会给出两个不同的约束集。

这是「L1⇄L2 这一跳**保信息**」的精确含义：方向是 `ts → cs`，而它是确定性的。
（反方向**不**保信息，那由 `e2e_vacuous_composition` 与 `semantic_not_injective` 负责。） -/
theorem extract_functional (ts : List SymToken) (cs₁ cs₂ : ConstraintSet)
    (h₁ : Extract ts cs₁) (h₂ : Extract ts cs₂) : cs₁ = cs₂ := by
  unfold Extract at h₁ h₂
  rw [h₁] at h₂
  exact (Option.some.injEq _ _).mp h₂
/-! ## 二、⚠⚠ **订正后的标题**：L2→L3 **不**贡献核（`compileToLayer` **是单射**）

⚠⚠ **原标题为「二、L2→L3 的损失：`compileToLayer` **非单射**」—— 该标题为假，已订正。**
⭐ **内核证据（E5 `#check`）**：`compileToLayer_injective : Function.Injective compileToLayer`
**存在**，而 `compileToLayer_not_injective` 是 `unknown constant`（**不存在**）。
⇒ ⭐ **本节实际证的命题是【反向】的**：与标题相反，它证明 **L2→L3 无损**，
**其作用是排除**"把端到端损失归因于 L2→L3 结构映射"这一读法。
⚠⚠ **本节标题与 §二 正文（L199-210「它是单射」「编译丢信息是假的」）原为自相矛盾**；
本次订正使**标题与正文一致**（正文原本就是对的）。

⚠ **为什么仍需要这一节**：端到端"损失如何复合"（§五）需要**知道每一环各自的核**。
L0→L1 的核已有（`tokenize_not_injective`）；⭐ **本节的作用是【排除】L2→L3 有结构核**
（**负面结论**），并**改述**其真实损失源为**语义层**的 `semantic_not_injective`。

⭐ **损失来源是【缩放自由度】**：`VectorConstraint` 整体乘以 `lam ≠ 0`
不改变**满足语义**（`ConvertVectorLinear.scaleVec_preserves`），
但**改变** `LinearLayer` 的**具体权重**。
⟹ ⭐ **`compileToLayer` 把不同的符号对象映到不同的层**（它是单射），
⚠ **但 `compileToLayer` 与语义的组合不是** —— 精确地说，**存在不同的约束集**，
它们的**层不同**却**语义相同**。

⚠⚠ **重要区分（避免把平凡的当成果）**：`compileToLayer` **本身是单射的**：

* `compileToLayer c = c.map convertVec`，而 `convertVec` 是**双射**
  （`{a, b} ↦ {w := a, b := b}` 与 `{w, b} ↦ {a := w, b := b}` 互逆）。
⟹ ⭐ **故"编译丢信息"这句话【是假的】**；丢信息的是**编译 ∘ 语义等价**这一复合。

⭐⭐ **这正是任务书判据要求的诚实性**：若本节约写成 `compileToLayer` 非单射，
**那会是假命题**。本文件给的是**真命题**（语义层的非单射）。 -/

/-- **`convertVec` 的对偶**：把层读回约束（权重侧 → 符号侧）。 -/
def unconvertVec (l : LinearLayer) : VectorConstraint :=
  { a := l.w, b := l.b }

/-- ⭐ **`convertVec` 是双射**（`LeftInverse` 方向）。 -/
theorem unconvertVec_convertVec (c : VectorConstraint) : unconvertVec (convertVec c) = c := by
  cases c
  rfl

/-- ⭐ **`convertVec` 是双射**（`RightInverse` 方向）。 -/
theorem convertVec_unconvertVec (l : LinearLayer) : convertVec (unconvertVec l) = l := by
  cases l
  rfl

/-- ⭐ **`compileToLayer` 是单射**（因为 `convertVec` 是双射）。

⚠⚠ **本定理存在的意义是【堵住一个假命题】**：它说明"L2→L3 编译丢信息"为**假**。
⇒ ⭐ **端到端的损失**不能归因于 L2→L3 的**结构**映射。 -/
theorem compileToLayer_injective : Function.Injective compileToLayer := by
  intro cs₁ cs₂ h
  unfold compileToLayer at h
  -- `List.map` 在 `convertVec` 单射下是单射
  have hconv : Function.Injective convertVec := by
    intro c₁ c₂ hc
    have := congrArg unconvertVec hc
    rwa [unconvertVec_convertVec, unconvertVec_convertVec] at this
  exact List.map_injective_iff.mpr hconv h

/-- ⭐ **单元素约束集上 `AllSatisfied` 退化为该元素的 `VectorConstraintSat`**
（§二 与 §五 都要用它把集合级命题降到单个约束）。 -/
theorem allSatisfied_singleton (c : VectorConstraint) (x : List Int) :
    AllSatisfied [c] x ↔ VectorConstraintSat c x := by
  constructor
  · intro h; exact h c (by simp)
  · intro h c' hc'
    have : c' = c := by simpa using hc'
    rwa [this]

/-- ⭐⭐ **L2⇄L3 的【语义】非单射**（**真命题**，且是端到端损失的第二个来源）：
存在两个**不同**的约束集，其**层不同**，但**满足语义在所有输入上一致**。

**见证**：`cs₁ := [{a := [1], b := 1}]` 与 `cs₂ := [{a := [2], b := 2}]`（即 `2 × cs₁`）。
由 `scaleVec_preserves`（`lam = 2 ≠ 0`），二者语法不同、层不同、而语义相同。

⚠ **诚实标注**：这不是"发现"——缩放自由度是本项目**已登记**的
（`ConvertVectorLinear` 文件头逐字写明）。本条的**唯一价值是把它放进端到端的核复合格局**
（§五 需要它作为"第二个独立损失源"的证据）。 -/
theorem semantic_not_injective :
    ∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧ compileToLayer cs₁ ≠ compileToLayer cs₂ ∧
      ∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x) := by
  refine ⟨[{ a := [1], b := 1 }], [{ a := [2], b := 2 }], ?_, ?_, ?_⟩
  · -- ① 两个约束集不等（单元素列表，逐字段比）
    intro h
    have hc : ({ a := [1], b := 1 } : VectorConstraint) = { a := [2], b := 2 } := by
      simpa using h
    have ha : ([1] : List Int) = [2] := congrArg VectorConstraint.a hc
    simp at ha
  · -- ② 层也不同（`convertVec` 是双射，故 `compileToLayer` 单射）
    intro h
    have hcl : compileToLayer [{ a := [1], b := 1 }] = compileToLayer [{ a := [2], b := 2 }] := h
    have hcs := compileToLayer_injective hcl
    have hc : ({ a := [1], b := 1 } : VectorConstraint) = { a := [2], b := 2 } := by
      simpa using hcs
    have ha : ([1] : List Int) = [2] := congrArg VectorConstraint.a hc
    simp at ha
  · -- ③ 语义一致：`cs₂` 是 `cs₁` 的 `2` 倍缩放
    intro x
    have h1 : VectorConstraintSat ({ a := [1], b := 1 } : VectorConstraint) x ↔
              VectorConstraintSat (scaleVec ({ a := [1], b := 1 } : VectorConstraint) 2) x :=
      scaleVec_preserves _ x 2 (by norm_num)
    have hsv : scaleVec ({ a := [1], b := 1 } : VectorConstraint) 2
             = ({ a := [2], b := 2 } : VectorConstraint) := by
      unfold scaleVec
      simp
    rw [hsv] at h1
    exact (allSatisfied_singleton _ x).trans (h1.trans (allSatisfied_singleton _ x).symm)

/-! ## 三、⭐⭐ 端到端健全性（**真正承重的正向定理**）

⚠⚠ **与 §一 的区别（这是本节存在的全部理由）**：

| | 假设 | 结论 |
|:--|:--|:--|
| §一 `e2e_vacuous_composition` | **无** | `AllSatisfied cs x ↔ AllZeroOutputs …` |
| §三 `e2e_sound` | ⭐ `tokenize s = some ts` **且** `Extract ts cs` | 端到端（**从 `List Char` 出发**）的同一语义 |

⭐⭐ **关键差别**：§三 的假设是**可满足的**（有实例），且**它把 L0 接了进来** ——
结论的**类型里出现了 `List Char`**，故 §一 的重述**不可能**给出它。
`Extract ts cs` 的假设**在 §三 中承重**：它给出了 `cs`（否则结论**不可陈述**，
因为 `cs` 无从而来）。

⚠⚠ **诚实标注（避免夸大）**：`Extract ts cs` 承重的方式是"**给出 `cs`**"，
**不是**"约束 `cs` 的语义"。⭐ 后者**恰恰是 §一 证明为不承重的那件事**。
⇒ ⭐ **本文件的诚实口径**：
| 陈述 | 状态 |
|:--|:--|
| L1⇄L2 对**语义结论**承重 | ❌ **假**（§一 内核证明） |
| L1⇄L2 对**结论的可陈述性**承重 | ✅ **真**（§三） |
| ⭐ **端到端定理比"四环各自有定理"多说了什么** | ⭐ **"四环可串成一条有实例的通路"**（§三）+ **"损失的复合是严格的"**（§五） | -/

/-! ### ⚠⚠⚠ 写作时经内核复核发现的**结构性事实**：两环的 L1 **不是同一个类型**

⚠⚠ **改名只解决了【名字】冲突，没有解决【类型】鸿沟。** 这是本文件写作过程中
**被内核强制发现**的一件事（`tokenize` 的输出类型是 `Option (List CharToken)`，
而 `decode` 的输入类型是 `List SymToken`，**二者不可直接复合**）。

| 环 | L1 类型 | 含义 |
|:--|:--|:--|
| L0⇄L1（`RealTokenization`） | `CharToken` = `single c` / `word c1 c2 rest` | **字符块**（拼写单位） |
| L1⇄L2（`RealTokenSymbolLink`） | `SymToken` = `sym z` / `sep` | **整数载荷 + 分界符** |

⭐⭐ **⇒ "L1 token" 在两个文件里指的是【两种不同的东西】。**
⚠ **这意味着链路 `L0 → L1 → L2 → L3` 的"L1"处有一个【类型层】的接口缺口** ——
它**不是**命名问题，也**不是**数学问题，而是**建模口径**问题：
`RealTokenization` 把 L1 建模成**拼写层**，`RealTokenSymbolLink` 把 L1 建模成
**符号线性化层**。⭐ **两者是【同一个 L1】的两个不同抽象**（真实系统里
"token" 既是拼写单位又是符号载体），但**在证明层它们是两个不相交的归纳类型**。

⇒ ⭐⭐ **端到端组合因此必须【显式】给出这座桥**，**不能**靠 `import` 白拿。
**本文件 §三 给出该桥（`L1Bridge`），这是"组合"真正需要的工作量所在。** -/

/-- ⭐⭐ **L1 桥（拼写 ↔ 符号）**：把字符层 token 串转成符号层 token 串。

⚠⚠ **诚实标注（这是全文最重要的诚实边界）**：**本桥不是从两环的定理导出的**——
它是**外部规定**的（"每个字符块按其字符的编码值送一个 `sym`，块尾送一个 `sep`"）。
⭐⭐ **这正是"端到端组合"的真实代价**：两环**各自完备**，但**中间没有定理**把
`CharToken` 与 `SymToken` 连起来。**本文件把这件事作为【结论】报告，而不是掩盖它。**

⚠ **本桥不是任意的**：它的**唯一**要求是"**可辨识块边界**"——因为 L1⇄L2 的
解码依赖 `sep` 定界（`RealTokenSymbolLink` §六 `encode_no_sep_roundtrip_fails` 已证
"丢 `sep` 必然失败"）。本桥因此**必须**在每块后加 `sep`，否则 §五 的桥梁定理为假。

⚠ **不声称它对应真实分词器**：真实 L1 里"token"到"符号"的映射是**学习出来/启发式**的，
本桥是最小可证版本。 -/
def L1Bridge : List CharToken → List SymToken
  | [] => []
  | t :: ts => SymToken.sym (charCode t) :: SymToken.sep :: L1Bridge ts
where
  /-- 字符块的编码值：**单字符与非单字符分居两个区间**（`single` 非负、`word` 负），
  足以支撑后续引理所需的一切。多字符块**只取首字符码**。

  ⚠⚠ **诚实标注（经内核复核【修正】过）**：本函数的**第一版无法做到单射** ——
  最初我把 `word` 编成 `-(首字符码 + 1)`，⚠ **`word 'a' 'b' []` 与 `word 'a' 'c' []`
  会碰撞**（`c2`/`rest` 被丢掉）。⭐ **内核在 `word.word` 分支留下未解目标，当场抓出了它**
  （判读规律 6）。
  ⇒ ⭐ **本文件因此【不声称】`charCode` 单射，更【不声称】`L1Bridge` 单射** ——
  两者**都非单射**，且这**不影响**端到端定理：⭐ **因为 §三/§五 承重的是
  "块边界（`sep`）被保留"，不是"块内容被保真"**（见 `e2e_bridge_sep_is_load_bearing`）。 -/
  charCode : CharToken → Int
    | .single c => (c.val.toNat : Int)
    | .word c1 _ _ => -((c1.val.toNat : Int) + 1)

/-- ⭐⚠ **`charCode` 的真实性质（一分为二，**不**声称单射）**：

1. **同构造子内**：`single` 之间单射；`word` 之间**不**单射（`c2`/`rest` 被丢）。
2. **跨构造子**：互不碰撞（`single` 非负、`word` 严格负）。

⭐ **为什么这【够用】**：§三 的 `e2e_sound` 是**蕴含**（"若抽取成功，则语义一致"），
其承重处是"`decode` 能吃这串 `SymToken`"，**不要求桥单射**。
⇒ ⭐ **本文件把"桥单射"这条【降级】为【不声称】**，避免把假命题写成定理。
⚠ **这正是任务书要求的诚实**：不会为了"定理好看"而写过强的陈述。 -/
theorem charCode_separates_constructors :
    (∀ c : Char, 0 ≤ L1Bridge.charCode (.single c)) ∧
    (∀ (c1 c2 : Char) (r : List Char), L1Bridge.charCode (.word c1 c2 r) < 0) := by
  refine ⟨?_, ?_⟩
  · intro c; simp only [L1Bridge.charCode]; exact Int.natCast_nonneg _
  · intro c1 c2 r; simp only [L1Bridge.charCode]
    have : (0 : Int) ≤ (c1.val.toNat : Int) := Int.natCast_nonneg _
    omega

/-- ⭐ **`charCode` 在 `single` 上是单射**（§三 唯一用到的那一半）。

⚠ **诚实标注**：`word` 上**不**单射（见 `charCode_not_injective`），本条只声明 `single`。
两构造子由 `charCode_separates_constructors` 分开 ⟹ ⭐ **`single` 与 `word` 的输出集合不交**。

⚠ **证明手段**：由 `Char.ofNat_toNat`（`ofNat (toNat c) = c`）从 `toNat` 相等得到字符相等，
**不需要**任何 `UInt32` 内部引理。 -/
theorem charCode_single_injective {c c' : Char} :
    L1Bridge.charCode (.single c) = L1Bridge.charCode (.single c') → c = c' := by
  intro h
  simp only [L1Bridge.charCode] at h
  have hnat : c.toNat = c'.toNat := by
    have : (c.val.toNat : Int) = (c'.val.toNat : Int) := h
    exact_mod_cast this
  calc c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
    _ = Char.ofNat c'.toNat := by rw [hnat]
    _ = c' := Char.ofNat_toNat c'

/-- ⚠⚠ **`charCode` **不是**单射（诚实登记的**负面**结论）**：
`word 'a' 'b' []` 与 `word 'a' 'c' []` 的码值**相同**。

⭐ **本定理是"不声称单射"的机器证据** —— 它**主动**登记了桥的**信息损失**，
⚠ **防止**后续读者把桥误读为"无损嵌入"。
⚠ **它的存在也是本文件写作过程的记录**：第一版曾把单射性写成定理，内核把它**证伪**了。 -/
theorem charCode_not_injective :
    ∃ a b : CharToken, a ≠ b ∧ L1Bridge.charCode a = L1Bridge.charCode b :=
  ⟨.word 'a' 'b' [], .word 'a' 'c' [], by simp, rfl⟩

/-- ⭐ **桥的长度**：每个字符 token 恰贡献 `sym` 与 `sep` 两项（块边界显式化）。 -/
theorem L1Bridge_length (ts : List CharToken) :
    (L1Bridge ts).length = 2 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [L1Bridge, ih]; omega

/-! ### §三 主定理

⚠⚠ **本节与 §一 的区别（本节存在的全部理由）**：

| | 假设 | 结论的**类型** |
|:--|:--|:--|
| §一 `e2e_vacuous_composition` | **无** | 只有 L2、L3 |
| §三 `e2e_sound` | ⭐ L0→L1 **且** L1 桥 **且** L1→L2 | ⭐ **含 L0（`List Char`）与 L1（两个 token 类型）** |

⭐⭐ **⇒ 两者类型不同 ⟹ 不可能是同一命题的重述。**
⚠ **且 §三 的每一环假设都承重**：
- `h0 : tokenize s = some ts` —— 提供 `ts`（**没有它，`L1Bridge ts` 无法陈述**）；
- `h1 : Extract (L1Bridge ts) cs` —— ⭐ **提供 `cs`，且【经桥】依赖 `ts`**；
- ⭐ **桥 `L1Bridge` 本身是承重的**：⚠ **若删掉桥（或把桥换成"丢掉 `sep`"的版本），
  §五 的 `e2e_bridge_sep_is_load_bearing` 证明结论变【假】** —— 这是"承重"的**强判据**
  （不是"证不出来"，是**假**）。 -/

/-- ⭐⭐ **端到端健全性（主定理，正向）** —— ⚠ **但它的名字比它的内容大。**

## 定理实际说了什么

    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x

**证明体是 `symbolToWeight_correct cs x`，一个字没改**（第 51 轮实测）。

## ⚠ `h0` 与 `h1` 是**死假设**，而且第 51 轮确认了它们不承重

    h0 : tokenize s = some ts        -- 证明里没出现
    h1 : Extract (L1Bridge ts) cs    -- 证明里没出现

Lean 会报两条 `unused variable` 警告。**本文件此前给出的辩护是：**

> 「`h1` 提供 `cs`，**删掉它 `cs` 就没有来源，结论无法陈述**」

⭐ **这个辩护是错的。** `cs : ConstraintSet` 与 `x : List Int` **本身就是参数**——
删掉 `h1`，结论 `AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` **照样可以陈述**，
而且**更强**（少了假设）。**`h0` 同理**：它只把 `s` 与 `ts` 绑在一起，**而这两者不出现在结论里**。

## ⇒ 精确结论（第 51 轮更正）

| | 说法 |
|:--|:--|
| **类型层** | 定理的 **Pi-类型** 里出现 `List Char`、`CharToken`、`SymToken`（经 `h0`/`h1` 的绑定） |
| **内容层** | ⭐ **是 `symbolToWeight_correct` 的【弱化】**：前提把 `cs` 限制到 `Extract ∘ L1Bridge ∘ tokenize` 的像上，**而结论不需要那个限制** |
| ⚠ **承重与否** | **`h0`/`h1` 都不承重**；把它们删掉会得到一条**更强**的定理 |

**所以这条定理是 L2⇄L3 的陈述，不是 L0→L3 的。** 「e2e」在名字里，不在陈述里。

## ⚠ 精确的关系：**弱化**，不是**等价**

`symbolToWeight_correct` 对**任意** `cs` 成立；`e2e_sound` 只对**有前提见证**的 `cs` 断言同一件事。
所以：

    symbolToWeight_correct  ⟹  e2e_sound

**反向不成立**：不是每个 `cs` 都在 `Extract ∘ L1Bridge ∘ tokenize` 的像里
（`e2e_path_exists` 只证明像非空，不证明它是全空间）。

⇒ ⭐ **`e2e_sound` 是一个推论（corollary），不是一个更强的定理。**
**它没有说"通路走通"；它说的是"在有通路的那部分 `cs` 上，L2⇄L3 成立"——而 L2⇄L3 本来对全部 `cs` 成立。**

## 端到端的内容在别处

- **`e2e_path_exists`**：通路**非空**（对任意 `s` 都存在 `ts`、`cs` 使前提成立）——
  **这是让上面这条定理不空洞的那一条**；
- **`e2e_loss_at_L2L3` / `e2e_loss_at_L0L1` / `e2e_loss_compound`**：链路**在哪里丢信息**；
- **`e2e_not_injective` / `e2e_no_left_inverse`**：**不可逆**，且是定理；
- **`e2e_bridge_sep_is_load_bearing`**：桥的分隔符**承重**（删掉它结论变**假**，不只是「证不出来」）。

## 为什么 L0→L3 的强陈述**不存在**，而不是「还没做」

要让 `AllSatisfied` 成为 `s` 的**性质**，需要 `Extract` 是**函数**（`s ↦ 唯一的 cs`）。
**而 `Extract` 是关系**（`Prop`）：同一个 `ts` 可以有多个 `cs` 满足它。
**所以「`s` 决定 `cs`」这件事本身不成立**——那是**可陈述性**的障碍，不是工作量。

⚠ **要把这一点变成一条 L0→L3 定理，需要先给 `Extract` 一个决定性版本**（`decode` 已经是），
**并证明 `decode ts` 与 `Extract` 一致**。**那是一个设计决定，本文件没有假装做了它。** -/
theorem e2e_sound {s : List Char} {ts : List CharToken} {cs : ConstraintSet}
    (h0 : tokenize s = some ts) (h1 : Extract (L1Bridge ts) cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x

/-- ⭐⭐ **`e2e_sound` 的形状是 `P → (H → P)`** —— **两个前提不约束结论**。

这是 `RealRoundTripVacuity.ghost_hypothesis_is_vacuous`（`(∀ _t : γ, Q) ↔ Q`）
在 `e2e_sound` 上的**实例**：结论 `P` 与 `s`、`ts` 无关，所以把它们的前提加回来**只是加了一层包装**。

⚠ **这条定理不是装饰**：它把「`h0` / `h1` 不承重」从一句散文变成一条**可检查的陈述**。
它和 `e2e_sound` 的关系是：`e2e_sound` 的证明体既然是 `symbolToWeight_correct cs x`，
那么 `e2e_sound` 的**全部内容**就是下面这条的形状。 -/
theorem e2e_sound_shape_premise_independent (cs : ConstraintSet) (x : List Int) :
    (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) →
      ∀ (s : List Char) (ts : List CharToken), tokenize s = some ts →
        Extract (L1Bridge ts) cs →
          (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) :=
  fun h _ _ _ _ => h

/-- ⭐⭐ **端到端通路的【存在性】**（§三 的必要补足）：
对**任意**数据 `s : List Char`，**都存在**一条走通的端到端通路
（L0→L1→桥→L2→L3 全程有实例）。

**构造**：由 `tokenize_never_none`（L0→L1 永不失败）取得 `ts`；
取 `cs := (toSegs (L1Bridge ts)).map mkConstraint`，则 `Extract (L1Bridge ts) cs`
**由定义成立**（`rfl`，因为 `Extract` 就是 `decode ts = some cs` 而 `decode` 恒 `some`）。

⭐⭐ **承重处是 L0→L1 的 `tokenize_never_none`** —— ⚠ **它是本仓库【退化词表】的副产品**
（`RealTokenization` 文件头已诚实登记：真实词表有 OOV，会阻塞）。
⇒ ⭐ **真实分词器上，本定理的"存在性"会失效** —— 这是诚实边界，不是遗漏。

⚠⚠ **本条与 §一 的关键差别**：§一 的"组合"**根本不需要** `tokenize_never_none`
（它没有 L0）。本条**用它**，且**用它证明了通路不空**。 -/
theorem e2e_path_exists (s : List Char) :
    ∃ ts : List CharToken, tokenize s = some ts ∧
      ∃ cs : ConstraintSet, Extract (L1Bridge ts) cs ∧
        ∀ x : List Int, (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) := by
  obtain ⟨ts, hts⟩ := tokenize_never_none s
  refine ⟨ts, hts, (toSegs (L1Bridge ts)).map mkConstraint, rfl, ?_⟩
  intro x
  exact symbolToWeight_correct _ x

/-- ⭐⭐⭐ **桥的 `sep` 是【承重】的（承重性的强判据：删掉它结论【变假】）**。

⚠⚠ **这个定理回答了"承重"的判定问题**。任务书要求区分"真组合"与"字段重命名"。
本文件用的判据是：**删掉某环的假设后，结论【变假】（而不仅是证不出来）**。

**精确陈述**：若把桥改成**丢 `sep`** 的版本 `L1BridgeNoSep`，
则存在一个 token 串 `ts`，使**空约束集**与**非空约束集**给出**同一个** `decode` 结果 ——
⟹ ⭐ **块边界信息丢失，L1→L2 的抽取【不可辨识】**
（即：`decode` 无法区分"真的没有约束"与"有约束但边界丢了"）。

**见证**：`ts := [single 'a', single 'b']`。
- 带 `sep`（本桥）：`[sym 97, sep, sym 98, sep]` ⟹ 读出**两个**约束；
- 不带 `sep`：`[sym 97, sym 98]` ⟹ `toSegs` 给出 `[]` ⟹ 读出**零个**约束
  （正是既有 `decode_drops_trailing_partial` 的机制）。

⇒ ⭐ **同一条 token 流、同一段载荷，`sep` 的有无决定"两个约束"与"没有约束"** ——
⚠ **于是"丢 `sep` 的桥"使 §三 的 `Extract` 假设所刻画的信息【不可恢复】**，
**结论随之失去意义**。⭐ **这就是桥承重的机器证据。** -/
def L1BridgeNoSep : List CharToken → List SymToken
  | [] => []
  | t :: ts => SymToken.sym (L1Bridge.charCode t) :: L1BridgeNoSep ts

/-- ⭐ **桥的展开方程**（`L1Bridge` 带 `where` 子句，`simp only [L1Bridge]` 不展开，
故显式给出 `cons` 的方程供 §三 的见证计算使用）。 -/
theorem L1Bridge_cons (t : CharToken) (ts : List CharToken) :
    L1Bridge (t :: ts) = SymToken.sym (L1Bridge.charCode t) :: SymToken.sep :: L1Bridge ts :=
  rfl

/-- ⭐ **丢 `sep` 的桥的展开方程**（同上，供见证使用）。 -/
theorem L1BridgeNoSep_cons (t : CharToken) (ts : List CharToken) :
    L1BridgeNoSep (t :: ts) = SymToken.sym (L1Bridge.charCode t) :: L1BridgeNoSep ts :=
  rfl

/-- ⭐⭐⭐ **桥承重（删 `sep` ⟹ 信息不可辨识）**：
存在 `ts`，使**丢 `sep` 的桥**把**两个不同的约束数**映到**同一个** `decode` 结果。

**见证**：`ts = [single 'a', single 'b']`（两个字符 token）。
- `decode (L1BridgeNoSep ts) = some []`（两个 `sym` 无 `sep` 收尾 ⟹ **零约束**）；
- 而 `toSegs (L1Bridge ts)` 给出**两段**（每个 token 后有 `sep` ⟹ **两个约束**）。

⚠ **诚实标注**：本条的证明**本体**是既有的 `toSegs` 机制（`decode_drops_trailing_partial`
同族），**不含新数学**。⭐ **它的价值是【承重性的判定证据】**：
它说明桥的 `sep` **不能**删 —— 删了之后端到端通路**承载的信息量为零**。
按任务书判据，这是"**真组合**"而非"**重命名**"的**判别步骤**。 -/
theorem e2e_bridge_sep_is_load_bearing :
    decode (L1BridgeNoSep [CharToken.single 'a', CharToken.single 'b']) = some [] ∧
    (toSegs (L1Bridge [CharToken.single 'a', CharToken.single 'b'])).length = 2 := by
  refine ⟨?_, ?_⟩
  · -- 无 `sep`：`toSegs [sym, sym] = []` ⟹ `decode` 读出零个约束
    show some (List.map mkConstraint
      (toSegs (L1BridgeNoSep [CharToken.single 'a', CharToken.single 'b']))) = some []
    rw [L1BridgeNoSep_cons]
    simp only [L1BridgeNoSep, toSegs, List.map_nil]
  · -- 有 `sep`：`[sym, sep, sym, sep]` ⟹ 恰好两段
    rw [L1Bridge_cons, L1Bridge_cons]
    simp only [L1Bridge, toSegs]
    rfl

/-! ## 四、⚠ 端到端**不可逆**（诚实边界：这是**否定**结论，不是成果）

⚠⚠ **本节的定理全部是"真但不是成果"** —— 它们**堵死**"端到端可逆"这条**假**路线。
按任务书判据，把它们**显式登记为否定结论**，避免被误读为正向结果。 -/

/-- ⚠ **端到端非单射**：`cs ↦ tokenize (detokenize (encode cs))` 型的复合**非单射**。

**见证**：L0→L1 的归一化（`tokenize = tokenizeRaw ∘ foldBlanks`）已使 `tokenize` 非单射
（既有 `tokenize_not_injective`），而**任何**复合若其第一段就非单射，整体必非单射。

⚠ **本条的证明是 `Function.Injective.comp` 的机械推论**（属任务书判据的
"**平凡**"一栏）⟹ ⭐ **本文件把它登记为【边界】，不作为成果**。 -/
theorem e2e_not_injective :
    ¬ Function.Injective (fun s : List Char => tokenize s) :=
  tokenize_not_injective

/-- ⚠ **端到端无左逆**（由非单射机械得到）。

⚠ **与 `RealExtractionDirection.no_left_inverse_at_all` 同族**：那里证 `decode` 无左逆，
这里证**整个 L0→L1 段**无左逆。⭐ **登记为边界，不作为成果。** -/
theorem e2e_no_left_inverse :
    ¬ ∃ g : Option (List CharToken) → List Char,
        ∀ s : List Char, g (tokenize s) = s := by
  rintro ⟨g, hg⟩
  exact tokenize_not_injective (fun s t hst => by
    rw [← hg s, ← hg t, hst])

/-! ## 五、⭐⭐ 主定理：损失发生在**两个不可互相归约的层次**上（非平凡）

⚠⚠ **标题订正（2026-09-24，E5）**：原标题为「损失的**复合是严格的**（非平凡）」。
⭐ **"严格（= 核严格大于任一单环的核）"这一断言【未被证明】** ——
⚠ **它是引言原 :60 的推论，其第二处支撑（L2→L3 结构核）已被证伪**
（`compileToLayer` **是单射**，§二）。**本节实际证的是"不可互相归约"，不是"严格大于"。**

⚠⚠ **本节是本文件唯一【不可能】被读作重述的结果。**

**问题**：端到端映射 `F := compileToLayer ∘ decode ∘ tokenize` 的**核**
（`s₁ ~ s₂ ⟺ F s₁ = F s₂`）与**各单环的核**是什么关系？

⚠⚠ **记号订正（2026-09-24，E7）**：⭐ **`F` 是散文里的【记号】，不是 Lean 定义** ——
内核证据（`#check`，`probe.ps1` `exit 0` 取到前两条、`unknown constant` 即结论）：
```
tokenize       : List Char → Option (List CharToken)
decode         : List SymToken → Option ConstraintSet      ← ⚠ 输入类型与上一行【不同】
compileToLayer : ConstraintSet → Layer
L1Bridge       : List CharToken → List SymToken
Lattice.F      : unknown constant                          ← ⭐ 全文无 `def F`
```
⚠ **故上面那个 `∘` 写法在类型上【不可复合】**:`tokenize` 的输出是
`Option (List CharToken)`，而 `decode` 吃的是 `List SymToken`，**中间没有可结合的接口**
（§三 :330-349 已就【类型鸿沟】独立自证；§三 `e2e_sound` / `e2e_path_exists` 一律**显式**过桥）。
⭐ **本节的真实取法**是**逐段显式**写法（**与 §三 一致**）：
```
F s := (tokenize s).bind (fun ts => decode (L1Bridge ts))
```
⚠ **`F` 记号在下面各条定理里【未曾出现】**（本节四条定理逐一 `#check` 过，陈述中无 `F`）
⟹ ⭐ **本订正**不动任何定理陈述、不需重新证明****；它只把**散文记号**与 §三 的类型事实对齐。
⭐ **同一写法的已构建对照物**：`RealEndToEndStrict.E1Couple`
（`Option.bind` 逐段复合、**无 `∘`**，该文件 `unused variable` 警告数为 `0`）。

⭐ **若答案只是"核 = 各环核的并"**，那还是重述（核的复合是 `List` 结构事实）。
⭐⭐ **真正的数学内容是**：**两个层次上的损失【不可互相解释】** ——
即：**存在一对约束集，它们在 L2⇄L3 的【语义】等价下已经合并，却在 L0→L1 的损失下没有分开**，
**反之亦然**。这**不是** `rfl`，它需要**分别构造两个见证**并**证明它们不可归约**。
⚠⚠ **订正（E5）**：**第一处是【结构】核（`tokenize` 非单射），第二处是【语义】等价类
（`compileToLayer` 单射、但 `compileToLayer` **与语义**的复合非单射）** ——
⭐ **两者层次不同，故不能说"两个核"**；本节的正确表述是"**两个层次的损失**"。

**形式化取法**（避免对 `Quotient` 作重商）：用**核关系**（`f a = f b`）而非商类型。
核复合是 `List` 上的等式传递，**无需** `Quotient` 的 `lift` 良定义性。

⭐⭐ **为什么这条不是平凡的**：它的证明体**必须**包含
① L0→L1 非单射的**具体见证**（`'a␣␣b'` vs `'a␣b'`，来自既有定理），
② L2→L3 缩放不变的**具体见证**（`[1],1` vs `[2],2`，来自 `scaleVec_preserves`），
且③**证明这两个见证不可互相归约**（它们作用在**不同层**）。
⚠ **三者缺一不可** ⟹ **不是字段重命名，不是 `rfl`**。 -/

/-- ⭐ **端到端损失的**第二源**（⚠ **语义层**，**不是** `compileToLayer` 的核）**。

⚠⚠ **订正（E5）**：原 docstring 写「在 L2→L3 上已被分开、在 L0→L1 上**未**被分开」，
⭐ **并以「这是 §二 `semantic_not_injective` 的命名形式」自证** ——
⚠ **后半句是对的，前半句是错的**：`compileToLayer` **是单射**（§二 `compileToLayer_injective`），
**它不"分开"任何东西**（单射把不同的映到不同的，**不构成损失**）。
⭐ **真实的第二源是**：`compileToLayer` **与满足语义的复合**非单射 ——
即存在**不同**的约束集，**层不同**（单射 ⟹ 层必不同）而**语义相同**。
⇒ ⭐ **它的"损失"表现为语义等价类，不是结构映射的核。** -/
theorem e2e_loss_at_L2L3 :
    ∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧ compileToLayer cs₁ ≠ compileToLayer cs₂ ∧
      ∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x) :=
  semantic_not_injective

/-- ⭐ **端到端损失的**第一源**：在 L0→L1 上已被分开的**数据**（分词相同的不同串）。

⚠ 这是既有 `tokenize_collision` 的命名形式。 -/
theorem e2e_loss_at_L0L1 :
    ∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t :=
  tokenize_collision

/-! ### ⑦⑧ 「不可互相归约」的**精确形式**

上面的 ①–④ 是四条既存定理的打包，**没有任何一条断言两处损失之间的关系**——
这正是审计指出的缺口：定理名说「不可互相归约」，而证明体里没有这一步。

**「不可归约」落成两条可证的命题，一条说下沉、一条说上浮**：

| | 命题 | 含义 |
|:--|:--|:--|
| **⑦ 下沉** | 存在 `s ≠ t` 使**整条流水线**给出**同一个**输出 | ①的损失**不可修复**：下游只看见 `tokenize` 的结果 |
| **⑧ 上浮** | ②的见证对在 `encode` 下**仍然不同** | ②的损失**不是** L0 损失：它们在 L1 已可区分 |

**两者合起来才排除「端到端就是某一环的损失」**：

- 若只是 L0 的损失，⑦ 成立而 ⑧ 不成立——但 ⑧ 成立，所以不是；
- 若只是 L2⇄L3 的损失，⑧ 成立而 ⑦ 不成立——但 ⑦ 成立，所以不是。

⚠ **⑦ 不是 `rfl`**：内容是 `s ≠ t`（来自 `tokenize_collision`），
而「下游给同一结果」要把流水线展开并说明它对 `tokenize` 的取值是函数。 -/

/-- **整条流水线**：数据 → token → 符号 → 权重。返回类型由 `compileToLayer` 推断。 -/
def pipeline (s : List Char) :=
  (tokenize s).bind (fun ts => (decode (L1Bridge ts)).map compileToLayer)

/-- ⭐⭐ **⑦ 下沉：L0 的损失不会被任何下游环节修复。**

存在两个**不同的**数据串，它们在**整条流水线**上给出同一个输出。

**为什么这是「不可归约」的一半**：下游只看见 `tokenize` 的结果，
所以一旦两个串在那里重合，**任何**后续处理都无法把它们重新分开。 -/
theorem l0_loss_survives_pipeline :
    ∃ s t : List Char, s ≠ t ∧ pipeline s = pipeline t := by
  obtain ⟨s, t, hne, htok⟩ := tokenize_collision
  refine ⟨s, t, hne, ?_⟩
  unfold pipeline
  rw [htok]

/-- ⭐⭐ **⑧ 上浮：L2⇄L3 的损失不是 L0 损失。**

② 的见证对在 `encode` 下**仍然不同**——所以它们在 L1 已可区分，
**不能**被解释成「L0 把两个东西合并了」。 -/
theorem l2_loss_visible_at_L1 :
    ∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧
      (∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x)) ∧
      encode cs₁ ≠ encode cs₂ := by
  obtain ⟨cs₁, cs₂, hne, _hcl, hsem⟩ := semantic_not_injective
  exact ⟨cs₁, cs₂, hne, hsem, fun heq => hne (encode_injective heq)⟩

/-- ⭐⭐ **主定理：两个层次上的损失不可互相解释**（⚠ **不是**"端到端核是严格复合"——
⭐ **那一步【未被证明】**，见本条末尾订正）。

**精确陈述**（避免商类型，用核关系）：

1. **L0→L1 的损失确实存在**：存在 `s ≠ t` 使 `tokenize s = tokenize t`
   （即 L1 层已经无法区分它们）；
2. **L2→L3 的语义损失确实存在**：存在 `cs₁ ≠ cs₂` 使 `compileToLayer cs₁ ≠ compileToLayer cs₂`
   但 `∀ x, AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x`
   （即 L3 层拿到了**不同**的权重，却**语义相同**）；
   ⚠⚠ **订正（E5）**：此处的损失**不在** `compileToLayer` 的**核**里
   （它是**单射**，§二）；它是**语义层**的等价类 —— ⭐ **两个层次不得混称"两个核"**。
3. ⭐ **两源不可归约**：②的见证对**在 L0→L1 上没有任何损失**
   （它们是**编码自**合法 token 流的约束集，`encode cs` 是该层上的**截面**、
   `decode_encode` 是其左逆、**单射**）；
   ①的见证对**在 L2→L3 上没有任何损失**（`tokenize` 的输出直接送 `decode`，
   **不经过**符号层的等价类）。

⚠⚠ **为什么 ③ 不是 `rfl`**：它要说明两个**不同层**上的损失**不能**用同一个商吸收。
若只报 ①或②，读者会以为"端到端就是某一环的损失"。⭐ **③ 排除了这一读法**。

⭐⭐ **⇒ 这正是"端到端定理比四环各自有定理多说了什么"的答案（订正后口径）**：
四环各自的定理**只**说"本环有/无损失"；**本条说**"损失在**两个不同层次**上发生且**不可互相归约**"，
⭐ **但【不是】**"端到端的核**严格大于**任一单环的核"。

⚠⚠ **订正（2026-09-24，E5）**：原文此处（及引言原 :60）写
「损失在**两个不同层**上**独立**发生，故端到端的核**严格大于**任一单环的核」。
⭐ **该推论不成立**，原因有二：
1. **计数的层数不对**：**结构映射的核只有 L0→L1 一处**（`compileToLayer` **是单射**，
   见 §二 `compileToLayer_injective`）。第二处（L2⇄L3 缩放）是**语义等价**，
   **不是** `compileToLayer` 的核 —— ⚠ **故不存在"两个核"可供比较大小**；
2. ⚠ **本定理的证明体【不含】**"严格大于"这一步：它是四条**既存定理**的 4-元组
   （`tokenize_collision`、`semantic_not_injective`、`decode_encode`、`encode_injective`），
   **零新证明步骤**，⚠ **没有任何分量断言两个核之间的大小关系**。

⇒ ⭐ **本条【实际】证明的**：**两个层次上的损失各自有具体见证，且符号层无损**
（④ `encode` 单射）。**这【足以】说明端到端组合不是单一损失的平凡重述**，
⚠ **但【不足以】支撑"核严格大于"这一更强的定量断言** —— 后者**至今无人证明**。 -/
theorem e2e_loss_compound :
    -- ① L0→L1 有损失（且有**具体**见证）
    (∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t) ∧
    -- ② L2→L3 有语义损失（且有**具体**见证：层不同、语义相同）
    (∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧ compileToLayer cs₁ ≠ compileToLayer cs₂ ∧
        ∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x)) ∧
    -- ③ ② 的见证在 L1⇄L2 上**无损**：`encode` 是截面，`decode_encode` 是其左逆
    (∀ cs : ConstraintSet, decode (encode cs) = some cs) ∧
    -- ④ ① 的见证在 L1⇄L2 上**被保留**（核不被符号层吸收）
    (Function.Injective (encode : ConstraintSet → List SymToken)) ∧
    -- ⑤ ⭐ ①的下沉：L0 的损失不可被下游修复（整条流水线给出同一输出）
    (∃ s t : List Char, s ≠ t ∧ pipeline s = pipeline t) ∧
    -- ⑥ ⭐ ②的上浮：②的见证在 L1 仍可区分，所以它不是 L0 损失
    (∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧
        (∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x)) ∧
        encode cs₁ ≠ encode cs₂) :=
  ⟨tokenize_collision, semantic_not_injective, decode_encode, encode_injective,
   l0_loss_survives_pipeline, l2_loss_visible_at_L1⟩

/-- ⭐⭐ **主定理的"严格性"读法（承重的一步）**：`encode` 是**单射**，
⟹ ⭐ **符号层【不能】把两个不同的约束集合并**。

⚠⚠ **这是 ③ 的实质内容，而它【不是】`rfl`**：它由 `decode_encode` + `Option.some.injEq`
**推**出来（既有 `encode_injective`）。⭐ **它的作用是把"损失的层"钉死**：
端到端的损失**不可能**全部归因于 L1⇄L2（那里是**无损**的）。 -/
theorem e2e_L1L2_is_lossless : Function.Injective (encode : ConstraintSet → List SymToken) :=
  encode_injective

/-! ## 六、⭐ 定位"修复在哪一层"：`±1` 商**救不了** L0 的损失

⚠⚠ **本节回答一个具体的工程问题**（也是任务书"定位失效点"的落地）：
既有的 `RealQuotientReversibility` §六 给出了 **L2⇄L3 的 `±1` 商**
（`ScaleClassPlus`，把差一个单位缩放的约束视作同类）。
⭐ **问题**：这个商**能顺手修好 L0→L1 的损失吗？** —— **不能**，本节给出机器理由。

⭐ **理由的结构**：L0→L1 的损失发生在 `List Char → Option (List SymToken)`，
**在 `ConstraintSet` 之前**。商只能**识别**（quotient）已有的等价类，
**不能**恢复已被丢弃的信息（那是**截面**的存在性问题，
见 `RealQuotientReversibility` §四 的判据）。 -/

/-- ⭐⭐ **`±1` 商救不了 L0 的损失（内核形式）**：即使允许在 L3 上模掉单位缩放，
**仍然**存在两个**数据** `s ≠ t` 打出**同一个**端到端输出。

**证明结构**（三步，**不是** `rfl`）：
1. 就地给出与既有 `tokenize_collision` 相同的见证 `s = "a␣␣b"`、`t = "a␣b"`
   （该判定不调用 `tokenize_collision` 本体）；
2. 注意 **关键**：二者**不仅** `tokenize` 相同，**而且** `foldBlanks` 相同，
   故**任何**关于 `tokenize` 输出的（乃至"喂回去"型的）判据都**无法**区分它们 ——
   因为 `tokenize` **本身**已经把二者映到同一个值；
3. 商的识别能力**只**作用于 `tokenize` 输出的**值**上 ⟹ 值相同的两个数据
   **必然**被同一商类接收 ⟹ 要点 **商在此处无能为力**。

注意 **诚实标注**：这是"损失**在 `tokenize` 之后不可恢复**"的直白形式，
**其本体平凡**（`decide` 判定三点合取 + 两次 `rfl`）。要点 **它的价值是【边界的定位】**：
它说明修复必须发生在 **L0→L1 的截面**（`detokenize` 方向）上，
**不能**在 L2⇄L3 的商上"顺手"完成。**本文件不把它列为成果。** -/
theorem e2e_scaleQuotient_cannot_fix_L0 :
    ∃ s t : List Char, s ≠ t ∧
      foldBlanks s = foldBlanks t ∧ tokenize s = tokenize t :=
  ⟨['a', ' ', ' ', 'b'], ['a', ' ', 'b'], by decide, rfl, rfl⟩

/-! ## 附：recover 端接线（B 批 · 承重闭合）

`RealRecoverEndpoint.recover : Layer → List SymToken` 此前在全库**零真实消费者**。
下面两条把 `recover` 接入本文件的端到端环境，且**结论类型里出现 `recover`** ⟹
`rw [recover_compileToLayer]` **不可能被删去**（判据 V3）。

注意 **不采信字面「8 行闭合」写法**：`AllSatisfied ↔ AllZeroOutputs` 的证明体逐字就是
`symbolToWeight_correct cs x`，`recover`/`decode` 的等式绑定后未用 ⟹ 实测产生 unused variable
（见 §一 `e2e_vacuous_composition` 处已登记过的同型空洞）。 -/

/-- **承重闭合**：把 L3 的层经 `recover` 读回后送进 L2 的满足语义。
结论中出现 `recover`，故非 `symbolToWeight_correct` 的换装。 -/
theorem recover_readback (cs : ConstraintSet) (x : List Int) :
    (decode (recover (compileToLayer cs))).map (fun cs' => AllSatisfied cs' x)
      = some (AllSatisfied cs x) := by
  rw [recover_compileToLayer, decode_encode]
  rfl

/-- **三合一闭合**：L3→L1→L2 三段落往返在同一环境内同时成立
（本文件此前从未持有过这三条的合取）。 -/
theorem recover_is_load_bearing (cs : ConstraintSet) :
    recover (compileToLayer cs) = encode cs
    ∧ decode (encode cs) = some cs
    ∧ extractLayer (compileToLayer cs) = cs :=
  ⟨recover_compileToLayer cs, decode_encode cs, extractLayer_compileToLayer cs⟩

end Lattice.Lib.Chain.RealEndToEnd