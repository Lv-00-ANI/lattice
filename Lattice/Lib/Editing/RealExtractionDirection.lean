import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Editing.RealExtractInvertibility
/-!
# LATTICE: RealExtractionDirection —— L1⇄L2「抽取方向」（文本 → 符号）的健全性边界

## 定位：本环此前**完全空白**，且**不能**照 `RealTokenSymbolLink` 的形态补

`RealTokenSymbolLink`（298 行）证的是 `decode (encode cs) = some cs` —— **已结构化信息**
在 token 与符号之间的**结构往返**。该文件**自己**在诚实边界里写明：

> **编码不是自然的**：真实 L1⇄L2 是「文本→关系抽取/规则化」的**有损、启发式**过程
> （doc/02 §3 自述「LLM 作外部工具」）。本文件给出的是该跳的**可逆子类**。

本文件处理**那一跳本身**。关键区别：**抽取方向没有编码器**。
`SymToken` 字母表在往返版中由**人**在编码端固定，于是 `sep` 必然存在、段必然完整；
而抽取方向面对的是**任意** token 流 —— `sep` 不保证存在，段不保证完整。

## ⚠⚠ 第 0 步（先判「不要证什么」）：三条已登记否定结论的逐条核对

`lean/README.md` §「⛔ 已知否定结论」已登记三条（另有 `activated_*`、
`linearization_collapses_models` 与之同族）。本文件**逐条核对**，
结论：**本文件的全部主定理都不蕴含其中任何一条的反面**。

| 已登记否定结论 | 本文件的处置 |
|:--|:--|
| ⭐ `no_extractor_preserves_both`（**参数层可逆 ∧ 语义层可逆 不可兼得**） | ⭐ **本文件不构造"完美抽取器"**——恰恰相反：§七 用**同一个见证族**（缩放轨道）把「参数层单射 vs 语义层非单射」的分裂**搬到 L1 侧并机器验证**（`decode_not_injective`，`:373`；配套 `no_left_inverse_at_all`，`:398`）。**不蕴含其反面；是其 L1 侧对应物。** |
| `closed_loop_adds_nothing`（**闭环不携带新语义**） | 本文件**不声称**抽取闭环携带新语义。§六 的往返定理只断言**结构**恢复，且其成立范围被 §五 的否定结论**严格限制**（只在 `sep` 收尾的规范段上）。**不蕴含其反面。** |
| ⭐ `validity_does_not_determine_syntax`（**行为等价推不出语法相等**） | ⭐ 本文件**不声称**「合法性 ⟹ 唯一语法」。§五 给出**独立于缩放轨道的第二个**「多读法」来源（`sep` 缺省：残段丢弃 vs 空段保留），并证明**完备性为假**。**不蕴含其反面；是同一母题在 L1 侧的第二个实例。** |

⇒ ⭐⭐ **一句话**：**"可逆"在已有登记下已被封死，故本文件不去证"可逆"，
而是精确刻画【什么不可能】与【在什么范围内仍然成立】。**
**这正是任务书「不要为了闭合缺口而写假命题」的直接执行。**

## 主结果（全部为**真定理**；无 sorry/axiom/admit/native_decide）

| 定理 | 内容 | 角色 |
|:--|:--|:--|
| `extract_sound` | ⭐ **健全性**：抽取出的符号必是 token 流的**忠实读法** | 主定理（真） |
| `extract_sound_setSat` | 健全性接到 L2 语义（`AllSatisfied`） | 与 L2 接口 |
| `toSegs_length_le_sep_count` | 读法段数 ≤ `sep` 计数 + 1 | 信息量上界 |
| `readLength_determinate_of_sep_final` | ⭐ **条件完备性**：`sep` 收尾 ⟹ 读法段数**确定**为 1 | 正面结果 |
| `extract_lossy_of_no_sep_final` | ⭐⭐ **有损性**：无 `sep` 收尾 ⟹ 该段**整体被丢弃** | 主定理（真） |
| `extraction_completeness_false` | ⭐⭐⭐ **完备性为假**（机器验证反例） | **核心否定结论** |
| `extraction_completeness_counterexample` | 上条的显式见证形式 | 反例可复核 |
| `renderSurjective_holds` | ⚠ **空洞真**（登记，说明"存在性完备性"太弱） | 判读规律 1 样本 |
| `extract_render_left_inverse` | ⭐ **单向**：`extract ∘ render = id`（严格左逆） | 主定理（真） |
| `decode_not_injective` | ⭐⭐⭐ **`decode` 非单射**（承重反例 `[]` vs `[sym 1]`） | **核心否定结论** |
| `no_left_inverse_at_all` | ⭐⭐⭐ **左逆不存在**（连一侧都没有） | **核心否定结论** |
| `extract_to_weights` | ⭐⭐ L1 → L2 → L3 **语义串联** | 链路接口 |
| `constraintSet_is_list_of_constraints` | 两条链路共用同一符号类型 | 结构桥 |

## ⭐⭐ 核心发现：L1⇄L2 **不**收敛到「商可逆」，而是收敛到「单向」

任务书的结构性线索是：**L0⇄L1 与 L2⇄L3 都收敛到「商可逆」**，
故推测这是**一般定理级结论**。**本文件给出该推测的边界。**

| 环 | 映射 | 失效模式 | 可逆性形态 |
|:--|:--|:--|:--|
| **L0⇄L1** | `tokenize` | ⚠ **满射 + 非单射**（`tokenize_never_none` 保证有像） | ⭐ **商可逆**（`detokenize ∘ tokenize` 在 σ 上 = id） |
| **L2⇄L3** | `compileToLayer` | ⚠ **非单射**（缩放轨道：多权重 → 同一函数） | ⭐ **商可逆**（语义等价类上有左逆） |
| ⭐ **L1⇄L2** | `decode` | ⚠⚠ **非单射**（**残段塌缩**：`[sym 1]` 与 `[]` 同读法） | ⚠⚠ **仅单向**（`decode ∘ encode = id` 有；**反向无左逆**） |

⭐ **本文件机器验证的差异**（**这是"不适用"的确切内容**）：

| | L0⇄L1 / L2⇄L3 | ⭐ L1⇄L2 |
|:--|:--|:--|
| **单向左逆** | ✅ 有 | ✅ 有（`extract_render_left_inverse`） |
| ⭐ **反向左逆** | ✅ **有**（在商上；`detokenize` / `extract` 落在**同基**且**满**） | ❌ **无**（`no_left_inverse_at_all`） |
| **商化能否救** | ⭐ **能** —— 失效为"多对一"，商掉等价类即可 | ❌ **不能** —— 见下 |

⚠⚠ **为什么商化救不了 L1⇄L2**（本文件**诚实标注的推理边界**）：
"商可逆"要成立，需要存在一个**商结构**使左逆在商上单值。
L0⇄L1 的商是 `SameTokens`（由 `tokenize` 自身定义，且 `tokenize_never_none` 保证**满**）；
L2⇄L3 的商是"行为等价"（由 `compileToLayer` 的**像**定义）。
**两者的共同前提是：失效点可以被"喂回去再算一遍"识别出来** ——
即存在一个**规范代表**（`detokenize ts` / `cUnit` 型的规范形）。

⚠ 而 L1⇄L2 的失效点是**残段**：末段无 `sep` 时被丢弃。
**丢弃的信息是"那里本来有一段"这件事本身**，而 `decode` 的输出
（`Option ConstraintSet`）**不携带"我丢了东西"的标记** ——
两个不同流给出**同一个** `some []`（`decode_not_injective`）。
⇒ **商结构无从定义**（无法在输出侧区分"真的空"与"丢了一段后的空"），
**故"商可逆"这一形态在 L1⇄L2 上不可构造。**

⭐ **⇒ 判定：任务书的线条【不适用】于 L1⇄L2。**
**「商可逆」的前提是"失效可被输出侧识别（从而可商）"；
L1⇄L2 的失效对此不可识别 ⟹ 只能退到"单向"。**
⚠ **这是对"一般定理级结论"的【边界条件】，而非反例** ——
它说明该一般结论**需要一条额外前提**（"失效可识别"），
**该前提在另两环由满射性/规范形自动满足，在 L1⇄L2 不满足。**

## 诚实边界（本文件**不证 / 不声称**的）

- ⚠ **`extract` 不是"自然语言理解"**：本文件不建模 LLM、不做语义角色标注、
  不碰真实分词器输出。它建模的是**该跳的结构骨架**：从任意 token 流到符号约束集的
  **忠实读法**关系。「有损、LLM 辅助」这件事被**精确化为** §四/§五 的否命题，
  **而非**被证成或证伪。
- ⚠ **本文件不声称**「所有自然语言都能被抽取」—— §五 **恰恰证明完备性为假**。
- ⚠ **本文件不声称**「抽取在语义层可逆」—— §六 **证明**其反向左逆**不存在**。
  这与已登记的 `no_extractor_preserves_both` / `validity_does_not_determine_syntax`
  **一致**（是其 L1 侧对应物，**不是反面**）。
- ⚠ **不构造 LLM 接口**：`Extract` 是**关系**而非函数，故"抽取器"在本文件中
  **不是一个可实现算法**，而是**读法关系**。这与 doc/02 §3「LLM 作外部工具」的定位一致：
  **工具在证明层被记为关系，其内部不被形式化。**
- ⚠⚠ **"商化救不了" 的论证是【推理】，不是【内核定理】**：本文件**没有**形式化
  "不存在可行的商结构"这一元命题（那需要对所有可能的商结构量化）。
  **内核已验证的是** `decode_not_injective` 与 `no_left_inverse_at_all`；
  "因此商可逆不适用"是**基于这两个定理的论证**。⚠ **两者不可混同**（见 §六 末的标注）。
- ⚠ **`render` 只是"恰好可逆的那一侧"**：`render := encode` 对**任意** `cs` 有定义，
  且 `extract (render cs) = cs` 对**全部** `cs` 成立（`decode_encode`）。
  但它**不是**"能处理任意 token 流的解码器" —— §六 证明反向不可能。
- **只读引用既有模块**：不修改 `RealTokenSymbolLink` / `RealTokenization` / `RealFCA` /
  `ConvertVectorLinear` / `SymbolToWeightCorrectness` 任何文件。
- 无 `sorry` / `axiom` / `admit` / `native_decide`。

## ⚠ 跨文件重名的预防（STYLE「跨文件同名 `def` 是潜伏断裂」）

`VectorConstraint` / `dot` / `VectorConstraintSat` / `ConstraintSet` / `AllSatisfied` /
`scaleVec` / `scaleVec_preserves` / `SymToken` / `decode` / `encode` / `toSegs` /
`mkConstraint` / `splitLast` / `decode_encode` —— **全部复用既有定义**，
**本文件一个都不重新声明**。新增名字均带 `a9` 无关的唯一前缀或足够特殊的名字，
并在 `namespace Lattice` 内（**不新开命名空间**，与 `RealTokenSymbolLink` 一致）。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、抽取关系：`Extract`（**关系**，不是函数）

⚠ **第一步的判断**：任务是"文本 → 符号"，且用户明说该跳是**有损、LLM 辅助**。
⇒ **不建"完美抽取器"**（那是假命题，`no_extractor_preserves_both` 已封死）。
⇒ **建关系**：一个 token 流可以**忠实**地读成（至多）一个符号集，
且**允许一个都不是**（`sep` 段落不全时残段被丢弃）。

`Extract ts cs` 的直观读法：`cs` 是 token 流 `ts` 的一个**忠实读法**
（"这个流可以被读成这样一组约束"）。它是 `Prop` 而非 `Bool` ——
"能读成"是**存在性**判断，与"读出什么"分开。 -/

/-- **抽取关系（L1 → L2）**：`ts` 可被忠实读成 `cs`。

**不是函数**：一个 `ts` 也可**没有任何** `cs` 之外的读法（§五 表明残段被丢弃）。

**为什么用 `∃ cs, decode ts = some cs` 的形状而非把 `cs` 当参数**：
`decode` 是既有定义且是**全函数**（结果构造性地总是 `some`），
"失败"体现在**段被丢弃**（`RealTokenSymbolLink` §四 的诚实标注）。
故本关系取 `decode` **作为**读法，并把"有损"放在 §四/§五 单独证明 ——
**不重复实现一个平行的解码器**（那会制造 STYLE 警告的第二个权威）。 -/
def Extract (ts : List SymToken) (cs : ConstraintSet) : Prop := decode ts = some cs

/-- **健全性（核心定理）**：抽取**永不编造** ——
若 `ts` 被读成 `cs`，则 `cs` 确实由 `ts` 的 `sep` 段构成，
且 `ts` 本身的 `toSegs` 展开正是 `cs` 各约束的 `(a ++ [b])` 拼接。

精确形式：`cs` 的每个约束都对应 `ts` 的一个 `sep` 段（**段段对应**），
这就是"抽取出的符号是 token 流的忠实读法"的机器可验证含义。 -/
theorem extract_sound (ts : List SymToken) (cs : ConstraintSet) (h : Extract ts cs) :
    (toSegs ts).map mkConstraint = cs := by
  unfold Extract at h
  exact (Option.some.injEq _ _).mp h

/-- **健全性的语义推论**：抽取结果**不改变**原 token 流所承载的约束语义。

即：把 `ts` 的忠实读法 `cs` 拿去问"某个输入 `x` 是否满足"，
与直接问"`ts` 的所有段是否都满足"是**同一件事**。
这把 §一 的健全性接到 L2 的语义（`AllSatisfied`），是通往 L3 的接口。 -/
theorem extract_sound_setSat (ts : List SymToken) (cs : ConstraintSet)
    (h : Extract ts cs) (x : List Int) :
    AllSatisfied cs x ↔ AllSatisfied ((toSegs ts).map mkConstraint) x := by
  rw [extract_sound ts cs h]

/-! ## 二、读法的**长度**：抽取能恢复多少信息？

`decode` 的输出长度 = `toSegs ts` 的长度。这是"抽取方向能恢复多少"的**唯一**载体：
每个 `sep` 恰好贡献一个段，**末段若无 `sep` 收尾则被丢弃**。

故本节先证"长度"的两种行为：`sep` 收尾时**确定**，否则**丢失**。 -/

/-- **`toSegs` 的长度上界**：段数**不超过** `sep` 的个数加一。

每一步消费一个 token：`sep` 开一个新段，`sym` 不新开段。
故段数 ≤ `sep` 计数 + 1（最后可能的未收尾段）。
这是"抽取的信息量受 `sep` 计数限制"的结构性事实。 -/
theorem toSegs_length_le_sep_count (ts : List SymToken) :
    (toSegs ts).length ≤ ts.count SymToken.sep + 1 := by
  induction ts with
  | nil => simp [toSegs]
  | cons t rest ih =>
    cases t with
    | sep =>
      -- toSegs (sep :: rest) = [] :: toSegs rest，长度 = 1 + |toSegs rest|
      have h1 : (toSegs (SymToken.sep :: rest)).length = (toSegs rest).length + 1 := by
        simp [toSegs]
      rw [h1, List.count_cons_self]
      -- 目标：(toSegs rest).length + 1 ≤ rest.count sep + 1 + 1
      omega
    | sym z =>
      -- toSegs (sym z :: rest)：`sym` 不新开段，长度**不增**
      -- ⚠ `count` 的被计数元素是 `SymToken.sep`（不是 `sym z`），故前提方向是 `sep ≠ sym z`
      have hne : (SymToken.sep ≠ SymToken.sym z) := by simp
      have hlen : (toSegs (SymToken.sym z :: rest)).length ≤ (toSegs rest).length := by
        simp only [toSegs]
        split
        · simp
        · rename_i seg segs heq
          rw [heq]
          simp
      rw [List.count_cons_of_ne hne]
      omega

/-! ## 三、渲染：`render`（符号 → token）—— **恰好可逆的那一侧**

`render` 直接取 `RealTokenSymbolLink.encode`（**不重新实现**）：
它是 `decode` 的**严格左逆**（由既有的 `decode_encode` 立即得到）。

⚠ **为什么这不算"完美抽取器"**：本文件**不主张** `render` 与 `extract` 互逆。
§七 将**证明**其另一侧**不存在**。 -/

/-- **渲染（L2 → L1）**：复用 `RealTokenSymbolLink.encode`。 -/
def render (cs : ConstraintSet) : List SymToken := encode cs

/-- ⭐ **单向可逆（核心定理之一）**：`extract ∘ render = id`。

即 `decode (encode cs) = some cs` —— **严格左逆**，
且**对全部** `cs : ConstraintSet` 成立，**无任何附加假设**
（不是"在商上"，不是"在子类上"）。这直接复用既有的 `decode_encode`。

⚠ **诚实标注**：这是**一侧**的左逆。§七 证明**另一侧不存在**，
故本定理**不**读作"抽取方向可逆"。 -/
theorem extract_render_left_inverse (cs : ConstraintSet) :
    Extract (render cs) cs :=
  decode_encode cs

/-! ## 四、⭐ 条件的完备性：`sep` 收尾 ⟹ 读法确定

本节给出**正面结果**（任务书三个结果之一："只在某子类上成立 ⟹ 给出条件 + 证它"）：
在**规范类**（`sep` 收尾的自然段结构）上，抽取的信息量是**确定的**。 -/

/-- **`sep` 收尾の规范揭示**：若 token 流形如 `<段体> ++ [sep]`，
则 `toSegs` 恰好给出**一个**段，且段体就是 `<段体>` 的 `sym` 载荷。

这是 §五 两条对偶结论（确定 vs 有损）的**共同引理**。 -/
theorem toSegs_append_sep_singleton (l : List Int) :
    toSegs (l.map SymToken.sym ++ [SymToken.sep]) = [l] := by
  have h := toSegs_map_sym_append_sep l []
  simpa [toSegs] using h

/-- ⭐ **条件的完备性（读法个数唯一）**：`sep` 收尾的段 ⟹ 恰好一个读法段。

即：**当流以 `sep` 收尾时，抽取不丢信息** —— 该段**确定地**被读出一个约束。 -/
theorem readLength_determinate_of_sep_final (l : List Int) :
    (toSegs (l.map SymToken.sym ++ [SymToken.sep])).length = 1 := by
  rw [toSegs_append_sep_singleton]
  rfl

/-- ⭐⭐ **有损性（对偶结论，核心定理之一）**：**同一条流**去掉尾 `sep`
⟹ 该段**整体被丢弃**。

即 `toSegs (l.map sym)`（**无**尾 `sep`）**不给出该段**。
这机器验证了"抽取方向有损"的**精确位置**：损失全部集中在**末段的收尾符**上。

**见证**：`l = [1, 2]` 时 `[sym 1, sym 2, sep]` 读出 `[[1,2]]`（一个约束），
而 `[sym 1, sym 2]` 读出 `[]`（**零个**约束）—— 同一段体，收尾符有无决定一切。 -/
theorem extract_lossy_of_no_sep_final (l : List Int) :
    toSegs (l.map SymToken.sym) = [] := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    -- toSegs (sym h :: t.map sym)：`ih` 给出 toSegs (t.map sym) = []
    simp only [List.map_cons, toSegs, ih]

/-- **有损性的显式见证（与补全互为对照）**：
`[sym 1, sym 2]`（无尾 `sep`）被读成**空**约束集。 -/
theorem extract_drops_unterminated :
    decode [SymToken.sym 1, SymToken.sym 2] = some [] :=
  decode_drops_trailing_partial

/-! ## 五、⭐⭐ 完备性为假（核心否定结论）

任务书判定：「**完备性（通常为假）**：「所有合法符号都能被抽取」⟹ 很可能是假命题
→ **给出反例并登记**」。

本节给出**内核反例**。⚠ 关键是：反例必须**满足原命题的全部假设**，
否则它只是"空洞真 vs 承重"判断里的空心反例。故先**精确陈述**完备性。 -/

/-- **完备性（被否证的命题）**：**任意**符号约束集都能从**某个** token 流被抽取出来。

⚠ **这是"提取器存在性"的最强形式**（即 `render` 是满射 / 抽取是全的）。
由 §六 的 `render` 它显然成立 —— **故此处必须把它写成对它自身的否定，
否则就是空洞真**。真正有内容的完备性是下一条 `ExtractionComplete`。 -/
def RenderSurjective : Prop := ∀ cs : ConstraintSet, ∃ ts : List SymToken, Extract ts cs

/-- **`render` 是满的（真定理，但是**空洞的**）**：取 `ts := encode cs` 即可。

⚠ **本条是"空洞真"的教科书样本**（任务书判读规律第 1 条）：
它成立**仅因为** `render` 是全函数 —— **不含任何关于"抽取能恢复什么"的信息**。
本文件显式登记它，正是为了说明**"存在性完备性"太弱、必须换成"读法上的完备性"**。 -/
theorem renderSurjective_holds : RenderSurjective :=
  fun cs => ⟨encode cs, decode_encode cs⟩

/-- ⭐⭐ **完备性（有内容的版本，本文件证明它为假）**：
**每一个** token 流都能被抽取成"至少一个非空约束集"。

即：**不存在**「什么都抽不出来」的流。
这是"文本 → 符号"的**乐观形式**（"任何文本都蕴含着符号"）。 -/
def ExtractionComplete : Prop :=
  ∀ ts : List SymToken, ts ≠ [] → ∃ cs : ConstraintSet, cs ≠ [] ∧ Extract ts cs

/-- ⭐⭐⭐ **核心否定结论：完备性为假（机器验证反例）**。

**反例**：`ts := [SymToken.sym 1, SymToken.sym 2]`（一个非空的 token 流）。
它**满足** `ExtractionComplete` 的**全部假设**（`ts ≠ []`），
但它**不满足**结论：唯一的忠实读法是**空集**（§四 `extract_drops_unterminated`），
而 `[] = []` 使 `cs ≠ []` **为假**。

⚠ **⇒ 反例满足原命题的全部假设** ⟹ 这是**真反例（承重）**，
不是"空洞真"（任务书判读规律第 1 条）。

⭐ **含义**：**"自然语言文本必定能抽出符号结构"是假的** ——
至少当"文本"被精确化为 token 流、而符号被精确化为约束集时为假。
**根因**：抽取需要一个"段的边界"信号（`sep`），
**没有该信号的信息在 L1 层不可恢复**（§四 `extract_lossy_of_no_sep_final`）。
这与 doc/02 自述的"有损、LLM 辅助"**一致**：**LLM 的辅助作用正是补上这个缺失的边界信号**，
而**该辅助本身不在证明层被形式化**（本文件的诚实边界）。 -/
theorem extraction_completeness_false : ¬ ExtractionComplete := by
  intro h
  obtain ⟨cs, hne, hdec⟩ := h [SymToken.sym 1, SymToken.sym 2] (by simp)
  unfold Extract at hdec
  rw [extract_drops_unterminated] at hdec
  exact hne ((Option.some.injEq _ _).mp hdec).symm

/-- **完备性失败的最小量化形态**：**存在**非空 token 流，其**所有**忠实读法都是空集。

这是 `extraction_completeness_false` 的显式见证形式（不依赖定义展开）。 -/
theorem extraction_completeness_counterexample :
    ∃ ts : List SymToken, ts ≠ [] ∧ ∀ cs : ConstraintSet, Extract ts cs → cs = [] := by
  refine ⟨[SymToken.sym 1, SymToken.sym 2], by simp, ?_⟩
  intro cs h
  unfold Extract at h
  rw [extract_drops_unterminated] at h
  exact ((Option.some.injEq _ _).mp h).symm

/-! ## 六、⭐⭐⭐ 左逆不存在 —— **这是 L1⇄L2 与另两环的根本差异**

§三 给了**一侧**严格左逆（`extract ∘ render = id`，即 `decode ∘ encode = id`）。
本节证明**另一侧不可能**：`decode` **没有**左逆，
即**不存在** `g` 使 `g (decode ts) = ts` 对一切 `ts` 成立。

**为什么这条是本文件的核心**：它把"L1⇄L2 不是商可逆"从**直觉**变为**内核定理**。

⚠⚠ **论证的独立性**（避免与已登记的 `validity_does_not_determine_syntax`
重复计一次）：本反例**不使用**缩放轨道（`scaleVec`）、**不使用**语义等价，
只用**纯结构事实**：`decode` 在两条**不同**的 token 流上取值**相同**。
故它是**独立于 L2⇄L3 的第二个否定来源**。 -/

/-- ⭐⭐⭐ **见证（承重）**：`decode [] = decode [sym 1]`，而 `[] ≠ [sym 1]`。

**为什么这是对的一对**（写作时经内核复核才确定）：
`[sym 1]` 是**无 `sep` 收尾的残段** ⟹ 被 `toSegs` **整段丢弃** ⟹ 读出 `[]`；
而空流本就读出 `[]`。**两者都是合法输入**（`decode` 定义在所有 `List SymToken` 上）。

⚠ **为什么不是别的对**（记录被排除的错误见证，避免后人重犯）：
- `[sym 1, sep]` vs `[sym 2, sep]`：读出的约束 `⟨[],1⟩` vs `⟨[],2⟩` **不同** ✗
- `[sym 1, sym 2, sep]` vs `[sym 2, sym 1, sep]`：读出 `⟨[1],2⟩` vs `⟨[2],1⟩` **不同** ✗
- `[sep]` vs `[sep, sep]`：读出 `[⟨[],0⟩]` vs `[⟨[],0⟩,⟨[],0⟩]` **不同** ✗
⇒ **残段**（末段无 `sep`）是**唯一**能把不同流折叠到同一读法的结构，
这正好是 §四 `extract_lossy_of_no_sep_final` 所刻画的**信息损失处**。
**"有损"与"右逆不存在"是同一事实的两面。** -/
theorem decode_not_injective : ¬ Function.Injective (decode : List SymToken → Option ConstraintSet) := by
  intro hinj
  have h : decode ([SymToken.sym 1] : List SymToken) = decode ([] : List SymToken) := by
    show some (List.map mkConstraint (toSegs [SymToken.sym 1])) = some (List.map mkConstraint (toSegs []))
    simp only [toSegs]
  have hne : ([SymToken.sym 1] : List SymToken) ≠ [] := by simp
  exact hne (hinj h)

/-- ⭐⭐⭐ **左逆不存在（核心否定结论）**：**不存在**函数
`g : Option ConstraintSet → List SymToken` 使 `g (decode ts) = ts` 对**一切** `ts` 成立。

由 `decode_not_injective` 与既有的 `leftInverse_iff_injective` 立即得到
（该定理说"存在左逆 ⟺ 单射"，故非单射即无左逆）。

⚠ **⇒ 对已登记结论的定位**：本条是 `no_extractor_preserves_both` 在 **L1 侧**的
**对应物**（**不是反面**）。那条说"参数层 ∧ 语义层**不可兼得**"；
本条更强：**连纯结构层的左逆都不存在**。

⚠⚠ **⇒ 这就是 L1⇄L2 与 L0⇄L1 / L2⇄L3 的**根本差异**：
后两环的 `detokenize` / `extract` 落在**同基**上，且其映射是**满的**
（`tokenize_never_none` 保证有像；`compileToLayer` 按构造有像），
故"回不到原像"**只**表现为**等价类** ⟹ **商掉即可**（商可逆）。
而 L1⇄L2 的 `decode` 落在**一个字母表**上、且**其像远小于 `List SymToken`**
（残段全部塌缩到 `[]`）⟹ **商化救不了它** ——
**因为失效不是"多对一"，而是"一个更小的基"。** -/
theorem no_left_inverse_at_all :
    ¬ ∃ g : Option ConstraintSet → List SymToken,
        ∀ ts : List SymToken, g (decode ts) = ts := by
  rintro ⟨g, hg⟩
  have hinj : Function.Injective (decode : List SymToken → Option ConstraintSet) :=
    (leftInverse_iff_injective (decode : List SymToken → Option ConstraintSet)).mp ⟨g, hg⟩
  exact decode_not_injective hinj

/-! ### ⚠⚠ 本节的诚实边界（**必须与上面的定理分开读**）

**内核已验证的**（本文件的定理）：
1. `decode_not_injective`：`decode` 非单射（承重见证 `[]` vs `[sym 1]`）；
2. `no_left_inverse_at_all`：`decode` **无左逆**（由 1 + `leftInverse_iff_injective`）。

⚠⚠ **以上两条是"单向"的全部内核内容。** 而文件头与本节上文所说的
**"因此商可逆不适用 / 商化救不了它"**，是**基于这两条定理的【论证】，
不是内核定理** —— 要对它做内核形式化，需要对**所有可能的商结构**量化
（"不存在 `Quotient` 构造使之左逆单值"），那**不在本文件范围内**。

⇒ ⚠ **故本文件的诚实口径**：
| 陈述 | 状态 |
|:--|:--|
| `decode` 非单射且无左逆 | ✅ **内核已验证** |
| 另两环（L0⇄L1 / L2⇄L3）在其商上**有**左逆 | ✅ **内核已验证**（在各自文件中） |
| ⭐ **"L1⇄L2 因此不能商可逆"** | ⚠ **推理**（证据：输出侧无法区分"真空"与"丢段后的空"），**未形式化** |

**这正对应任务书判读规律第 5 条**（"docstring 里的『根因诊断』都可能是错的"）——
**故本处把"已验证"与"已推理"分栏列出，不把推理写成已证。** -/

/-- ⭐⭐ **两条链路的交汇点（结构桥）**：L1⇄L2 的符号类型与 L2⇄L3 的符号类型
**是同一个类型** —— `ConstrainSet` 的定义来自 `SymbolToWeightCorrectness`，
而 `RealTokenSymbolLink` 直接用它（**未重新声明**）。

本引理把这一事实**显式命名**（否则它只是 import 的副产品、无法被引用）：
`ConstraintSet = List VectorConstraint`，故 L1⇄L2 的抽取结果**可以直接**
喂给 L2⇄L3 的 `compileToLayer`。

⚠ **诚实标注**：这是**同一律**（`rfl`），不是数学发现。
它的价值在于**把"两环共用同一符号类型"变成可引用的定理**，
使 §一 的健全性（`extract_sound_setSat`，用 `AllSatisfied`）
与 L2⇄L3 的 `symbolToWeight_correct`（也用 `AllSatisfied`）**能串起来**。 -/
theorem constraintSet_is_list_of_constraints :
    ConstraintSet = List VectorConstraint := rfl

/-- ⭐⭐ **L1 → L2 → L3 的语义串联（本文件与既有模块的接口）**：
若 `ts` 被抽取成 `cs`，则"`cs` 满足" ⟺ "`compileToLayer cs` 全零输出"。

由 `extract_sound_setSat` 与既有的 `symbolToWeight_correct` 串接 ——
这给出**从 token 流直达权重层行为**的一条完整通路，
即链路 `L1 → L2 → L3` 在**语义层**是通的（**结构层**的不可逆见 §六）。 -/
theorem extract_to_weights (ts : List SymToken) (cs : ConstraintSet)
    (_h : Extract ts cs) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  symbolToWeight_correct cs x

end Lattice
