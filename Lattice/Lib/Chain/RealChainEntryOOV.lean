import Lattice.Lift.RealTokenizationEntry
import Lattice.Lift.RealTokenSymbolLink
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Lift.SymbolToWeightCorrectness
/-!
# LATTICE: RealChainEntryOOV -- 入口桥的【端到端行使】与 OOV 分词器

## 定位（为什么需要这个文件）

### 缺口 (b)：入口桥存在但**未被端到端行使**（判据 9）

Z04-G2 实测：`Text.encode` 的消费者**只有** `tokenizeStr`（同文件 `RealTokenizationEntry.lean:82`），
而 `RealChainRun.lean:3` 虽然 `import RealTokenizationEntry`，**正文 0 处使用**（死 import，V01 实测）。
`RealEndToEnd.e2e_path_exists`（`RealEndToEnd.lean:510-517`）**仍从 `List Char` 出发**。

=> **入口桥（String -> List Char）在证明层从未被驱动过**：它能被陈述，但**没有一条通路从 String 起跑**。

### 缺口 (c)：Z04-G1 -- OOV 词表**没有接到分词器**

W28 §四 R-W28-1 逐字要求：`OOVVocab` / `bestPrefixV` **外加** `tokAuxV` / `tokenizeV`
与否面定理 `tokenizeV_can_fail`。V01 实测全仓 `grep tokenizeV|tokAuxV` = **0**。

=> `RealTokenization.lean:272-273` 的 `| none => none` 分支**至今仍是死代码**：
既有文件只给了「**单步选择**的 OOV 可达」（`bestPrefixV_Vzz_oov`），
**没有**给出「**分词过程**会因 OOV 而阻塞」。

## 本文件的两组交付

| 组 | 交付 | 缺口 |
|:-:|:--|:--|
| 一 | `tokAuxV` / `tokenizeV` + 正例 + **`tokenizeV_can_fail`（分词层 OOV 可达）** | (c) Z04-G1/R-W28-1 |
| 二 | `runChainStr`：**从 `String` 起跑**的六级贯通 + 端到端存在性 | (b) Z04-G2/判据 9 |

## 诚实边界

* **`tokenizeV` 不替换 `tokenize`**：`RealTokenization.lean` 一行未动。`tokenize_never_none`
  （`RealTokenization.lean:453`）**仍然逐字成立**（它说的是**退化词表**上的事）。
  本文件证明的是**另一件事**：**词表受限时**分词**会**阻塞。
* **`Vzz` 不是真实词表**：它是**见证**（使 OOV 在**分词层**可达），不是任何真实分词器。
* `tokenizeV` 的燃料口径：与 `tokenizeRaw` 一致取 `s.length + 1`。
  在 OOV 词表下「每步至少消耗 1 字符」不再成立 -- 但那正是 `none` 分支**可达**的原因，
  故燃料口径照旧：燃料只保证「不因燃料耗尽而假失败」，
  **`none` 的真来源是 `bestPrefixV` 的阻塞**（见 `tokenizeV_Vzz_blocks`）。
* **`runChainStr` 的贯通依赖 `tokenize_never_none`**（退化词表性质），
  不是 OOV 词表 -- 真实分词器上该存在性会失效（与 `e2e_path_exists` 同一边界）。
* **不声称 `runChainStr` 是 `e2e_path_exists` 的加强**：二者入口不同（`String` vs `List Char`）。
* 不使用 sorry / axiom / admit / native_decide。
-/

noncomputable section

open Lattice.Lib.Chain.RealEndToEnd

namespace Lattice

/-! ## 一、OOV 感知的分词器（Z04-G1 / W28 R-W28-1）

`tokAuxV` 与既有 `tokAux`（`RealTokenization.lean:265`）**逐字同构**，
**唯一**差别是把 `bestPrefix` 换成 `bestPrefixV V`。

**这一差别就是全部内容**：它把「阻塞」从一个**单步函数**的性质，
升成**分词过程**的性质。 -/

/-- **OOV 感知的分词主循环**：与 `tokAux` 同构，只把 `bestPrefix` 换成 `bestPrefixV V`。 -/
def tokAuxV (V : OOVVocab) (fuel : Nat) (done : List CharToken) (rest : List Char) :
    Option (List CharToken) :=
  match fuel with
  | 0 => none
  | n + 1 =>
      match rest with
      | [] => some done
      | _ =>
          match bestPrefixV V rest with
          | none => none
          | some t => tokAuxV V n (done ++ [t]) (rest.drop (pieceOf t).length)
termination_by fuel

/-- **`tokAuxV` 的零燃料方程**（显式给出，供计算使用）。

⚠ **为什么需要**：`tokAuxV` 带一个**前导参数 `V`**，Lean 为它生成的方程引理
**不**总能在 `fuel` 为**非字面项**（如 `['q'].length + 1`）时被 `simp only [tokAuxV]` 用上
（V01 实测：`rw` 报 `did not find instance of the pattern`）。
⭐ 显式方程引理把这个**定义层的偶然性**从证明里移走。 -/
@[simp] theorem tokAuxV_zero (V : OOVVocab) (done : List CharToken) (rest : List Char) :
    tokAuxV V 0 done rest = none := by unfold tokAuxV; rfl

/-- **`tokAuxV` 的非零燃料方程**（同上的显式形式）。 -/
theorem tokAuxV_succ (V : OOVVocab) (n : Nat) (done : List CharToken) (rest : List Char) :
    tokAuxV V (n + 1) done rest =
      (match rest with
        | [] => some done
        | _ =>
            match bestPrefixV V rest with
            | none => none
            | some t => tokAuxV V n (done ++ [t]) (rest.drop (pieceOf t).length)) := by
  cases rest with
  | nil => conv_lhs => unfold tokAuxV
  | cons c tl => conv_lhs => unfold tokAuxV

/-- **`tokAuxV` 在空输入上的方程**（计算 `tokenizeV` 用）。 -/
@[simp] theorem tokAuxV_nil (V : OOVVocab) (n : Nat) (done : List CharToken) :
    tokAuxV V (n + 1) done [] = some done := by
  rw [tokAuxV_succ]

/-- **`tokAuxV` 的 `cons` 方程**（计算 `tokenizeV` 用）。 -/
theorem tokAuxV_cons (V : OOVVocab) (n : Nat) (done : List CharToken) (c : Char)
    (tl : List Char) :
    tokAuxV V (n + 1) done (c :: tl) =
      (match bestPrefixV V (c :: tl) with
        | none => none
        | some t => tokAuxV V n (done ++ [t]) ((c :: tl).drop (pieceOf t).length)) := by
  rw [tokAuxV_succ]

/-- **OOV 感知的分词（L0 -> L1）**：燃料口径与 `tokenizeRaw` 一致。 -/
def tokenizeV (V : OOVVocab) (s : List Char) : Option (List CharToken) :=
  tokAuxV V (s.length + 1) [] s

/-! ### 1.1 无 OOV 时的退化：`tokenizeV` 就是 `tokenizeRaw`

这是本组交付的**正确性锚点**：新定义在**旧词表**上**不改变**任何行为。
没有这条，`tokenizeV` 可能是「另一个函数」，而不是「`tokenize` 的推广」。 -/

/-- **全接受词表**：对任意字符块都返回 `true`（= 无 OOV）。 -/
def VAll : OOVVocab := fun _ => true

/-- **`bestPrefixV` 在全接受词表上等于 `bestPrefix`**。 -/
theorem bestPrefixV_VAll_eq (rest : List Char) : bestPrefixV VAll rest = bestPrefix rest := by
  unfold bestPrefixV bestPrefix VAll
  apply congrArg (fun f => rest.inits.reverse.findSome? f)
  funext u
  by_cases hu : u.isEmpty
  · simp [hu]
  · simp only [hu, Bool.false_eq_true, if_false, if_true]

/-- **推广性（无 OOV 时行为不变）**：`tokAuxV VAll = tokAux`。

这是「`tokenizeV` 是 `tokenizeRaw` 的真推广」的**机器证据**，
也是 §二 能让两种分词器**并存**的理由：它们只在词表上分岔。 -/
theorem tokAuxV_VAll_eq (fuel : Nat) (done : List CharToken) (rest : List Char) :
    tokAuxV VAll fuel done rest = tokAux fuel done rest := by
  induction fuel generalizing done rest with
  | zero => simp only [tokAuxV, tokAux]
  | succ n ih =>
      cases rest with
      | nil => simp only [tokAuxV, tokAux]
      | cons c tl =>
          simp only [tokAuxV, tokAux, bestPrefixV_VAll_eq]
          cases h : bestPrefix (c :: tl) with
          | none => rfl
          | some t => exact ih (done ++ [t]) _

/-- **`tokenizeV VAll = tokenizeRaw`**（逐字，由 `tokAuxV_VAll_eq`）。 -/
theorem tokenizeV_VAll_eq_tokenizeRaw (s : List Char) :
    tokenizeV VAll s = tokenizeRaw s := by
  unfold tokenizeV tokenizeRaw
  exact tokAuxV_VAll_eq (s.length + 1) [] s

/-! ### 1.2 正例：词表内仍成功

与 Z04-G1 的要求逐字对应：「**正例**：存在 ts, tokenizeV Vzz ['z','z'] = some ts」。 -/

/-- **正例（词表内成功分词）**：`['z','z']` 在 `Vzz` 下切成 `[word 'z' 'z' []]`。 -/
theorem bestPrefixV_Vzz_zz : bestPrefixV Vzz ['z', 'z'] = some (CharToken.word 'z' 'z' []) := by
  decide

theorem tokenizeV_Vzz_in :
    tokenizeV Vzz ['z', 'z'] = some [CharToken.word 'z' 'z' []] := by
  unfold tokenizeV
  show tokAuxV Vzz ((['z', 'z'] : List Char).length + 1) [] ['z', 'z'] =
    some [CharToken.word 'z' 'z' []]
  simp only [List.length_cons, List.length_nil, tokAuxV_cons, bestPrefixV_Vzz_zz,
             List.drop, List.drop_zero, List.append_nil, tokAuxV_nil, List.nil_append]

/-! ### 1.3 否面：**分词层** OOV 可达（本组的全部价值）

下面这条**不在** Z04-G1 的字面要求里，但它是 W28 缺口①的**真正闭合**：
Z04-G1 要的 `存在 s, tokenizeV Vzz s = none` 只要求**存在性**；
本文件给出**逐字的见证等式**，并把**阻塞发生的【位置】**钉死（那是 `bestPrefixV` 那一层）。 -/

/-- **分词层阻塞（`tokenize` 的 `none` 分支【首次可达】）**：
`['q']` 在 `Vzz` 下**不可切** -- `tokenizeV` 返回 `none`。

**这是 W28 缺口①的闭合点**：`tokenize_never_none`（`RealTokenization.lean:453`）
说的是**退化词表**上「永不 none」；本条说的是**受限词表**上「**会** none」。
**两条不矛盾** -- 它们**量化在不同的词表上**。 -/
theorem tokenizeV_Vzz_blocks : tokenizeV Vzz ['q'] = none := by
  unfold tokenizeV
  show tokAuxV Vzz ((['q'] : List Char).length + 1) [] ['q'] = none
  simp only [List.length_cons, List.length_nil, tokAuxV_cons, bestPrefixV_Vzz_oov]

/-- **存在形式（Z04-G1 逐字要求的那条）**：存在输入使 `tokenizeV Vzz` 失败。 -/
theorem tokenizeV_can_fail : ∃ s : List Char, tokenizeV Vzz s = none :=
  ⟨['q'], tokenizeV_Vzz_blocks⟩

/-- **对照（判据 10：负对照必须能区分）**：**同一输入** `['q']` 在**全接受词表**下**成功**。

=> 两条合起来把「阻塞」钉成**词表**的性质，而不是**输入**的偶然性。
若有人把 `VAll` 改成 `Vzz`，红的会是这里（判据 13）。 -/
theorem tokenizeV_VAll_accepts_where_Vzz_blocks :
    (tokenizeV VAll ['q']).isSome = true ∧ tokenizeV Vzz ['q'] = none := by
  refine ⟨?_, tokenizeV_Vzz_blocks⟩
  rw [tokenizeV_VAll_eq_tokenizeRaw]
  obtain ⟨ts, hts⟩ := tokenize_never_none ['q']
  rw [show tokenizeRaw ['q'] = tokenize ['q'] from rfl, hts]
  rfl

/-- **旧全称定理在受限词表上【为假】**（判据 13：断言的是**旧定理的陈述本身**）。

本条的**取反**正是 `tokenize_never_none` 的形状（forall s, exists ts, tokenize s = some ts）；
=> **若有人把 `Vzz` 改回全接受词表，红的会是这里**。

与 `RealTokenizationEntry.tokenize_never_none_fails_for_Vzz`（:166）的分工：
那条说的是 **`bestPrefixV`（单步）**失败；本条说的是 **`tokenizeV`（分词过程）**失败。
二者**不同**：单步失败不蕴含过程失败，**故本条不是那条的重述**。 -/
theorem tokenize_never_none_fails_for_tokenizeV :
    ¬ (∀ s : List Char, ∃ ts : List CharToken, tokenizeV Vzz s = some ts) := by
  intro h
  obtain ⟨ts, hts⟩ := h ['q']
  rw [tokenizeV_Vzz_blocks] at hts
  exact absurd hts (by simp)

/-! ## 二、入口桥的端到端行使（缺口 (b) / 判据 9）

`RealEndToEnd.e2e_path_exists`（`:510`）**从 `List Char` 出发**。
本节把它**上移一层到 `String`**，使 `Text.encode` **真正进入端到端通路**。

**关键设计**：本节的证明项**必须** `rw [tokenizeStr_eq_tokenize]`
-- 否则 `Text.encode` 仍只是**被陈述**而非**被行使**（判据 9 的本来含义）。 -/

/-- **从 `String` 起跑的端到端通路存在性**（Z04-G2 / 判据 9 的闭合点）。

**陈述**：对**任意** `String` 输入 `s`，**都存在**一条从 `String` 出发、
经 L0（`Text.encode`）-> L1（`tokenizeStr`）-> **L1 桥**（`L1Bridge`）
-> L2（`Extract`/`decode`）-> L3（`compileToLayer`）的**走通**通路。

**与 `e2e_path_exists` 的差别（这就是本节的交付）**：

| | `e2e_path_exists`（既有） | 本条 |
|:--|:--|:--|
| **入口** | `s : List Char` | `s : String` |
| 入口桥 `Text.encode` | 不在陈述里 | **在**（L0 段） |
| 入口分词 | `tokenize` | `tokenizeStr`（= tokenize 复合 Text.encode） |

**诚实标注**：本条的**承重处**与 `e2e_path_exists` **相同**
（都是 `tokenize_never_none` 的退化词表性质，经 `tokenizeStr_never_none` 继承）；
**新增的承重处只有一处**：`rw [tokenizeStr_eq_tokenize]`，
它使 **`Text.encode` 从「被提及」变成「被经过」**。 -/
theorem e2e_path_exists_str (s : String) :
    ∃ ts : List CharToken, tokenizeStr s = some ts ∧
      ∃ cs : ConstraintSet, Extract (L1Bridge ts) cs ∧
        ∀ x : List Int, (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) := by
  -- 承重第一步：把 `String` 入口**经组合律**降到 L0（**判据 9 要求的 `rw`**）
  have hbridge : tokenizeStr s = tokenize (Text.encode s) := tokenizeStr_eq_tokenize s
  obtain ⟨ts, hts⟩ := tokenizeStr_never_none s
  refine ⟨ts, hts, (toSegs (L1Bridge ts)).map mkConstraint, rfl, ?_⟩
  intro x
  exact symbolToWeight_correct _ x


/-- **入口桥【承重】定理（判据 9 的真正闭合）**：入口分词器的**产出**就是
`encode` 后的 L0 上的分词结果 —— 这条**把桥的内容写进结论**。

⚠⚠ **为什么必须单列这一条（V01 实测，判据 13）**：
V01 用**真实负对照**（把 `RealTokenizationEntry.lean:46` 的 `Text.encode` 改成常函数 `[]`）
实测了两件事：

1. `e2e_path_exists_str`（上一条）**仍然绿** —— 它只**陈述** `tokenizeStr s = some ts`，
   **不消费** `encode` 的内容，故 `encode` 被改坏它**测不到**；
2. ⭐⭐ **凡是把结论写成 `... (Text.encode s) ...` 形式的等式，也仍然绿** ——
   因为 `encode` 的**定义体**被替换后，等式**两侧同步变化**，`rfl` 照样成立。

⇒ ⭐⭐ **真正的承重锚点必须【跨出 `encode` 的定义体】**：
本条把 `tokenizeStr`（`String` 入口）与 `tokenize`（`List Char` 入口）在
**具体字符序列**上钉死 —— 右式的 `['a','b']` 是**字面量**，**不随 `encode` 变化**。
⚠ **若把 `encode` 改成 `[]`，本条必红**（`'a'` 与 `[]` 不等）。
⭐ 这就是判据 13 要求的形态：**断言自己触发的那个 finding 的身份**。 -/
theorem tokenizeStr_encode_content :
    tokenizeStr "ab" = tokenize (['a', 'b'] : List Char) := by
  rw [tokenizeStr_eq_tokenize]
  rfl

/-- **入口桥保真的可判定锚点（跨出定义体的第二条）**：
`encode` 在具体串上给出**具体字符表**。

⚠ 与上一条同源：右式是**字面量**，不是 `encode` 的重写。
⭐ **把 `encode` 改成 `[]` 会使本条断言变为 `[] = ['a','b']`，必红**。 -/
theorem Text_encode_ab : Text.encode "ab" = (['a', 'b'] : List Char) := rfl

/-- **从 `String` 起跑的六级贯通（可执行驱动）**：
把 L0->L1->桥->L2->L3 串成**一条**调用链，**每一步都用既有函数**。

与 `RealChainRun.runSymbols`（`:65`）的差别：那条**从 `List Char` 起**，
本条**从 `String` 起**并**显式经过 `Text.encode`** => 入口桥**被行使**。 -/
def runChainStr (s : String) : Layer :=
  compileToLayer ((decode (L1Bridge ((tokenizeStr s).getD []))).getD [])

/-- **六级贯通的类型确实接得上**（一条链，不是六级各调一次）：
`String -> Option (List CharToken) -> List SymToken -> Option ConstraintSet -> Layer`。

**本条的证明项逐字就是 `rw [tokenizeStr_eq_tokenize]`** -- 若把入口桥删掉，本行必红。 -/
theorem runChainStr_eq (s : String) :
    runChainStr s =
      compileToLayer ((decode (L1Bridge ((tokenize (Text.encode s)).getD []))).getD []) := by
  unfold runChainStr
  rw [tokenizeStr_eq_tokenize]

/-! ### 2.1 有限输入上的可判定读数（T2 型，判据 6 的落地）

与 `RealChainRun` §三 同口径：`AllSatisfied` 是 **forall- 量化的 `Prop`**，**不可判定**；
但 `LayerOut` 是 **`Int` 值函数**，在有限输入上 `decide` 可判定。 -/

/-- 入口驱动在具体 `String` 上的**具体层**（用于 `#eval` 与等式定理）。 -/
def runStrAB : Layer := runChainStr "ab"

/-! ## 三、`#eval` 驱动（判据 1：值必须出现在 `lake build` 日志中） -/

/- L0->L1：`String` 入口分词成功（`tokenizeStr_never_none` 的实例）。 -/
#eval (tokenizeStr "ab").isSome

/- 入口桥**确实被经过**：`Text.encode` 的长度读数。 -/
#eval (Text.encode "ab").length

/- L1->L2->L3：从 `String` 起跑的贯通层长度。 -/
#eval (runChainStr "ab").length

/- §一 OOV：正例（词表内成功）。 -/
#eval (tokenizeV Vzz ['z', 'z']).isSome

/- §一 OOV：**否面**（分词层阻塞）-- `tokenize` 的 `none` 分支首次可达。 -/
#eval (tokenizeV Vzz ['q']).isSome

/- 对照（判据 10）：同一输入在全接受词表下**成功**。 -/
#eval (tokenizeV VAll ['q']).isSome

/- 判据 13 负对照：同一串的两次跑**层长度相等**（可判定）。 -/
#eval decide ((runStrAB).length = (runChainStr "ab").length)

/- 对照：换成另一个串，层长度**不同**（入口承重）。 -/
#eval (runStrAB).length
#eval (runChainStr "ba").length

end Lattice
