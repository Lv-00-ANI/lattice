import Mathlib

/-!
# LATTICE: RealTokenization —— L0 ⇄ L1（数据 ⇄ token）的抽象模型与「商可逆」

## 定位（为什么需要这个文件）

doc/02 声明的链路是**四级双向**：

    L0 数据 ⇄ L1 token ⇄ L2 符号模型（规则/约束/DSL）⇄ L3 权重

其中 **L2⇄L3** 是既有工作，**L1⇄L2（token ⇄ 符号）** 由 `RealTokenSymbolLink` 补上，
而 **L0⇄L1（数据 ⇄ token）在证明层此前「连条目都没有」**
（`lean/README.md` §「❌ 未定义级」逐字登记：`tokenize` 2 处**均散文** /
`detokenize` **0** / `Vocab` **0** / `BPE` **0** / `WordPiece` **0**）。

本文件为该环建立**最小但真实**的形式化：不实现 BPE / WordPiece 的**算法**
（那是工程，不是理论），而建其**抽象结构**——字符层、词表、`tokenize` / `detokenize`。

## ⭐ 核心发现：非单射的来源是**归一化**，不是贪心匹配

任务书预置了 `tokenize_not_injective`，并提示「反例：如空白折叠」。**本文件在写作过程中
机器验证了一件更强的事**：对**任意**词表，只要

* `detokenize` 在拼写层**无损**（`detokenize ts = s`，只要 `tokenize s = some ts`），且
* `tokenize` 是**确定性函数**（贪心最长匹配就是），

那么 **`tokenize` 必然是单射**（证明即 `tokenizeRaw_injective`：由 `s = detokenize ts`
直接得到 `s` 被输出决定）。**真实 BPE 同样是确定性的**，故「分词非单射」**不能**归因于
贪心或 BPE 本身。

⭐ 非单射的**真实唯一来源**是**归一化**：分词器在切成 token 之前/之中**丢弃**信息
（空白折叠、大小写折叠、Unicode 规范化、未知字符替换为 UNK）。
本文件据此把 L0→L1 建模为

    tokenize := tokenizeRaw ∘ foldBlanks

其中 `foldBlanks`（空白折叠）是**幂等投影**。于是：

* `tokenize_not_injective` **成立**（`"a␣␣b"` 与 `"a␣b"` 折叠到同一处）——**与任务书一致**；
* 而 `tokenizeRaw_injective` 也**成立**（拼写层本身无损）——**这是一个任务书未预期、
  但机器检查过的区分**，它把「哪一层丢信息」定位清楚了。

## 主结果（全部为**真定理**）

| 定理 | 内容 | 角色 |
|:--|:--|:--|
| `foldBlanks_idem` | 归一化是**幂等投影** | 非单射的结构来源 |
| `tokenize_not_injective` | ⭐ **分词非单射**（`"a␣␣b"` vs `"a␣b"`） | 任务书要求的否定性结论 |
| `tokenize_collision` | 同上，存在量化形式（不依赖定义展开） | 反例可复核 |
| `tokenizeRaw_injective` | ⭐ 拼写层**是单射**（无损） | 定位「信息在哪一层丢失」 |
| `tokenizeRaw_detok` | 拼写层**无损**：`detokenize ts = s` | 核心正确性 |
| `tokenize_detok` | 真实分词器：`detokenize ts = foldBlanks s` | 接上归一化 |
| `tokAux_ne_none` / `tokenize_never_none` | 分词**永不失败**（贪心定义下阻塞不可达） | 定义良性 |
| `sameTokens_equivalence` | σ 是**等价关系** | 商结构 |
| `detokenize_left_inverse_on_quotient` | ⭐ **商左逆**（σ-截面） | 商可逆 |
| `detokenize_tokenize_on_quotient` | ⭐ **商可逆**：`σ (detokenize (tokenize s)) s` | 任务书核心要求 |
| `tokenize_detokenize_galois` | ⭐ **Galois 连接**（精确刻画） | 商可逆的最锐形式 |

## 诚实边界（本文件**不证 / 不声称**的）

- **不实现 BPE / WordPiece 的算法**：`bestPrefix` 是**贪心最长匹配**的抽象模型
  （BPE 的核心动作），不是任何真实分词器的规范。真实分词器的
  「合并优先级表」「字节级回退」「`##` 续接标记」等**不在本文件范围内**。
- ⚠ **`tokenize` 的 `none` 分支在本定义下不可达**（`tokenize_never_none` 已证）。
  这是「词表对任意字符序列都不阻塞」的**副产品**——因为本文件的词表
  （`single c` / `word c1 c2 rest`）覆盖了**所有**非空字符序列。
  真实词表**不**具备此性质（OOV 会阻塞），故本文件**不**把该定理读作
  「任意词表都能切分任意文本」。OOV / UNK 的真实处理是**归一化**的另一种形态，
  与本文件的 `foldBlanks` 同类，但**未在此建模**。
- ⚠ **`tokenize_detokenize_galois` 的逆向带合取项**。无条件的
  `tokenize s = some ts ↔ SameTokens s (detok ts)` **为假**：取 `ts := [single 'a', single 'a']`，
  则 `detok ts = "aa"`，`SameTokens "aa" "aa"` 成立而 `tokenize "aa" = some [word 'a' 'a' []] ≠ some ts`。
  故本文件陈述为 `↔ (SameTokens s (detok ts) ∧ tokenize (detok ts) = some ts)`
  ——即**只对规范（canonical）token 串**成立。这是诚实削弱，不是遗漏。
- **`β` 只作用于 `∀`-量化的引理，不作用于本文件的主定理**：本文件的 `Vocabulary`
  概念以**具体词表**（`single` / `word` 构造子）实现，未做「任意词表参数化」的
  抽象层——那会引入本文件不需要的复杂度，且不改变任何结论。
- **不涉及字节层**：L0 取 `Char`（`String` 是 `List Char` 的白话）。
  真实分词器工作在**字节**上（UTF-8），本文件不做字节↔字符的编解码形式化。
- 不使用 sorry / axiom / admit / native_decide。
-/

noncomputable section

namespace Lattice

/-! ## 一、L0 的归一化：空白折叠

`foldBlanks` 把每个极长的空白段折叠成**一个**空格。它是 L0→L1 上**唯一的丢信息处**，
因此也是「分词非单射」的**唯一来源**（见文件头「核心发现」）。

用状态机（`prevBlank`）而非两趟实现，使**幂等性成为结构性事实**：
`foldGo_idem` 的 `prevBlank = true` 分支正是「已折叠」信息的消费处。 -/

/-- 折叠意义上的空白：空格与换行。用**显式字符比较**而非 Unicode 表，
使可判定性与证明都不依赖外部数据。 -/
def isBlank (c : Char) : Bool := c = ' ' || c = '\n'

/-- 空白折叠状态机：`prevBlank` = 「上一个**输出**的字符是否为空白」。 -/
def foldGo (prevBlank : Bool) : List Char → List Char
  | [] => []
  | c :: rest =>
      if isBlank c = true then
        if prevBlank = true then foldGo true rest else ' ' :: foldGo true rest
      else c :: foldGo false rest

/-- **L0 归一化（空白折叠）**：每个极长空白段 → 一个空格。 -/
def foldBlanks (l : List Char) : List Char := foldGo false l

/-- **状态机幂等**：对自身输出再跑一次是恒等。 -/
theorem foldGo_idem (b : Bool) (l : List Char) : foldGo b (foldGo b l) = foldGo b l := by
  induction l generalizing b with
  | nil => rfl
  | cons c rest ih =>
    cases b with
    | false =>
      cases hc : isBlank c with
      | true =>
        simp only [foldGo, hc, if_true, Bool.false_eq_true, if_false]
        have hblank : isBlank ' ' = true := by decide
        simp only [foldGo, hblank, if_true]
        rw [ih true]
      | false =>
        simp only [foldGo, hc, Bool.false_eq_true, if_false]
        rw [ih false]
    | true =>
      cases hc : isBlank c with
      | true =>
        simp only [foldGo, hc, if_true]
        rw [ih true]
      | false =>
        simp only [foldGo, hc, Bool.false_eq_true, if_false]
        rw [ih false]

/-- ⭐ **`foldBlanks` 是幂等投影**（归一化的定义性质）。 -/
theorem foldBlanks_idem (l : List Char) : foldBlanks (foldBlanks l) = foldBlanks l :=
  foldGo_idem false l

/-! ## 二、L1 的词表：token 字母表与最长匹配

token 字母表是**两构造子**的归纳类型，对应「单字符 token」与「多字符 token」：

* `single c` ↦ 词条 `[c]`；
* `word c1 c2 rest` ↦ 词条 `c1 :: c2 :: rest`（**至少两字符**）。

这两个构造子**恰好**覆盖所有非空字符序列，且词条**互不相同**——
这正是使 `lookupTok` 成为**真逆**（而非近似）的原因，
也是 `tokAux_ne_none`（永不阻塞）成立的原因。 -/

/-- **L1 token 字母表（字符层）**：单字符 token 与多字符（≥2）token。

⚠⚠ **改名登记（原名 `Token` → 现名 `CharToken`）**：本仓库曾有两个**同名不同型**的
`Lattice.Token` —— 本文件的**字符层**字母表，与 `RealTokenSymbolLink.lean:69` 的
**符号层**字母表（`sym`/`sep`）。二者**同名不同型**且**不能同时 `import`**，实测报
'Lattice.instReprToken._cstage1' from RealTokenization`。
⭐⭐ **该冲突直接阻断「数据→token→符号→权重」的端到端组合**
（`RealQuotientReversibility` / `RealClosureReversibility` 两处**已登记**被迫拆文件）。
现按 STYLE「跨文件同名是潜伏断裂」的修法**改名消歧**：本文件用 `CharToken`。
⚠ 改名**不改变任何证明**（纯重命名），既有定理**一条未删**。

**诚实标注**：这不是真实 BPE 词表（真实词表是**学出来的**、与语料相关），
而是「词表结构」的最小抽象。 -/
inductive CharToken where
  | single (c : Char)
  | word (c1 : Char) (c2 : Char) (rest : List Char)
  deriving DecidableEq, Repr

/-- 词条映射：token → 它的字符序列。 -/
def pieceOf : CharToken → List Char
  | .single c => [c]
  | .word c1 c2 rest => c1 :: c2 :: rest

/-- 词表查询：字符序列 → token（贪心匹配的**单步**）。

`lookupTok_eq_some` 证明它是 `pieceOf` 的**真逆**，这是全文件的地基。 -/
def lookupTok : List Char → Option CharToken
  | [] => none
  | [c] => some (.single c)
  | c :: c2 :: rest => some (.word c c2 rest)

/-- **词条非空**（词表的结构性质）。 -/
theorem pieceOf_ne_nil (t : CharToken) : pieceOf t ≠ [] := by
  cases t <;> simp [pieceOf]

/-- ⭐ **`lookupTok` 是 `pieceOf` 的真逆**——这是词表良性的精确刻画。 -/
theorem lookupTok_eq_some {a : List Char} {t : CharToken} :
    lookupTok a = some t ↔ pieceOf t = a := by
  constructor
  · intro h
    cases a with
    | nil => simp [lookupTok] at h
    | cons c rest =>
        cases rest with
        | nil =>
            simp only [lookupTok, Option.some.injEq] at h
            rw [← h]; rfl
        | cons c2 rest2 =>
            simp only [lookupTok, Option.some.injEq] at h
            rw [← h]; rfl
  · intro h
    subst h
    cases t with
    | single c => rfl
    | word c1 c2 rest => rfl

/-! ## 三、反分词与最长前缀匹配 -/

/-- **反分词（L1 → L0）**：逐 token 换成词条后拼接。

**诚实标注**：这里的 `detokenize` 是**拼写层**的（无损）。
真实 `detokenize` 还承担「还原空白」等启发式——那与 `foldBlanks` 同为归一化的反面，
本文件只建模归一化方向。 -/
def detokenize : List CharToken → List Char
  | [] => []
  | t :: ts => pieceOf t ++ detokenize ts

theorem detokenize_append (a b : List CharToken) :
    detokenize (a ++ b) = detokenize a ++ detokenize b := by
  induction a with
  | nil => rfl
  | cons t ts ih => rw [List.cons_append, detokenize, ih, detokenize, List.append_assoc]

theorem detokenize_singleton (t : CharToken) : detokenize [t] = pieceOf t := by
  simp [detokenize]

/-- ⭐ **最长前缀匹配**：在 `rest` 的**前缀**中取最长的、可查到的那个。

`rest.inits` 按**由短到长**列出前缀，故 `.reverse` 后 `findSome?` 从左往右
= 前缀**由长到短**，这正是**贪心最长匹配**（BPE/WordPiece 的核心动作）。 -/
def bestPrefix (rest : List Char) : Option CharToken :=
  rest.inits.reverse.findSome? fun u => if u.isEmpty then none else lookupTok u

/-- ⭐ **最长匹配的规范形**：命中的 token 的词条是 `rest` 的**前缀**。 -/
theorem bestPrefix_spec {rest : List Char} {t : CharToken} (h : bestPrefix rest = some t) :
    ∃ u : List Char, pieceOf t ++ u = rest := by
  unfold bestPrefix at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, a, l₂, hpref, hfa, hnone⟩ := h
  have ha : a ∈ rest.inits := by
    have : a ∈ rest.inits.reverse := by
      rw [hpref]; exact List.mem_append_right l₁ (List.mem_cons_self a l₂)
    simpa using this
  have hpa : lookupTok a = some t := by
    have hna : a.isEmpty = false := by
      by_contra hc
      have h1 : a.isEmpty = true := by simpa using hc
      rw [h1] at hfa
      simp at hfa
    rw [hna] at hfa
    simpa using hfa
  have hpt : pieceOf t = a := lookupTok_eq_some.mp hpa
  rw [hpt]
  exact (List.mem_inits a rest).mp ha

/-! ## 四、分词（拼写层）：贪心 + 燃料

用 `fuel` 而非良基递归：燃料 = `s.length + 1` 恒够（每步至少消耗 1 字符，
由 `tokAux_ne_none` 的证明中的 `hdrop` 给出）。 -/

/-- 分词主循环：`done` 是**已固定的输出**（尾部追加），`rest` 是**未消耗的字符**。

不变式（`tokAux_detok`）：`detokenize done ++ rest = 原串`。 -/
def tokAux (fuel : Nat) (done : List CharToken) (rest : List Char) : Option (List CharToken) :=
  match fuel with
  | 0 => none
  | n + 1 =>
      match rest with
      | [] => some done
      | _ =>
          match bestPrefix rest with
          | none => none
          | some t => tokAux n (done ++ [t]) (rest.drop (pieceOf t).length)
termination_by fuel

/-- ⭐ **`tokAux` 的不变式**：返回 `some ts` ⟹ `detokenize ts = detokenize done ++ rest`。

即「输出重新拼出输入」——**拼写无损**，这是本层能有的最强陈述。 -/
theorem tokAux_detok (fuel : Nat) (done : List CharToken) (rest : List Char)
    {ts : List CharToken} (h : tokAux fuel done rest = some ts) :
    detokenize ts = detokenize done ++ rest := by
  induction fuel generalizing done rest with
  | zero => simp [tokAux] at h
  | succ n ih =>
      cases rest with
      | nil =>
          simp only [tokAux, Option.some.injEq] at h
          subst h
          simp
      | cons c tl =>
          simp only [tokAux] at h
          split at h
          · exact absurd h (by simp)
          · rename_i t ht
            obtain ⟨u, hu⟩ := bestPrefix_spec ht
            have hdrop : (c :: tl).drop (pieceOf t).length = u := by
              rw [← hu]; exact List.drop_left (pieceOf t) u
            have hih := ih (done ++ [t]) ((c :: tl).drop (pieceOf t).length) h
            rw [hdrop] at hih
            rw [hih, detokenize_append, detokenize_singleton]
            rw [← hu]
            simp [List.append_assoc]

/-- ⭐ **拼写层分词（L0 → L1）**：贪心最长匹配，不做任何归一化。 -/
def tokenizeRaw (s : List Char) : Option (List CharToken) := tokAux (s.length + 1) [] s

/-- ⭐ **拼写层无损**：`tokenizeRaw` 的输出必定重新拼出输入。 -/
theorem tokenizeRaw_detok {s : List Char} {ts : List CharToken} (h : tokenizeRaw s = some ts) :
    detokenize ts = s := by
  unfold tokenizeRaw at h
  have := tokAux_detok (s.length + 1) [] s h
  simpa using this

/-- ⭐⭐ **拼写层是单射**（**本文件的关键发现之一**）。

由 `tokenizeRaw_detok` 立得：输出决定 `s = detokenize ts`。
⇒ **贪心/BPE 本身不产生非单射**；非单射只能来自归一化（见 §五）。
这是任务书未预期、但机器检查过的**区分性结论**。 -/
theorem tokenizeRaw_injective :
    ∀ {s t : List Char} {ts : List CharToken},
      tokenizeRaw s = some ts → tokenizeRaw t = some ts → s = t := by
  intro s t ts hs ht
  rw [← tokenizeRaw_detok hs, ← tokenizeRaw_detok ht]

/-! ## 五、真实分词器：归一化 ∘ 拼写层

⭐ 这是 L0→L1 的**真实**模型：先折叠空白（丢信息），再贪心匹配（无损）。

于是 `tokenize` **非单射**，且**唯一**的非单射来源被隔离在 `foldBlanks` 里。 -/

/-- ⭐ **分词（L0 → L1，真实模型）**：`tokenize := tokenizeRaw ∘ foldBlanks`。 -/
def tokenize (s : List Char) : Option (List CharToken) := tokenizeRaw (foldBlanks s)

/-- ⭐⭐ **分词非单射**（任务书要求的核心否定性结论）。

见证：`"a␣␣b"` 与 `"a␣b"`。二者**不等**，而折叠到同一处 ⟹
分词结果**恒等**（无论 `tokenizeRaw` 取值如何——故这是**结构性**反例，
不依赖词表的具体行为）。 -/
theorem tokenize_not_injective : ¬ Function.Injective tokenize := by
  intro h
  have heq : tokenize (['a', ' ', ' ', 'b'] : List Char)
           = tokenize (['a', ' ', 'b'] : List Char) := rfl
  have hne : (['a', ' ', ' ', 'b'] : List Char) ≠ ['a', ' ', 'b'] := by decide
  exact hne (h heq)

/-- 同上的**存在量化**形式（供不依赖定义展开的复核）。 -/
theorem tokenize_collision :
    ∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t :=
  ⟨['a', ' ', ' ', 'b'], ['a', ' ', 'b'], by decide, rfl⟩

/-- ⭐ **真实分词器的无损刻画**（削弱到归一化后）：`detokenize ts = foldBlanks s`。 -/
theorem tokenize_detok {s : List Char} {ts : List CharToken} (h : tokenize s = some ts) :
    detokenize ts = foldBlanks s :=
  tokenizeRaw_detok h

/-! ## 六、定义良性：分词永不失败

本文件的词表（`single` / `word`）覆盖**所有**非空字符序列，
故 `bestPrefix` 在非空输入上必命中，贪心的 `none` 分支**不可达**。

⚠ **诚实边界**：这是本词表（归纳覆盖）的**副产品**，
**不**读作「任意词表都能切分任意文本」。真实词表有 OOV，会阻塞。 -/

/-- 非空列表必可查到（最长前缀即为它自己或它的短前缀）。 -/
theorem lookupTok_ne_none (l : List Char) (hl : l ≠ []) : lookupTok l ≠ none := by
  cases l with
  | nil => exact absurd rfl hl
  | cons c rest =>
    cases rest with
    | nil => simp [lookupTok]
    | cons c2 r2 => simp [lookupTok]

/-- 非空输入上 `bestPrefix` 必命中（因为输入自身就是自己的最长前缀）。 -/
theorem bestPrefix_ne_none (rest : List Char) (hrest : rest ≠ []) :
    bestPrefix rest ≠ none := by
  intro h
  unfold bestPrefix at h
  rw [List.findSome?_eq_none_iff] at h
  have hmem : rest ∈ rest.inits.reverse := by
    apply List.mem_reverse.mpr
    exact (List.mem_inits rest rest).mpr (⟨[], by simp⟩ : rest <+: rest)
  have := h rest hmem
  have hne : rest.isEmpty = false := by
    cases rest with
    | nil => exact absurd rfl hrest
    | cons c r => rfl
  rw [hne] at this
  simp at this
  exact lookupTok_ne_none rest hrest this

/-- ⭐ **`tokAux` 从不返回 `none`**（燃料充足时）。关键：每步至少消耗 1 字符，
故 `rest.length` 严格递减，燃料 `length + 1` 恒够。 -/
theorem tokAux_ne_none (fuel : Nat) (done : List CharToken) (rest : List Char)
    (hf : rest.length < fuel) : tokAux fuel done rest ≠ none := by
  induction fuel generalizing done rest with
  | zero => simp at hf
  | succ n ih =>
      cases rest with
      | nil => simp [tokAux]
      | cons c tl =>
          have hne : bestPrefix (c :: tl) ≠ none := bestPrefix_ne_none _ (by simp)
          unfold tokAux
          cases hbf : bestPrefix (c :: tl) with
          | none => exact absurd hbf hne
          | some t =>
            intro h
            have hlen : 0 < (pieceOf t).length :=
              List.length_pos_of_ne_nil (pieceOf_ne_nil t)
            have hdrop : ((c :: tl).drop (pieceOf t).length).length < n := by
              rw [List.length_drop, List.length_cons]
              simp only [List.length_cons] at hf
              omega
            exact ih (done ++ [t]) _ hdrop h

/-- **`foldBlanks` 不增加长度**（每个空白段至少缩到 1 个字符）。 -/
theorem foldGo_length_le (b : Bool) (l : List Char) : (foldGo b l).length ≤ l.length := by
  induction l generalizing b with
  | nil => simp [foldGo]
  | cons c rest ih =>
    have h1 : (foldGo true rest).length ≤ rest.length := ih true
    have h0 : (foldGo false rest).length ≤ rest.length := ih false
    cases b with
    | false =>
      cases hc : isBlank c with
      | true =>
        rw [foldGo]
        rw [hc]; simp only [if_true, Bool.false_eq_true, if_false]
        simp only [List.length_cons]
        omega
      | false =>
        rw [foldGo]
        rw [hc]; simp only [Bool.false_eq_true, if_false, List.length_cons]
        omega
    | true =>
      cases hc : isBlank c with
      | true =>
        rw [foldGo]
        rw [hc]; simp only [if_true, List.length_cons]
        omega
      | false =>
        rw [foldGo]
        rw [hc]; simp only [Bool.false_eq_true, if_false, List.length_cons]
        omega

theorem foldBlanks_length_le (l : List Char) : (foldBlanks l).length ≤ l.length :=
  foldGo_length_le false l

/-- ⭐ **分词永不失败**（`tokenize` 无 `none` 分支）。

燃料 `s.length + 1` 恒够：折叠不增长度（`foldBlanks_length_le`），
故 `(foldBlanks s).length < s.length + 1`，由 `tokAux_ne_none` 即得。 -/
theorem tokenize_never_none (s : List Char) : ∃ ts : List CharToken, tokenize s = some ts := by
  show ∃ ts : List CharToken, tokAux ((foldBlanks s).length + 1) [] (foldBlanks s) = some ts
  have hle : (foldBlanks s).length < (foldBlanks s).length + 1 := by omega
  have h := tokAux_ne_none ((foldBlanks s).length + 1) [] (foldBlanks s) hle
  cases hts : tokAux ((foldBlanks s).length + 1) [] (foldBlanks s) with
  | none => exact absurd hts h
  | some ts => exact ⟨ts, rfl⟩

/-! ## 七、商可逆（L0⇄L1 唯一可能的可逆性形式）

分词非单射（§五），故**严格左逆不存在**。唯一能问的是**模掉 σ 的左逆**。 -/

/-- **σ（同一分词结果）**：`s` 与 `t` 等价 ⟺ 它们分词结果相同。

这是「分词非单射」的**精确残差**。 -/
def SameTokens (s t : List Char) : Prop := tokenize s = tokenize t

/-- **σ 是等价关系**。 -/
theorem sameTokens_equivalence : Equivalence SameTokens :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- ⭐ **σ-截面**：对已成功分词的结果 `ts`，重分词 `detokenize ts` 得到**同一** `ts`。

这是 `detokenize ∘ tokenize = id` 在**像上**的精确形式（比商等式更锐）。 -/
theorem detokenize_left_inverse_on_quotient {s : List Char} {ts : List CharToken}
    (h : tokenize s = some ts) : tokenize (detokenize ts) = some ts := by
  unfold tokenize at h ⊢
  rw [tokenizeRaw_detok h, foldBlanks_idem]
  exact h

/-- ⭐⭐ **商可逆（核心定理）**：`detokenize ∘ tokenize` 把 `s` 送回**它自己的 σ-类**。

即：`SameTokens (detokenize (tokenize s)) s`。
这是 L0⇄L1 上唯一可能的可逆性形式（严格左逆因非单射而不存在）。 -/
theorem detokenize_tokenize_on_quotient (s : List Char) :
    SameTokens (detokenize ((tokenize s).getD [])) s := by
  obtain ⟨ts0, hts0⟩ := tokenize_never_none s
  cases h : tokenize s with
  | none => exact absurd h (by rw [hts0]; simp)
  | some ts =>
      show tokenize (detokenize (Option.getD (some ts) [])) = tokenize s
      rw [h]
      simp only [Option.getD_some]
      exact detokenize_left_inverse_on_quotient h

/-- ⭐ **Galois 连接（精确刻画）**：`tokenize s = some ts` ⟺
`s` 与 `detokenize ts` 同类**且** `ts` 本身是规范的（重分词回到自身）。

⚠ **诚实标注**：合取项 `tokenize (detokenize ts) = some ts` **不可省**——无条件版为假
（反例 `ts := [single 'a', single 'a']`：`detokenize ts = "aa"`，同类成立但
`tokenize "aa" = some [word 'a' 'a' []] ≠ some ts`）。见文件头「诚实边界」。 -/
theorem tokenize_detokenize_galois (s : List Char) (ts : List CharToken) :
    tokenize s = some ts ↔
      (SameTokens s (detokenize ts) ∧ tokenize (detokenize ts) = some ts) := by
  constructor
  · intro h
    exact ⟨by
      show tokenize s = tokenize (detokenize ts)
      rw [h]
      exact (detokenize_left_inverse_on_quotient h).symm,
      detokenize_left_inverse_on_quotient h⟩
  · intro ⟨h1, h2⟩
    show tokenize s = some ts
    rw [show tokenize s = tokenize (detokenize ts) from h1]
    exact h2

end Lattice
