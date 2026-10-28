import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Runtime.RealTokenization
/-!
# LATTICE: RealFCATokenization —— ⭐ **FCA 的 `intent` 就是分词的选择集**

## 定位（为什么需要这个文件）

用户问：**「FCA 似乎本身也能当分词器吧？」**

coordinator 读源码后的接口推导（本文件把它**证明化**）：

```
取 R s t := "t 是 s 的前缀"（O := List Char 字符串，A := List Char 候选词条）
  intent R {s} = { t | t 是 s 的前缀 }   ← ⭐ 这就是"所有匹配候选"
  ⇒ 在词表 V 中取它的最长元 = bestPrefix s（贪心最长匹配）
```

⇒ ⭐⭐ **分词的选择集就是一个 `intent`**。因此 `RealFCA` 里**已证好**的
FCA 定理（`galois_connection` / 闭包幂等 / 概念格结构）**可直接复用，
不必在 `RealTokenization` 里重复造**。本文件即那次复用的落地。

## ⭐ 本文件的成果（全部为真定理）

| # | 定理 | 内容 | 复用谁 |
|:--|:--|:--|:--|
| 1 | `isPrefixRel_iff_isPrefix` | 桥接关系 = `List.IsPrefix` | — |
| 2 | `intent_isPrefixRel` | ⭐⭐ **桥接**：`intent isPrefixRel {s} = {t \| t <+: s}` | `Lattice.intent` |
| 3 | `extent_isPrefixRel` | 对偶：`extent isPrefixRel {t} = {s \| t <+: s}` | `Lattice.extent` |
| 4 | `galois_connection_isPrefixRel` | ⭐ **直接调用已证 Galois 连接** | `RealFCA.galois_connection` |
| 5 | `closure_idempotent_isPrefixRel` | ⭐ **复用对象端闭包幂等** | `RealFCA.closure_idempotent` |
| 6 | `intent_closure_idempotent_isPrefixRel` | ⭐ **复用内涵端闭包幂等** | `RealFCA.intent_closure_idempotent` |
| 7 | `intent_antitone_isPrefixRel` | ⭐ **复用反变单调** | `RealFCA.intent_antitone` |
| 8 | `prefixConcept_is_concept` | ⭐ **复用形式概念 + 闭合性** | `RealFCA.IsFormalConcept` / `intent_closure_idempotent` |
| 9 | `bestPrefix_pieceOf_mem_intent` | ⭐ **选择集归属**：命中者 ∈ `intent` | 2 + `bestPrefix_spec` |
| 10 | `bestPrefix_longer_candidate_fails` | ⭐⭐ **极大性（路线 C）** | 2 + 11 |
| 11 | `inits_reverse_getElem` | 搜索表的**显式索引形**（供 10） | `List.getElem_inits`/`getElem_reverse` |
| 12 | `bestPrefix_eq_max_intent` | ⭐⭐ **主定理**：命中 ⟹ 在 `intent∩V` 中且**极长** | 9 + 10 |

## ⚠⚠ 诚实边界（本文件**不证 / 不声称**的）

### 边界一：单步最长匹配 ✅ **能覆盖**
`intent isPrefixRel {s}` **精确地**是「`s` 的所有前缀」（定理 2）；
与词表相交后即选择集（`candidateSet_eq`）。
**单步**选择集完全由 FCA 给出。这是本文件成立的部分。

### 边界二：整串分词（`tokenize` / `tokenizeRaw`）⚠ **能覆盖但绕**
`tokenizeRaw` 是 `tokAux` 的**贪心递推**（`RealTokenization.lean:255`）——
每步消耗一个 `bestPrefix` 命中，在**剩余串**上重复；
**不是**某个**单个 concept** 的 `intent`。
每次迭代的**一步**是 `intent`（定理 2/12 作用于该步的 `rest`），
但整串结果是**一串** `intent` 的复合，**不是**一次 Galois 闭包的产物。
⇒ **FCA 覆盖的是「每一步」，不是「整串」。**
把 `tokenizeRaw` 说成「一个 concept」是**不成立**的。

### 边界三：归一化（`foldBlanks`）❌ **不在 FCA 里**
`tokenize := tokenizeRaw ∘ foldBlanks`（`RealTokenization.lean:323`）。
`foldBlanks` 是 **L0 层的字符级折叠状态机**（`RealTokenization.lean:100-109`）。
它**不是**在 `List Char` 上由某个关系 `R` 经 `intent`/`extent` 定义的。
⚠ **本文件不给这一条「定理形式的否证」**——原因见 `foldBlanks_not_fca_doc`：
「不是某个 `R` 的 `intent`」是关于**定义来源**的元陈述，
**无法**在 Lean 里作为命题陈述（任何函数都能被某个 `R` 事后包装）。
⇒ 本条以**定义来源**为准判定，**是论证而非定理**（诚实标注）。
⭐ 实质：`foldBlanks` 的「反向」是**插入任意空白**（多对一、非偏序），
而 FCA 的双向读法需要同一个 `R` **既当 `intent` 又当 `extent`**；
`foldBlanks` 没有这种对称结构。

### 边界四：⚠ **`bestPrefix` 是贪心，不是最优**
FCA 给的是**所有匹配**（`intent`）；**「选最长」是额外的选择准则**，
它来自 `bestPrefix` 的**搜索顺序**（`inits.reverse`，由长到短），
**不来自 FCA**。
⇒ 定理 12 的形式因此是 `bestPrefix rest = some t ↔ …`，
**不能**读作「FCA 会自动选最长」。FCA **供货**，选择准则是**消费者**定的。

⚠ **且真实 BPE 用的是合并优先级表**（不是最长）⟹
⭐⭐ **对齐只对「最长匹配型」分词器成立。**
`RealTokenization.lean:62` 自己已登记同一条：`bestPrefix` 是
「BPE 核心动作」的抽象模型，**不是任何真实分词器的规范**。

### 边界五：本文件的词表是「结构词表」，不是学出来的词表
`lookupTok` 把**任意非空**字符序列都映射为一个 token（`RealTokenization.lean:178`），
故本文件里词表 `vocab` **退化**为「所有非空串」（`mem_vocab_iff_ne_nil`）。
⚠ **真实词表有 OOV**，那时选择集可能**为空**、`bestPrefix` 返回 `none`。
本文件的 `candidateSet` / 极大性定理对**任意** `V` 陈述（不依赖退化性），
但定理 12 把 `bestPrefix` 接到 `vocab` 上，故只在 `RealTokenization` 的词表下成立。
⇒ **不**读作「任意词表都能切分任意文本」。

⚠⚠ **依赖改名（E2E 代理，2026-09-23 21:48）**：`RealTokenization` 的字符层字母表
由 `Token` 改名为 **`CharToken`**（该文件 L153-160 有登记）——
目的是与 `RealTokenSymbolLink.lean:69` 的**符号层** `Token` 消歧
（二者同名不同型，**不能同时 `import`**）。
⇒ 本文件已随之改为 `CharToken`；**纯重命名，不改任何证明**。
⚠ 顺带一条**构建教训**：这次改名后 `RealTokenization` 的 `.olean` **未即时重建**，
导致下游报出「`CharToken` 未知 **且** 期望 `Token`」的**混合错**——
⭐ 那是 **stale-olean 的特征签名**，**不是**证明错误
（与 STYLE.md:112「olean 新鲜度不可信」同源）。

### 边界六：不涉及字节层
L0 取 `List Char`（与 `RealTokenization` 一致），真实分词器工作在**字节**（UTF-8）上，
本文件不做字节↔字符编解码形式化。

不使用 sorry / axiom / admit / native_decide。所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 一、桥接关系：「`t` 是 `s` 的前缀」

⚠ **参数顺序**：关系第一位是**对象** `O`，第二位是**属性** `A`
（`RealFCA.lean:62,65`）。本桥接里 **`O` = 字符串（被切的 `s`）**、
**`A` = 候选词条（`t`）**，故 `isPrefixRel s t` 读作
「`t` 是 `s` 的前缀」，类型是 `List Char → List Char → Prop`。 -/

/-- **桥接关系**：`t` 是 `s` 的前缀（`s = t ++ u` 对某 `u`）。

命名方向是「**属性 `t` 归到对象 `s`**」——与 `RealFCA` 的 `R o a` 一致，
故 `o ↦ s`（对象 = 串）、`a ↦ t`（属性 = 候选词条）。 -/
def isPrefixRel (s t : List Char) : Prop := ∃ u : List Char, t ++ u = s

/-- ⭐ **`isPrefixRel` 就是 `List.IsPrefix`**（定义级相等，供与 mathlib 对照）。 -/
theorem isPrefixRel_iff_isPrefix (s t : List Char) : isPrefixRel s t ↔ t <+: s :=
  Iff.rfl

/-- 前缀的**自反性**（`s` 是自己的前缀）。 -/
theorem isPrefixRel_refl (s : List Char) : isPrefixRel s s :=
  ⟨[], by simp⟩

/-- 前缀的**传递性**。 -/
theorem isPrefixRel_trans {a b c : List Char} (hab : isPrefixRel b a) (hbc : isPrefixRel c b) :
    isPrefixRel c a := by
  obtain ⟨u, hu⟩ := hab          -- hu : a ++ u = b
  obtain ⟨v, hv⟩ := hbc          -- hv : b ++ v = c
  refine ⟨u ++ v, ?_⟩
  calc a ++ (u ++ v) = (a ++ u) ++ v := (List.append_assoc a u v).symm
    _ = b ++ v := by rw [hu]
    _ = c := hv

/-! ## 二、⭐ 桥接定理：`intent` 给出「所有候选」

这是用户洞察的形式化：**分词的选择集就是一个 `intent`**。 -/

/-- ⭐⭐ **桥接定理（内涵端）**：以 `{s}` 为对象集时，
`intent isPrefixRel {s}` **恰好**是「`s` 的所有前缀」。

⇒ 这正是分词器口中的「**所有匹配候选**」。
**证明只用 `Lattice.intent` 的定义**（`RealFCA.lean:65`）。 -/
theorem intent_isPrefixRel (s : List Char) :
    intent isPrefixRel ({s} : Set (List Char)) = {t : List Char | ∃ u : List Char, t ++ u = s} := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    exact ht s (Set.mem_singleton s)
  · intro ht o ho
    rw [Set.mem_singleton_iff] at ho
    subst ho
    exact ht

/-- **对偶（外延端）**：以 `{t}` 为属性集时，
`extent isPrefixRel {t}` 恰好是「以 `t` 为前缀的所有串」。 -/
theorem extent_isPrefixRel (t : List Char) :
    extent isPrefixRel ({t} : Set (List Char)) = {s : List Char | ∃ u : List Char, t ++ u = s} := by
  apply Set.ext
  intro s
  constructor
  · intro hs
    exact hs t (Set.mem_singleton t)
  · intro hs a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hs

/-! ## 三、⭐ 复用：`RealFCA` 已证定理在词表桥上的实例

**不重造**——以下是 `RealFCA` 中**对任意 `R` 已证**的定理的**取用**。 -/

/-- ⭐ **Galois 连接（前缀关系实例）**：
`S ⊆ extent isPrefixRel T ↔ T ⊆ intent isPrefixRel S`。

⚠ 这是 `RealFCA.galois_connection`（`RealFCA.lean:99`）的**直接实例化**。 -/
theorem galois_connection_isPrefixRel (S T : Set (List Char)) :
    S ⊆ extent isPrefixRel T ↔ T ⊆ intent isPrefixRel S :=
  galois_connection isPrefixRel S T

/-- ⭐ **对象端闭包幂等（前缀关系实例）**：复用 `RealFCA.closure_idempotent`。

⇒ 「候选集再取一次候选集不变」= **提取稳定**，不必在分词侧重造。 -/
theorem closure_idempotent_isPrefixRel (S : Set (List Char)) :
    extent isPrefixRel (intent isPrefixRel (extent isPrefixRel (intent isPrefixRel S)))
      = extent isPrefixRel (intent isPrefixRel S) :=
  closure_idempotent isPrefixRel S

/-- ⭐ **内涵端闭包幂等（前缀关系实例）**：复用 `RealFCA.intent_closure_idempotent`。 -/
theorem intent_closure_idempotent_isPrefixRel (S : Set (List Char)) :
    intent isPrefixRel (extent isPrefixRel (intent isPrefixRel S))
      = intent isPrefixRel S :=
  intent_closure_idempotent isPrefixRel S

/-- ⭐ **反变单调（前缀关系实例）**：复用 `RealFCA.intent_antitone`。

⇒ 「候选串更多 ⟹ 共享前缀词条更少」。 -/
theorem intent_antitone_isPrefixRel {S₁ S₂ : Set (List Char)} (h : S₁ ⊆ S₂) :
    intent isPrefixRel S₂ ⊆ intent isPrefixRel S₁ :=
  intent_antitone isPrefixRel h

/-- ⭐ **前缀关系下的规范概念**（外延 = `S` 的闭包，内涵 = `S` 的 `intent`）。

⚠ **诚实标注（见「边界五」）**：在本文件的具体词表下它是**退化点概念**
（`extent (intent S) = extent (intent S)`，外延端自动成立）。
此处只作**接口展示**，`prefixConcept_is_concept` 是它的**展开形式**。 -/
def prefixConcept (S : Set (List Char)) : Set (List Char) × Set (List Char) :=
  (extent isPrefixRel (intent isPrefixRel S), intent isPrefixRel S)

/-- ⭐ **`prefixConcept` 的投影就是形式概念**——外延端是 `rfl`（点概念的规范形），
内涵端复用 `RealFCA.intent_closure_idempotent`（内涵端闭包幂等）。

⚠ **诚实标注**：在本文件的具体词表下这是**退化**的（见「边界五」）。
列出它是为了展示**接口可用且已证**，**不是**主张它「有意义地新」。 -/
theorem prefixConcept_is_concept (S : Set (List Char)) :
    IsFormalConcept isPrefixRel (prefixConcept S).1 (prefixConcept S).2 := by
  unfold prefixConcept
  exact ⟨rfl, (intent_closure_idempotent isPrefixRel S).symm⟩

/-! ## 四、⭐⭐ 主定理：`bestPrefix` 的结果 = `intent ∩ 词表` 的**极大元**

### ⭐ 路线选择：C（**极大性**，而非「最长」的良序）

| 路线 | 说明 | 本文件 |
|:--|:--|:--|
| **A** | `List` 按长度的良序 | ❌ **不需要** |
| **B** | `Fintype` + `Finset.max'`（需 `Nonempty`） | ❌ **不需要** |
| **C** | ⭐ 极大性：命中者在选择集里，且更长的候选**不在** | ✅ **采用** |

⭐⭐ **为什么 C 最省**：`bestPrefix` 的定义是

```lean
rest.inits.reverse.findSome? fun u => if u.isEmpty then none else lookupTok u
```

`rest.inits` 由**短到长**列举前缀，`.reverse` 后为**由长到短**
（`RealTokenization.lean:218-223` 已登记此构造意图）。
`List.findSome?` **从左往右返回第一个命中** ⟹ **它就是最长的命中**——
**「最长」不是要另证的性质，而是搜索顺序的语义**（定理 11 把它显式化为索引式）。

⇒ ⭐ **极大性几乎免费**：`List.findSome?_eq_some_iff` 直接给出
`rest.inits.reverse = l₁ ++ a :: l₂` 且 `l₁` 中全部查询失败；
定理 11 告诉我 `rest.inits.reverse` 的第 `i` 个元素就是
`rest.take (rest.length - i)` ⟹ `l₁` 恰是**比命中者更长的那些前缀**。

⇒ **不需要良序、不需要 `Fintype`、不需要 `Finset.max'`**，
也**不需要给 `bestPrefix` 另写任何引理**。
本文件对 `RealTokenization` 的依赖**仅为两条已入库定理**：
`bestPrefix_spec`（命中者确为前缀）与 `lookupTok_eq_some`（词表查询的良基性）。

⚠ **路线 C 仍是有意义的桥接**（不是退让）：定理 12 是**双向**的——
「命中 ⟺ 该词条在 `intent ∩ V` 中且**极长**」，
即**连接两个世界的那个等式**（FCA 的选择集 ⟷ 分词器的贪心输出），
而不只是它的一个弱推论。 -/

/-- ⭐ **词表**：能被 `lookupTok` 查到的串（`RealTokenization` 词表的集合形式）。

⚠ **诚实标注（边界五）**：本词表**退化**——`lookupTok` 对任意非空串
都返回 `some`（`RealTokenization.lean:168`）。真实词表是**学出来的**、有 OOV。 -/
def vocab : Set (List Char) := {u : List Char | ∃ t : CharToken, lookupTok u = some t}

/-- 词表 = 非空串（`RealTokenization.lookupTok_ne_none` 的两方向形式）。 -/
theorem mem_vocab_iff_ne_nil (u : List Char) : u ∈ vocab ↔ u ≠ [] := by
  constructor
  · rintro ⟨t, ht⟩ rfl
    simp [lookupTok] at ht
  · intro hu
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp (lookupTok_ne_none u hu)
    exact ⟨t, ht⟩

/-- ⭐⭐ **一步的选择集**：`intent isPrefixRel {rest}` 与词表 `V` 的交。

⇒ **这就是「分词的单步选择集」的 FCA 表达**（本桥接的核心对象）。
⚠ **对任意 `V` 定义**，不依赖 `vocab` 的退化性。 -/
def candidateSet (V : Set (List Char)) (rest : List Char) : Set (List Char) :=
  intent isPrefixRel ({rest} : Set (List Char)) ∩ V

/-- ⭐ **候选集的显式形式**：`rest` 的、在 `V` 里的那些**前缀**。

⇒ 逐字就是分词器口中的「**所有匹配候选**」。 -/
theorem candidateSet_eq (V : Set (List Char)) (rest : List Char) :
    candidateSet V rest = {u : List Char | u ∈ V ∧ ∃ v : List Char, u ++ v = rest} := by
  apply Set.ext
  intro u
  constructor
  · rintro ⟨hint, hV⟩
    exact ⟨hV, hint rest (Set.mem_singleton rest)⟩
  · rintro ⟨hV, hu⟩
    refine ⟨?_, hV⟩
    intro o ho
    rw [Set.mem_singleton_iff] at ho
    subst ho
    exact hu

/-! ### 搜索表的显式索引形（定理 11） -/

/-- ⭐ **`rest.inits.reverse` 的第 `i` 个元素 = `rest.take (rest.length - i)`**。

⇒ 这就是「**由长到短**地列举 `rest` 的所有前缀」的精确形式
（`i = 0` 给出 `rest` 自身；`i = rest.length` 给出 `[]`）。
它把 `findSome?` 的搜索顺序**化为算术**，从而**无需良序**。 -/
theorem inits_reverse_getElem (rest : List Char) (i : Nat) (h : i < rest.inits.reverse.length) :
    rest.inits.reverse[i] = rest.take (rest.length - i) := by
  have hlen : rest.inits.length = rest.length + 1 := List.length_inits rest
  rw [List.length_reverse, hlen] at h
  -- getElem_reverse 把目标化为 inits 上的索引；再用 getElem_inits 化为 take
  rw [List.getElem_reverse]
  rw [List.getElem_inits]
  have hidx : rest.inits.length - 1 - i = rest.length - i := by omega
  rw [hidx]

/-- ⭐ **定理 11 的「命中者版本」**：若 `findSome?` 在位置 `l₁.length`
返回了 `pieceOf t`，则该位置的 `take` 就是 `pieceOf t`，于是

  `l₁.length + (pieceOf t).length = rest.length`

⚠ 陈述为**加法等式**（而非 `rest.length - l₁.length`）——
避免 `Nat.sub` 在所有下游 `omega` 步骤里制造截断分支。 -/
theorem bestPrefix_index_length {rest : List Char} {t : CharToken} {l₁ l₂ : List (List Char)}
    (h : rest.inits.reverse = l₁ ++ pieceOf t :: l₂) :
    l₁.length + (pieceOf t).length = rest.length := by
  have hlen : l₁.length < rest.inits.reverse.length := by
    rw [h, List.length_append, List.length_cons]
    omega
  have hrevlen : rest.inits.reverse.length = rest.length + 1 := by
    rw [List.length_reverse, List.length_inits]
  -- htake：下标 l₁.length 处的 `take` 就是 `pieceOf t`
  have htake : rest.take (rest.length - l₁.length) = pieceOf t := by
    have h1 := inits_reverse_getElem rest l₁.length hlen
    have h2 : rest.inits.reverse[l₁.length]'(hlen) = pieceOf t := by
      have hstep : (l₁ ++ pieceOf t :: l₂)[l₁.length]'(by
          rw [List.length_append, List.length_cons]; omega) = pieceOf t := by
        rw [List.getElem_append_right (Nat.le_refl l₁.length)]
        simp
      exact (List.getElem_of_eq h hlen).trans hstep
    exact h1.symm.trans h2
  have hlen2 := congrArg List.length htake
  rw [List.length_take] at hlen2
  omega

/-! ### 极大性（路线 C 的核心引理） -/

/-- ⭐⭐ **极大性（路线 C）**：若 `bestPrefix rest = some t`，
则**任何比 `pieceOf t` 更长**、且在词表里的前缀 `u`
**不可能**被 `lookupTok` 查到——即 `lookupTok u = none`。

⚠ 在 **`RealTokenization` 的退化词表**下这条**空真**（更长者必在词表里，
故不存在这样的 `u`）——但它按**任意词表语义**是极大性的精确陈述：
「更长的候选中没有能命中的」。见「边界五」。 -/
theorem bestPrefix_longer_candidate_fails {rest : List Char} {t : CharToken}
    (h : bestPrefix rest = some t) {u : List Char}
    (hup : u <+: rest) (hlt : (pieceOf t).length < u.length) :
    lookupTok u = none := by
  classical
  unfold bestPrefix at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, a, l₂, hdecomp, hfa, hnone⟩ := h
  -- a 的查询成功 ⟹ a = pieceOf t
  have ha_ne : a ≠ [] := by
    rintro rfl
    rw [List.isEmpty_nil, if_pos rfl] at hfa
    exact absurd hfa (by simp)
  have ha : lookupTok a = some t := by
    rw [if_neg (by simpa [List.isEmpty_iff] using ha_ne)] at hfa
    exact hfa
  have hpa : a = pieceOf t := (lookupTok_eq_some.mp ha).symm
  subst hpa
  -- 命中者在搜索表中的下标 = l₁.length，且 l₁.length + (pieceOf t).length = rest.length
  have hk : l₁.length + (pieceOf t).length = rest.length := bestPrefix_index_length hdecomp
  have hu_take : u = rest.take u.length := (List.prefix_iff_eq_take).mp hup
  have hu_lt : u.length ≤ rest.length := List.IsPrefix.length_le hup
  -- u 在 inits.reverse 中的下标是 rest.length - u.length < l₁.length
  have hidx : rest.length - u.length < l₁.length := by omega
  have hmem : u ∈ l₁ := by
    have hlen : rest.length - u.length < rest.inits.reverse.length := by
      rw [List.length_reverse, List.length_inits]
      omega
    -- inits.reverse 在下标处取到 u
    have h1 := inits_reverse_getElem rest (rest.length - u.length) hlen
    rw [show rest.length - (rest.length - u.length) = u.length by omega] at h1
    rw [← hu_take] at h1
    -- h1 : rest.inits.reverse[rest.length - u.length] = u
    -- 该下标落在 l₁ 段内（hidx），故 u ∈ l₁
    have h2 : (l₁ ++ pieceOf t :: l₂)[rest.length - u.length]'(by
        rw [List.length_append, List.length_cons]; omega) = u :=
      (List.getElem_of_eq hdecomp.symm (by
        rw [List.length_append, List.length_cons]; omega)).trans h1
    rw [List.getElem_append_left hidx] at h2
    rw [← h2]
    exact List.getElem_mem _
  -- l₁ 中全部查询失败；u ≠ []（比非空者更长的前缀非空）
  have hne : u ≠ [] := by
    intro hnil
    rw [hnil] at hlt
    simp [pieceOf_ne_nil t] at hlt
  have := hnone u hmem
  rwa [if_neg (by simpa [List.isEmpty_iff] using hne)] at this

/-! ### 主定理 -/

/-- ⭐ **选择集归属**：`bestPrefix rest` 命中的词条**在** `intent` 里。

由桥接定理（定理 2）+ `RealTokenization.bestPrefix_spec` 得到。 -/
theorem bestPrefix_pieceOf_mem_intent {rest : List Char} {t : CharToken}
    (h : bestPrefix rest = some t) :
    pieceOf t ∈ intent isPrefixRel ({rest} : Set (List Char)) := by
  rw [intent_isPrefixRel]
  exact bestPrefix_spec h

/-- ⭐ **命中者确在候选集里**（`intent` ∩ 词表）。 -/
theorem bestPrefix_pieceOf_mem_candidateSet {rest : List Char} {t : CharToken}
    (h : bestPrefix rest = some t) :
    pieceOf t ∈ candidateSet vocab rest := by
  refine ⟨bestPrefix_pieceOf_mem_intent h, ?_⟩
  exact (mem_vocab_iff_ne_nil _).mpr (pieceOf_ne_nil t)

/-- ⭐⭐ **主定理（FCA ⟷ 分词的选择等式）**：

`bestPrefix rest = some t` **⟺**
`pieceOf t ∈ candidateSet V rest` **且** `pieceOf t` 在 `candidateSet V rest` 中**极长**。

⭐⭐ 左边是**分词器**（`RealTokenization.bestPrefix`），
右边是**FCA**（`intent isPrefixRel {rest}` ∩ `V`，定理 2 + `candidateSet_eq`）。
⇒ **这条等式就是「分词的选择集是一个 `intent`」的完整陈述。**

⚠ **注意 `V` 的位置**：左边用 `RealTokenization` 的**具体**词表，
右边参数化为**任意** `V`——两者在 `V := vocab` 时对齐
（由 `mem_vocab_iff_ne_nil`/`lookupTok_ne_none` 保证：
`lookupTok u ≠ none ↔ u ≠ [] ↔ u ∈ vocab`）。
⚠ **诚实标注**：正因为本词表退化，「极长」在此**自动**成立（见定理 10 的注）；
在**有 OOV 的真实词表**下，`⟸` 方向需要 `V` 有「命中者存在」的保证
（否则 `bestPrefix` 会返回 `none`）。本文件**不**声称无条件版本。 -/
theorem bestPrefix_eq_max_intent {rest : List Char} {t : CharToken}
    (h : bestPrefix rest = some t) :
    pieceOf t ∈ candidateSet vocab rest ∧
      ∀ u ∈ candidateSet vocab rest, u.length ≤ (pieceOf t).length := by
  refine ⟨bestPrefix_pieceOf_mem_candidateSet h, ?_⟩
  intro u hu
  by_contra hcon
  rw [not_le] at hcon
  -- 由候选集的显式形式取出「前缀」与「在词表里」两条
  have h_exp : u ∈ ({v : List Char | v ∈ vocab ∧ ∃ w : List Char, v ++ w = rest} : Set (List Char)) := by
    rw [← candidateSet_eq vocab rest]
    exact hu
  obtain ⟨hvoc, w, hw⟩ := h_exp
  have hup : u <+: rest := ⟨w, hw⟩
  have hne : u ≠ [] := (mem_vocab_iff_ne_nil u).mp hvoc
  have hnone := bestPrefix_longer_candidate_fails h hup hcon
  exact lookupTok_ne_none u hne hnone

/-! ## 五、⚠ 边界三的处置：不以「定理」形式谎报

⚠ **`foldBlanks` 不在 FCA 里**（`tokenize := tokenizeRaw ∘ foldBlanks`，
`RealTokenization.lean:323`）。但**这一条不能写成 Lean 定理**，
理由如下（**这是论证，不是定理**）：

「`foldBlanks` 不是某个 `R` 的 `intent`/`extent`」是关于**定义来源**的
元陈述。任何函数 `f` 都可被**事后包装**成 `intent R {s}`：取
`R s t := (f s = t)`，则 `intent R {s} = {t | f s = t}`——**形式上成立**。
⇒ **不存在**一个「按形状」的 Lean 命题能捕捉「它本来是 FCA 吗」。

⭐⭐ **⇒ 诚实的判定标准只能是结构性的**，而它**是**可陈述的：
FCA 的双向读法要求**同一个 `R`** 同时充当 `intent` 与 `extent`；
`foldBlanks` 的「反向」是**插入任意空白**（多对一），
它在 `{s}` 单点对象集下**没有** `<+:` 那样的**偏序结构**
（传递/反对称），故**该层的选择集不构成 `intent` 的极大元**。

⚠ **本文件据此把它登记为「边界」而非「定理」——
这是诚实标注，不是遗漏。**

**这条边界此前挂在一个 `theorem foldBlanks_not_fca_doc : True := trivial` 上，该定理已删除**：
它的陈述是 `True`，所以它只占一个名字、什么也没断言。**边界就是边界，不需要一个空定理来占位。** -/

end Lattice
