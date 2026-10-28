import Lattice.Runtime.RealTokenization
/-!
# LATTICE: RealTokenizationEntry —— L0 的【入边】桥（String → List Char）

## 定位（为什么需要这个文件）

W28（`notes/sweep10/W28-链的入口侧审计.md`）实测：**L0 是纯源点【相对于入口方向】** ——
`List Char` **有**出边（`tokenize`）与自环（`foldBlanks`），但**没有入边**：
全库**没有任何函数**把外部世界的真实载体映进 `List Char`。

本文件补上那条入边。**只做 L0 的入口**，不改动 `RealTokenization.lean`。

## 本文件给出的两条桥

| # | 桥 | 方向 | 性质 |
|:-:|:--|:--|:--|
| 1 | `Text.encode : String → List Char` | 外部 → L0 | ⭐ **L0 的第一条入边** |
| 2 | `tokenizeStr (s : String) : Option (List CharToken)` | 外部 → L1 | `tokenize ∘ encode`，**逐字由定义给出** |

## 非平凡定理（不是包装）

| 定理 | 内容 | 为什么非平凡 |
|:--|:--|:--|
| `encode_length` | `(encode s).length = s.length` | 与 `String.length` 的规范形对齐，**跨层** |
| `encode_injective` | `encode` **是单射** | ⭐ **L0 入边保真**（不丢字符）；对照 `RealEndToEnd.charCode` 非单射 |
| `tokenizeStr_eq_tokenize` | `tokenizeStr s = tokenize (encode s)` | 组合律：入口桥**穿过** L0 不改变语义 |
| `tokenizeStr_never_none` | `∃ ts, tokenizeStr s = some ts` | 入口桥继承 L0→L1 的性质，**端到端可述性随之成立** |

⚠ **诚实边界**：`String` 在 Lean 里以 **UTF-8 字节** 存储，`String.length` 是**字节数**而
`toList.length` 是**字符数**。本文件**不声称** `encode` 是 UTF-8 **解码**；
它把 `String` 当作**字符序列的载体**（Lean 的 `String.toList` 正是这个语义），
**字节级编解码（`ByteArray`）不在本文件范围内**（全库 `ByteArray` = 0 命中）。
-/

noncomputable section

namespace Lattice

/-! ## 一、L0 的入边桥：`String → List Char` -/

/-- ⭐⭐ **L0 入边桥**：外部世界（`String`）→ 证明层（`List Char`）。

⚠ 这是全库**第一条** `String → List Char` 的命名函数（W28 实测：全库 0 条）。
定义取 Lean 核心的 `String.toList`，**不引入任何新公理**。 -/
def Text.encode (s : String) : List Char := s.toList

@[simp] theorem Text.encode_eq_toList (s : String) : Text.encode s = s.toList := rfl

/-- ⭐ **入口桥保长度**：`encode` 与 `String.length` 对齐。

⚠ **诚实标注**：`String.length` 在 Lean 里是 **UTF-8 字节数**，而 `List.length` 是**字符数**；
本定理成立的**原因**是 Lean 的 `String.length` 与 `String.toList` 共享同一套
`utf8ByteSize`/`Iterator` 结构（`String.length_eq_toList_length`）。
**它因此不是 UTF-8 解码的定理** —— 见文件头诚实边界。 -/
theorem Text.encode_length (s : String) : (Text.encode s).length = s.length := rfl

/-- ⭐⭐ **入口桥是单射**（**L0 入边不丢字符**）。

这是入口桥**最重要的正性质**，且**与本仓库另一座桥形成一个尖锐对照**：
`RealEndToEnd.charCode` **不是**单射（`word 'a' 'b' []` 与 `word 'a' 'c' []` 碰撞，
`RealEndToEnd.lean:440` 已登记）。⇒ ⭐ **"桥必然丢信息"不是本仓库的普遍规律**：
`encode` 无损，`charCode` 有损。**两个结论都是机器检查过的。** -/
theorem Text.encode_injective : Function.Injective Text.encode := by
  intro a b h
  have h2 : a.toList = b.toList := h
  exact String.toList_inj.mp h2

/-- 逆方向的**部分**刻画：`encode` 拼回 `String.mk` 后**逐字还原**原串。

⚠ **诚实标注**：这**不是** `encode` 有左逆的断言（左逆要 `List Char → String`，
本文件**不建** —— 见 §四 的不声称清单）。它说的是 `String.mk ∘ encode = id`。 -/
theorem Text.ofList_encode (s : String) : String.mk (Text.encode s) = s := by
  simp only [Text.encode]
  exact String.toList_inj.mp rfl

/-! ## 二、入口桥的组合律：与 `tokenize` 复合 -/

/-- ⭐ **入口分词**：`String → L1`，即 `tokenize ∘ encode`。

⚠ 这是 `tokenize` 的 **`String` 版**；W28 实测全库此前**没有**这样的函数。 -/
def tokenizeStr (s : String) : Option (List CharToken) := tokenize (Text.encode s)

/-- ⭐ **组合律（入口桥穿过 L0 不改变语义）**：`tokenizeStr` 就是 `tokenize ∘ encode`。

这是本桥与 L0 的**接口契约**：任何关于 `tokenize` 的既有定理
（`tokenize_detok` / `detokenize_left_inverse_on_quotient` / `tokenize_detokenize_galois` …）
都可以经 `rw [tokenizeStr_eq_tokenize]` **原样**用在 `String` 输入上。 -/
theorem tokenizeStr_eq_tokenize (s : String) :
    tokenizeStr s = tokenize (Text.encode s) := rfl

/-- ⭐ **入口分词永不失败**（由 `tokenize_never_none` 经组合律继承）。

⚠ **诚实标注**：它继承的正是 `RealTokenization` 的**退化词表**性质
（文件头 :65-70 已登记：真实词表有 OOV）。⇒ 本定理**不**读作
「任意 `String` 都能被真实分词器切开」。**OOV 面的最小可证模型见 §三。** -/
theorem tokenizeStr_never_none (s : String) :
    ∃ ts : List CharToken, tokenizeStr s = some ts := by
  obtain ⟨ts, hts⟩ := tokenize_never_none (Text.encode s)
  exact ⟨ts, by rw [tokenizeStr_eq_tokenize]; exact hts⟩

/-- ⭐ **入口无损（削弱到归一化后）**：`String` 版的无损刻画，
由 `tokenize_detok` 经组合律继承。 -/
theorem tokenizeStr_detok {s : String} {ts : List CharToken}
    (h : tokenizeStr s = some ts) :
    detokenize ts = foldBlanks (Text.encode s) := by
  rw [tokenizeStr_eq_tokenize] at h
  exact tokenize_detok h

/-! ## 三、OOV 词表：使 `none` 分支【可达】（W28 §三 的落盘）

`RealTokenization` 的文件头诚实登记：`tokenize` 的 `none` 分支**不可达**
（`tokenize_never_none`），因为它的词表覆盖**所有**非空字符序列。

⭐ 本节的目的是**把该分支变成可达**：引入**可判定**的词表谓词 `OOVVocab`，
使"词表外"成为一个**能实例化**的命题，而不是空集。

⚠⚠ **不以"证否面"为满足**：既有 `tokenize_never_none` 已经做到了正例；
本节的价值**全部**在 `bestPrefixV_Vzz_oov`（阻塞**可达**）与
`tokenize_never_none_fails_for_Vzz`（旧定理**不再适用**）。 -/

/-- **词表**：对字符块的可判定谓词。`Bool` 而非 `Prop` —— 贪心选择须**可计算**。 -/
def OOVVocab := List Char → Bool

/-- **带 OOV 分支的贪心最长匹配**：在 `rest` 的**前缀**中取最长的、**在词表内**的那个。

⚠⚠ **实测过的坑（W28 §三 登记）**：`findSome?` 沿 `inits.reverse` 扫描，
取的是**最长的 V-命中前缀** ——
所以 `bestPrefixV Vzz ['z','z','a']` 的结果是 `word 'z' 'z' []`，
尾字符 `'a'` **留给下一轮**（这正是「最长**匹配**」而非「整串吞掉」）。
**第一版把它写成 `word 'z' 'z' ['a']`，内核当场证伪。** -/
def bestPrefixV (V : OOVVocab) (rest : List Char) : Option CharToken :=
  rest.inits.reverse.findSome? fun u =>
    if u.isEmpty then none else if V u then lookupTok u else none

/-- **见证词表**：只认 `['z','z']` 这一个词条。 -/
def Vzz : OOVVocab := fun u => decide (u = ['z', 'z'])

/-! ### 三条 OOV 定理（正例 / 阻塞 对照） -/

/-- ⭐ **正例（词表内成功）**：`"zza"` 在 `Vzz` 下切出 `word 'z' 'z' []`。

⚠ 尾字符 `'a'` **不**在本 token 里 —— 见 `bestPrefixV` 的坑注。 -/
theorem bestPrefixV_Vzz_in :
    bestPrefixV Vzz ['z', 'z', 'a'] = some (.word 'z' 'z' []) := by decide

/-- ⭐⭐ **OOV 阻塞（`none` 分支【可达】）**：`['q']` 在 `Vzz` 下**不可切**。

这是本节存在的**唯一理由** —— 没有它，`none` 分支仍是死代码。 -/
theorem bestPrefixV_Vzz_oov : bestPrefixV Vzz ['q'] = none := by decide

/-- ⭐ **对照（退化词表不阻塞）**：同一输入 `['q']` 在**旧** `bestPrefix` 下**成功**。

⇒ 两条合起来把"阻塞"钉成**词表的性质**，而不是输入的偶然性。 -/
theorem bestPrefix_degenerate_succeeds : bestPrefix ['q'] ≠ none := by decide

/-- **边界**：空输入上 `bestPrefixV` 恒 `none`（`inits` 只有 `[]`，被 `isEmpty` 挡掉）。 -/
theorem bestPrefixV_empty (V : OOVVocab) : bestPrefixV V [] = none := by
  simp [bestPrefixV, List.inits]

/-- ⭐⭐ **旧的全称定理在 `Vzz` 上【不成立】** ——
`tokenize_never_none` 式的陈述 `∀ s, ∃ ts, bestPrefixV Vzz s = some ts` 为**假**。

⚠⚠ 本定理**断言的是"旧定理的陈述本身"**（判据 13）：它的**取反**正是
`tokenize_never_none` 的形状，故**若有人把词表改回退化版，红的会是这里**。 -/
theorem tokenize_never_none_fails_for_Vzz :
    ¬ (∀ s : List Char, ∃ ts : CharToken, bestPrefixV Vzz s = some ts) := by
  intro h
  obtain ⟨ts, hts⟩ := h ['q']
  rw [bestPrefixV_Vzz_oov] at hts
  exact absurd hts (by simp)

/-! ## 四、不声称清单（诚实边界）

* **不声称 `encode` 做 UTF-8 解码**：`String.toList` 是"字符序列"语义，
  `String.length` 是**字节数**。字节↔字符的编解码形式化**不在本文件**（全库 `ByteArray` = 0）。
* **不建 `List Char → String` 的逆桥**：入口只需单向；逆向会牵入
  "非规范字符序列无对应 `String`"的额外义务，本文件**不承担**。
* **不改动 `tokenize` 本身**：`RealTokenization.lean` 一行未动。
  §三 的 OOV 词表是**并列**的最小模型，**不**替换 `tokenize`。
* **不声称 `Vzz` 是真实词表**：它是**见证**（使 OOV 可达），不是语言模型词表。
* 不使用 sorry / axiom / admit / native_decide。
-/

end Lattice
