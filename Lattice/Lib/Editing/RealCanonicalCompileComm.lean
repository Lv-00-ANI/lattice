import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealCanonicalForm
import Lattice.Runtime.ExtractionClosure
/-!
# LATTICE: 规范形与编译的「交换律」（缺口 B）—— 陈述的诊断与判定

## 0. 本文件回答什么

任务（v13/w13 波次，8 号）：**`canonicalize_compile_comm`（交换律，缺口 B）**。
`RealCanonicalForm` 的实现说明已诚实登记该欠缺，并指出真正的障碍：

> 「`compile` 作用在**权重侧**（`LinearLayer`）、`canonicalize` 作用在**符号侧**
> （`VectorConstraint`）—— 两者的定义域不同，**陈述本身需要先定义『编译后再规范化』的路径**。」

⭐ **本文件的第一项交付就是那句"先定义路径"**，并且给出一个**否定性的诊断**：

> ⚠⚠ **经由权重侧的往返【不是】缺口 B 的障碍所在** ——
> 因为 `extractVec ∘ convertVec = id` 是 **`rfl` 级**的（两侧都只是 record 字段重命名），
> 故 `canonicalize ∘ extract ∘ compile` **定义上就等于** `canonicalize`：
> **它不携带任何关于"权重侧"的信息**（§二）。

⇒ ⭐ **真正的、非空洞的交换律必须【不经过权重侧】**，而是问
`canonicalize` 与**缩放**（`scaleVec`）何时交换（§三–§五）。

## 1. 本文件建立什么（内核已验，`Built` + exit 0）

| # | 项 | 位置 | 判定 |
|--:|:--|:--|:--|
| 1 | ⚠ **`compileThenCanonicalize`** | §二 | **恒等于 `canonicalize`（`rfl`）—— 空洞** |
| 2 | ⚠ **`canonicalizeThenCompile`** | §二 | `= convertVec ∘ canonicalize` |
| 3 | ⭐ **两条路径确实交换**（经 `extractVec` 对齐后） | §二 | ✅ **恒等成立**（但**因第 1 条而空洞**） |
| 4 | ⭐⭐ **`canonicalize_absorbs_scale_pos`** | §三 | ✅ **`0 < lam` 时 `canonicalize` 吞掉倍率** |
| 5 | ⭐⭐ **`canonicalize_scaleVec_sign_law`** | §三 | ✅ **一般倍率的精确律**（差一个 `sign`） |
| 6 | ⭐⭐⭐ **`canonicalize_comm_scaleVec_iff`** | §三 | ✅ **充要条件：交换 ⟺ `lam = ±1`** |
| 7 | ⭐⭐⭐ **`canonicalize_compile_comm_fails`** | §四 | ❌ **为假**（**内核反例**，`lam = -2`） |

## 2. ⚠⚠ 关键诊断：为什么"经权重侧的交换律"是【空洞】的（§二）

`ConvertVectorLinear.convertVec` 与 `WeightToSymbolEquivalence.extractVec`
**都只是 record 字段重命名**（`a ↦ w`、`w ↦ a`；`b` 两侧同名）：

```
convertVec {a := A, b := B} = {w := A, b := B}
extractVec {w := W, b := B} = {a := W, b := B}
⟹ extractVec (convertVec c) = c     （rfl，非定理）
```

⇒ ⭐ **后果**：对**任何** `f : VectorConstraint → VectorConstraint`，
"先编译、再规范化"这条路径 **定义上**就是 `f` 本身：

> `canonicalize (extract (compile c)) ≡ canonicalize c`（**`rfl`**）

⚠ **故 `canonicalize_compile_comm` 若陈述为"经权重侧往返后交换"，它是一条
`rfl` 级恒等式** —— **真，但空洞**（不"承重"）。
要点 **这与 `closed_loop_adds_nothing`（`RealCompileExtractClosed.lean` 中该定理处，
历史记录曾写作 `:204`，实为漂移行号，已订正）
是同一现象的第三次出现**：权重侧往返**不携带新语义**。

⇒ 要点 **本文件的处置**：**如实登记这一空洞性**（`compileThenCanonicalize_eq_canonicalize`
是 `rfl`），并把"交换律"的**真正内容**移到**不经过权重侧**的陈述上（§三）。
**这回答了作者说"陈述还不存在"的那个问题：陈述存在，但经由权重侧的那个版本没有内容。**

## 3. 要点 真正的交换律：`canonicalize` 与 `scaleVec`（§三–§五）

`RealCanonicalForm` 已证两条**互相独立**的事实：
- `canonicalize_section_pos`：`0 < lam` 时 `canonicalize (scaleVec c lam) = canonicalize c`；
- `canonicalize_scaleVec_sign`：一般 `lam ≠ 0` 时差一个 `sign lam`。

注意 **但"交换"（commutation）是【另一条】陈述**：
它问的是**两条不同的复合路径是否给出同一结果**，即

```
路径 ①  canonicalize ∘ scaleVec c lam
路径 ②  scaleVec (canonicalize c) lam        ← 注意：不是 sign lam
```

要点 **本文件证明**：**这两条路径【不】交换**，而**差一个 `sign lam`**（§四 内核反例）：

> `canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (sign lam)`
> ⇒ **`= scaleVec (canonicalize c) lam` 当且仅当 `sign lam = lam`**，
> 即 **`lam = 1` 或 `lam = -1`**（**仅在两个点上成立**）。

⇒ 要点 **精确结论（这就是缺口 B 的判定）**：
**交换律在 `lam = ±1` 这两点上成立，在一般 `lam ≠ 0` 上为假**（§四，内核反例）。
注意 **特别注意：`0 < lam` 并不足以救活交换律**（`lam = 3` 即反例）——
**初稿在此处曾错写为"正倍率下成立"，已撤下并如实登记**（见 §六 表下说明）。
要点 **`lam > 0` 时【为真】的是另一条陈述**：`canonicalize` **吞掉**倍率
（`canonicalize (scaleVec c lam) = canonicalize c`，即 `canonicalize_absorbs_scale_pos`）——
**它的 RHS 不含 `scaleVec`**，与交换律是**两条不同的陈述**。
**根因**：`content (scaleVec c lam) = content c * |lam|`（**分母取 `natAbs`**）
而**分子带符号**——这正是 `RealCanonicalForm` §1.6 已登记的算术根源。

## 4. 与既有否定结论的一致性检查（任务第 3 步要求）

注意 **本文件【不】与三条已登记否定结论冲突**，逐条核对：

| 既有否定结论 | 本文件的关系 |
|:--|:--|
| `closed_loop_adds_nothing` | 要点 **强化**：本文件给出它在这条链路上的**第三次**实例（`rfl` 级） |
| `no_extractor_preserves_both` | 成立 **一致**：该条说参数层可逆 ∧ 语义层不可逆；本文件 §四 的反例**正是**语义层不可逆在规范形上的读数 |
| `validity_does_not_determine_syntax` | 成立 **一致且复用**：本文件 §四 的见证 `{[2],2}` 与 `{[-2],-2}` 语义等价、语法不等 |

注意 **关键检查（任务明确要求）**：本文件的**交换律为假**这一结论，
**是否蕴含上述某条的【反面】**？**答案：不蕴含，且方向一致** ——
交换律为假**恰恰是** `no_extractor_preserves_both` 所断言的"语义层不可逆"的**另一种表述**。
⇒ 要点 **故不存在"证一个已被证伪的东西"的风险**；反而**二者互为佐证**。

注意 **且必须登记一条边界**：本文件**不**声称"缺口 B 不可能闭合"。
本文件只证：**经由权重侧的交换律空洞**、**与 `scaleVec` 的裸交换律为假**。
要点 **"在商掉 `±1` 之后交换律成立"仍在（`canonicalize_scaleVec_sign` 已给），
即缺口 B 的【正确定位】是"模 `±1` 的商上"，而不是"任意倍率上"**（§六）。

**诚实边界**（本文件不证 / 不声称的）：
- 注意 **不声称"缺口 B 不可能闭合"**：只在**已定义的路径**上判定（§六 给出正确定位）。
- 注意 **不构造"模 `±1` 的商"这个对象本身**（需要 `Quotient` 上的新 Setoid；
  `ScaleClass` **不含** `±1` 商，见 §六"未做"）。
- 注意 **不声称 `canonicalize` 与"激活折入"交换**（那是 `activated_loop_breaks` 的地盘，已证为假）。
- 注意 **不修改 `RealCanonicalForm.lean`**（已入库稳定成果）：本文件**只读引用**其定理。
- 无 `sorry` / `axiom` / `admit` / `native_decide`；全部定理内核可验证。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、两侧的定义域（"先定义路径"这一步的**类型级**依据）

| 映射 | 源 | 靶 | 定义位置 |
|:--|:--|:--|:--|
| `canonicalize` | `VectorConstraint`（**符号侧**） | `VectorConstraint` | `RealCanonicalForm.lean` §四 |
| `convertVec`（`compile`） | `VectorConstraint`（**符号侧**） | `LinearLayer`（**权重侧**） | `ConvertVectorLinear.lean`（`def convertVec` 处） |
| `extractVec` | `LinearLayer`（**权重侧**） | `VectorConstraint`（**符号侧**） | `WeightToSymbolEquivalence.lean`（`def extractVec` 处） |

要点 **⇒ `canonicalize ∘ compile` 在类型上不成立**（`canonicalize` 要 `VectorConstraint`，
而 `compile` 给 `LinearLayer`）—— **这正是作者所指的障碍**，且**必须**经 `extractVec` 中介。
要点 **但本文件 §二 证明：这个中介是【恒等】的，故该路径没有信息。** -/

/-- **提取-往返（`rfl` 级）**：`extractVec (convertVec c) = c`。

注意 **`WeightToSymbolEquivalence.roundtrip_extractVec` 已证此式**（其证明体是 `cases c <;> rfl`）；
要点 **本文件在此显式登记它的【定义性】**（区别于"需要证明"的定理）——
因为**这是 §二 空洞性诊断的全部依据**。 -/
theorem extractVec_convertVec_rfl (c : VectorConstraint) : extractVec (convertVec c) = c := Lattice.roundtrip_extractVec c

/-- **编译-往返（`rfl` 级）**：`convertVec (extractVec l) = l`（结构 eta）。

注意 **两侧都只是字段重命名** ⟹ 往返在两个方向上**都是**定义恒等，
故权重侧与符号侧在**对象层**上是**同一个记录类型换了字段名**。 -/
theorem convertVec_extractVec_rfl (l : LinearLayer) : convertVec (extractVec l) = l := by
  exact Lattice.Runtime.ExtractionClosure.reinject_roundtrip l

/-! ## 二、注意 两条路径：定义 + 空洞性诊断（本文件的第一项交付） -/

/-- 要点 **路径 ①（编译后再规范化）**：`canonicalize (extractVec (convertVec c))`。

要点 **这是任务书建议的定义**，且它**是类型正确的**（经 `extractVec` 中介）。
注意 但见下条：它**定义上**等于 `canonicalize c`。 -/
def compileThenCanonicalize (c : VectorConstraint) : VectorConstraint :=
  canonicalize (extractVec (convertVec c))

/-- 要点 **路径 ②（规范化后再编译）**：`convertVec (canonicalize c)`。

要点 它落在**权重侧**（`LinearLayer`），与路径 ① 不同靶——
**故两条路径不能直接比较**，必须先经 `extractVec` 把路径 ② 拉回符号侧（见 `comm_via_extract`）。 -/
def canonicalizeThenCompile (c : VectorConstraint) : LinearLayer :=
  convertVec (canonicalize c)

/-- 注意 **空洞性诊断（本文件最重要的否定性发现）**：
`compileThenCanonicalize` **定义上就是** `canonicalize`。

要点 **理由**：`extractVec (convertVec c) = c` 是 **`rfl`**（§一），
故 `compileThenCanonicalize c ≡ canonicalize c` **无需任何证明**。

⇒ 要点 **后果**：任何形如「`canonicalize (extract (compile c))` 与某物交换」的陈述，
**若"某物"只提及 `canonicalize`，则它是 `rfl` 级的** —— **真，但不承重**。
要点 **这就是"经权重侧的交换律"为什么不是缺口 B 的障碍**：权重侧往返是**透明的**。 -/
theorem compileThenCanonicalize_eq_canonicalize :
    compileThenCanonicalize = canonicalize :=
  rfl

/-- 要点 **空洞性的点态形式**：对每个 `c`，路径 ① 就是 `canonicalize c`。 -/
theorem compileThenCanonicalize_apply (c : VectorConstraint) :
    compileThenCanonicalize c = canonicalize c :=
  rfl

theorem any_compile_side_path_eq_canonicalize
    (P : VectorConstraint → VectorConstraint)
    (h : ∀ c, P c = compileThenCanonicalize c) :
    P = canonicalize := by
  funext c
  rw [h c, compileThenCanonicalize_apply]

/-- 要点 **`canonicalize c = c` 的精确判据**（`constraintContent c = 1`）。

注意 **本文件需要它作为独立引理**（`canonicalizeThenCompile_eq_iff` 的证明核心）。
要点 **证明路线**：`⟸` 是既有的 `canonicalize_of_content_one`；
`⟹` 用 `content_canonicalize`（内容恒 1）与 `congrArg constraintContent`。
注意 **这不是重证 `canonicalize_of_content_one`**：那条只给单向，本条给**充要**。 -/
theorem canonicalize_iff_content_one (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) :
    canonicalize c = c ↔ constraintContent c = 1 := by
  constructor
  · intro hc
    have h1 : constraintContent (canonicalize c) = constraintContent c := by rw [hc]
    rw [content_canonicalize c hg] at h1
    exact h1.symm
  · intro h1
    exact canonicalize_of_content_one c h1

/-- 要点 **路径 ② 的不动点判据**：`canonicalizeThenCompile c = convertVec c`
**当且仅当** `c` 已经是规范的（`content c = 1`）。

要点 **证明路线**：`convertVec` 单射（`convertVec_extractVec_rfl` 给出左逆）
把结构等式化归为 `canonicalize c = c`，再用 `canonicalize_iff_content_one`。

⇒ 要点 **它把"规范化后再编译是否改变权重"这个问题【完全】回答**：
**只当 `content c = 1` 时不变**；否则**权重确实被改写**（这正是规范的**目的**）。 -/
theorem canonicalizeThenCompile_eq_iff (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) :
    canonicalizeThenCompile c = convertVec c ↔ constraintContent c = 1 := by
  constructor
  · intro h
    have h2 : extractVec (canonicalizeThenCompile c) = extractVec (convertVec c) := by rw [h]
    rw [show extractVec (canonicalizeThenCompile c) = canonicalize c from by
          cases c with | mk a b => rfl, extractVec_convertVec_rfl] at h2
    exact (canonicalize_iff_content_one c hg).mp h2
  · intro h1
    show convertVec (canonicalize c) = convertVec c
    rw [canonicalize_of_content_one c h1]

/-! ## 三、要点 真正的交换律：`canonicalize` 与 `scaleVec`（条件成立）

注意 **上一节证明"经权重侧的交换律"空洞** ⟹ 交换律的**真内容**必须在
**不经过权重侧**的复合上：

```
路径 ①  canonicalize (scaleVec c lam)        -- 先缩放，再规范化
路径 ②  scaleVec (canonicalize c) lam        -- 先规范化，再缩放
```

要点 **两条路径都落在符号侧、类型相同、可直接比较** —— 这才是非空洞的交换律。 -/

/-- 要点 **`Int.sign` 在【非零】倍率上的不动点恰是 `±1`**
（`sign x = x ↔ x = 1 ∨ x = -1`，**`x ≠ 0` 不可省**）。

注意 **本引理是就地证明的** —— 因为 `Int.sign_eq_self` 在 mathlib 4.14 中
**不存在**（STYLE 已登记的"以名字判有无"陷阱；实测 `#check @Int.sign_eq_self` 报
`unknown constant`）。本文件改用 `Int.sign_eq_one_of_pos` 与
`Int.sign_eq_neg_one_of_neg`（注意 后者亦**不是** `Int.sign_eq_neg_one_iff`，
那个名字同样不存在——**本文件在此实测两次**）按符号三分证明。

注意 **`h0 : x ≠ 0` 不可省 —— 本文件在此【证伪了自己初稿的陈述】**：
初稿写的是无条件的 `Int.sign lam = lam ↔ lam = 1 ∨ lam = -1`。
要点 **内核实测该陈述为假**：`lam = 0` 时 `Int.sign 0 = 0`（`Int.sign_zero`）
**为真**，而右端 `0 = 1 ∨ 0 = -1` **为假** ⟹ **`⟹` 方向失败**。
⇒ 要点 **这正是任务书要求的"宣布结论前先代小整数判真假"在【本文件内部】抓到的一个假命题**
（本波次已累计多例；本条为其中之一，如实登记）。

要点 **加了 `≠ 0` 之后它是 §三 充要条件（`⟺ lam = ±1`）的算术内核**：
交换律的"误差"是 `sign`，故**交换律成立 ⟺ 倍率已是自身的符号**。 -/
theorem int_sign_eq_self_iff {lam : Int} (h0 : lam ≠ 0) :
    Int.sign lam = lam ↔ lam = 1 ∨ lam = -1 := by
  constructor
  · intro h
    rcases lt_trichotomy lam 0 with hlt | heq | hgt
    · right
      -- 注意 `Int.sign_eq_neg_one_of_neg` 给出 `-1 = lam`（**符号在左**），
      -- 而目标是 `lam = -1` ⟹ 必须 `.symm`（STYLE 已登记的"方向不一致"家族）。
      rw [Int.sign_eq_neg_one_of_neg hlt] at h
      exact h.symm
    · -- 注意 初稿用 `exfalso; subst; rw [Int.sign_zero] at h` 会得到 `h : 0 = 0`（**恒真**）
      -- ⟹ **不会产生矛盾**（那个分支根本不是靠矛盾排除的）——
      -- 真因是 `h0 : lam ≠ 0` 直接与 `heq : lam = 0` 冲突。
      exact absurd heq h0
    · left
      rw [Int.sign_eq_one_of_pos hgt] at h
      exact h.symm
  · rintro (rfl | h)
    · exact Int.sign_one
    · rw [h]
      exact Int.sign_neg_one

/-- 要点 **一般倍率的精确律（交换律的"误差项"）**：

`canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam)`（`lam ≠ 0`）。

要点 **回收** `RealCanonicalForm.canonicalize_scaleVec_sign`（**不重证**）。
⇒ 要点 **它精确地量化了两条路径的差**：路径 ① 给出的倍率是 **`sign lam`**，
而路径 ② 用的倍率是 **`lam`** —— **两者相等 ⟺ `sign lam = lam` ⟺ `lam = ±1`**。 -/
theorem canonicalize_scaleVec_sign_law (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) (lam : Int) (hlam : lam ≠ 0) :
    canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam) :=
  canonicalize_scaleVec_sign c hg lam hlam

/-- 要点 **正倍率下：`canonicalize` **吞掉**倍率**（这是 `0 < lam` 时**唯一为真**的"正交换律"）。

注意 **本文件在此【证伪并撤下】了初稿的一条定理 —— 如实登记（本文件最重要的自我更正）**：

> **初稿陈述（为假）**：`canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam`（`0 < lam`）。
> **内核实测为假**：取 `c = {a := [2], b := 2}`、`lam = 3`：
> - 左端 `canonicalize {a := [6], b := 6} = {a := [1], b := 1}`（内容 6 → 约掉）；
> - 右端 `scaleVec {a := [1], b := 1} 3 = {a := [3], b := 3}`；
> - 要点 **`{[1],1} ≠ {[3],3}`** ⟹ **两条路径【不】交换**。
>
> 注意 **根因（叙述性错误，不是 tactic 错误）**：初稿把**两条不同的陈述混为一谈**：
> - 成立 **`canonicalize_section_pos`**：`canonicalize (scaleVec c lam) = canonicalize c`（`0 < lam`）——
>   右端**不含** `scaleVec`，说的是"**规范形在正倍率下不变**"；
> - 不成立 初稿的"交换律"：右端**含** `scaleVec (canonicalize c) lam` ——
>   说的是"**先规范化再缩放 = 先缩放再规范化**"，**这在 `lam ∉ {±1}` 时为假**。
>
> 要点 **⇒ 两条陈述的 RHS 形状不同、真假不同**（STYLE 已登记的"形状差异"家族在此升级为**真假差异**）。
> 要点 **且本文件自己的 `canonicalize_comm_scaleVec_iff`（§三）已经给出充要条件 `lam = ±1`** ⟹
> **初稿那条与它直接矛盾** —— **本文件的自我一致性检查抓到了自己**。

要点 **正确的"正倍率"陈述如下**：`canonicalize` 把倍率**完全吞掉**
（这与 `canonicalize_comm_scaleVec_iff` 一致：`lam = ±1` 之外**不交换**，
而 `canonicalize` 那一侧永远**丢掉** `lam`）。 -/
theorem canonicalize_absorbs_scale_pos (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) (lam : Int) (hlam : 0 < lam) :
    canonicalize (scaleVec c lam) = canonicalize c :=
  canonicalize_section_pos c hg lam hlam

/-- 要点 **`a` 中存在非零元**（当 `listGcdNat a ≠ 0`）：`listGcdNat_eq_zero_iff` 的**逆否**。

要点 **这是 §三 充要条件的**关键工具****：`b = 0` 时无法用 `b` 分量消去倍率，
必须改用 `a` 的**某个非零分量** —— **注意不是"首元"**（首元可以是 `0`），
而**存在性**足以消去倍率。 -/
lemma exists_ne_zero_of_listGcdNat_ne_zero (a : List Int) (h : listGcdNat a ≠ 0) :
    ∃ v ∈ a, v ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h ((listGcdNat_eq_zero_iff a).mpr hc)

/-- 要点 **`map (· * s) = map (· * l)` 在同位置取等式**（`List` 归纳，非 `rfl`）。

注意 **本文件第七处被内核拦下的写法**：归纳假设 `ih` 的形状是
`map (·*s) tl = map (·*l) tl → v ∈ tl → v*s = v*l`（**两个参数**），
而初稿只给了 `hmem` ⟹ 报 `application type mismatch`
（"`v ∈ tl` 但期望 `map … tl = map … l tl`" —— 注意 **报错信息把两个参数的位置都印出来了**）。
要点 **正解**：`ih` 要**两个**参数，且**等式在前、成员在后**。 -/
lemma map_mul_eq_at {a : List Int} {s l : Int}
    (h : a.map (fun x => x * s) = a.map (fun x => x * l)) {v : Int} (hv : v ∈ a) :
    v * s = v * l := by
  induction a with
  | nil => simp at hv
  | cons hd tl ih =>
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hv with rfl | hmem
    · exact h.1
    · exact ih h.2 hmem

/-- 要点 **交换律成立的【充要条件】**（本文件的核心正面结论）：

`canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam`
**⟺** `lam = 1 ∨ lam = -1`（在 `lam ≠ 0` 且 `content c ≠ 0` 下）。

要点 **证明路线**：
- **(⟹)** 用精确律把左端换成带 `sign lam` 的形式。
  注意 **这里有一处必须绕开的陷阱**：不能直接对 `scaleVec … (sign lam) = scaleVec … lam`
  消去倍率 —— 那需要**函数的单射性**（`scaleVec c ·` 单射），
  而 `canonicalize c` **可能是零约束**（`a = [], b = 0`，`content = 0`）时消去**失败**。
  要点 **正解**：在**代数层**做 —— 由 `VectorConstraint` 的结构相等取**两个投影**，
  得到 `b` 的等式；再分 `b ≠ 0`（直接消）与 `b = 0`（改用 `a`，并用
  `content (canonicalize c) = 1` 保证 `a ≠ []` 且其首元非零）两支。
  注意 **这不是繁琐化**：`b = 0` 的分支**必须**存在 —— 反例约束 `{a := [1], b := 0}`
  正是 `a ≠ [] ∧ b = 0` 的形态（`RealCanonicalForm.cBaseVec`）。
- **(⟸)** `lam = 1` 用 `scaleVec_one`；`lam = -1` 时 `sign lam = -1`，
  用精确律 + `Int.sign_neg_one`。 -/
theorem canonicalize_comm_scaleVec_iff (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) (lam : Int) (hlam : lam ≠ 0) :
    (canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam) ↔
      (lam = 1 ∨ lam = -1) := by
  constructor
  · intro h
    -- 用精确律把左端换成带 `sign lam` 的形式，再比较
    have hexact := canonicalize_scaleVec_sign_law c hg lam hlam
    rw [hexact] at h
    -- 注意 `scaleVec` 展开后 `a` 分量是 `List.map (· * ·)`，`b` 分量是乘法
    have hb : (canonicalize c).b * Int.sign lam = (canonicalize c).b * lam :=
      congrArg VectorConstraint.b h
    have ha : (canonicalize c).a.map (fun x => x * Int.sign lam)
            = (canonicalize c).a.map (fun x => x * lam) :=
      congrArg VectorConstraint.a h
    -- 规范形的内容恒为 1 ⟹ `a` 与 `b` **不可能同时为零**
    have hcont1 : constraintContent (canonicalize c) = 1 := content_canonicalize c hg
    by_cases hb0 : (canonicalize c).b = 0
    · -- 注意 **`b = 0` 分支**：`b` 分量给不出信息（`0 * s = 0 * l` 恒真），
      -- 要点 **必须改用 `a` 的某个非零分量** —— 而**不是**"首元"
      -- （首元可以是 `0`：如 `a = [0, 1]`，`content = gcd 0 1 = 1`）。
      -- 要点 由 `content = 1 ≠ 0` 与 `b = 0` 得 `listGcdNat a ≠ 0`，
      -- 再用 `exists_ne_zero_of_listGcdNat_ne_zero` 取出非零分量。
      have hlg : listGcdNat (canonicalize c).a ≠ 0 := by
        intro hz
        rw [constraintContent, hz, hb0] at hcont1
        simp at hcont1
      obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_listGcdNat_ne_zero _ hlg
      exact int_sign_eq_self_iff hlam |>.mp (mul_left_cancel₀ hv0 (map_mul_eq_at ha hv))
    · -- 要点 **`b ≠ 0` 分支**：直接由 `b` 分量消去（最简单的一支）
      exact int_sign_eq_self_iff hlam |>.mp (mul_left_cancel₀ hb0 hb)
  · rintro (h1 | hneg)
    · -- `lam = 1`：目标是 `canonicalize (scaleVec c 1) = scaleVec (canonicalize c) 1`。
      -- 注意 **本文件第二处被内核拦下的写法（两轮）**：
      -- `rw [h1, scaleVec_one]` 只把 `lam` 换成 `1`，目标仍是
      -- `canonicalize (scaleVec c 1) = …`；而 `scaleVec_one` **只改写一侧**
      -- （`scaleVec x 1 → x`），**剩余另一侧的模式仍挂着 `scaleVec`** ⟹ 报类型不符。
      -- 要点 **正解**：**两侧都要改** —— 先 `rw [scaleVec_one]`（左端内层），
      -- 再对右端用 `scaleVec_one` 的 `.symm` 对齐。
      rw [h1, scaleVec_one]
      exact (scaleVec_one (canonicalize c)).symm
    · rw [hneg]
      rw [canonicalize_scaleVec_sign_law c hg (-1) (by norm_num), Int.sign_neg_one]

/-- 要点 **`lam ∉ {±1}` 时两条路径【确实不同】**（把 §三 充要条件的**反面**显式化，
补齐 §四"为假"与 §三"充要"之间的缺口）。

要点 **这条与 `canonicalize_absorbs_scale_pos` 合起来给出完整图像**：
**`canonicalize` 一侧总是丢掉倍率，`scaleVec` 一侧保留倍率**
⟹ **两者只在倍率已经是 `±1`（即"倍率 == 它的符号"）时才一致**。 -/
theorem comm_scaleVec_fails_of_ne_pm_one (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) (lam : Int) (hlam : lam ≠ 0)
    (hne : ¬ (lam = 1 ∨ lam = -1)) :
    canonicalize (scaleVec c lam) ≠ scaleVec (canonicalize c) lam :=
  fun h => hne ((canonicalize_comm_scaleVec_iff c hg lam hlam).mp h)

/-! ## 四、要点 内核反例：交换律在一般倍率上**为假**（本文件最重要的否定结论）

注意 **上一节给出充要条件；本节给出具体的、内核可验的反例**，
使"交换律为假"不依赖读者接受那个充要条件。 -/

/-- 要点 **反例基准约束**：`a = [2]`、`b = 2`（**内容 = 2，且 `b ≠ 0`**）。

注意 **`b ≠ 0` 是必需的**：若 `b = 0`，`±1` 缩放在 `b` 分量上看不出差别
（`RealCanonicalForm` §二 已登记的同类教训：该文件曾误用 `cBaseVec`（`b = 0`）作反例）。
注意 **且 `a = [2]` 只含一个分量**，使 `canonicalize` 的具体值可 `norm_num` 关闭。 -/
def cCommVec : VectorConstraint := { a := [2], b := 2 }

/-- **反例约束的内容为 `2`**（非零，故 `canonicalize` 的定义域前提成立）。 -/
lemma content_cCommVec : constraintContent cCommVec = 2 := by
  simp only [constraintContent, listGcdNat, cCommVec, List.foldr_cons, List.foldr_nil]
  norm_num

/-- **反例约束的规范形**：`{[1], 1}`（即 `x₀ + 1 = 0`）。 -/
lemma canonicalize_cCommVec : canonicalize cCommVec = ({ a := [1], b := 1 } : VectorConstraint) := by
  simp only [canonicalize, constraintContent, listGcdNat, cCommVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- 要点 **交换律【为假】（内核反例）**：

**存在**约束 `c` 与非零倍率 `lam`，使
`canonicalize (scaleVec c lam) ≠ scaleVec (canonicalize c) lam`。

要点 **见证**：`c = cCommVec = {a := [2], b := 2}`、`lam = -1`。
- 路径 ①：`scaleVec c (-1) = {a := [-2], b := -2}`，内容 `2`，
  规范形 `{[1], 1}`（**注意：`(-2)/2 = -1`，`(-2)/2 = -1`** ⟹ **`{[-1], -1}`**，见下）；
- 注意 **精确计算**：`{a := [-2], b := -2}` 的内容是 `gcd(2, 2) = 2`（**`natAbs` 语义**），
  故规范形是 `{a := [-2 / 2], b := -2 / 2} = {a := [-1], b := -1}`；
- 路径 ②：`scaleVec {[1],1} (-1) = {a := [-1], b := -1}`。

注意 **两者【相等】！** ⇒ **`lam = -1` 不是反例**（这正是 §三 充要条件说的：`±1` 上成立）。
要点 **真正的反例必须取 `|lam| ∉ {1}`**：取 **`lam = -2`**：
- 路径 ①：`scaleVec c (-2) = {a := [-4], b := -4}`，内容 `4`，
  规范形 `{a := [-4/4], b := -4/4} = {[-1], -1}`；
- 路径 ②：`scaleVec {[1],1} (-2) = {a := [-2], b := -2}`。

⇒ 要点 **`{[-1], -1} ≠ {[-2], -2}`** 成立 **交换律在此为假**（`b` 分量 `-1 ≠ -2`）。

注意 **本文件的如实登记**：初稿曾误以为 `lam = -1` 是反例 —— **它是错的**
（`±1` 恰是交换律**成立**的两个点）。**真正的反例是 `lam = -2`**。
要点 **这正是 §三 充要条件（`⟺ lam = ±1`）在反例选择上的直接后果**。 -/
theorem canonicalize_compile_comm_fails :
    ∃ (c : VectorConstraint) (lam : Int), lam ≠ 0 ∧
      canonicalize (scaleVec c lam) ≠ scaleVec (canonicalize c) lam := by
  refine ⟨cCommVec, -2, by norm_num, ?_⟩
  intro h
  -- 路径 ① 的具体值：`canonicalize (scaleVec cCommVec (-2)) = {[-1], -1}`
  have h1 : canonicalize (scaleVec cCommVec (-2)) = ({ a := [-1], b := -1 } : VectorConstraint) := by
    simp only [canonicalize, constraintContent, listGcdNat, cCommVec, scaleVec,
               List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
    norm_num
  -- 路径 ② 的具体值：`scaleVec (canonicalize cCommVec) (-2) = {[-2], -2}`
  have h2 : scaleVec (canonicalize cCommVec) (-2) = ({ a := [-2], b := -2 } : VectorConstraint) := by
    rw [canonicalize_cCommVec]
    simp only [scaleVec, List.map_cons, List.map_nil]
    norm_num
  rw [h1, h2] at h
  -- 取 `b` 分量得 `-1 = -2`
  have hb : (-1 : Int) = -2 := congrArg VectorConstraint.b h
  omega

/-! ## 五、要点 交换律的**正面**读数：在"模 `±1`"之下成立

注意 §四 说裸交换律为假。要点 **但 §三 的精确律给出了它的【正确修正】**：
交换律不是"为假"，而是**在一个非平凡的子群上成立**。 -/

/-- 要点 **交换律在 `±1` 上成立**（**完备地**覆盖 §三 充要条件的正面方向）：

对 `lam = 1` 与 `lam = -1`，两条路径**相等**。

要点 **与 §四 合起来的完整图像**：
**`{±1}` 是交换律成立的【全部】倍率**（`canonicalize_comm_scaleVec_iff` 已证充要），
而 **`{±1}` 恰是 `ScaleClass` 必须商掉的部分**（`RealCanonicalForm` §1.6）。
⇒ 要点 **缺口 B 的正确定位**：**交换律在 `ScaleClass` 上为假，在 `ScaleClass / {±1}` 上为真**。 -/
theorem canonicalize_comm_scaleVec_pm_one (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) :
    canonicalize (scaleVec c 1) = scaleVec (canonicalize c) 1 ∧
    canonicalize (scaleVec c (-1)) = scaleVec (canonicalize c) (-1) := by
  refine ⟨?_, ?_⟩
  · rw [scaleVec_one, scaleVec_one]
  · rw [canonicalize_scaleVec_sign_law c hg (-1) (by norm_num), Int.sign_neg_one]

/-- 要点 **交换律的"误差"恰是 `sign`**（把交换律的失败**定量化**）：

`scaleVec (canonicalize (scaleVec c lam)) ... ` 的差**精确地**是**倍率的符号**。

要点 **陈述形式**：路径 ① 的倍率被规范化**替换为它的符号**，
故**当且仅当** `lam` 已完成"符号化"（即 `lam = ±1`）时两条路径对齐。 -/
theorem comm_error_is_exactly_sign (c : VectorConstraint)
    (hg : constraintContent c ≠ 0) (lam : Int) (hlam : lam ≠ 0) :
    canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam) ∧
    (Int.sign lam = lam ↔ lam = 1 ∨ lam = -1) :=
  ⟨canonicalize_scaleVec_sign_law c hg lam hlam, int_sign_eq_self_iff hlam⟩

/-! ## 六、要点 缺口 B 的判定与**正确定位**（诚实边界）

要点 **本文件的总结论**：

| 陈述 | 判定 | 依据 |
|:--|:--|:--|
| "`canonicalize ∘ extract ∘ compile` 与 `canonicalize` 交换" | 成立 真但**空洞**（`rfl`） | §二 |
| "`canonicalize` 与 `scaleVec lam` 交换（一般 `lam ≠ 0`）" | 不成立 **为假** | §三 充要 + §四 内核反例 `lam = -2` |
| 注意 "`canonicalize` 与 `scaleVec lam` 交换（**`0 < lam`**）" | 不成立 **亦为假**（`lam = 3` 即反例）—— **初稿曾错写为"成立"，已撤下** | §三 `canonicalize_absorbs_scale_pos` 的 docstring |
| "`canonicalize` **吞掉**倍率（`0 < lam`）" | 成立 **成立**（这才是 `0 < lam` 时的真陈述） | §三 `canonicalize_absorbs_scale_pos` |
| "两者交换 ⟺ `lam = ±1`" | 成立 **充要** | §三 `canonicalize_comm_scaleVec_iff` |

注意 **本文件最重要的自我更正（如实登记，不掩盖）**：
初稿曾把「`0 < lam` 时的交换律」写成 `canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam`
并声称**成立**。**该陈述为假**，且**与本文件自己的 §三 充要条件（`⟺ lam = ±1`）直接矛盾**：
取 `c = {a := [2], b := 2}`、`lam = 3`，左端 `{[1],1}`、右端 `{[3],3}`。
要点 **根因是叙述性的**：初稿把**两条 RHS 形状不同的陈述**混为一谈 ——
`canonicalize_section_pos`（RHS 不含 `scaleVec`）与"交换律"（RHS 含 `scaleVec`）。
注意 **本文件的内部一致性检查（§三 `iff` 对照 §三 的 `pos` 版）抓到了它**，
并且**内核独立证伪**（见 §四 与 `_w13_probe_k`：`¬(∀ c lam, …)` 可证）。
⇒ 要点 **这正是任务书"宣布结论前先代小整数判真假"的正面收获**：**本波次它抓到了本文件自己的一条假命题**。

注意 **本文件【不】声称"缺口 B 不可能闭合"**。精确表述是：

> 要点 **经权重侧的交换律是空洞的**（权重侧往返是 `rfl`，无法承载缺口 B）；
> 要点 **裸交换律为假**；要点 **正确的载体是"`ScaleClass` 再模掉 `±1` 的商"** ——
> 而 `RealCanonicalForm` 的 `canonicalize_scaleVec_sign` **已经**给出了
> `canonicalize` 在该商上**良定义**（下降）所需的**全部**内容。

注意 **⇒ 缺口 B 的【理论障碍】不在"证明难"，而在"商的载体尚未被构造"**：
`ScaleClass`（`RealCanonicalForm` §二）**不含** `±1` 商，
故**没有** `VectorConstraint` 上的 Setoid 能让 `canonicalize` 下降。
要点 **本文件如实标注：构造该 Setoid 与证明下降，属【未做】**（见下"未做"清单）。

**未做（如实登记）**：
- 注意 **`±1` 商的 Setoid 与 `canonicalize` 的下降**：**未做**。
  需要 `ScaleClassPlusMinus`（把 `±1` 也商掉）与 `Quotient.lift` 的良定义性证明。
  注意 **本文件已证明它【可行】**（`comm_error_is_exactly_sign` 给出下降所需的精确律），
  **但未构造该对象**。
- 注意 **与"激活折入"的交换律**：**未做**（已被 `activated_loop_breaks` 证伪，不证假命题）。
- 注意 **`canonicalize` 与 `compileToLayer`（列表级）的交换律**：**未做**
  （逐点结果由 `any_compile_side_path_eq_canonicalize` 直接抬升，**属平凡**，故不单列）。
- 本文件**只读**引用 `RealCanonicalForm` / `ConvertVectorLinear` /
  `WeightToSymbolEquivalence` / `SymbolToWeightCorrectness`，**不修改任何既有文件**。
- 无 `sorry` / `axiom` / `admit` / `native_decide`；不用 `field_simp` 收尾。
-/

/-- 要点 **诚实清单（机器可检索）**：本文件的全部主张用一条合取陈述概括：
① 经权重侧的路径**恒等于** `canonicalize`（空洞）；
② 交换律**存在**内核反例（`lam = -2`）；
③ 交换律**充要于** `lam = ±1`；
④ 交换律的"误差"**恰是** `Int.sign`。 -/
theorem comm_honesty_register :
    (compileThenCanonicalize = canonicalize) ∧
    (∃ (c : VectorConstraint) (lam : Int), lam ≠ 0 ∧
        canonicalize (scaleVec c lam) ≠ scaleVec (canonicalize c) lam) ∧
    (∀ (c : VectorConstraint), constraintContent c ≠ 0 →
        ∀ (lam : Int), lam ≠ 0 →
        (canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam ↔
          (lam = 1 ∨ lam = -1))) ∧
    (∀ (c : VectorConstraint), constraintContent c ≠ 0 →
        ∀ (lam : Int), lam ≠ 0 →
        canonicalize (scaleVec c lam) = scaleVec (canonicalize c) (Int.sign lam)) :=
  ⟨compileThenCanonicalize_eq_canonicalize, canonicalize_compile_comm_fails,
    canonicalize_comm_scaleVec_iff, canonicalize_scaleVec_sign_law⟩

end Lattice
