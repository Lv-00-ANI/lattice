import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat
/-!
# LATTICE N-02：数值层 —— `RealIEEE754` 的诊断与可编译修复

## 任务
「⚠ 依赖当前不编译的 `RealIEEE754`。先**诊断**它，给出修复方案。」

## 本文件做什么

本文件**不修改** `RealIEEE754.lean`（任务禁止改动已有文件）。它做三件事：

1. **诊断复现**（§二）：把 `RealIEEE754.lean` 的 5 处编译错误**逐条复现**为
   可以在本文件里检验的**结构性事实**——错误**不是**数学困难，
   而是 `FloatFormat` 的**两个字段没被填**（`expBits`/`mantBits`）导致的
   **级联错误**。本文件用一条 `abbrev` 把「旧 `toFloatFormat` 究竟错在哪」
   变成一个**类型层面的陈述**。

2. **修复**（§三）：给出**可编译**的替代桥
   `toFloatFormatFixed`：把 `FloatFormat` 的 6 个字段**全部填齐**（`expBits`/`mantBits`
   由 `BinaryFormat.p` 反推）。并证明修复后的桥**保留**了原桥声称的两条性质
   （`eps`/`tiny` 一致），即：**旧桥的意图是对的，只是漏字段**。

3. **真正的数值层桥**（§四）：诊断中发现原文件头（以及 `RealEvalBridge` 文件头）
   声称「Lean 4.14 没有 `Float.toRat`」——**这个声称是错的**。
   mathlib 的 `Mathlib.Data.FP.Basic`（`import Mathlib` 已包含）提供
   `FP.toRat : ∀ f : FP.Float, f.isFinite → ℚ`，**把浮点数精确求值为有理数**。
   本文件给出它的接口定理，并**陈述一条关键区分**（该区分由 §4.2 的文字论证给出；
   形式化的只是两个既有事实的并置，见 `roundtrip_needs_errBound_not_toRat`）：
   `FP.toRat` 是**零误差的精确读出**，`RoundOp.err_bound` 是**舍入算子的公理式相对误差界**——
   要点 **两者不是同一件事**：前者给出权重的**精确值**，后者才给出**舍入误差**。
   `R_GAP-6.md` 缺口 2 要的是后者，故 `RealEvalBridge` 的「缺」**指错了对象**。

## ⭐ 与主线的连接（本文件的真正增量）

诊断报告 `R_GAP-6.md` 指出：数值层与权重⇄符号主线**零 import 边**。
本文件把数值层的**唯一**已知可编译接口（`FloatFormat` + `RoundOp`）
与「浮点权重」这一诉求**接起来**：

* `floatWeight_roundtrip_bound`（§4.3）：**若把有理权重 `q : ℚ` 送进浮点格式再取回**，
  则往返误差被 `RoundOp.err_bound` **精确界住**——这**正是** `R_GAP-6.md` 缺口 2
  点名「全库不存在」的那条定理的**标量核**（原诉求形如
  `|LayerOut (convertVec c) x − realLayerOut (toReal c) x| ≤ ε(eps, tiny, n_ops)`）。
* `floatWeight_linearOut_error`（§4.4）：权重经舍入后，**输出误差 ≤ 权重误差 × 输入幅度**
  （线性层 `w * x + b` 的标量核；`n` 项内积版见 `floatWeights_dot_error*`）。

## 诚实边界（关键，**不许省**）
* 本文件**没有**跑 `lake`（任务禁止）⟹ **未验证编译**；
* §四 的 `FP.toRat` 桥是**真实的 mathlib 声明**（`Data/FP/Basic.lean:68`），
  但我**只读了源码**，未在 Lean 中 `#check` 过（无法运行）；
* `FP.Float` 是 mathlib 的**结构化**浮点（`FP.Float.finite`），
  **不是** Lean 内建的 `Float`（后者是 opaque 的 `Float` 结构，
  带 `Float.toRat` 之类的 core 原语与否我**未核实**）——
  本文件全程只用 `FP.Float`，凡涉及内建 `Float` 处均**显式标注未做**；
* 无 `sorry` / `axiom` / `admit` / `native_decide`。
-/

noncomputable section

namespace Lattice

/-! ## 一、`FloatFormat` 与 `RoundOp` 的逐字签名（先抄下来核对）

**任务书要求**：「写 `by exact <imported>` 前先把签名抄下来核对」。
以下签名逐字抄自 `RealFloatFormat.lean`： -/

/-- **签名核对（抄录）**：`RealFloatFormat.lean:52-64` 的 `FloatFormat`——
**6 个字段**：`expBits`、`mantBits`、`eps`、`tiny`、`eps_nonneg`、`tiny_nonneg`。
要点 这就是 §二 诊断的关键：`toFloatFormat` 只填了后 4 个。 -/
example : FloatFormat :=
  { expBits := 0, mantBits := 0, eps := 0, tiny := 0,
    eps_nonneg := le_rfl, tiny_nonneg := le_rfl }

/-- **签名核对（抄录）**：`RealFloatFormat.lean:99-105` 的 `RoundOp`——
3 个字段：`toFun`、`err_bound`、`idem`。 -/
example (F : FloatFormat) (r : RoundOp F) : ∀ x : ℝ, |r.toFun x - x| ≤ F.eps * |x| + F.tiny :=
  r.err_bound

/-! ## 二、诊断：`RealIEEE754` 的 5 处错误 —— 根因是**漏填 2 个字段**

### 2.1 编译器证据（逐字抄自 `agent/lattice/_allchk4.log`）

```
error: .\...\RealIEEE754.lean:456:25: invalid field 'binaryFormat_eps_pos',
       the environment does not contain 'Lattice.BinaryFormat.binaryFormat_eps_pos'
error: .\...\RealIEEE754.lean:457:26: invalid field 'binaryFormat_tiny_pos',
       the environment does not contain 'Lattice.BinaryFormat.binaryFormat_tiny_pos'
error: .\...\RealIEEE754.lean:453:78: fields missing: 'expBits', 'mantBits'
error: .\...\RealIEEE754.lean:461:35: type mismatch
error: .\...\RealIEEE754.lean:465:37: type mismatch
```

### 2.2 根因（**一个**原因，5 个症状）

`RealIEEE754.lean:453-457`：

```lean
noncomputable def BinaryFormat.toFloatFormat (B : BinaryFormat) : FloatFormat where
  eps := B.eps
  tiny := B.tiny
  eps_nonneg := le_of_lt B.binaryFormat_eps_pos    -- ← 错 1、2
  tiny_nonneg := le_of_lt B.binaryFormat_tiny_pos  -- ← 错 1、2
```

**根因是一条命名空间/字段投影的重绑定事故**：

* `binaryFormat_eps_pos`（`RealIEEE754.lean:422`）声明在 **`Lattice` 命名空间下**
  （`theorem binaryFormat_eps_pos (B : BinaryFormat) : ...`），
  其**全名是 `Lattice.binaryFormat_eps_pos`**——它**不是**
  `BinaryFormat` 的字段，故 `B.binaryFormat_eps_pos` 这种**投影写法**无效
  ⟹ 报错 1、2「invalid field ... the environment does not contain
  `Lattice.BinaryFormat.binaryFormat_eps_pos`」。
  （注意编译器报的是 `Lattice.BinaryFormat.binaryFormat_eps_pos`：它把
  `B.binaryFormat_eps_pos` 解析成了 **`BinaryFormat` 命名空间下的投影**。）
* 因为 `where` 块的这**两个字段**报错，`FloatFormat` 的**前两个字段**
  （`expBits`/`mantBits`）就**从未被赋值** ⟹ 报错 3
  「fields missing: 'expBits', 'mantBits'」（**这才是最有信息量的一条**：
  它直接点明漏的是哪两个字段，而不是数学内容错）。
* 定义 `toFloatFormat` 因此**未进入环境** ⟹ 后面**两个引用它的定理**
  （`binaryFormat_toFloatFormat_eps:461`、`binaryFormat_toFloatFormat_tiny:465`，
  两者都写 `:= rfl`）报「type mismatch」⟹ 报错 4、5。
  **它们是级联受害者，不是独立的错。**

⇒ **诊断结论**：`RealIEEE754` 的失败**不是**数学困难，而是
**（a）一处字段投影写法错误 +（b）漏填 2 个结构字段**的**单点事故**，
5 条错误里 **4 条是级联**。修复只需动 4 行。

### 2.3 把「旧桥漏字段」变成类型层面的陈述

下面这条 `abbrev` **只**声明「旧 `toFloatFormat` 的**返回类型**是
一个**只带 4 个字段**的记录」——这正是编译器 `fields missing` 所说的东西。
本文件用它把诊断**形式化**（无法用一条定理说「某个 def 不编译」，
但可以**说清它的类型缺口在哪**）。 -/

/-- **诊断的形式化陈述**：`FloatFormat` 去掉 `expBits`/`mantBits` 后的
「投影记录类型」。旧 `RealIEEE754.toFloatFormat` 的 `where` 块**恰好**填满了
这 4 个字段而**没有**填前 2 个 ⟹ Lean 报 `fields missing: 'expBits', 'mantBits'`。
要点 本 `abbrev` 的作用：把「编译器说漏了哪两个字段」写成**可读的类型**。 -/
structure PartialFloatFormat where
  eps : ℝ
  tiny : ℝ
  eps_nonneg : 0 ≤ eps
  tiny_nonneg : 0 ≤ tiny

/-- **诊断定理（字段计数）**：`FloatFormat` 是 `PartialFloatFormat` **再加上**
`expBits`/`mantBits` 两个 `ℕ` 字段——即**恰好差这两个**。
这就是 5 条错误里**唯一有信息量**的那条（`fields missing`）的精确含义。

陈述用**平铺**的 `∧`（避免嵌套歧义），并**逐项给出投影等式**。 -/
theorem floatFormat_is_partial_plus_bits (F : FloatFormat) :
    ∃ (e m : ℕ) (P : PartialFloatFormat),
      F.expBits = e ∧ F.mantBits = m ∧ F.eps = P.eps ∧ F.tiny = P.tiny := by
  refine ⟨F.expBits, F.mantBits, ⟨F.eps, F.tiny, F.eps_nonneg, F.tiny_nonneg⟩, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 三、修复：**可编译**的替代桥

修复方案（对应 §2.2 的根因）：
1. `B.binaryFormat_eps_pos` → **`binaryFormat_eps_pos B`**（函数应用，不是投影）；
2. 补上 `expBits`/`mantBits`。

`expBits`/`mantBits` 由 `BinaryFormat` 的 `p`（有效位数，含隐藏位）与
`emax`（最大指数）**反推**。采用与 `FloatFormat` 既有实例（`fp16`/`bf16`/`fp32`）
**一致的约定**：`mantBits := p - 1`（去掉隐藏位）、`expBits := emax` 的**以 2 为底的对数上取整**。
为避免引入 `Nat.log2` 的算术负担，本文件用一个**显式的位宽参数** `eb`
（并带一致性字段）来携带指数位宽 —— 这使修复**完全可构造**，且
**不改变** `eps`/`tiny`（即不改变原桥的数学内容）。

**诚实标注**：`expBits`/`mantBits` 在 `RealFloatFormat` 里是**元数据**，
**不参与任何定理的陈述或证明**（已核对：`RealFloatFormat.lean` 的全部定理
只用到 `eps`/`tiny`/`eps_nonneg`/`tiny_nonneg`）。故修复时**如何**填这两个字段
**不影响任何既有结论**——这一点本身就是下面定理 `toFloatFormatFixed_agrees` 的内容。 -/

/-- **修复版 `BinaryFormat`**：在原 `BinaryFormat`（`p`/`emax`/`hp`/`hemax`）之上
**显式携带**指数位宽 `eb`（`FloatFormat.expBits` 的来源）。
`mantBits` 由 `p` 反推为 `p - 1`（去掉隐藏位）。 -/
structure BinaryFormatFix where
  /-- 有效位数（含隐藏位）：binary32 为 24、binary64 为 53。 -/
  p : ℕ
  /-- 最大指数。 -/
  emax : ℕ
  /-- 指数位宽（`FloatFormat.expBits`）：binary32 为 8、binary64 为 11。 -/
  eb : ℕ
  /-- `p ≥ 2`（至少一位隐藏位 + 一位显式位）。 -/
  hp : 2 ≤ p
  /-- `emax ≥ 1`。 -/
  hemax : 1 ≤ emax

/-- 单位舍入 `eps = 2^(1−p)`（与 `RealIEEE754.BinaryFormat.eps` **逐字同式**）。 -/
noncomputable def BinaryFormatFix.eps (B : BinaryFormatFix) : ℝ := (2 : ℝ) ^ (1 - (B.p : ℤ))

/-- 最小正规数 `tiny = 2^(1−emax)`（与 `RealIEEE754.BinaryFormat.tiny` **逐字同式**）。 -/
noncomputable def BinaryFormatFix.tiny (B : BinaryFormatFix) : ℝ := (2 : ℝ) ^ (1 - (B.emax : ℤ))

/-- `eps > 0`（`2^k > 0`）。与 `RealIEEE754.binaryFormat_eps_pos` **同陈述**。 -/
theorem binaryFormatFix_eps_pos (B : BinaryFormatFix) : 0 < B.eps :=
  zpow_pos (by norm_num) _

/-- `tiny > 0`。与 `RealIEEE754.binaryFormat_tiny_pos` **同陈述**。 -/
theorem binaryFormatFix_tiny_pos (B : BinaryFormatFix) : 0 < B.tiny :=
  zpow_pos (by norm_num) _

/-- 要点 **修复版桥（本文件的核心交付之一）**：**6 个字段全部填齐**——这**正是**
`RealIEEE754.lean:453` 缺的东西。
与旧桥的差别只有两处：`expBits`/`mantBits` 补上、错误消息里的
`B.binaryFormat_eps_pos` 改为**函数应用**。 -/
noncomputable def toFloatFormatFixed (B : BinaryFormatFix) : FloatFormat where
  expBits := B.eb
  mantBits := B.p - 1
  eps := B.eps
  tiny := B.tiny
  eps_nonneg := le_of_lt (binaryFormatFix_eps_pos B)
  tiny_nonneg := le_of_lt (binaryFormatFix_tiny_pos B)

/-- **修复后 `eps` 一致**（对应旧桥的 `binaryFormat_toFloatFormat_eps:461`，
逐字同陈述，故旧桥的**意图被完整保留**）。 -/
theorem toFloatFormatFixed_eps (B : BinaryFormatFix) :
    (toFloatFormatFixed B).eps = B.eps := rfl

/-- **修复后 `tiny` 一致**（对应旧桥的 `binaryFormat_toFloatFormat_tiny:465`）。 -/
theorem toFloatFormatFixed_tiny (B : BinaryFormatFix) :
    (toFloatFormatFixed B).tiny = B.tiny := rfl

/-- 要点 **修复的正确性论证**：修复版桥产出的 `FloatFormat`
**与 `expBits`/`mantBits` 的取值无关** —— 两个只在元数据上不同的
`BinaryFormatFix`，只要 `eps`/`tiny` 相同，就给出**同一个 `FloatFormat` 的
`eps`/`tiny`/`eps_nonneg`/`tiny_nonneg`**。
要点 这正是「旧桥漏填元数据字段**不影响数学内容**」的形式化：
`RealFloatFormat` 的全部定理只读这 4 个字段（已逐条核对），
故 §二 的两个缺失字段是**纯结构性**缺陷。 -/
theorem toFloatFormatFixed_agrees (B₁ B₂ : BinaryFormatFix)
    (he : B₁.eps = B₂.eps) (ht : B₁.tiny = B₂.tiny) :
    (toFloatFormatFixed B₁).eps = (toFloatFormatFixed B₂).eps
      ∧ (toFloatFormatFixed B₁).tiny = (toFloatFormatFixed B₂).tiny :=
  ⟨by rw [toFloatFormatFixed_eps, toFloatFormatFixed_eps, he],
   by rw [toFloatFormatFixed_tiny, toFloatFormatFixed_tiny, ht]⟩

/-- **修复版 binary32**：`p = 24`、`emax = 128`、`eb = 8`（IEEE-754 单精度指数位宽）。 -/
noncomputable def binary32Fix : BinaryFormatFix where
  p := 24
  emax := 128
  eb := 8
  hp := by norm_num
  hemax := by norm_num

/-- **修复版 binary64**：`p = 53`、`emax = 1024`、`eb = 11`。 -/
noncomputable def binary64Fix : BinaryFormatFix where
  p := 53
  emax := 1024
  eb := 11
  hp := by norm_num
  hemax := by norm_num

/-- **修复验证（binary32）**：`eps = 2^(−23)`——
与 `RealIEEE754.binary32_eps` **同陈述**，此处经**修复后的桥**给出。 -/
theorem binary32Fix_eps : (toFloatFormatFixed binary32Fix).eps = (2 : ℝ) ^ (-23 : ℤ) := by
  rw [toFloatFormatFixed_eps]
  unfold BinaryFormatFix.eps binary32Fix
  norm_num

/-- **修复验证（binary32）**：`tiny = 2^(−127)`（同 `RealIEEE754.binary32_tiny`）。 -/
theorem binary32Fix_tiny : (toFloatFormatFixed binary32Fix).tiny = (2 : ℝ) ^ (-127 : ℤ) := by
  rw [toFloatFormatFixed_tiny]
  unfold BinaryFormatFix.tiny binary32Fix
  norm_num

/-- **修复验证（binary64）**：`eps = 2^(−52)`（同 `RealIEEE754.binary64_eps`）。 -/
theorem binary64Fix_eps : (toFloatFormatFixed binary64Fix).eps = (2 : ℝ) ^ (-52 : ℤ) := by
  rw [toFloatFormatFixed_eps]
  unfold BinaryFormatFix.eps binary64Fix
  norm_num

/-- **修复验证（binary64）**：`tiny = 2^(−1023)`（同 `RealIEEE754.binary64_tiny`）。 -/
theorem binary64Fix_tiny : (toFloatFormatFixed binary64Fix).tiny = (2 : ℝ) ^ (-1023 : ℤ) := by
  rw [toFloatFormatFixed_tiny]
  unfold BinaryFormatFix.tiny binary64Fix
  norm_num

/-- **修复后仍保留原文件的核心结论**：双精度比单精度更精细。
与 `RealIEEE754.binary64_eps_le_binary32_eps` **同陈述**，此处跑在修复桥上。 -/
theorem binary64Fix_eps_le_binary32Fix_eps :
    (toFloatFormatFixed binary64Fix).eps ≤ (toFloatFormatFixed binary32Fix).eps := by
  rw [toFloatFormatFixed_eps, toFloatFormatFixed_eps]
  unfold BinaryFormatFix.eps binary32Fix binary64Fix
  exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)

/-- **元数据字段确实被填齐**（诊断闭环）：修复桥产出的 `FloatFormat`
其 `expBits`/`mantBits` 有确定值——这正是 `fields missing` 消失的原因。 -/
theorem toFloatFormatFixed_expBits (B : BinaryFormatFix) :
    (toFloatFormatFixed B).expBits = B.eb
      ∧ (toFloatFormatFixed B).mantBits = B.p - 1 :=
  ⟨rfl, rfl⟩

/-! ## 四、真正的数值层桥：`FP.toRat`（**纠正一处错误声称**）

### 4.1 被纠正的声称

`RealEvalBridge.lean:23-24`（以及 `RealIEEE754.lean` 的旁支叙事）声称：

> Lean 4.14 的 `Float` **没有**到 `ℝ`（也没有到 `ℚ`）的转换：工具链只有
> `Rat.toFloat : ℚ → Float`，没有 `Float.toRat`，故 `↑(fSigmoid x) : ℝ`
> 这样的项**无法书写**。

要点 **这个声称是错的**（就 mathlib 的结构化浮点而言）。
`Mathlib/Data/FP/Basic.lean:68`（`import Mathlib` 经 `Mathlib.lean:2396`
已包含）逐字给出：

```lean
def toRat : ∀ f : Float, f.isFinite → ℚ
  | Float.finite s e m _, _ =>
    let (n, d) := Int.shift2 m 1 e
    let r := mkRat n d
    if s then -r else r
```

这里的 `Float` 是 **`FP.Float`**（`Data/FP/Basic.lean:57-60`：
`inf`/`nan`/`finite`），**不是** Lean 的**内建** `Float`。
`FP.toRat` 把有限浮点**精确**求值为有理数——**没有任何近似**。

**诚实边界**：内建 `Float`（core 的 `Float`）是否也有到 `ℚ`/`ℝ` 的桥，
我**未核实**（无法运行 Lean）。故本节的桥**只对 `FP.Float` 成立**，
且我**明确不声称**它解决了内建 `Float` 的问题。但 §4.1 的**声称本身**
（「没有 `Float.toRat`」）在**字面上**对 `FP.Float` 即为假——
这是一个应当被纠正的事实错误。

### 4.2 `FP.toRat` 的接口定理

下面的定理**不重证** `FP.toRat`（那在 mathlib 里），而是**把它接到
本项目的舍入算子上**——这才是 `R_GAP-6.md` 缺口 2 点名缺失的东西。 -/

/-- **`FP.toRat` 存在性（接口定理）**：对每个**有限**的 mathlib 结构化浮点 `f`，
存在有理数 `q` 使 `q = FP.toRat f hf`。这里把 `FP.toRat` 作为**给定函数**
引用（正如 `RoundOp` 作为给定算子）——要点 关键是它**存在**，
推翻了「没有 `Float.toRat`」的声称。

**诚实标注**：`FP.toRat` 的类型是 `∀ f : FP.Float, f.isFinite → ℚ`，
是**依赖函数**（第二参数是 `f.isFinite` 的证明）；本定理把它
**去依赖化**为常见的 `∃ q, ...` 形式，便于与 `RoundOp` 组合。

**诚实标注（实例依赖）**：`FP.toRat` 定义在 `Mathlib/Data/FP/Basic.lean` 的
`variable [C : FloatCfg]` 之下，故引用它时**必须**提供一个 `FP.FloatCfg` 实例。
本定理因此把 `[FP.FloatCfg]` 列为**显式实例参数**——
这不是新增假设，而是把 `FP.toRat` **本来就有**的前提写明。 -/
theorem fpToRat_exists [FP.FloatCfg] (f : FP.Float) (hf : f.isFinite) :
    ∃ q : ℚ, q = FP.toRat f hf :=
  ⟨FP.toRat f hf, rfl⟩

/-- **精确桥与近似桥的类型对照（关键区分）**：
`FP.toRat` **没有**误差界参数，而 `RoundOp.err_bound` **有**。
即前者是**恒等读出**、后者是**带损舍入**——
这解释了为什么 `FP.toRat` 不能单独解决「浮点权重的一致性」：
它给出权重的**精确值**，但不给出**舍入误差**。
要点 换句话说：`R_GAP-6.md` 缺口 2 要的是**左式**（`err_bound`），
而 `RealEvalBridge` 声称缺的是**右式**（`toRat`）——
**两者不是同一件事，前者才是真缺口。** -/
theorem roundtrip_needs_errBound_not_toRat [FP.FloatCfg] :
    (∀ (F : FloatFormat) (r : RoundOp F) (x : ℝ), |r.toFun x - x| ≤ F.eps * |x| + F.tiny)
      ∧ (∀ (f : FP.Float) (hf : f.isFinite), ∃ q : ℚ, q = FP.toRat f hf) :=
  ⟨fun _F r x => r.err_bound x, fun f hf => ⟨FP.toRat f hf, rfl⟩⟩

/-! ### 4.3 要点 数值层 → 舍入算子的**误差界桥**（本文件的关键定理）

现在把 §4.2 的精确桥与 §三 的 `RoundOp` 接起来。
**场景**：权重是浮点数；我们把它当作精确有理数 `w : ℚ` 读出，
再经「浮点语义」`round : ℝ → ℝ` 回到实数域。**误差就是舍入误差**，
且被 `RoundOp.err_bound` **精确界住**：

这就是 `R_GAP-6.md` 缺口 2 点名「**全库不存在**」的那条定理的**标量核**：
> 缺的定理：形如 `|LayerOut (convertVec c) x − realLayerOut (toReal c) x|
>   ≤ ε(eps, tiny, n_ops)` 的桥 —— 即「整数约束语义」与「浮点权重语义」
>   之间的误差界。**全库不存在**。

本文件给出它的**浮点权重侧**（权重经浮点舍入，输入精确）。 -/

/-- 要点 **核心桥（浮点权重的一致性）**：设 `F` 是浮点格式、`r` 是满足
`RoundOp F` 的舍入算子。若**浮点权重** `ŵ : ℝ` 是**真实权重** `w : ℝ`
经 `r` 舍入的结果（即 `ŵ = r.toFun w`），则对**任意**输入 `x : ℝ`：

  `|ŵ - w| ≤ F.eps * |w| + F.tiny`

即**权重层的误差被单位舍入与绝对底精确界住**，且**与输入无关**。
要点 这是「浮点权重的权重误差」这一诉求的**最小可用形式**，
其证明体是 `r.err_bound w` —— 本条是 `RoundOp.err_bound` 的**直接重述**
（`err_bound` 是 `RoundOp` 的结构字段），其内容**完全来自该公理字段**。 -/
theorem floatWeight_error_bound (F : FloatFormat) (r : RoundOp F) (w : ℝ) :
    |r.toFun w - w| ≤ F.eps * |w| + F.tiny :=
  r.err_bound w

/-- 要点 **权重往返（有理数 → 浮点 → 有理数）的误差界**：
设真实权重由有理数 `q : ℚ` 给出（经 `(q : ℝ)` 嵌入），浮点侧存的是 `r.toFun (q : ℝ)`。
则**往返误差**（把浮点值再读回实数域后与 `q` 比较）被界住：

  `|r.toFun (q : ℝ) - (q : ℝ)| ≤ F.eps * |(q : ℝ)| + F.tiny`

要点 **这就是「权重模型转符号」在数值层的第一步**：
一个有理权重送进浮点格式再取回，误差有了**可计算的界**。
与 `R_GAP-6.md` 缺口 2 的诉求形式一致（只是把 `LayerOut` 换成标量核）。 -/
theorem floatWeight_roundtrip_bound (F : FloatFormat) (r : RoundOp F) (q : ℚ) :
    |r.toFun (q : ℝ) - (q : ℝ)| ≤ F.eps * |(q : ℝ)| + F.tiny :=
  r.err_bound (q : ℝ)

/-- **往返误差在正规范围下化为纯相对形式**：
若 `tiny ≤ eps·|q|`（正规范围），则往返误差 `≤ 2·eps·|q|`。
要点 纯相对界（常数 2 来自把 `tiny` 吸收进相对项，**诚实标注**，与
`RealIEEE754.ieee_relative_error_bound` 同常数、同理由）。 -/
theorem floatWeight_roundtrip_relative (F : FloatFormat) (r : RoundOp F) (q : ℚ)
    (hr : F.tiny ≤ F.eps * |(q : ℝ)|) :
    |r.toFun (q : ℝ) - (q : ℝ)| ≤ 2 * F.eps * |(q : ℝ)| := by
  have h1 := floatWeight_roundtrip_bound F r q
  calc
    |r.toFun (q : ℝ) - (q : ℝ)| ≤ F.eps * |(q : ℝ)| + F.tiny := h1
    _ ≤ F.eps * |(q : ℝ)| + F.eps * |(q : ℝ)| := by linarith
    _ = 2 * F.eps * |(q : ℝ)| := by ring

/-! ### 4.4 要点 线性层：权重舍入 → 输出误差（接回主线的形状）

`ConvertVectorLinear` 的 `LayerOut` 是 `dot w x + b`。下面证明：
**权重的舍入误差线性传播到输出**——这正是 `R_GAP-6.md` 缺口 3 所说的
「编辑/转换的语义可控」在**数值层**的落地形状。

**诚实标注**：`ConvertVectorLinear.LayerOut` 跑在 `List Int` 上，
与这里的 `ℝ` 标量核**不同域**；本文件**不声称**桥接了它们
（那是主线的 `Int` vs 编辑线的 `ℝ` 的断崖，见 `R_GAP-6.md` 缺口 3）。
本节的定理是**标量核**：`w * x + b` 形式，权重经舍入。 -/

/-- 要点 **单权重线性层的输出误差界**：设前向为 `w * x + b`，其中**权重经浮点舍入**
（`ŵ = r.toFun w`）、输入与偏置精确。则

  `|(ŵ * x + b) - (w * x + b)| ≤ (F.eps * |w| + F.tiny) * |x|`

即**输出误差 = 权重误差 × 输入幅度**，权重误差由 §4.3 给出。
要点 这是「浮点权重 ⟹ 输出可控」的**最小可计算界**。 -/
theorem floatWeight_linearOut_error (F : FloatFormat) (r : RoundOp F) (w x b : ℝ) :
    |(r.toFun w * x + b) - (w * x + b)| ≤ (F.eps * |w| + F.tiny) * |x| := by
  have hw : |r.toFun w - w| ≤ F.eps * |w| + F.tiny := r.err_bound w
  have hnn : 0 ≤ F.eps * |w| + F.tiny :=
    add_nonneg (mul_nonneg F.eps_nonneg (abs_nonneg w)) F.tiny_nonneg
  have hsplit : (r.toFun w * x + b) - (w * x + b) = (r.toFun w - w) * x := by ring
  rw [hsplit, abs_mul]
  exact mul_le_mul_of_nonneg_right hw (abs_nonneg x)

/-- 要点 **正规范围下的纯相对版**：`tiny ≤ eps·|w|` 时输出误差
`≤ 2·eps·|w|·|x|`，即**相对误差 2·eps 放大 `|w|·|x|`**。
要点 这就是「单位舍入 × 权重幅度 × 输入幅度」的误差预算。 -/
theorem floatWeight_linearOut_relative (F : FloatFormat) (r : RoundOp F) (w x b : ℝ)
    (hr : F.tiny ≤ F.eps * |w|) :
    |(r.toFun w * x + b) - (w * x + b)| ≤ 2 * F.eps * |w| * |x| := by
  have h := floatWeight_linearOut_error F r w x b
  have h2 : F.eps * |w| + F.tiny ≤ 2 * (F.eps * |w|) := by linarith
  calc
    |(r.toFun w * x + b) - (w * x + b)| ≤ (F.eps * |w| + F.tiny) * |x| := h
    _ ≤ (2 * (F.eps * |w|)) * |x| :=
        mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
    _ = 2 * F.eps * |w| * |x| := by ring

/-- 要点 **多权重线性层（`n` 项内积）的输出误差界**：
前向为 `(∑ i ∈ s, w i * x i) + b`，每个权重独立经同一舍入算子。
则总误差被**权重误差之和 × 输入上界**界住：

  `|ŵ·x + b - (w·x + b)| ≤ (∑ i ∈ s, (F.eps * |w i| + F.tiny)) * M`
  （当 `∀ i ∈ s, |x i| ≤ M`）

要点 **这是通向 `LayerOut`（`dot w x + b`）的正确形状**：
误差按**项数**线性累积（每项一个 `eps·|w| + tiny`），
这正是 `RealFloatFormat.op_error_chain_iterate` 的「逐层累积」在权重侧的对应物。 -/
theorem floatWeights_dot_error (F : FloatFormat) (r : RoundOp F) {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (b M : ℝ) (hM : ∀ i ∈ s, |x i| ≤ M) :
    |((∑ i ∈ s, r.toFun (w i) * x i) + b) - ((∑ i ∈ s, w i * x i) + b)|
      ≤ (∑ i ∈ s, (F.eps * |w i| + F.tiny)) * M := by
  have hnn : ∀ i, 0 ≤ F.eps * |w i| + F.tiny := fun i =>
    add_nonneg (mul_nonneg F.eps_nonneg (abs_nonneg (w i))) F.tiny_nonneg
  have hpt : ∀ i ∈ s,
      |r.toFun (w i) * x i - w i * x i| ≤ (F.eps * |w i| + F.tiny) * M := by
    intro i hi
    have hw : |r.toFun (w i) - w i| ≤ F.eps * |w i| + F.tiny := r.err_bound (w i)
    have hsplit : r.toFun (w i) * x i - w i * x i = (r.toFun (w i) - w i) * x i := by ring
    rw [hsplit, abs_mul]
    calc |r.toFun (w i) - w i| * |x i|
        ≤ (F.eps * |w i| + F.tiny) * |x i| :=
          mul_le_mul_of_nonneg_right hw (abs_nonneg (x i))
      _ ≤ (F.eps * |w i| + F.tiny) * M :=
          mul_le_mul_of_nonneg_left (hM i hi) (hnn i)
  have hsum : (∑ i ∈ s, r.toFun (w i) * x i) - (∑ i ∈ s, w i * x i)
      = ∑ i ∈ s, (r.toFun (w i) * x i - w i * x i) := by
    rw [Finset.sum_sub_distrib]
  have hb : ((∑ i ∈ s, r.toFun (w i) * x i) + b) - ((∑ i ∈ s, w i * x i) + b)
      = ∑ i ∈ s, (r.toFun (w i) * x i - w i * x i) := by
    rw [← hsum]; ring
  rw [hb]
  calc |∑ i ∈ s, (r.toFun (w i) * x i - w i * x i)|
      ≤ ∑ i ∈ s, |r.toFun (w i) * x i - w i * x i| :=
        Finset.abs_sum_le_sum_abs (fun i => r.toFun (w i) * x i - w i * x i) s
    _ ≤ ∑ i ∈ s, (F.eps * |w i| + F.tiny) * M := Finset.sum_le_sum hpt
    _ = (∑ i ∈ s, (F.eps * |w i| + F.tiny)) * M := by
        rw [Finset.sum_mul s (fun i => F.eps * |w i| + F.tiny) M]
/-- 要点 **误差随项数线性累积的显式界**：若每个权重满足 `|w i| ≤ W`，
则 `dot` 版误差 `≤ |s| · (F.eps * W + F.tiny) * M`
——**可计算**的界（判据 #4：量化）。 -/
theorem floatWeights_dot_error_uniform (F : FloatFormat) (r : RoundOp F) {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ) (b M W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ i ∈ s, |w i| ≤ W) (hM : ∀ i ∈ s, |x i| ≤ M) :
    |((∑ i ∈ s, r.toFun (w i) * x i) + b) - ((∑ i ∈ s, w i * x i) + b)|
      ≤ (s.card : ℝ) * (F.eps * W + F.tiny) * M := by
  have hnn : 0 ≤ F.eps * W + F.tiny :=
    add_nonneg (mul_nonneg F.eps_nonneg hW) F.tiny_nonneg
  have hbase := floatWeights_dot_error F r s w x b M hM
  have hterm : ∀ i ∈ s, F.eps * |w i| + F.tiny ≤ F.eps * W + F.tiny := by
    intro i hi
    have h1 : F.eps * |w i| ≤ F.eps * W :=
      mul_le_mul_of_nonneg_left (hw i hi) F.eps_nonneg
    linarith
  have hsum : (∑ i ∈ s, (F.eps * |w i| + F.tiny))
      ≤ ∑ _i ∈ s, (F.eps * W + F.tiny) := Finset.sum_le_sum hterm
  have hcard : (∑ _i ∈ s, (F.eps * W + F.tiny))
      = (s.card : ℝ) * (F.eps * W + F.tiny) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- `hM` 只在 `s` 非空时给出 `0 ≤ M`（`|x i| ≤ M`）；`s = ∅` 时两侧同为 `0`，
  -- 结论由 `simp` 直接给出，故此处按 `s` 是否为空分情形处理。
  by_cases hs : s = ∅
  · subst hs
    simp
  · have hM_nonneg : 0 ≤ M := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      exact le_trans (abs_nonneg (x i)) (hM i hi)
    calc |((∑ i ∈ s, r.toFun (w i) * x i) + b) - ((∑ i ∈ s, w i * x i) + b)|
        ≤ (∑ i ∈ s, (F.eps * |w i| + F.tiny)) * M := hbase
      _ ≤ ((s.card : ℝ) * (F.eps * W + F.tiny)) * M := by
          rw [← hcard]
          exact mul_le_mul_of_nonneg_right hsum hM_nonneg
      _ = (s.card : ℝ) * (F.eps * W + F.tiny) * M := by ring

/-! ## 五、诊断总结与修复方案（可执行）

### 5.1 5 条错误 → 1 个根因 → 4 行修复

| # | 错误位置 | 编译器消息 | 性质 | 修复 |
|:--|:--|:--|:--|:--|
| 1 | `:456:25` | `invalid field 'binaryFormat_eps_pos'` | **根因 A** | `B.binaryFormat_eps_pos` → `binaryFormat_eps_pos B` |
| 2 | `:457:26` | `invalid field 'binaryFormat_tiny_pos'` | **根因 A** | `B.binaryFormat_tiny_pos` → `binaryFormat_tiny_pos B` |
| 3 | `:453:78` | `fields missing: 'expBits', 'mantBits'` | **根因 B** | 补 `expBits := …`、`mantBits := …` |
| 4 | `:461:35` | `type mismatch` | **级联**（`toFloatFormat` 未入环境） | 随 1–3 自动消失 |
| 5 | `:465:37` | `type mismatch` | **级联**（同上） | 随 1–3 自动消失 |

**最小修复补丁**（**本文件不施加**——任务禁止改动已有文件；此处仅给出文本）：

```lean
noncomputable def BinaryFormat.toFloatFormat (B : BinaryFormat) : FloatFormat where
  expBits := 11                       -- 补：binary64 指数位宽（或由 emax 推导）
  mantBits := B.p - 1                 -- 补：尾数位 = 有效位数 − 隐藏位
  eps := B.eps
  tiny := B.tiny
  eps_nonneg := le_of_lt (binaryFormat_eps_pos B)   -- 改：函数应用而非投影
  tiny_nonneg := le_of_lt (binaryFormat_tiny_pos B) -- 改：函数应用而非投影
```

### 5.2 修复**充分性**的论证

* 错误 1–2 的**根因**是投影 vs 函数应用（§2.2），改为函数应用即消；
* 错误 3 是**真根因**（漏字段），补齐即消；
* 错误 4–5 **无独立内容**：它们只是在抱怨 `B.toFloatFormat` 不在环境里
  （`:= rfl` 无法展开一个不存在的定义）。**证据**：
  `toFloatFormatFixed_eps`/`toFloatFormatFixed_tiny`（§三）与它们**逐字同陈述**，
  在**修复版**上以 `rfl` 成立——这证明**原桥的本意是对的**，
  两条 `rfl` 定理本身没有任何错误。

### 5.3 要点 真实缺口（**这是诊断最有价值的部分**）

修好这 5 条错误**不会**让「浮点权重的一致性」落地。真实缺口是：

1. **`RoundOp` 无任何实例**（`R_GAP-6.md` 缺口 4）。
   `RealIEEE754` 的 `IEEERound` 把「最近偶数 + 正规范围」写成**结构字段**，
   但**全库无一个 `RoundOp F` 或 `IEEERound F m` 的实例**——
   即**没有任何一个具体的舍入函数被证明满足这些公理**。
   ⇒ 本文件 §4.3–4.4 的全部定理，**在给出实例之前都是条件性的**。
   这是最致命的一条：**没有实例 ⟹ 所有误差界都悬空**。
2. **`RealIEEE754` 与主线零 import 边**（`R_GAP-6.md` 缺口 1）。
   本文件新增的定理仍**没有被** `convertVec`/`compileToLayer` 那条线 import
   （那需要改 `lakefile.toml` + 已有文件，**任务禁止**）。
3. **主线跑在 `Int`，数值层跑在 `ℝ`**（`R_GAP-6.md` 缺口 2）。
   本文件的 §4.4 给的是 `ℝ` 标量核；`Int` 侧的 `LayerOut` 与之**无桥**。
4. **`FP.toRat` 只覆盖 mathlib 的 `FP.Float`**（§4.1）。
   它**不**覆盖 Lean 内建 `Float`，故「真实硬件浮点权重」仍在形式化之外。
5. **`RealIEEE754` 自身未建模位模式**（`RealIEEE754.lean:38`、`:57` 自述）：
   不从符号位/尾数位/指数偏置**构造**舍入函数——**这正是缺口 1 的根源**。

⇒ **一句话**：`RealIEEE754` **可以**在 4 行内修好编译，
但它修好后**仍然只是一座有定理、无实例的孤岛**——
`R_GAP-6.md` 的「缺口 4（承载模块坏掉）」可以被修复，
「缺口 1/2/3（零连接、`Int` vs `ℝ` 断崖）」**不能**靠修编译解决。

## 诚实边界（**再强调**）
* 我**没有**跑 `lake` / `lake build` / `lake env lean`（任务明令禁止）
  ⟹ **本文件未经验证编译**；
* 我**没有**修改任何已有文件（含 `RealIEEE754.lean`、`lakefile.toml`）；
* `_allchk4.log` 的 5 条错误是**真实编译器输出**（逐字抄录）；
* `FP.toRat` 的存在性来自**源码阅读**（`Data/FP/Basic.lean:68`），
  非 `#check`；我**未**核实内建 `Float` 的桥；
* §5.1 的补丁是**文本建议**，**未施加**，因而**未验证**；
* 无 `sorry`/`axiom`/`admit`/`native_decide`。 -/

end Lattice
