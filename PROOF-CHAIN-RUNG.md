# LATTICE 四跳证明链（PROOF-CHAIN-RUNG）

> 本文件回答的不是「谁 import 谁」（那是 `gov/PROOF-CHAIN.md`，1.29 MB 的引用图的本职），
> 而是：**每一跳的义务是什么、由谁承担、前提由谁供给、前提是否承重**。
>
> 第四问给出的是**否证实验的结果**，不是判断。凡写「不承重」处，都有一次
> `lake env lean` 的实测作为依据（脚本 `agent-tmp/p13_loadbearing.py`、
> `p13_loadbearing2.py`，探针文件编译后即删除）。

## 0. 链条与层级

```
L0 数据  ⇄  L1 token  ⇄  L2 符号模型  ⇄  L3 权重
```

正向（编译）：L2 → L3，`约束损失`、`数据合成`、`结构化初始化`。
逆向（提取）：L3 → L2，`验证`、`修正`、`再注入`。
闭环：`验证回路`。

**本库只声称符号⇄权重这一跳为难点**（其余是成熟技术），因此下文对
L0⇄L2 只用一节概述，把四问集中在 L2⇄L3 与闭环。

---

## 1. 跳 L0 → L1：数据 → token

### 1.1 义务

`tokenize : List Char → Option (List CharToken)`，且 `tokenize` 与 `detokenize`
在商掉空白折叠后互逆。

### 1.2 承担者

`Lattice/Lift/RealTokenization.lean`（34 个声明），核心三条：

| 定理 | 内容 |
|:--|:--|
| `tokenize_never_none` | 对任何输入都存在 token 序列 |
| `detokenize_tokenize_on_quotient` | 在 `SameTokens` 的等价类上左逆成立 |
| `tokenize_detokenize_galois` | 两侧互为 Galois 连接 |

### 1.3 前提供给

全部由本文件内证明，向上只依赖 Mathlib。
代价是一条**已证否**的结论：`tokenize` **不是单射**（`tokenize_not_injective`，
反例 `tokenize_collision`）—— 这是空白折叠的必然后果，属于设计而非缺陷。

### 1.4 承重性

`tokenize_never_none` 的前提 `l ≠ []` 系列不可省（`lookupTok_ne_none`、
`bestPrefix_ne_none` 都以此为前提），因为空输入上这些函数返回 `none`。

**结论：这一跳成立，且逆问题已被如实登记。**

---

## 2. 跳 L1 → L2：token → 符号模型

### 2.1 义务

把 token 序列解码成符号约束（`decodePayload`）。

### 2.2 承担者

无独立的承担者。`Lattice/Geo/Pipeline.lean` 里 `decodePayload` 出现在
`token_to_weight` 与 `token_to_loss` 的**前提**中，但这个前提**不承重**（见 §3.4）。

### 2.3 结论

**这一跳目前没有承重载体。** 它不是「未证」，而是「被证否为不承重」：
解码结果在两条定理的结论里一次都没出现。

---

## 3. 跳 L2 → L3：符号 ⇄ 权重（**本项目的唯一难点**）

这一跳有四层载体，性质完全不同，必须分开陈述。

### 3.1 第 1 层：`Compiler` 结构（正向编译的义务）

**义务。** 给定 `C : Compiler P W`，有
`∀ p x, satP p x → satW (C.compile p) (C.encode x)`（字段 `sound`）。

**承担者。** 结构字段本身。派生定理：
`compileProgram_sound`、`compileProgram_models`、`compileProgram_append`。

**前提供给。** 每个 `Compiler` 实例自己提供。

**实例普查（实测）。** 全库只有 **1 个**实例：`Lattice.Geo.Compile.geoCompiler`。它的内容：

```lean
encode  := id                     -- 输入翻译是恒等
satP    := fun c pts => EqConstraint.poly c pts = 0
satW    := fun L pts => L pts = 0
compile := fun c => EqConstraint.loss c
sound   := by intro c x hx; unfold EqConstraint.loss; rw [hx]; ring
```

⇒ `sound` 是**定义等式**（`loss = poly²`，`poly = 0` 时为零），不是实质论证。
`encode := id` 意味着一端（权重侧的输入语言）与另一端相同。

**承重性。** 字段 `sound` 是这条定理的**全部内容**：删掉它，剩余的
`compileProgram_*` 定理只是 `List.map` 上的恒等式。这不是缺陷，而是结构设计的本意
（「字段即义务」），但**不能把它当成「已经证明了编译保语义」**。

### 3.2 第 2 层：`Representation` 结构（逆向提取的义务）

**义务。** `R.roundtrip : ∀ p, R.extract (R.compile p) = p`（字段）。

**承担者。** 字段。派生：`extract_compile`、`compile_injective`、
`roundtrip_idempotentOn`、`roundtrip_iterate`、`loop_fixed_point`。

**实例普查（实测）。2 个：**

| 实例 | 位置 | 性质 |
|:--|:--|:--|
| `ofEquiv` | `Lift/Extraction.lean` | 由 **双射** `P ≃ W` 构造 —— `compile`/`extract` 就是 `e` 及其逆 |
| `seqRepresentation` | `Geo/SeqRepresentation.lean` | 几何序列侧的具体实例 |

⇒ `ofEquiv` 说明：只要两侧存在双射，`Representation` 就自动成立。
这对「提取」的意义是**同构意义下的提取**，对「非可逆编码」（真实权重的量化、
非线性层）**没有覆盖**。

**承重性。** `representable ⇔ 存在双射`。真实难点在于权重侧不是符号侧的双射像，
而这一层正是靠假设双射来绕开它。

### 3.3 第 3 层：`Ladder` 结构（端到端四跳）

**义务。** 把 L0→L1→L2→L3 串起来。六个字段：`l0l1 : Tokenizer Data Tok`、
`l1l2 : Tokenizer Sym Tok`、`l2l3 : Sym → W`、`satSym`、`satW`、
`l2l3_sound : ∀ s, satSym s → satW (l2l3 s)`。

注意 `l1l2` 的类型是 `Tokenizer Sym Tok`：在 `Ladder` 里 L1→L2 被建模成**一个 tokenizer**。

> **第 41 轮更正**：此处原写「L1→L2 这一跳没有独立载体，它被吸收进 tokenizer 结构」。
> 那是**错的**——第 14 轮已在 `Lift/L1L2Roundtrip.lean` 给出独立载体：
> `decodePayload_encodeForm : decodePayload n (encodeForm c).payload = some c`。
> `Ladder` 选择用 `Tokenizer` 表达这一跳，是**结构设计**，不是**因为没有载体**。
> 两者的区别重要：前者是选型，后者是无能力。

**实例普查（实测）。`Ladder` 的实例数为 1：**

| 实例 | 位置 | L0→L1 | L1→L2 | L2→L3 |
:--|:--|:--|:--|:--|
| `linearLadder` | `Geo/LadderInstance.lean` | 恒等 | `encodeForm`/`decodePayload`（往返定理） | 线性形式 ↦ 残差平方 |

⇒ 端到端结构**已有第一个实例**，`ladder_forward` 等定理因此有了内容。

**但这个实例的边界必须一起说**：`W := ℝ` 取的是**损失值**而非权重参数；
`Tok := ℝ` 使 L0→L1 退化为恒等；`Sym` 取线性形式而非完整 `EqConstraint`。
它是**可做的最强最小实例**，不是「完整链路已通」。

### 3.4 第 4 层：`Geo.Pipeline`（几何侧的具体一步）

**义务。** 线性形式约束与其损失的关系。

**承担者。** `token_to_weight`、`token_to_loss`。

**承重性（实测）。不承重。**

```lean
theorem token_to_weight (c : LinearForm ℝ n) (pts : ℕ → Pt n) (rs : List ℝ)
    (_hdec : decodePayload n rs = some c) : ...     -- `_hdec` 以下划线开头
```

删掉 `_hdec` **并且删掉 `rs` 参数**后，同一结论仍然类型检查通过（exit 0）。
Lean 自己也报 `unused variable 'h'`。

⇒ 这两条定理的结论只讲一个线性形式的两个性质（约束成立 ⟺ 求值 = 0；求值 = 常数项 + 系数和），
**与 token 层无关**。「四跳」在此退化为「token 层与权重层的名字都被写过一遍」。

---

## 4. 闭环：验证回路

### 4.1 义务

修复算子在验证回路中收敛：从任一点出发，有限步后满足约束。

### 4.2 承担者

`Lattice/Geo/Loop.lean` 的 `loop_converges`、`loop_converges_in_one`；
`Lattice/Geo/ClosedLoop.lean` 的 `conj_loop_fixed_point`；
`Lattice/Lift/Extraction.lean` 的 `loop_fixed_point`、`loop_fixed_point_stable`。

### 4.3 前提供给

`Lattice.Core.Repair` 的 `progress`（`Nat` 度量）与
`Lattice.Core.RepairWF` 的 `progress_on_wf`（任意良基度量，本轮由 `progress'` 改名）。

### 4.4 承重性与边界

`loop_converges` 的度量是 `if satisfied then 0 else 1`，**值域只有 `{0,1}`**。
因此它只能说明「一步之内到达」，不能表达多步迭代。这一条已登记为 slot
slot `geo.loop.convergence_is_single_step`（状态 `.weakened`），且
`loop_converges_in_one` 是它的锋利形式——**弱化已到头**。

⇒ 闭环在「一步收敛」的意义上成立；多步收敛需要一个新的修复算子（单步不解决的谓词）。

---

## 5. 汇总：四跳的真实状态

| 跳 | 义务 | 承载结构 | 实例 | 承重性 | 判定 |
|:--|:--|:--|--:|:--|:--|
> **本表第 41 轮按实测重写。** 此前六行里五行已过时——第 14–34 轮的工作
> 逐条改变了它们，而表没有被随之更新。旧判定保留在「此前判定」列，
> 以便看出变化，而不是抹掉。

| 跳 | 义务 | 承载结构 | 实例 | 承重载体（实测） | 判定 | 此前判定 |
|:--|:--|:--|:--|:--|:--|:--|
| L0→L1 | tokenize/detokenize 互逆 | `Tokenizer.roundtrip` | 多个 | `RealTokenization.tokenize_detok` | ✅ **成立**（单射性已证否，属设计） | 同 |
| L1→L2 | 解码成符号约束 | `L1L2.decodePayload` | — | **`L1L2Roundtrip.decodePayload_encodeForm`** | ✅ **成立**（往返已证） | ❌ 无承重载体 |
| L2→L3 | 编译保语义 | `Compiler.sound` | **2** | **`NonIdentical.projectCompiler`**（`encode ≠ id`） | ✅ **有非恒等实例** | ⚠️ 只有恒等 encode |
| L3→L2 | 提取回符号 | `Representation.roundtrip` / `LossyRep.semEq` | **4** | **`RoundingBackend.roundingLossy`**（`compile` 非单射） | ✅ **覆盖非可逆编码** | ⚠️ 靠假设双射 |
| L0→L3 | 端到端 | `Ladder.l2l3_sound` | **1**（`linearLadder`） | 无（字段即内容） | ⚠️ **实例存在，但 `W` 取损失值** | 同 |
| 闭环 | 收敛 | `Repair` 三义务 | 多个 | **`RepairMultistep.countdown`**（测度无界） | ✅ **多步可表达，且界紧** | ⚠️ 多步未表达 |

### 3.5 重写后的读法

| 状态 | 跳数 |
|:--|--:|
| ✅ 成立且有实质载体 | **5**（L0→L1、L1→L2、L2→L3、L3→L2、闭环） |
| ⚠️ 有一处如实标注的局限 | **1**（L0→L3：`W` 取损失值而非权重参数） |

**唯一的 ⚠️ 是 `linearLadder` 的 `W := ℝ`。** 这不是缺证明，而是缺一个
**权重参数类型**——它与 `Slots` 的 `core.semantics.external_bridge`
（TorchLean 需 Lean ≥ 4.26）是同一个阻塞。

⇒ **链路的六跳里，五跳已有承重载体；第六跳的障碍是工具链，不是数学。**

**一句话结论**：结构层已经齐备（每个义务都有精确陈述与定理），
但**实例层几乎为空**——唯一有实质内容的实例是 L0⇄L1，其余三跳的实例要么是恒等/双射
构造，要么不存在。这是「符号⇄权重」难点的准确位置。

---

## 6. 本文件与生成物的分工

| 文件 | 回答什么 | 生成方式 |
|:--|:--|:--|
| `gov/PROOF-CHAIN.md`（1.29 MB） | 谁 import 谁 | 脚本生成 |
| `gov/PROOF-CHAIN-GEO.md` | 几何侧引用图 | 脚本生成 |
| **本文件** | 义务/承担者/前提供给/**承重性** | **人工维护**，否证实验可重跑 |

本文件必须人工维护，因为它记录的否证实验是**特定时点的一次实测**，
脚本无法判断「某个前提是否承重」——只能记录一次检验及其结果。
每次改动承重结构时，应重跑 `agent-tmp/p13_loadbearing2.py` 并更新 §3.4 与 §5。
