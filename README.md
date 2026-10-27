# LATTICE

**Representation Lattice for Symbolic↔Weight Training**（表示谱系格）
符号 ⇄ 权重双向转换的训练 / 后训练框架，Lean 4 证明保证正确性。

> **定位**：**符号 ⇄ 权重表示的认证转换层**（representation lattice）——
> 给定符号约束，给出**带 Lean 4 证明**的权重构造、提取与修复方案。
> **不实现**引擎、模型与训练框架；**可插入**现有训练栈，不绑定任何厂商或框架。
>
> **这个项目该用什么标准衡量**，见 [`PARADIGM.md`](PARADIGM.md)。
> 简言之：按「训练框架」衡量的分数（约 3%）**不是它该被打的分**；
> 按它自己的范式（表示格，约 40%）才是有意义的衡量。
>
> **状态**（下列数字全部由门禁守卫，见 `CONVENTIONS §6`）：
>
> | 指标 | 值 | 守卫 |
> |:--|--:|:--|
> | Lean 模块 | 788 | `audit_counts.py` |
> | 定理 / 引理 | 8291 | `audit_counts.py` |
> | 层文件数 Core/Lift/Geo/Lib | 18 / 55 / 92 / 605 | `audit_counts.py` |
> | 设计不变量 | 8（`I1`–`I8`） | `gate.py` |
> | 检查器注册项 | 56（38 门禁 + 18 报告器） | `audit_counts.py` |
> | **未清欠账** | **0** | `Slots.lean` 的 `decide` |
> | **永久边界** | **3** | 同上；因数学事实或外部工具链，本库无法关闭 |
> | 已登记否证 | 285 | `check_refutation_census.py` |
>
> **定理计数的口径（必须连同数字一起引用）**：排除 `Reference/`；**剥除注释**（docstring 里提到的 `theorem` 不计）；允许 `@[...]` 属性与 `private`/`protected`/`noncomputable` 修饰符出现在关键字之前。
> 同一测量在不同口径下曾给出 **7,919 / 8,011 / 8,068** 三个数，**三者都不是错的，错的是没有说明口径**。
> 详见 `audit_counts.total_theorems` 的 docstring。
>
> **否证计数的口径**：`theorem`/`lemma` 的结论以 `¬`、`not `、`→ False` 开头，或形如 `¬ ∃ …`。
> 裸 `∃ …` **不算**否证——那是正面存在性定理（第 56 轮修正，曾因此多计 109 条）。
> 详见 `check_refutation_census.is_negative`。
>
> **入口**：想用它 → [`USAGE.md`](USAGE.md)（每个代码块可编译）；
> 想知道它做不到什么 → [`REFUTATION-CENSUS.md`](REFUTATION-CENSUS.md)；
> 当前路线 → [`ROADMAP-v11.md`](ROADMAP-v11.md)。

---

## 0. 这个仓库是什么

这是 LATTICE 的**第二代目录结构**（`lattice-new`）。它把第一代（`lattice/lean` + `lattice/zero`）
的全部源代码按分层重新安置，并修掉了第一代在结构上的四处结构性缺陷：

| 第一代的缺陷（实测） | 本代的处置 |
|:--|:--|
| **582 个影子副本**：`zero/Zero/Reference/Legacy`(437) 与 `_archive/LegacyConflicted`(145) 是 `lean/` 的改名副本，逐行比对**内容差异为 0** | **不复制**。同一源码只有一处。 |
| **581 条 roots 显式列举**，两次合并必冲突；25 个文件不在构建里 | **roots = 1**（聚合入口 `Lattice`），按层聚合 |
| **521 个文件共用 `namespace Lattice`**，30 组限定名冲突，`Lattice::Expr` 出现在 4 个文件 | 命名空间承载分层：`Lattice.<层>.<领域>.<模块>`，冲突组按模块隔离 |
| **治理靠人写的 1.97 MB 登记表**，可漂移且无门禁 | 未证但承重的命题写成显式前提 + `Lattice/Slots.lean` 登记，由 `gov/gate.py` 的 I6 机械检查 |

第一代的两个工程（`lattice/lean`、`lattice/zero`）**保留、未删除、仍可构建**，作为回退基线。

---

## 1. 核心思想

**一条端到端的表示链路**：`数据 ⇄ token ⇄ 符号模型 ⇄ 权重`

```
                    ┌────────── 神经管线（常规，可绕过符号）──────────┐
                    ▼                                             │
  L0 数据 ────────► L1 token ────────► L3 权重（模型）
  原始语料/知识/     文本离散化          神经网络参数
  程序/传感器流        │                  ▲     │
                      │  L1⇄L2          │     │ L3⇄L2（转换层）★ 难点
                      ▼                  │     ▼
                  L2 符号模型（规则/约束/谓词/DSL，结构化知识）
                       ▲    实现在 Lattice/Core 上
                       │
                  符号引擎（约束 / 表达式 / 惩罚嵌入 / 修复回路）
```

- **正向（训练）**：把符号知识注入权重——符号约束作损失项 / 数据合成 / 结构化初始化；
- **逆向（后训练 / 验证 / 修复）**：把权重行为提取回符号——验证、修正、再注入；
- **三条路径统一进链路**：神经捷径（数据→token→权重）、符号捷径（知识→符号模型）、
  完整链路（数据→token→符号→权重）。

### 1.1 「可逆」必须分级陈述

本项目已用机器验证**证否了无条件**的说法：

| 层 | 可逆性 | 机器验证 |
|:--|:--|:--|
| **对象层**（约束 ↔ 层） | 成立 **双射** | `flatten_injective` / `Lattice.Lib.Lift.*` |
| **参数层** | **单射，非同构** —— 存在 `c ≠ c'` 语义逐点相同 | `reversibility_boundary` |
| **语义层** | **不可逆** —— 存在 `w ≠ w'` 表示同一函数且都是编译结果 | `semantic_not_injective` |
| **两层同时** | **不可能** —— 兼顾两层的提取器不存在 | `no_extractor_preserves_both` |

反例：`revC` 与 `scaleVec revC 2`（整数缩放）逐点语义等价、参数不同。
完整审计见 [`archive/REVERSIBILITY.md`](archive/REVERSIBILITY.md)。

---

## 2. 目录结构

```
lattice-new/
├── lakefile.toml           # roots = 1；复用已编译 mathlib，无需网络
├── lean-toolchain          # leanprover/lean4:v4.14.0
├── Lattice.lean            # 唯一公开聚合入口
├── Lattice/
│   ├── Core/      18       # 语言层：语法 / 语义 / 满足关系 / 修复 / 权重接口
│   ├── Lift/      55       # 链路层：L0⇄L1⇄L2⇄L3 全部环节 + zero 的抽象接口
│   ├── Slots.lean  1       # 空位层：未证但承重的命题，只声明不证明
│   ├── Geo/       92       # 约束几何与精确惩罚
│   ├── Lib/      605       # 应用库，按主题（建立在链路层之上）
│   │   ├── Architectures  66    Attention       36    Chain         69
│   │   ├── Compiler       45    Concentration   37    Convex        25
│   │   ├── Editing        69    FCA             15    InfoTheory    26
│   │   ├── LearningTheory 46    LinearAlgebra   33    Meta           8
│   │   ├── Optim          60    Quantization    18    Linear         8
│   │   ├── Lift            8    Penalty          2
│   └── Reference/          # 证据资产，不参与构建
│       └── LvFormal/  121  # Lv-00 上游（唯一源）
├── gov/                    # 门禁与审计（8 条不变量 + 56 项检查 + 反应性自检）
├── archive/                # 冻结档案，内容不改（见 §5）
└── .github/workflows/      # CI：门禁优先，构建必需
```

> **分层是在迁移中修出来的，不是设计时拍出来的。** 迁移前，链路的四个环节
> （`tokenize` / `L1Bridge` / `decode` / `compileToLayer`）物理上全在 `Lib/` 里，
> 于是每条"端到端"定理按 I5 的层判据都只触及 **1 层**。把链路移入 `Lift/` 之后，
> 端到端定理才真正跨层。反过来，9 个"用了链路层"的文件（`ConvertLinear` 等）被移回
> `Lib/`——它们是链路的**使用者**，不是链路的**环节**。两个方向都收干净后 I4、I5 才同时为绿。
>
> `Lib/Lift/` 留下的 8 个模块同样有依据：它们 import 了 `Lib/` 的其他主题，
> 因此按 I4 不能住在 `Lift/` 里。

### 2.1 分层铁律（由 `gov/gate.py` 强制）

1. `Lattice/Core` 不得 import 任何上层；
2. 同一语义概念只允许一处定义（I3）；
3. `Lattice/Lift` 只组合，不新增语义（I4）；
4. `Lattice/Slots` 只声明命题，不证明命题（I6）；
5. **内核**中任何 `axiom` / `sorry` / `admit` / `opaque` 为 0（I1、I2）；
6. 标为 `EndToEnd` 的定理必须真的用到它声称连接的每一层（I5）。

> **「逃逸为 0」的精确范围（第 57 轮补注）**：上述 I1/I2 覆盖**内核**——
> `Lattice/` 下除 `Reference/` 外的全部模块，加上仓库根的 7 个根模块。
>
> **不在范围内**：`Lattice/Reference/`（121 个文件）里有 **68 处 `admit` 与 1 处 `axiom`**（**代码级**，剥除注释后）。
> 那是**档案化的历史证据**，`Reference/` 里的东西不参与构建，`gate.py` 显式跳过它。
> 「全树 0 逃逸」是**错的**说法；正确的说法是「**内核 0 逃逸，`Reference/` 冻结**」。
>
> 此前有文档写「`Reference/` 有 68 处 sorry」，实测是 **68 处 `admit`**——审计记录的另一个数字漂移。

---

## 3. 三个核心决策

1. **符号模型直接实现在 `Lattice/Core` 上**——它是符号模型的宿主，不是中间层。
2. **真正的难点 = 转换（符号⇄权重）**——其余都是成熟技术。
3. **用 Lean 4 形式化证明转换的正确性**——把已验证的编译链延伸到权重。

### 3.1 关于编译链：原文路线 vs 已实现路线

目标原文写的是 `lvLang → IR → Cv00 → 权重`。**这三段的状态不同，必须分开陈述**
（否则就是把一个断链写成通链）：

| 段 | 状态 | 证据 |
|:--|:--|:--|
| lvLang → IR | ⚠️ 部分 | `compile_constraint` 有 12 处 `\| _ => none` |
| IR → Cv00 | ❌ 断 | `CompilerCorrectness` 全文 0 次出现 `Cv00` |
| Cv00 → 权重 | ❌ 不存在 | LvFormal 中提到 `Weight` 的文件 0 个 |
| **IR → 权重（已实现路线）** | ✅ | `Lattice.Geo.IRBridge.compileIR_sound` + 9 条 `compileIR_*_exact` |

**本库走 IR → 权重的短路径，绕过 Cv00。** 理由（不是省略，是论证）：

- Cv00 是虚拟机：它执行程序、不产生权重。把它接到权重需要**先发明**一个映射，
  而发明映射是设计、不是形式化；
- 补齐 `exec_stmt`（目前只实现 2/9 个构造子）等于实现一个引擎，与「不实现引擎」的定位冲突；
- Lv-00 的 121 个模块中 **56 个构建失败**，修它们只是让一条自相矛盾的链更完整。

断点与复现：`gov/check_g7.py`（已接入 `verify_all.py`）。

### 3.2 四条靶定理的载体

| 定理 | 命题 | 载体 |
|:--|:--|:--|
| T1 | 编译保语义 | `geo_compile_preserves` / `Lattice.Lib.Lift.*` |
| T2 | 约束嵌入可靠 | 逐载体的精确性定理（见下方边界说明）；**一般情形已证否** |
| T3 | 提取等价 | `flatten` 双射 + `semantic_not_injective` |
| T4 | 回路收敛不破坏语义 | `loop_converges` / `Repair.progress` / `conj_loop_fixed_point` |

**T2 的边界必须一起说**：`poly` 层在**非退化时**成立，而那个条件的生产者目前只有垂直约束一类。
写成「T2 无条件成立」就不完整。更根本的是，**T2 的无条件形式是假命题**——见 §3.3。

### 3.3 从「精确」转向「逼近精确」——本库的方向性决定

> 这一节记录一个**已经用机器验证证伪**的方案，以及它被替换成什么。
> 它不是未来工作，是当前立场的说明。

**原方案（精确嵌入）**：把符号约束嵌入为损失，使
*局部极小 ⟺ 约束成立*（`PenaltyExact`：`IsLocalMin (loss p) x → Sat p x`）。
若成立，训练收敛就等于约束成立，且没有余量。

**这个方案在一般情况下不成立，且已被证否。**
`Lattice.Lift.PenaltyEmbedding.sound_not_exact` 给出反例：常数正损失 + 恒假谓词
（`constEmbedding`），零损失层（A 层）**空洞地**成立，局部极小层（B 层）**处处失败**
（常数函数在每一点都是极小）。⇒ **A 层推不出 B 层，嵌套是严格的。**
这不是「还没证出来」，是**命题为假**。

精确性只在若干具体载体上成立，逐条列出（都在库里，可 `#check`）：

| 载体 | 定理 | 条件 |
|:--|:--|:--|
| `n = 1` 标量 | `Lattice.Lib.Linear.Penalty.sq_penalty_exact` | Fermat 路线 |
| 任意 `n`，对角约束 | `Lattice.Lib.Linear.PenaltyPerturbN.sq_penalty_exact_finN` | 扰动论证 |
| 满射权重矩阵 | `Lattice.Lib.Linear.PenaltyMatrix.sq_penalty_exact_matrix` | 沿满射见证一步归零 |
| 垂直约束 | `Geo.Nondegenerate.perpResid_localMin_of_nondegenerate` | 非退化 |

**⟹ 新方案：放弃「精确」，改为「逼近精确」，量化误差界并把它压小。**

这是方向的改变，不是措辞的改变。三条含义：

1. **正确性陈述从等价降为带界蕴含**：不再声称「最小点满足约束」，而是
   「**在 ε 邻域内**满足约束」或「违反量 ≤ ε」，其中 ε 由误差界显式给出。
2. **工作的重心从「证明精确」移到「压缩 ε」**：把一个界变紧，与证明一个等价命题
   是同一个量级的工作量，但它**是可达的**——精确版不可达。
3. **原精确命题作为极限情形的检验**：若某个 ε 能压到 0 而不需要额外假设，
   那就与该载体的精确性定理冲突，说明界不紧。这是自动的一致性检验。

**已有的可用部件**（都是现成定理，不需要新证明）：

| 部件 | 定理 | 它给的界 |
|:--|:--|:--|
| 采样验证 → 全域 | `Lattice.Lift.RealVerifierReliable.verifier_reliable_clean` | `ε₀ + (L+L')·δ` |
| 训练收敛 → 违背概率 | `Lattice.Lift.RealRandomVerify`（马尔可夫） | `μ{f ≥ ε} ≤ ε` |
| 量化链 → 端到端误差 | `Lattice.Lib.Quantization.RealQuantizedError.quantized_chain_error_lipschitz` | `Σ (∏ Ls)·εᵢ` |
| 浮点累加 | `RealMixedPrecision.accumulation_error_bound` | `2·n·eps·M` |
| 编译链浮点误差 | `RealConversionStabilityFloatBounds.ce_compile_error_bound` | 逐构造子 |

**尚未做的事（必须说清楚）**：

- 这些界目前**彼此独立**，没有任何一条把「惩罚嵌入的局部极小」与「ε 邻域内的满足」
  连接起来。缺的正是这一条桥：*给定一个 ε-近似极小点，违反量能被 ε 界的某个函数控制*。
- 「把 ε 压小」目前**没有收敛率定理**。`RealVerifierReliable` 头部自己写明：
  `ε₀`/`δ` 是自由参数，**未证明它们可任意调小**。
- `PenaltyEmbedding` 文件头把这一层标为 `C`（梯度范数界 + 强凸 ⇒ 距离界）并注 `later`——
  **至今仍是 later**。

⇒ 因此本库当前能诚实声称的是：**精确嵌入不成立（已证否）；逼近精确的各个误差界
已分别在若干载体上成立；把它们接到 T2 上的那条桥尚未建立。**

---

## 4. 构建与验证

```sh
# 构建（复用已编译 mathlib，无需网络）
lake build Lattice

# 8 条不变量
cd gov && python gate.py

# 全套 56 项检查 + 反应性自检（逐项打印耗时）
cd gov && python verify_all.py
```

**实测耗时**（本机，2026-10-25）：全量 `verify_all.py` **PASS，43/43 ok（6.1 分钟）**。
最重的一项是 `reactivity: gate`（约 200 秒，它要连跑四次构建来验证门禁确实会红），
其次 `audit: islands` / `audit: reachable` 这类全树遍历。
`gate.py` 本身约 20 秒（803 个文件的注释剥离与声明扫描）。

> 数字只在这里写一次，且注明测量时点。项目的老毛病正是「五份文档五个数」：
> 旧库的 roots 曾被写成 238/344/412/411/467/479/548/576 八个值，无一正确。

`lakefile.toml` 的 `packagesDir` 指向 `../lattice/lean/.lake/packages`，复用第一代已编译的
mathlib（5,387 个 olean，rev `4bbdccd9…`）。**这是刻意的**：重新拉取编译需要数小时，
且两份缓存会各自老化。代价是 CI 必须把同一 revision 物化到同一路径 —— workflow 里显式做了这件事。

> 写 `lakefile.toml` 的两个坑（已实测）：PowerShell 5.1 的 `Out-File -Encoding utf8` 会写 BOM，
> 导致 `expected end of input`；TOML 会把反斜杠当转义序列，路径必须用正斜杠。

### 4.1 门禁的诚实性来自「它能变红」

`gov/` 里有一组 `*_reactivity.py`：向树里注入已知缺陷，断言门禁**确实报警**。
一个从不报警的检查器没有价值，所以每一类检查都有「注入错误 → 确认报警」的测试。

**这里踩过一个坑，值得写下来**：`gate_reactivity.py` 原先把探针写到 `Lattice/Probe.lean`，
而该文件属于 `root` 区，不在 `verify_all.py --fast` 所设的 `kernel` 扫描范围内。
于是四个用例全部报 `got 0`——**测试失败是因为门禁没看那个文件，不是因为门禁瞎了**。
探针现在写在 `Lattice/Core/Probe.lean`（kernel 区内），两种 scope 下都通过。
教训与项目里那条老规矩同源：**一个恒红的检查器会被忽略，一个恒绿的检查器同样没有价值**。

### 4.2 这些话必须说在前面（本库的已知弱点）

**（a）「PASS」曾经掩盖了一半真相，现已拆开。**
`verify_all.py` 注册的检查里，**16 个脚本的 `main()` 以字面 `return 0` 结束**，
它们不可能失败。其中多数是**自认的报告器**（`audit_untracked.py:131` 写
`Exit 0 is deliberate`、`audit_region.py:28` 写 `report only`），这是合法设计；
问题在于**把它们与能失败的检查算进同一个数字**。现在汇总分成两行：

```
VERIFY ALL [full]: PASS  (…s)
  gating checks passed : 15  (these CAN fail)
  report-only checks   : 18  (these print findings; exit code is not a verdict)
```

**（b）四条不变量从未被证明会报警。**
I3（定义唯一）、I4（分层）、I7（产物）此前**没有任何反应性测试**，I8 也没有
（本次补上了 `check_i8_reactivity.py`）。声称某条不变量成立，与证明它**会失败**，
是两件事；前者只有后者背书才有意义。

**（c）提交路径上没有门禁。**
本库**不安装** git pre-commit 钩子，而且这不是疏忽：实测一个 sh 钩子在此环境会因
`couldn't create signal pipe, Win32 error 5` **阻断每一次提交**（`git commit` exit 1）。
装一个坏钩子比不装更糟。门禁只在**手工运行与 CI**时生效——而 CI 见 (d)。

**（d）CI 已修复，但仍未在真实 CI 上执行过。**
`.github/workflows/lattice.yml` 原本读 `lattice/lean/lake-manifest.json`——一个在**本仓库
里不存在**的路径，所以 `build-and-verify` job 从第一步就失败，`lake build` 从未在 CI 上跑过。
现已重写：rev 从本仓的 `lake-manifest.json` 读取，checkout 后用 `rev-parse HEAD` 断言
HEAD 等于该 rev，并用 `grep -qE '^error' build.log` 把构建错误变成 job 失败。
`gov/check_ci_workflow.py` 守着这些性质，`check_ci_workflow_reactivity.py` 证明它**会红**
（4 个注入的缺陷全部被检出）。

**仍然要说清楚**：这台机器跑不了 git transport（`git ls-remote` 报
`sh.exe: fatal error - couldn't create signal pipe, Win32 error 5`），
所以 workflow 里**联网、elan 安装、cache 服务这三段只经过静态检查，没有实跑过**。
第一次真实 CI 运行仍是未验证的。

**（e）构建可复现性已改善，但并非完全可复现。**
`lake-manifest.json` 现在把 mathlib 记为 `type: git` + `url` + `rev = 4bbdccd9…`，
rev 因此成为**可提交、可检查的事实**（此前是 `type: path`，不带任何 rev）。
它指向的目录仍是 `../lattice/lean/.lake/packages/mathlib`，所以本机构建不联网、不重编。
**（代价）**：换一台机器需要 `lake update` 下载 mathlib（约 4.2 GB）——这一点无法回避，
包总得从某处来。实测见 `ROADMAP-v3.md` P6。

**（f）文档里出现的每个数字都必须可被机器核对。**
`verify_all.py` 注册了 **56 项**检查：38 项能失败的**门禁**，16 项**报告器**（它们的退出码不是判决，见上文 (a)）。

`gov/audit_counts.py` 把 README 里写的计数与实测比对，不一致即失败。它核对的两项是：

| 项目 | README 声明 | 实测口径 |
|:--|:--|:--|
| 冻结 escape 基线条目 | **69** 处历史逃逸 | `gov/escape-baseline.json` 的条目数 |
| LvFormal 缺失依赖文件数 | **0** 个文件引用了不存在的模块 | 静态 import 检查 |

这一点值得单列，因为**该检查器此前四个模式全部失配**（README 从散文改成了目录树），
于是一直打印「every checked count matches」——什么都没比，却看起来像全部一致。
现在：模式匹配不到**本身就算失败**，不再静默跳过。

---

## 5. 治理层

> **本项目的诚实性在这里。**

| 文档 | 内容 | 性质 |
|:--|:--|:--|
| [`archive/CORRECTIONS.md`](archive/CORRECTIONS.md) | **更正登记 B1–B480，451 条** | **手工权威**，B 编号是引用骨架，**冻结不改** |
| [`archive/DIVERGENCES.md`](archive/DIVERGENCES.md) | 与基准的偏离 92 条；未登记即为 bug | 手工权威 |
| [`archive/PROCESS.md`](archive/PROCESS.md) | 每轮流程与判读规律（§8.1 C1–C23） | 手工权威 |
| [`archive/STYLE.md`](archive/STYLE.md) | 风格与判读细则 | 手工权威 |
| [`archive/REVERSIBILITY.md`](archive/REVERSIBILITY.md) | 可逆性独立审计，14 条反例 | 手工审计 |
| [`Lattice/Slots.lean`](Lattice/Slots.lean) + `gov/SLOTS.md` | 未证但承重的命题（机器可枚举） | **由代码承载**，`gate.py` 生成登记表 |

### 5.1 为什么 CORRECTIONS 冻结而不重编号

`B<n>` 编号被引用 **4,855 处**（文档）与 **625 处**（`lean/*.lean` 的 docstring）。
重新编号会让这些引用同时失去指代对象。所以本库把整份登记**原样**搬入 `archive/`，
逐字节校验一致（SHA256 比对通过）。

**已知缺陷（如实登记）**：`PROCESS.md` 引用了 **B481–B498**，但 `CORRECTIONS.md` 正文
最大只到 **B480**。这 18 条的判据**正文不可查**。本库不修复这个问题（修复它需要重写
PROCESS 的判据表，属于证明层的工作），仅在此标注。

---

## 6. 与第一代的分工

| | 第一代 | 本库 |
|:--|:--|:--|
| 源码位置 | `lattice/lean`(606) + `lattice/zero`(85) + 582 影子副本 | 单一份 |
| roots | 581 + 1 | 1 |
| 门禁 | `.ps1` 37 个 + `.py` 113 个，CI 主命令实测失败 | 纯 Python 76 个，CI 覆盖 |
| CI | 只跑旧 `lake build lattice`，**零覆盖 zero/** | 门禁优先 + 构建必需 |

第一代不删除：它是回退基线与证据来源。

---

## 7. 与目标的距离

本库完成的是**结构迁移 + 结构层面的缺陷清理**，不是研究目标完成。按目标逐条：

| # | 目标分句 | 状态 |
|--:|:--|:--|
| G1 | 四跳链路 | ⚠️ **过度声称，已降级**（见下） |
| G2 | 正向三路径 | ✅ |
| G3 | 逆向四步 | ✅ |
| G4 | 闭环收敛 | ✅（**注意**：`loop_converges` 的度量是「修一次即归零」，未表达多次迭代） |
| G5 | 符号引擎 | ✅ |
| G6 | 不绑定框架 | ✅（依赖事实，非定理；**但该事实目前不可在他机复现**，见 §4.2(e)） |
| G7 | lvLang→IR→Cv00→权重 | ⚠️ **原文路线断；IR→权重路线通**（见 §3.1） |
| G8 | 四条靶定理 | ⚠️ T1/T3/T4 有载体；**T2「精确嵌入」已证否，改走逼近精确**（见 §3.3） |
| G9 | 可逆性分层 | ✅ |

**G1 为什么降级**（实测，不是推断）。`Lattice/Geo/Pipeline.token_to_weight` 的签名是

```lean
theorem token_to_weight (c : LinearForm ℝ n) (pts : ℕ → Pt n) (rs : List ℝ)
    (_hdec : decodePayload n rs = some c) : ...
```

`_hdec` 以下划线开头，**结论里从未用到**。实测（`agent-tmp/verify_g1_vacuity.py`）：
删掉该假设、乃至删掉 `rs` 参数，同一证明仍然通过，Lean 自己报
`warning: unused variable 'h'`。⇒ 这条链的「L0/L1 → L3」不是一个承重的连接，
而是对一个线性形式重述两个已知事实。**「终点为权重」这句话在这里没有内容支撑**。

### 7.1 迁移中实际清掉的缺陷（8 条不变量为何从红到绿）

迁移前这些缺陷在旧库里**不可见**，因为旧库用 581 个独立 root 把每个模块隔开，
从不放进同一个环境。新库第一次聚合它们，门禁立刻报出：

| 不变量 | 迁移初报 | 根因 | 处置 |
|:--|--:|:--|:--|
| I3 定义唯一 | 12 条 | `Expr` 定义 4 次、`eval` 5 次，各是**不同的语言**；`Star`/`State` 各 2–4 次 | 按语义改名（`IntExpr`/`CondExpr`/`TypedExpr`/`FloatExpr`、`evalBool`/`evalInt`/`evalCond`/`evalTree`）；同语义的收敛为一个定义 |
| I4 分层 | 18 条 | 链路环节物理上全在 `Lib/`，且 9 个应用模块被误放在 `Lift/` | 双向归位（见 §2 注） |
| I5 端到端诚实 | 10 条 | 判据只认全限定前缀，且只看一层；真缺陷是 `e2e_sound` 证明体逐字是更弱定理 | 判据改为**声明层 + 传递闭包**；`multiSite_edit_end_to_end_bound` 改为 `..._nested_bound`（它并不跨跳） |
| I7 产物对应 | 20 条 | 模块移动后旧路径 olean 残留 | 清理陈旧产物 |

**I5 的判据改动是加重不是放水**：它现在沿着定义体递归展开，
`e2eF` 这类"委托给复合函数"的证明也计入其真实触及的层。

### 7.2 尚未做（不在本库范围内宣称）

**（一）逼近精确的那条桥。** §3.3 的全部误差界都还是孤立的；
把「ε-近似极小点」接到「违反量 ≤ f(ε)」上的那条桥**不存在**，
「ε 可任意压小」也**没有收敛率定理**。这是本库最主要的未完成项。

**（二）证明的承重性重审。** 按靶定理逐条审（`rfl` 级证明、前提不承重、结论退化）
只做到四条靶定理为止。I5 只保证「名字与所触及的层相符」，不保证数学内容有实质。
扫描器与实测数字见 §7.1 与 `agent-tmp`（未入库）。

---

## 协议

MIT
