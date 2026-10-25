# LATTICE

**Representation Lattice for Symbolic↔Weight Training**（表示谱系格）
符号 ⇄ 权重双向转换的训练 / 后训练框架，Lean 4 证明保证正确性。

> **定位**：通用基础设施——用于**所有 LLM 的训练与后训练**（不限规模、不限厂商）。
> **状态**：结构迁移完成（v2），目标见 §7「与目标的距离」。

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
│   ├── Core/      13       # 语言层：语法 / 语义 / 满足关系 / 修复 / 权重接口
│   ├── Lift/      24       # 链路层：L0⇄L1⇄L2⇄L3 全部环节 + zero 的抽象接口
│   ├── Slots.lean  1       # 空位层：未证但承重的命题，只声明不证明
│   ├── Geo/       52       # 约束几何与精确惩罚
│   ├── Lib/      588       # 应用库，按主题（建立在链路层之上）
│   │   ├── Architectures  66    Attention       36    Chain         69
│   │   ├── Compiler       45    Concentration   37    Convex        25
│   │   ├── Editing        69    FCA             15    InfoTheory    26
│   │   ├── LearningTheory 46    LinearAlgebra   33    Meta           8
│   │   ├── Optim          60    Quantization    18    Linear         8
│   │   ├── Lift            8    Penalty          2
│   └── Reference/          # 证据资产，不参与构建
│       └── LvFormal/  121  # Lv-00 上游（唯一源）
├── gov/                    # 门禁与审计（8 条不变量 + 32 项检查 + 反应性自检）
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
5. 任何 `axiom` / `sorry` / `admit` / `opaque` 为 0（I1、I2）；
6. 标为 `EndToEnd` 的定理必须真的用到它声称连接的每一层（I5）。

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
| T2 | 约束嵌入可靠 | `geo_penalty_exact`（12/12 构造子有精确惩罚） |
| T3 | 提取等价 | `flatten` 双射 + `semantic_not_injective` |
| T4 | 回路收敛不破坏语义 | `loop_converges` / `Repair.progress` / `conj_loop_fixed_point` |

**T2 的边界必须一起说**：`poly` 层在**非退化时**成立，而那个条件的生产者目前只有垂直约束一类。
写成「T2 无条件成立」就不完整。

---

## 4. 构建与验证

```sh
# 构建（复用已编译 mathlib，无需网络）
lake build Lattice

# 8 条不变量
cd gov && python gate.py

# 全套 32 项检查 + 反应性自检（实测约 21 分钟，逐项打印耗时）
cd gov && python verify_all.py
```

**实测耗时**（本机，2026-10-25）：全量 `verify_all.py` **PASS，32/32 ok**。
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
| G1 | 四跳链路 | ✅ 终点为权重（`Lattice.Geo.Pipeline.token_to_loss`） |
| G2 | 正向三路径 | ✅ |
| G3 | 逆向四步 | ✅ |
| G4 | 闭环收敛 | ✅（**注意**：`loop_converges` 的度量是「修一次即归零」，未表达多次迭代） |
| G5 | 符号引擎 | ✅ |
| G6 | 不绑定框架 | ✅（依赖事实，非定理） |
| G7 | lvLang→IR→Cv00→权重 | ⚠️ **原文路线断；IR→权重路线通**（见 §3.1） |
| G8 | 四条靶定理 | ✅（T2 带非退化前提） |
| G9 | 可逆性分层 | ✅ |

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

按靶定理逐条重审**证明的承重性**（`rfl` 级证明、前提不承重、结论退化）。
这一步尚未开始；I5 只保证"名字与所触及的层相符"，不保证数学内容有实质。

---

## 协议

MIT
