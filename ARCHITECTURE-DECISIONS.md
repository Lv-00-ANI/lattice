# ARCHITECTURE-DECISIONS

## 2026-11-23 解释修订：目标确认与旧记录适用范围

依据项目作者的澄清，现行目标及治理待办见 [DESIGN-ALIGNMENT.md](DESIGN-ALIGNMENT.md)。下方五条 ADR 保留为 2026-11-15 的历史记录；并非所有解释均获作者确认，且其中的实现数字不能当作当前测量。

- ADR-001 的“不是装载清单”“没有机器价值”过度排他。能力索引用途补充既有清单规格，不取消装载、参数及依赖用途。
- ADR-002/003 保留源码级接入与自举证明的目标，但不把加载器限制为某个未经核实的 C 函数，不将内部构造语言等同于标准 C。
- ADR-004 的“展示厅”改读为官方核心组合的维护与验证入口。插件可自带组合；不得把未完成路径自动排除。常规预训练的排除保留；其余排除项须逐项对照目标，不能沿用旧审计的推断。
- ADR-005 的“执行体是 C”“只有两项前置有意义”不作为现行设计约束。项目不要求全部能力直接由 C 实现；具体实现后端、接口及数值边界须分别验证。
- 项目目标包括经 IR 建立模型／权重的行为语义对应。任意精度逼近目标保留，需明确目标类、误差度量和允许增长的资源；不以固定规模模型的局部限制否定总体目标。
- 旧几何主线残留列为全库文档治理任务；本轮不删除几何代码，不把依赖迁移或通用化写成已完成。

以上修订明确旧记录的有效范围；其余未核实冲突进入待办，不以新的审计断言覆盖旧历史。

**本文件记录架构决定（ADR: Architecture Decision Record）。**

每条记录四件事：**决定是什么**、**为什么**、**影响到的旧说法（说明仍成立的部分）**、**日期**。

本文件**不是规格**。规格在 [`PLUGIN-SYSTEM.md`](PLUGIN-SYSTEM.md)；总览在 [`README.md`](README.md)。本文件记录的是“为什么这样决定”，以及“哪些旧读法被收窄了适用层”。

---

## 目录

| ADR | 标题 | 日期 |
|:--|:--|:--|
| [ADR-001](#adr-001--pluginyaml-的第一作用是能力索引) | `plugin.yml` 的第一作用是能力索引 | 2026-11-15 |
| [ADR-002](#adr-002--装载器的消费者是内部构造语言不是-lean-侧插件) | 装载器的消费者是内部构造语言，不是 Lean 侧插件 | 2026-11-15 |
| [ADR-003](#adr-003--自举链服务于-cic-内核的-c-实现) | 自举链服务于 CIC 内核的 C 实现 | 2026-11-15 |
| [ADR-004](#adr-004--compose-是官方组合展示厅) | `Compose/` 是官方组合展示厅 | 2026-11-15 |
| [ADR-005](#adr-005--执行体在-clean-侧是语义) | 执行体在 C，Lean 侧是语义 | 2026-11-15 |

---

## ADR-001 · `plugin.yml` 的第一作用是能力索引

**日期** 2026-11-15

### 决定

`plugin.yml` 的第一作用是**能力索引**：声明一个插件提供什么——哪些 `Primitive`、哪些 `Obligation`、哪些 `capabilities`。它服务于三类读者：

| 读者 | 读什么 | 用途 |
|:--|:--|:--|
| **人** | `provides` / `capabilities` | 一眼看出这个插件能做什么 |
| **编排器** | `capabilities` | 按能力标签组装，不需要加载状态机 |
| **编译期核对** | `provides.primitives[].lean` | `run_cmd` 核对全限定名必须在环境里存在 |

### 为什么

本库不做运行时插件装载，新能力只能通过增改源码进入仓库。在这个前提下，`plugin.yml` 如果只被当作“装载清单”，它就没有任何机器价值——因为没有任何东西会去装载它。

但它的**索引**价值仍然成立，而且很高：

- 当前 11 个插件各有 12 个 `PluginProof` 槽，其中 **87 个是字面 `True`**。**没有任何 gov 检查读取 `PluginProof`。** `plugin.yml` 是让这些槽第一次可被机器核对的最短路径。
- `verifiedObligation name kind file thmName h` 的两个参数 `thmName` 与 `h` **互不链接**——什么搭配都能通过。`plugin.yml` 的 `lean:` 字段是补上这条链接的入口。

### 影响到什么

| 旧说法 | 是否仍成立 |
|:--|:--|
| §7 的 17 键规格 | ✅ **全部成立**，一条不改 |
| §7.6 的 23 个违反码 | ✅ **全部成立** |
| §7.3 的 5 字段参数 | ✅ **全部成立** |
| “清单系统 0% 实现” | ✅ **仍成立**（`plugin.yml` / `module.yml` / `params.yml` 各 0 个） |

**被收窄的是“用途”，不是“规格”。** §7 开头新增一段“读法”，说明 17 键中哪些是索引字段、哪些是装载字段。

---

## ADR-002 · 装载器的消费者是内部构造语言，不是 Lean 侧插件

**日期** 2026-11-15

### 决定

`LoaderState` / `loadAll` / `allok`（`PLUGIN-SYSTEM.md §9` Q4/Q7）的消费者是**内部构造语言（CIC 内核的 C 实现）的加载器**，不是 Lean 侧的插件加载器。

### 为什么

Lean 侧不存在运行时插件装载。如果 `LoaderState` 的设计目标是“让 Lean 能热插拔”，它永远不会被使用。但它在 C 侧是必需的：内部构造语言要读自己的清单、校验依赖、建立参数表、并在失败时给出可观测的失败状态。

**所以 Q4/Q7 的设计目标被明确为：给 C 侧一个可被证明的加载语义。**

### 影响到什么

| 旧说法 | 是否仍成立 |
|:--|:--|
| Q4 的全部规格 | ✅ **全部成立** |
| Q7 的全部规格 | ✅ **全部成立** |
| `LoaderState` 的状态机、`allok` 的可观测性 | ✅ **全部成立** |
| “Q4–Q18 全部 0” | ✅ **仍成立**（代码中 `Scope`/`Exit`/`PluginState`/`LoaderState` 全部 0 定义） |

**被收窄的是“消费者”，不是“规格”。**

---

## ADR-003 · 自举链服务于 CIC 内核的 C 实现

**日期** 2026-11-15

### 决定

`PLUGIN-SYSTEM.md` 附录 I 的自举链**是需要的**。它的消费者是内部构造语言（CIC 内核的 C 实现），不是外部 Lean 插件。

### 为什么

内部构造语言需要能加载自己的清单，而这个加载器本身必须是可证明正确的——这就是“自举”在这里的全部内容。

`loaderPrim.sound` 陈述的正是：**C 侧的 `lattice_load_all` 在什么条件下返回什么**。它不是一条“Lean 内部的热插拔定理”，它是**一条 C 侧函数的规格**。

### I.9 六项验收的归属

| 项 | 归属 | 理由 |
|--:|:--|:--|
| 1 | **纯 Lean 可机** | 加载结果的可枚举性 |
| 2 | **纯 Lean 可机** | 收敛性 |
| 3 | **纯 Lean 可机** | 幂等性 |
| 4 | **半可** | 观测等价，需两侧各出一半证据 |
| 5 | **必须内部语言侧** | 与真实 C 加载器的对照 |
| 6 | **必须内部语言侧** | 与真实 C 加载器的对照 |

### 已知缺陷

**I.5 的证明草图有类型错误。** 它写：

```lean
loadAll (loadAll ms) = loadAll ms
```

但 `loadAll : List Manifest → LoaderState`，所以 `loadAll (loadAll ms)` 的第二个参数类型不符。

**修法**：补一个 `reify : LoaderState → List Manifest`，并把第二轮的输入改成 `reify (loadAll ms)`：

```lean
theorem bootstrap_idempotent (ms : List Manifest) :
    loadAll (reify (loadAll ms)) = loadAll ms
```

### 影响到什么

| 旧说法 | 是否仍成立 |
|:--|:--|
| 附录 I 的全部设计 | ✅ **全部成立** |
| `bootstrap_converges` / `bootstrap_observable_eq` 的陈述 | ✅ **全部成立** |
| I.9 六项验收 | ✅ **全部成立**（归属被明确） |
| “`loaderPrim` 连陈述都写不出” | ✅ **仍成立**（`loadAll`/`LoaderState`/`Manifest` 全部 0 定义） |

**被收窄的是“消费者”，不是“设计”。**

---

## ADR-004 · `Compose/` 是官方组合展示厅

**日期** 2026-11-15

### 决定

`Compose/` 是**官方组合的展示厅**。插件可以自带组合。

具体地：

1. **`Compose/` 放什么**：`README.md §1` 链路图里的官方组合，以及它们的端到端默认演示（`Compose/Showcase/`）。这是**权威展示**——官方认可的每一条链路，都在这里有一条对应的组合定理。
2. **插件可以自带组合**：组合是能力的一部分。一个插件需要把三个自己的 `Primitive` 串起来，就在自己的目录里串，不需要绕道 `Compose/`。
3. **`Compose/` 不是“组合的唯一合法场所”**——这是被放宽的更强读法。

### 为什么

组合层当前的病不在代数，在于**它证明的东西没有一个用户，而使用它的那个地方（`Plugins/Compose/Manifest.lean`）是伪造的**。

如果 `Compose/` 的定位是“唯一合法场所”，那么它必须被所有组合使用者 import——但它现在是 **`Lib/` 对 `Lattice.Compose` 的 import = 0**，`Runtime`/`Core/IR`/`Core/CIC` 也是 0。

如果它的定位是“官方展示厅”，那么“没有用户”就不算缺陷——**参考实现本来就不必须有用户，它的价值是示范 + 端到端默认路径**。

### 官方展品清单

见 [`PLUGIN-SYSTEM.md`](PLUGIN-SYSTEM.md) 附录 M。摘要：

| # | 展品 | 现状 |
|--:|:--|:--|
| M-1 | 完整链路 L0→L1→L2→L3 | `pipeline` 已存在，但手写 `bind`，未用 `Compose` |
| M-2 | 神经捷径 L0→L1→L3 | **不存在** |
| M-3 | 符号捷径 知识→L2 | **部分存在**（`parse_models_full`） |
| M-4 | L1⇄L2 | `decode_encode` 有真内容 |
| M-5 | L3⇄L2 | `extract_compile` 真；`compile_sound` 重言 |

**被明确排除**（不进展示厅）：常规预训练、`Import`/`PostTrain`/`Merge`/`semanticEdit`、四跳 G1、`lvLang→IR→Cv00`、T2 精确嵌入、C 实现。

### 已知缺陷

**`Plugins/Compose/Manifest.lean` 的 9 条 `file` 指向不存在的文件。**

| obligation | 声称的 `file` | 实际存在? |
|:--|:--|:--:|
| `compose_sound` | `Lattice/Plugins/Compose/Proofs.lean` | ❌ |
| `compose_assoc` | `Lattice/Plugins/Compose/Proofs.lean` | ❌ |
| `identity_law` | `Lattice/Plugins/Compose/Proofs.lean` | ❌ |
| …（共 9 条） | `Lattice/Plugins/Compose/{Proofs,Combinators,ComposeObligation}.lean` | ❌ |

**正确路径是 `Lattice/Compose/{Proofs,Combinators,ComposeObligation}.lean`**（那些文件真实存在）。

`compose_migrated` 现在是靠 `Migrated` 的字符串前缀检查伪造通过的——`Migrated dir m := ∀ o ∈ m.obligations, StringPrefix dir o.file`（`Migration.lean:105-106`）**只比前缀，从不检查文件是否存在**。

### 影响到什么

| 旧说法 | 是否仍成立 |
|:--|:--|
| `README §3.5` “组合子只在 `Compose`” | ✅ **仍成立**（在“官方组合”意义上） |
| `Compose/` 的 12 个文件、74 条定理 | ✅ **全部保留** |
| 六条代数律 | ✅ **全部保留** |
| 附录 K 的全部设计 | ✅ **全部成立** |
| “K.9 十三项在代码库里一项都不存在” | ✅ **仍成立** |

**被收窄的是“必需性”，不是“内容”。**

---

## ADR-005 · 执行体在 C，Lean 侧是语义

**日期** 2026-11-15

### 决定

Lean 侧**不是执行体**。`Runtime/` 是运行**语义**层（描述“如果执行会怎样”），不是执行器。执行体是 C。

**并且：当前只实现了 CIC 内核的 C 实现；其余部分是 CIC 内核自我构造的内部语言，严格来说不是标准 C ABI。**

### 为什么

这解释了此前被当缺陷的一件事：`SEMANTICS-MAINLINE.md §7.1` 的 12 个 `lattice_*` 在 Lean 树里 **0/12 存在**。

如果这些名字是“标准 C 的函数名”，那么它们不存在是缺陷。但项目走的是**内部构造语言**路线——`CInterface/ABI.lean:117-129` 的 `abiTable` 的 11 个 primitive 才是内部语言的内置函数表。所以：

- **12 个 `lattice_*`（0/12）** = 标准 C 命名，与内部语言路线无关；
- **11 个 `abiTable` primitive** = 内部语言的内置函数表，真实存在。

### 影响到什么

| 旧说法 | 是否仍成立 |
|:--|:--|
| `README §2` 的 `Runtime/ 66` | ✅ **全部保留** |
| `Runtime/EndToEnd.lean` 的 `Ladder` | ✅ **全部保留** |
| `ProgramAST` / `Instr` / `Semantics` | ✅ **全部保留** |
| `README §3.7` “C 接口现在，C 实现最后” | ✅ **完全一致** |
| `README §3.8` “Lean 只处理抽象对象” | ✅ **完全一致** |
| `README:387` “C 是后续系统插件，不进入 `ProofComplete`” | ✅ **完全一致** |

**被收窄的是“`Runtime` 的角色”，不是“`Runtime` 的内容”。**

### 对审计结论的影响

审计中有一条判断需要因此修正：

> ❌ 旧：“12 条 C 前置 0 全通，是系统完成度的缺口。”
>
> ✅ 新：“在内部构造语言路线下，真正‘给 C 用’的前置只有两条——`slotOf_lt_two_pow_53`（数值安全）与 `layerWords ↔ compileWith`（两套表示的桥）。其余 10 条（字宽、字节序、padding、错误码、`lattice_*` 名字表）是**标准 C ABI 的需求**，与内部语言路线无关。”

---

## 附录 · 五条 ADR 的关系

```
ADR-005（执行体在 C）
    │
    ├── ADR-002（装载器给内部语言）
    │       │
    │       └── ADR-003（自举链给 C 实现）
    │
    └── ADR-001（plugin.yml 是索引，不是装载清单）

ADR-004（Compose/ 是展示厅）
    └── 独立于上面四条，但与 ADR-001 共享同一个前提：
        “没有运行时装载”⟹ 能力与索引同批提交 ⟹ 展示厅是官方认可的展示
```

---

## 与既有文档的一致性核验

| 本文件 | 与哪份文档一致 | 原文 |
|:--|:--|:--|
| ADR-001 | `PLUGIN-SYSTEM.md §11.5.1` | “The plugin system is part of the proof, not a coat of paint” |
| ADR-002 | `README.md:387` | “C 在新架构中是后续系统插件…不进入 `ProofComplete`” |
| ADR-003 | `PLUGIN-SYSTEM.md` 附录 I | 自举链的完整设计 |
| ADR-004 | `README.md:349-350` | “组合子只在 `Compose`；组合是用户的事” |
| ADR-005 | `README.md:389-400` | “Lean 只处理抽象对象…不处理 C、conformance” |
