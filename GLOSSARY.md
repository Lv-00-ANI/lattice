# GLOSSARY

本文件固定 LATTICE 文档中的状态词、流程词、产物词与插件词。
同一术语在不同文档中不得改变含义。

## 1. 状态词

| 词 | 含义 | 是否算完成 |
|:--|:--|:--|
| **exact** | 精确定理，前提不空转，结论就是声称的内容 | ✅ |
| **exact-negative** | 证明当前对象不可能，并给出精确替代对象 | ✅（替代对象必须存在） |
| **exact→approx** | 显式 ε / 误差界 / 收敛定理，且 `ε→0` 有定理 | ✅（唯一允许的减弱） |
| **受限闭合** | 只在子类、解处、2/12 构造子、SafeBranch 上成立 | ❌ |
| **名义闭合** | 名字/结构存在，但没有承重语义 | ❌ |
| **register / boundary / nominal / limited** | 登记、边界、名义、受限 | ❌ 不是完成 |
| **Opaque** | 只有字节，不能语义解析 | 仅工程 fallback |
| **Imported** | 外部产物，未经 LATTICE 证明 | 证书最弱 |
| **Empirical** | 测试通过，但没有证明 | 不是 Proof |

## 2. 流程词

| 词 | 含义 |
|:--|:--|
| **L0** | 数据层 |
| **L1** | token 层 |
| **L2** | 符号模型层：**CIC term**（几何/程序/DSL 都是它的编码实例） |
| **L3** | 权重层（模型参数） |
| **Forward** | 符号 → 损失/数据/初始化 |
| **Reverse** | 权重 → 符号/行为 |
| **Repair** | 违反约束 → 修正权重 |
| **Construct** | 规格 → term → 权重 → 模型，从零构造 |
| **Delegate** | 调外部训练器产生候选，再验证 |
| **Confluence** | 动态演化后的最终模型 = 从最终规格重建 |

## 2bis. 载体词

| 词 | 含义 |
|:--|:--|
| **CIC** | Calculus of Inductive Constructions；LATTICE 的主符号载体 |
| **Term** | CIC 项；`Lattice/Core/CIC/Syntax.lean` |
| **Typable** | `Typable Γ t A`：在 context `Γ` 下 `t : A` 可类型化 |
| **NormalForm** | 归约到的不动点；`extract_compile` 的落点 |
| **steps** | 归约步数上界；T2 的 `ε` 来源 |
| **encode** | 几何（或其他 Domain）→ CIC term；单向 `sound` |
| **compile** | `Term → Weights`；elaboration 的抽象对应 |
| **Domain instance** | 用 CIC 编码进来的具体领域；几何是一个实例 |
| **domain-legacy** | 旧几何载体上的定理；保留为 Domain 级证据，不进 `ProofComplete` |

## 3. 靶定理

| 词 | 内容 |
|:--|:--|
| **T0** | 构造：从 `Typable` 构造 term，再 `compile` 到权重 |
| **T1** | 编译保语义：结论必须出现输入 term |
| **T2** | 约束嵌入：精确载体 exact；一般情形 `steps t * ε` 显式界 |
| **T3** | 提取：对象层双射 + 语义层不可逆 + 无 extractor 同时保两层 |
| **T4** | 修复：收敛、不动点、不破坏语义 |
| **T5** | 时间可组合：卸载只撤销自己的影响 |
| **T6** | 空间可组合：激活门 + 依赖顺序 + 解析一致 |
| **T7** | 汇合：动态演化 = 从最终 Spec 重建 |
| **T8** | 失败隔离：失败插件不污染其他插件 |

## 4. 产物词

| 词 | 含义 |
|:--|:--|
| **ModelArtifact** | Lean 内的抽象模型：`arch : Arch` + `weights : Weights`；来源是 `Term` 的编码 |
| **RawModel** | 工程侧的字节/格式对象：`bytes` + `format` |
| **Weights** | 抽象权重，不是 `ByteArray`、不是文件 |
| **ResultEquiv** | `weights` / `behavior` / `approx ε`；`bytes` 属于工程测试 |
| **ProofComplete** | 证明部分完成判据：T0–T8 + `PluginRegistryComplete`；实际形状以 `Lattice/Plugins.lean` 为准 |

## 5. 插件词

| 词 | 含义 |
|:--|:--|
| **ServiceKey** | 服务键：名称 + 版本 |
| **Plugin** | 能力契约 + Semantics + Manifest + install |
| **VerifiedPlugin** | 带 `PluginProof` 的插件 |
| **Obligation** | 一条证明义务：名称、类型、定理名、文件 |
| **PluginRegistry** | 证明插件的静态注册表 |
| **SystemRegistry** | 工程/后端插件的注册表（C、loader、conformance） |
| **Fiber** | 插件实例的生命周期对象 |
| **Effect** | 可逆/可快照/近似的状态变换 |
| **Coeffect** | 依赖声明与 provider 解析 |
| **Confluence** | 动态历史不留下痕迹 |

## 6. 禁止用法

- 用 `register` 代替定理；
- 用 2/12、解处、SafeBranch 9/12 代替完整覆盖；
- 用 `Imported`/`Empirical` 冒充 `Proof`；
- 用 `Opaque` 冒充 `Structured`；
- 用“训练 loss 小”冒充语义等价；
- 用“有名字 / 0 sorry”冒充完成；
- 用 `def X : String := "..."` 冒充义务；
- 用 `theorem X : A → True` 冒充定理；
- 用只数自己写下的字面量的 `rfl`（如 `proved_target_count := 9`）冒充 ledger；
- 用别名 def 冒充独立义务；
- 用绑定变量不出现在结论里的命题（如 `∀ n, ∃ S : Spec n, S.constraints = []`）冒充对 `n` 的陈述；
- 用 `Option.bind_assoc` 冒充汇合；
- 用 `if failing then none` 的定义展开冒充失败隔离。
