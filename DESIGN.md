# LATTICE DESIGN

> **[待移除] 主线载体（2026-11-06）**：主符号载体是 **CIC term**（`Lattice/Core/CIC/`）。
> **几何（`Domains/Geometry` / `Domains/Constraints`）已标待移除，**仅作参考与反例来源**。

## 0. 目的

本文件定义 LATTICE 的单一设计口径：

- LATTICE 是什么、不是什么；
- L0–L3 主线；
- 新类型预训练/后训练如何映射到 Forward / Reverse / Construct；
- 插件运行时与插件证明；
- T0–T8 与 `ProofComplete`。

它不替代：

- `README.md`（入口与状态）；
- `PROOF-DEBT.md`（逐条证明债，生成物）；
- `MACRO-STATUS.md`（结构测量，生成物）。

## 1. 定位

LATTICE 是**符号 ⇄ 权重的带证明转换层**：

- **正向**：符号知识 → 损失项 / 数据合成 / 结构化初始化；
- **逆向**：权重 → 符号/行为 → 验证 → 修复 → 再注入；
- **构造**：符号规格 → CIC term → 权重 → 完整模型；
- **可扩展**：编译器、提取器、验证器、修复器、架构载体都是插件；
- **时空可组合**：插件可动态加载/卸载/替换，最终状态等于从最终规格重建。

**主符号载体是 CIC term**（`Lattice/Core/CIC/`），不是几何约束。
几何（`Domains/Geometry`、`Domains/Constraints`）保留为**一个 CIC 编码实例**，
其定理作为 Domain 级证据，不再是靶定理的陈述对象。决定与理由见
`CARRIER-REPLACEMENT.md`，设计与映射见 `CARRIER-CIC.md`。

**不是**：

- 常规训练框架（不实现 optimizer / data loader / SFT / DPO / RLHF）；
- 通用架构空间（Conv/Attention/Norm/DAG 只是 L3 载体插件）；
- 训练收敛或泛化证明系统。

## 2. 主线 L0–L3

```text
L0 数据 ──► L1 token ──► L3 权重（模型）
   │             │          ▲     │
   │             │ L1⇄L2    │     │ L2⇄L3
   ▼             ▼          │     ▼
              L2 符号模型（CIC term：规则/约束/谓词/DSL）
```

三条路径：

1. **神经捷径**：L0 → L1 → L3；
2. **符号捷径**：知识 → L2；
3. **完整链路**：L0 → L1 → L2 → L3。

LATTICE 负责 L1⇄L2、L2⇄L3 的转换与证明；训练引擎由外部框架承担。

**L2 的载体是 CIC term**，不是某个具体领域语言：

- 几何约束被编码为 term（`Encode/Geometry`，单向 `sound`）；
- 其他领域（程序、规则、DSL）同样以编码方式接入；
- 因此 L2⇄L3 的定理陈述在 CIC 上，几何只是其中一个实例。

## 3. 新类型预训练

### 3.1 Construct（从零构造）

```text
Typable Γ t A → Term t → compile t → Weights → ModelArtifact
```

- 构造的对象是 **term**，不是点配置；
- 「可构造」= 「可类型性」+ 「`compile` 有定义」，因此**可判定**；
- 规格唯一确定权重时 **exact**；
- 欠定时选 **canonical**（最小范数/对称固定/规范形）；
- 不可精确时 **approx ε**（`ε` 来自归约步数，见 `PROOF-OBLIGATIONS.md` T2）；
- 无 `Typable` 见证时 **unsupported**，不能假装构造。

几何上的旧构造（`ExpressibleSpec n → Pt n`）保留为 Domain 实例：
`no_specSolver` 已证明它**不可能**对任意 spec 成立，因此几何构造只以 family 强度存在。

### 3.2 Forward（注入现有训练）

符号 → 损失项 / 数据合成 / 结构化初始化，插入外部训练栈。
训练过程不由 LATTICE 证明。

### 3.3 Delegate（可选）

外部训练器产生候选，LATTICE 验证；证书只能是 `Imported` / `Empirical`。

## 4. 新类型后训练

```text
ModelArtifact → 符号/行为 → verify → repair → re-inject
```

- `edit` / `merge` / `quantize` / `repair` / `rewrite`；
- exact / approx / irreversible；
- 证书：`post_preserves` / `post_approx`。

不实现 SFT/DPO/RLHF；它们由外部框架完成，LATTICE 可包装为 Delegate。

## 5. 模型/权重语义

Lean 内只存在：

```lean
structure ModelArtifact where
  arch : Arch
  weights : Weights
```

- 没有 `format`；
- 没有 `ByteArray`；
- 没有文件系统。

`Arch` 与 `Weights` 的来源是 **CIC term 的编码**：
`compile : Term → Weights`，`archOf : Term → Arch`。
几何侧的 `pt n → Weights` 保留为一条 Domain 实例路径。

格式解析、I/O、C、conformance 属于 `ENGINEERING.md`，不进入 `ProofComplete`。
CIC 的语法与类型规则属于本仓库（`Lattice/Core/CIC/`）；
CIC 的**实现**（parser / elaborator / evaluator）属于工程侧，已单独立项。

## 6. 插件运行时

见 `PLUGIN-PROTOCOL.md`：

- `LatticeContext`；
- `LatticePlugin`；
- `LatticeEffect`；
- `Coeffect` / `Fiber`；
- `Registry`。

## 7. 插件 Lean 证明

见 `PLUGIN-PROOFS.md`：

- 每个能力一个插件；
- 每插件在其层级目录下有语义命名证明子文件夹；
- `ProofComplete` 由 `proofRegistry` 驱动；
- C 在 `systemRegistry`，不进入 `ProofComplete`。

## 8. 时空可组合

见 `SPATIOTEMPORAL.md` / `CONFLUENCE.md`：

- 时间：可逆效应 + snapshot；
- 空间：反应式余效应 + provider 解析；
- 汇合：动态演化 = 从最终 Spec 重建。

effect 的载体是 **CIC 编码**（elaborator state 的抽象），
不是 `K → Option ℕ` 玩具模型；玩具模型保留为最小语义实例。

## 9. 架构载体

Conv / Attention / Norm / DAG / GNN 是 L3 载体插件，不是主线。
在新载体下，它们是 **CIC term 上的架构编码**。
见 `ARCHITECTURE-CARRIERS.md`。

## 10. 证明义务

T0–T8，见 `PROOF-OBLIGATIONS.md`。
每条义务在 CIC 载体上陈述；几何版本作为 Domain 实例保留。

## 11. ProofComplete

**判据的实际形状由 `Lattice/Plugins.lean` 的定义为准。**
文档中的形状必须与代码逐项一致；任何一处不一致都按缺陷处理。

概念形状：

```lean
def ProofComplete : Prop :=
  PluginRegistryComplete ∧ ¬ pluginCensusPending ∧
  RegistryMigratedFor pluginDirOf proofRegistry ∧
  T1 ∧ T2 ∧ T3 ∧ T4 ∧ T5 ∧ T6 ∧ T7 ∧ T8
```

不含：

- 格式解析；
- 权重 I/O；
- C ABI；
- conformance；
- 外部训练器；
- SFT/DPO/RLHF；
- optimizer；
- 泛化。

**纪律：** 判据里不允许出现以下形状：

- `def X : Prop := True`；
- `theorem X : A → True`；
- `def X : String := "..."`；
- 只数自己写下的字面量的 `rfl`（如 `proved_target_count := 9`）；
- 别名 def 冒充独立义务；
- 绑定变量在命题中不出现。

## 12. 非目标

- 常规的端到端训练工具链（优化器、数据加载、分布式）；
- 训练收敛；
- 泛化界；
- 私有权重格式；
- 任意文件的字节级兼容；
- 把权重字面量导出当成构造。

## 13. 术语

见 `GLOSSARY.md`。
