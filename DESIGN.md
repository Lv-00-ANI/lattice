# LATTICE DESIGN

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
- **构造**：符号规格 → 约束 → 解权重 → 完整模型；
- **可扩展**：编译器、提取器、验证器、修复器、架构载体都是插件；
- **时空可组合**：插件可动态加载/卸载/替换，最终状态等于从最终规格重建。

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
              L2 符号模型（规则/约束/谓词/DSL）
```

三条路径：

1. **神经捷径**：L0 → L1 → L3；
2. **符号捷径**：知识 → L2；
3. **完整链路**：L0 → L1 → L2 → L3。

LATTICE 负责 L1⇄L2、L2⇄L3 的转换与证明；训练引擎由外部框架承担。

## 3. 新类型预训练

### 3.1 Construct（从零构造）

```text
Spec → Constraints → Solve → Params → ModelArtifact
```

- 只对 `ExpressibleSpec`；
- 规格唯一确定权重时 **exact**；
- 欠定时选 **canonical**（最小范数/对称固定/规范形）；
- 不可精确时 **approx ε**；
- 无符号规格时 **unsupported**，不能假装构造。

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

格式解析、I/O、C、conformance 属于 `ENGINEERING.md`，不进入 `ProofComplete`。

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

## 9. 架构载体

Conv / Attention / Norm / DAG 是 L3 载体插件，不是主线。
见 `ARCHITECTURE-CARRIERS.md`。

## 10. 证明义务

T0–T8，见 `PROOF-OBLIGATIONS.md`。

## 11. ProofComplete

```lean
def ProofComplete : Prop :=
  T0_construct ∧
  T1_compile ∧
  T2_penalty ∧
  T3_extract ∧
  T4_repair ∧
  T5_recovery ∧
  T6_spatial ∧
  T7_confluence ∧
  T8_failure ∧
  PluginRegistryComplete
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

## 12. 非目标

- 常规的端到端训练工具链（优化器、数据加载、分布式）；
- 训练收敛；
- 泛化界；
- 私有权重格式；
- 任意文件的字节级兼容；
- 把权重字面量导出当成构造。

## 13. 术语

见 `GLOSSARY.md`。
