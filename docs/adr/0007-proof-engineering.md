# ADR-0007：证明/工程分离

## 状态

已接受。

## 决策

证明部分：

- Lean 语义；
- Construct；
- Compile；
- Extract；
- Repair；
- Effect / Coeffect；
- Confluence；
- 插件证明。

工程部分：

- 格式解析；
- 权重 I/O；
- C ABI；
- conformance；
- runtime loader。

## 后果

- `ProofComplete` 不含 `Format`；
- 工程失败不影响数学定理，但影响系统；
- 工程必须显式声明信任边界；
- 工程文档不得写“已证明”。
