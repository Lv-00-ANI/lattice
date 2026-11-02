# ROADMAP

## 证明路线

### P0 Lean 插件框架

- `PluginManifest` / `VerifiedPlugin` / `Registry`；
- 语义化证明文件夹；
- `ProofComplete` 由 registry 驱动。

### P1 插件清点 + 试点

- `gov/plugin_inventory.py`；
- `plugin-map.tsv`；
- 试点 `Domains/Constraints/Penalty`。

### P2 批量迁移

- Core/Constraint；
- Core/Repair；
- Runtime/Tokenization；
- Runtime/ProgramSemantics；
- Domains/Constraints；
- Domains/Geometry；
- Compose；
- Semantics；
- Architectures。

### P3 Registry + ProofComplete

- 所有插件入 registry；
- 所有 obligation 有定理；
- `ProofComplete` 类型检查；
- `#print axioms` 干净。

### P4 语义化证明文件夹

- `Soundness/`、`Completeness/`、`Laws/`、`Exactness/`；
- `Approximation/`、`Recovery/`、`Spatial/`、`Confluence/`；
- `Equivariance/`、`Idempotence/`、`Invariants/`。

### P5 架构载体插件

- Conv / Attention / Norm / DAG；
- 各自 `Manifest` / `Semantics` / 证明文件夹。

### P6 证明升级

- `ProofUpgrade`；
- 加强/推广/抽象；
- `PROOF-DEBT` 按插件生成。

## 工程路线（不在 ProofComplete）

### E1 FormatAdapter / 权重 I/O

- `RawModel` / `FormatAdapter`；
- 不支持格式显式拒绝。

### E2 C backend

- `systemRegistry`；
- 不进入 `ProofComplete`。

### E3 conformance / runtime loader

- 测试证据；
- 不冒充证明。

### E4 外部训练器 adapter

- Delegate；
- 证书 Imported/Empirical。

## 验收

每项给：

- 定理名；
- `file:line`；
- `#check`；
- 反例/边界；
- ε（如适用）。
