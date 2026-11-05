# ROADMAP

> **2026-11-05 重排：** 主载体从几何改为 CIC（见 `CARRIER-REPLACEMENT.md`）。
> CIC 的最小验证（C0）先于一切；旧的 P0–P6 顺序保留为“CIC 之后的内容”。

## CIC 路线（先行）

### C0 最小验证（3 天）

- `Lattice/Core/CIC/Syntax.lean`：`Term` / `Level` / de Bruijn；
- `Lattice/Core/CIC/Reduction.lean`：β/δ/ι/ζ；
- `Lattice/Core/CIC/Typing.lean`：`Typable`；
- **V1** `typable_has_term`；
- `Lattice/Core/CIC/Encode/Geometry.lean`：`encode` 12 构造子；
- **V2** `encode_sound`。

**通过条件：** V1 与 V2 都 `lake build` 通过，且都不是 `rfl`。
**不通过：** 回滚（见 `CARRIER-REPLACEMENT.md §4`）。

### C1 CIC 完整层（7 天）

- `Substitution.lean`；
- `Normalization.lean`（弱规范化 + `steps` 界）；
- `Encode/Geometry.lean` 补完备性；
- 反方向 `decode` 的部分性与 `no_full_decode` 反例。

### C2 T0–T4 在 CIC 上重述（10 天）

- T0 `construct`：`Typable → Term → Weights`；
- T1 `compile_sound`：结论必须含 `t`；
- T2 `modulus`：`steps t * ε`；
- T3 `extract_compile`：到 `NormalForm`；
- T4 `repair` + `conj_loop_fixed_point`。

### C3 T5–T8 在 CIC 上（8 天）

- effect = elaborator state；
- `canActivate` / `unload_removes_only_own`；
- `Trace` / `finalSpec` / `construct` / `ResultEquiv`；
- `Fiber` / `rollback` / `Cert`。

### C4 几何降级（4 天）

- `Domains/Geometry` 标注为 `Encode/Geometry` 实例；
- 旧几何靶定理标 `[domain-legacy]`；
- `Plugins/Targets` 双写期结束。

---

## 判据诚实性（与 CIC 并行，不依赖 C0）

### H0 P0 判据（2 天）

- 清 7 条自数 `rfl`；
- 清 3 条 `String` 伪证明；
- 清 4 条 `True` 结论；
- 别名 `c6` 去掉；
- `t0_empty_spec` 的 `n` 修正；
- `migratedPluginCount` / `registeredPluginCount` 改为推导；
- 4 处 `theoremName` / 路径修正；
- 新建 `gov/check_obligation_names.py`；
- `gate.py` 给 `Plugins` rank、`Semantics` 改名；
- README 补 6 层。

### H1 P1 去重（3 天）

- `Plugins.lean` 四处 11 元 `rcases` → 一处；
- 11 条 `_mem` → 1 条；
- 8 条 `pluginDirOf_X` → 1 条；
- 6 条 `*_under_dir` → 内联；
- 三个 solver → 参数化 `anchoredSolve`；
- 四条 `holdsSet_*` + 三条 `penaltySum_*` → 各一条；
- 三条 `*Anchor_separates` → 一条；
- `T2Min` 重复反例删除。

净省约 490 行。

### H2 P2 语义重组（4 天）

- `PluginProof` 按 `Obligation.theoremName` 索引（不是按 kind，GNN 有 3 条 `equivariance`）；
- `SymbolicSummary` 迁 `Core`；
- `T3Instances` + `T3NonVacuous` 合并；
- `mem_merged_*` 迁 `Semantics/Merge`；
- `violation` 迁 `Domains/Geometry`；
- `affineLayerToMLayer` 迁 `Core`；
- `Core` 两个 `relu` 统一。

### H3 P3 层迁移（6 天）

前置：`gate.py` 给 `Plugins` rank 后，19 处反向依赖会红——预期。

顺序：

1. A2 `Spatiotemporal` + `RTargets` → `Runtime/`；
2. A3 `Core/{Constraint,Repair}` → `Core/`；
3. A4 `Domains/Constraints/{Penalty,Tokens}` → `Domains/`；
4. A1 `Targets` → `Semantics/Spec`；
5. A5 `ChainSlot`（259 KB）→ `Core/`。

---

## 旧 P0–P6（CIC 之后仍适用）

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

五个载体统一 `CarrierPlugin`；接 CIC。

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
- 不进入 `ProofComplete`；
- 只写 Lean 侧规格（ABI / 布局 / 序列化 / conformance / refinement），不写 C 代码。

### E3 conformance / runtime loader

- 测试证据；
- 不冒充证明。

### E4 外部训练器 adapter

- Delegate；
- 证书 Imported/Empirical。

### E5 CIC 实现（工程侧，已立项）

- parser / elaborator / evaluator；
- 与 Lean 侧语法/规则解耦；
- 实现更换不影响证明。

## 验收

每项给：

- 定理名；
- `file:line`；
- `#check`；
- 反例/边界；
- ε（如适用）。
