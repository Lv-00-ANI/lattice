# MIGRATION TO PLUGINS

## 1. 目标

把现有证明全部重构为能力插件，并保证：

- 每个定理恰好归属一个插件；
- 每个插件至少一个 obligation；
- 没有 orphan；
- 没有 duplicate；
- 旧路径迁移期只做 facade，完成后删除。

## 2. 粒度

按**能力边界**划分，约 20–40 个插件。
不是“一个文件一个插件”，也不是“873 个插件”。

## 3. Phase 0：清点

新增脚本：

```text
gov/plugin_inventory.py
```

输出：

```text
plugin-map.tsv
```

字段：

```text
theorem | file | line | proposed_plugin | proposed_obligation
```

验收：

- 每定理恰好一个插件；
- 每插件至少一个 obligation；
- orphan = 0；
- duplicate = 0。

## 4. Phase 1：试点

先迁移：

```text
Domains/Constraints/Penalty/
```

迁移内容：

- `Semantics.lean`；
- `Soundness/`；
- `Exactness/`；
- `Approximation/`；
- `Manifest.lean`；
- `Plugin.lean`。

旧路径保留 facade，只 import 新插件。

验收：

- `Plugin.lean` `#check`；
- `ProofComplete` 能看到该插件；
- 旧 import 仍工作；
- I3 无重复定义。

## 5. Phase 2：批量迁移

顺序：

1. Core/Constraint；
2. Core/Repair；
3. Runtime/Tokenization；
4. Runtime/ProgramSemantics；
5. Domains/Constraints；
6. Domains/Geometry；
7. Compose；
8. Semantics；
9. Architectures/Conv、Attention、Norm、DAG。

规则：

- **移动，不复制**；
- 旧路径只 facade；
- 更新 `plugin-map.tsv`；
- `gate` 跑 I3/I4/I5。

## 6. Phase 3：Registry

```lean
-- Lattice/Plugins/Registry.lean
import Lattice.Plugins.Core.Constraint.Plugin
...
def proofRegistry : List VerifiedPlugin := [...]
```

验收：

- 所有插件在 registry；
- 所有 obligation 有 theorem；
- `ProofComplete` 类型检查；
- `#print axioms` 干净。

## 7. Phase 4：删除 facade

- 删除旧路径；
- 全库 import 改为插件路径；
- orphan / duplicate 归零；
- `PROOF-DEBT` 按插件生成。

## 8. 禁止

- 复制语义（只允许移动 + facade）；
- 在证明文件夹 import `Plugin.lean`；
- 让插件反向依赖上层；
- 用 `axiom` / `sorry` / `register` 填充 obligation。
