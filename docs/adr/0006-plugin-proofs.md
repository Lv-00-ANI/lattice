# ADR-0006：证明按插件/层级/语义命名管理

## 状态

已接受。

## 决策

- 插件是能力契约，不是“一个文件一个插件”；
- 每个插件在其层级目录下有语义命名证明子文件夹；
- `Plugin.lean` 组装 `VerifiedPlugin`；
- `Registry.lean` 汇总 `proofRegistry`；
- `ProofComplete` 由 registry 驱动；
- `Proof/` 不作为泛化目录名，使用 `Soundness/` 等语义名。

## 后果

- 每个定理必须归属一个插件；
- 旧路径迁移期只做 facade；
- 迁移完成后删除 facade；
- `gate` 需要 orphan/duplicate 检查。
