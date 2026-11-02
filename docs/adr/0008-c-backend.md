# ADR-0008：C 是后续系统插件

## 状态

已接受。

## 决策

C 后端放在：

```text
Lattice/Plugins/Backends/C/
```

并在 `systemRegistry` 中，不进入 `ProofComplete`。

## 后果

- C 是可能的后续插件；
- 若将来要进入证明，必须先补 C 形式语义；
- 新增 `CRefinement` 义务；
- 在此之前，C 只是系统实现与信任边界。
