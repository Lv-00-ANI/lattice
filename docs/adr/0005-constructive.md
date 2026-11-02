# ADR-0005：可从零构造，但不是权重抄写

## 状态

已接受。

## 决策

`Construct` 从 `Spec` 解出权重，生成 `ModelArtifact`。

只对 `ExpressibleSpec` 成立。

把 checkpoint 的权重写成字面量不算 `construct`。

## 后果

- `construct_sound` / `construct_complete` 只对 `ExpressibleSpec`；
- 无符号规格的模型只能 `import` / `transform`；
- 训练不是 `construct` 的必要条件；
- `Construct` 与 `Import` 必须分开。
