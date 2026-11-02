# ADR-0002：产物只针对模型/权重

## 状态

已接受。

## 决策

Lean 内只存在抽象模型对象：

```lean
structure ModelArtifact where
  arch : Arch
  weights : Weights
```

- 没有 `format`；
- 没有 `bytes`；
- 没有文件系统。

格式解析、权重 I/O、导出、C、conformance 属于 `ENGINEERING.md`，不进入 `ProofComplete`。

## 后果

- `ResultEquiv` 使用 `weights` / `behavior` / `approx`；
- `bytes` 等价属于工程测试；
- `Opaque` 只作为工程 fallback；
- 不声称任意文件格式的语义解析。
