# ADR-0003：T2 精确不可达，ε 桥是主线

## 状态

已接受。

## 决策

T2 的无条件精确形式已被证否。

一般情形改为：

```lean
IsLocalMin (loss p) x → violation p x ≤ g ε
```

精确只在具体载体上声明。

## 后果

- 不再用 2/12、解处、SafeBranch 作为闭合；
- 必须补 `penalty_min_to_violation`；
- `ε→0` 必须有定理；
- `PenaltyEmbedding` 的 C 层不再标 `later` 而不进债务。
