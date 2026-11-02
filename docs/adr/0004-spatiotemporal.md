# ADR-0004：时空可组合运行时

## 状态

已接受。

## 决策

采用 Cordis 式时空可组合设计：

- 时间：可逆效应 + snapshot；
- 空间：反应式余效应 + provider 解析；
- 汇合：动态演化后的最终模型 = 从最终 Spec 重建。

## 后果

- 每个转换插件必须给 inverse 或 snapshot；
- 依赖必须无环；
- 证书绑定 provider/artifact；
- 导出是 emission，不可逆；
- T5–T8 必须在 Lean 中重新证明，不能直接导入论文定理。
