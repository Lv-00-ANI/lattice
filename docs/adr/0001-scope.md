# ADR-0001：转换层，不是常规训练框架

## 状态

已接受。

## 决策

LATTICE 不实现 optimizer、data loader、分布式训练、SFT、DPO、RLHF。

它实现：

- 符号 ⇄ 权重的转换；
- 构造性预训练（`Construct`）；
- 逆向提取、验证、修复；
- 可扩展插件运行时。

## 后果

- 训练正确性不由 LATTICE 证明；
- 外部训练产物标记 `Imported` / `Empirical`；
- `ProofComplete` 不包含训练；
- 训练框架仍可作为 `Delegate` 后端。
