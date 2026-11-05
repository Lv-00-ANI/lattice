# CONFLUENCE

## 0. 载体

`trace`、`construct`、`finalSpec` 定义在 **CIC 载体**上：

- `run : Trace → CIC.State → CIC.State`；
- `construct : Spec → Option ModelArtifact`；
- `finalSpec : Trace → Spec`；
- `ResultEquiv` 的 `behavior` 或 `approx` 口径。

几何版本（`Plugins/Runtime/RTargets.t7_confluence`）只是两个单键写入的交换性，
**不是**本文件第 1 节的命题；不得以它冒充 T7。

## 1. 命题

动态加载/卸载/替换插件后的最终模型，等价于从最终配置重新构造一次：

```lean
theorem lattice_confluence :
  ∀ trace, quiescent (run trace s) →
    run trace s ≃ construct (finalSpec trace)
```

- `≃` 是 `ResultEquiv` 的 `behavior` 或 `approx` 口径，不是字节相等；
- `construct (finalSpec trace)` 必须对最终 Spec 有定义；
- 如果最终 Spec 不可构造（不在 `Typable` 或有 `no_specSolver` 形态），只能 import/transform，
  不能声称从零重建。

## 2. 条件

1. 依赖优先级无环；
2. 每个插件 total：激活后提供所有声明的 service；
3. 效果 pairwise independent，或重叠键已串行化；
4. 无 `FAILED`；
5. 无未补偿 emission；
6. `construct (finalSpec trace)` 有定义；
7. 每个插件的 `Obligation.theoremName` 在树中真实存在（由 `check_obligation_names.py` 检查）。

## 3. 反例

- 两个插件写同一权重键，且写操作不可交换；
- provider 在依赖者 deactivate 前被卸载；
- 编译失败但继续使用半成品；
- 导出到外部文件后回滚；
- 非 total 插件只提供部分 service；
- 最终 Spec 不可构造。

## 4. 变体

| 变体 | 条件 | 结论 |
|:--|:--|:--|
| `serialized_confluence` | 重叠键串行化 | 最终 = 串行重建 |
| `compensated_confluence` | emission 有补偿 | 最终 ≈ 重建 |
| `approx_confluence` | 允许 ε | 最终 ≈ε 重建 |

## 5. 证明草图

1. 每个插件的 recovery exactness（T5）；
2. 独立 effect 的交换引理；
3. 删除已卸载 fiber 的 episode 不改最终状态；
4. 归纳到 canonical 顺序；
5. canonical 顺序 = 从最终配置组装；
6. 由 `construct` 定义得到最终 = `construct(finalSpec)`。

## 6. 不覆盖

- emission 的物理不可逆；
- 失败插件的内部状态；
- 私有格式解析；
- 训练过程本身。

