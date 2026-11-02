# SPATIOTEMPORAL COMPOSABILITY

## 0. 参考

**A Programming Paradigm for Spatiotemporal Composability**
Yifan Shi, Wei Zhang, Tianyi Cui
Peking University / DeepSeek-AI
arXiv:2608.25512
<https://arxiv.org/abs/2608.25512>
<https://github.com/cordiverse/paper>

该论文是 **preprint under active revision**；本项目只借其运行时设计，不把论文中的定理当作已机器验证的前提。LATTICE 的 T5–T8 必须在 Lean 中重新证明。

## 1. 两个维度

### 1.1 时间可组合性

论文把 effect 定义为：

```text
Γ → Γ × (Γ → Γ)
```

- 前半：修改后的上下文；
- 后半：显式 inverse；
- 组合：twisted composition（inverse 逆序累积）；
- 卸载：按 LIFO 执行 inverse。

LATTICE 对应：

| 论文 | LATTICE |
|:--|:--|
| `Γ` | `LatticeContext` |
| effect | `compile` / `edit` / `merge` / `quantize` / `repair` |
| inverse | snapshot / delta / ε-compensation |
| fiber | 插件实例 |
| `recover` | 卸载插件时执行 undo |

### 1.2 空间可组合性

论文的 coeffect context 是依赖键到值的依赖部分函数：

```text
Σ = (k : K) ⇀ V_k
```

组件声明 `d ⊆ K`，`notify` 把状态变化分类为：

```text
activating | deactivating | neutral
```

LATTICE 对应：

- service key：SymbolDomain / Carrier / Compiler / Extractor / Verifier / Repairer；
- 插件 `requires` / `provides`；
- provider 出现 → 依赖者激活；
- provider 消失 → 依赖者先撤销自己的 effect，再允许 provider 卸载。

## 2. LATTICE 的 effect 模型

```lean
structure LatticeEffect where
  run  : State → State × (State → State)
  mode : EffectMode
  cert : Option Cert
```

```lean
inductive EffectMode
| reversible      -- exact undo
| snapshot        -- restore previous artifact
| approximate     -- ε; undo by snapshot
| irreversible    -- must commit; cannot pretend reversible
```

### 2.1 `compile` 不是 `extract` 的逆

LATTICE 已有：

```lean
semantic_not_injective
no_extractor_preserves_both
```

因此：

- `compile` 的 inverse **不能**写成 `extract`；
- 正确做法：`compile` 记录旧 artifact 的 snapshot；
- `undo` = restore snapshot；
- `extract` 是观察，不是 inverse；
- `merge` / `quantize` 可能是 `irreversible` 或 `approximate`；
- 导出到外部文件/网络是 **emission**，不可逆，只能版本化/补偿。

## 3. 空间依赖

依赖顺序：

```text
Carrier < Compiler < Extractor < Verifier < Repairer < Orchestrator
```

禁止反向依赖：

- `Carrier` 不依赖 `Compiler`；
- `Compiler` 不依赖 `Repairer`；
- `Repairer` 不反向依赖 `Orchestrator`。

## 4. 证明义务 T5–T8

```lean
theorem lattice_recovery_exact : ...
theorem lattice_ordering : ...
theorem lattice_resolution_coherent : ...
theorem lattice_confluence : ...
theorem lattice_failure_isolated : ...
```

- T5：卸载插件只撤销自己的影响，保留其他插件效果；
- T6：依赖满足才启动；provider 替换时先 deactivate 依赖者；
- T7：动态演化后的最终模型 = 从最终 Spec 重建；
- T8：失败插件隔离并回滚。

## 5. 边界：acquisition vs emission

| 类别 | 例子 | 是否可逆 |
|:--|:--|:--|
| acquisition | 注册符号、保存权重快照、写证书、缓存 | ✅ 可撤销 |
| emission | 导出文件、上传、网络、调用外部训练器 | ❌ 只能补偿 |

LATTICE 的“完全可逆”只覆盖边界内的符号/权重/证书。
导出是工程行为，不属于证明部分。

## 6. 扩展

- **异步**：inertia，不中断 in-flight effect；
- **失败**：FAILED fiber + rollback；
- **隔离**：realm，键为 `K × R`；
- **配置修订**：retire + reinsert，依赖者自动重算。

## 7. 诚实边界

- 论文是 preprint；
- 只借设计，不导入定理；
- T5–T8 必须自己在 Lean 中证明；
- 外部 emission 不承诺撤销。
