# 层间反向依赖：实测清单与处理决定（阶段 C，P3-5）

## 本轮做了什么，以及它暴露了什么

**第 889 轮删除了 12 个**纯 façade**（零声明、只转导出 `Plugins/` 下真实模块）：**

| 被删的 façade | 指向 |
|:--|:--|
| **`Core/Logic`** | **`Plugins.Core.Constraint.Proofs`** |
| **`Core/Repair`, `Core/RepairAtomicity`, `Core/RepairConvergence`, `Core/RepairMultistep`, `Core/RepairWF`** | **`Plugins.Core.Repair.*`** |
| **`Core/VariableDerivative`** | **`Plugins.Extractors.ChainSlot.VariableDerivative`** |
| **`Lib/Architectures/RealBatchNormConsistency`** | **`Plugins.Architectures.Norm.Proofs`** |
| **`Lib/Architectures/RealGNNEquivariance`** | **`Plugins.Architectures.GNN.Proofs`** |
| **`Compose/Combinators`, `Compose/ComposeObligation`, `Compose/Laws`** | **`Plugins.Compose.*`** |

**删除后 38 个导入方被改指到 `Plugins/` 下的真实模块，构建保持绿色。**

## 结果：反向边数**上升**了，而且这正是**真实**的数目

| 度量 | 改前 | 改后 |
|:--|--:|--:|
| **`Core → Plugins`** | **8** | **4** |
| **`Lib → Plugins`** | **2** | **9** |
| **`Runtime → Plugins`** | **2** | **8** |
| **`Compose → Plugins`** | **3** | **4** |
| **`Primitives → Plugins`** | **0** | **2** |
| **反向边总计** | **56** | **68** |

**=> `Core → Plugins` 从 8 降到 4（façade 消除的直接效果），但 `Lib`、`Runtime`、`Primitives`
的反向边上升了。**

**原因是：那 12 个 façade 原本**替**下游模块承担了"我依赖 Plugins"这件事，
把它们删掉之后，那 38 个真实导入方各自暴露了自己的依赖。**

**=> 旧数字 56 是**被 façade 掩盖过的**；新数字 68 是**实际存在**的。
这不是退步，是把账记实。**

## 一个必须写下来的判断

**`Core(rank 1) → Plugins(rank 5)` 是**真正**的分层违规，`gate.py` 的 I4 本该抓到它。**

**I4 之所以一直是绿的，是因为它只检查 `Core/` 目录**直接导入**的模块名是否落在
`LAYER_OF` 的禁止集合里，而 `Core/Logic.lean` 导入的是 `Lattice.Plugins.Core.Constraint.Proofs`
—— 这在 `LAYER_OF` 里映射为 `plugins`，**确实**比 `core` 高，按理应当被抓到。**

**=> 值得独立核实 I4 的判定是否真的覆盖"经 façade 的间接依赖"。这一点尚未查清，
本轮**不**声称 I4 有缺陷，只登记这个疑点。**

## 本轮不做的事，以及理由

**把 `Plugins` 的内容下沉到 `Core`/`Lib` 是**大工程**：`Plugins/` 有 86 个模块，
其中 `Plugins.Core.Repair.*` 与 `Plugins.Core.Constraint.Proofs` 承载着 `Targets.*` 的验证链。**

**）而更根本的问题是**语义归属**：`Plugins/` 下的这些模块**是不是真的属于插件层**？
如果 `Repair` 与 `Constraint.Proofs` 是**框架基石**而不是插件，那么它们本来就该在 `Core` 里，
`Core → Plugins` 就不是违规而是**放错了位置**。**

**=> 这需要一次"模块归属审计"，而不是一次目录搬迁。本文件为那次审计准备清单。**

## 当前清单（每轮由 `gov/audit_layer_fanin.py` 重新测量）

**反向边共 10 类 68 处，按处数降序：**

1. **`Plugins(5) → Reference(7)` 19 处** —— 详见 `LAYER-CYCLE.md`（定义归属）
2. **`Semantics(4) → Reference(7)` 14 处**
3. **`Lib(3) → Plugins(5)` 9 处**
4. **`Runtime(2) → Plugins(5)` 8 处**
5. **`Usage(6) → Reference(7)` 6 处**
6. **`Compose(4) → Plugins(5)` 4 处**
7. **`Core(1) → Plugins(5)` 4 处** ← **最严重的分层违规**
8. **`Primitives(2) → Plugins(5)` 2 处**
9. **`Compose(4) → Reference(7)` 1 处**
10. **`Evidence(6) → Reference(7)` 1 处**
