# 层间循环依赖：`Reference ⇄ Plugins`（阶段 C，P3-4）

## 实测到的事实

**`Lattice/Reference/` 与 `Lattice/Plugins/` 之间存在**双向依赖**，两个方向都是真实边，不是 façade：**

| 方向 | 边数 | 典型例子 |
|:--|--:|:--|
| **`Reference → Plugins`** | **17** | **`Geometry.Constraints.FlattenAgreement → Plugins.Domains.Constraints.Tokens.Flatten`** |
| **`Plugins → Reference`** | **19** | **`Plugins.Domains.Constraints.Tokens.Flatten → Geometry.Constraints.Expr`** |

**=> 这不是"某个文件导入错了"，而是两个层各自持有对方所需的定义。**

## 本轮已经消除的部分

**第 887 轮删除了 5 个**纯 façade**（`Reference/Geometry/Constraints/{Flatten, LossExtraction,
SeqRepresentation, NetLossDerivative, PenaltyLoss}.lean`，各 7 行、只有 1 条 import），
并把它们全部 16 个导入方改为直接指向 `Lattice.Plugins.Domains.Constraints.*`。**

**=> 这一项消除了 `Reference → Plugins` 中的 5 条边（原 22 降 17），构建保持绿色。**

**这 5 个 façade 的价值是**零**：它们不含任何声明，只把旧路径映射到新路径。
删除它们之后，那 16 个导入方拿到的是同一个模块，只是路径不再绕道。**

## 未能消除的部分，以及**为什么**

**剩下的 17 与 19 条边不是"路径问题"，是**定义归属问题**：**

- **`Geometry.Constraints.Expr`** 被 `Plugins.Domains.Constraints.Tokens.Flatten` 与 `SeqRepresentation` 使用 ——
  **表达式 AST 定义在 Reference 里，而 token 侧的实现需要它；**
- **`Geometry.Constraints.{Constraint, Dist, Lipschitz, DistLipschitz}`** 被
  `Plugins.Domains.Constraints.Penalty.PenaltyLoss` 使用 —— **约束/距离/李普希茨的定义在 Reference 里；**
- **`Geometry.Geometry.{PolyLipschitz, WeightSideLadder, ExprLocalMin, Semantic, ClosedLoop}`** 被
  `Plugins.Domains.Constraints.*` 与 `Plugins.Targets.*` 使用；**
- **反方向**：`Geometry.Constraints.FlattenAgreement`、`Geometry.Geometry.ClosedLoop` 等需要
  `Plugins.Domains.Constraints.Tokens.*` 的**实现**。

**=> 要消除循环，必须把 `Expr`、`Constraint`、`Dist`、`Lipschitz` 这批**共享定义**
从 `Reference` 移到**更低层**（`Core` 或 `Primitives`），使两侧都只往下依赖。**

**这是一次**跨 30+ 文件的重排**，而且会改动 `Reference` 的**语义归属**
（"参考实现"与"共享基础"是两种不同的角色）。**

## 为什么本轮不做这个重排

**三条理由，按重要性排列：**

1. **`Reference` 是归档/参考角色，`Plugins` 是在役代码。把定义从 `Reference` 提到 `Core`，
   等于宣布"这批几何定义是在役基础设施"，而第 187 轮刚刚判定几何内容**作废**。
   这两个判断冲突，必须先由使用者裁定哪一个成立；**
2. **循环依赖**没有**让构建失败**：`lake build Lattice` 绿，I1-I8 绿。
   Lean 的导入图允许循环，只是同一个模块不能被两个不同的 elaboration 路径重复定义。
   **=> 这是**可维护性**问题，不是**正确性**问题，因此按项目纪律应当**先登记**；**
3. **它会改动 `Plugins` 的 19 个在役模块**，而这些模块承载着 `Targets.*` 的一条完整验证链
   （`T2Min`、`T3NonVacuous`、`T4FixedPoint`）—— **在役代码的重排需要独立的验证轮次。**

## 因此本文件的作用

**把循环依赖登记为**已知的架构债**，包含精确的边清单，使任何后续处理都能：

- **知道准确范围（17 + 19 条边、涉及哪些模块）；**
- **不重复本轮的调查；**
- **在裁定"几何定义是否在役"之后，立即按清单执行重排。**

**`gov/audit_layer_fanin.py` 会在每一轮报告当前边数，因此这个数字**不会漂移而不被发现**。**
