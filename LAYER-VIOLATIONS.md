# I4 分层违规：实测 42 条（阶段 C，P3-5）

## 本轮最重要的一件事：I4 之前**看不见 `Plugins/`**

**`gate.py` 的 `LAYER_OF` 里**没有** `Lattice/Plugins`，`rank` 表里也没有 `plugins`。
于是 `layer_of()` 对 `Plugins/` 下全部 86 个模块返回 `"top"`，而 `check_layering` 对 `"top"` 的处理是**跳过**。**

**=> I4 从未检查过任何一个插件模块的导入。**

## 补上之后，I4 立刻报出 42 条违规

**在第 889 轮把 `Plugins`（rank 3）与 `Usage`（rank 7）加入两张表之后：**

| 方向 | 条数 |
|:--|--:|
| **`plugins → reference`** | **19** |
| **`runtime → plugins`** | **8** |
| **`core → plugins`** | **5** |
| **`plugins → audit`** | **4** |
| **`plugins → compose`** | **4** |
| **`primitives → plugins`** | **2** |
| **合计** | **42** |

**这些边**一直存在**；它们之所以从未被报告，只是因为那两个层不在映射表里。**

## 每条的方向判读

**`core → plugins`（5 条）与 `primitives → plugins`（2 条）是**真正的倒置**：
内核层依赖插件层。`Core/IR/T4Repair.lean`、`Core/Invariant.lean`、`Core/OneStepBridge.lean`、
`Core/PluginComplete.lean` 都导入 `Plugins.Core.Repair.*` 或 `Plugins.Core.Constraint.Proofs`。**

**`runtime → plugins`（8 条）同理，`Runtime` 是 rank 2，`Plugins` 是 rank 3。**

**`plugins → reference`（19 条）与 `plugins → audit`（4 条）是**向上的**，方向本身合法
（rank 3 → 4 / 5），但 `LAYER-CYCLE.md` 已说明 `plugins → reference` 构成了循环。**

**`plugins → compose`（4 条）方向合法（3 → 6）。**

## 这些违规的**真实**解释：模块归属放错了，不是导入写错了

**`Plugins.Core.Repair.*` 与 `Plugins.Core.Constraint.Proofs` 被 `Core/` 直接依赖 —— 说明它们
**不是插件**，而是**框架基石**。一个"插件"若被内核层必需，它就不是可插拔的。**

**=> 正确的修法不是删掉那些 import，而是把这几组模块**下沉到 `Core/`**，
使 `Core` 依赖自己层内的东西。**

**这与 `LAYER-CYCLE.md` 的处理是同一种判断：语义归属问题，需要一次模块归属审计，
而不是一次目录搬迁。**

## 本轮的处置：登记，而不是掩盖

**我**没有**把 `Plugins` 从映射表里撤回去让它重新变绿。**

**=> 那个 green 是**假的**：它来自一个从未被检查过的层。
把 42 条违规重新藏起来，等于用一次回归换取一个漂亮的报告。**

**=> 本文件是那 42 条的登记册；`gov/gate.py` 会**每轮**报告它们，
数字变动立即可见。**

## 待办的模块归属审计（下一轮或使用者裁定后）

**三个问题按优先级：**

1. **`Plugins.Core.Repair.*`（5 个模块）是否应下沉到 `Core/`？**
   它们被 `Core/Invariant.lean`、`Core/OneStepBridge.lean`、`Core/PluginComplete.lean`、
   `Core/IR/T4Repair.lean` 直接依赖 —— **证据指向"应下沉"。**
2. **`Plugins.Core.Constraint.Proofs` 同理**（被 `Core/` 与 `Lib/` 依赖）。
3. **`Plugins.Targets.*` 与 `Plugins.Domains.Constraints.*` 是否真的是"插件"？**
   它们被 `Runtime`、`Primitives`、`Semantics`、`Usage`、`Evidence` 使用 ——
   **若被半个树依赖，"插件"这个名字就不适用了。**

**=> 三个问题都指向同一个结论：`Plugins/` 这个名字下的内容混杂了两类东西 ——
**可插拔的架构插件**（`Architectures.Attention` 等）与**框架基石**（`Core`、`Targets`）。
把它们分开是一次**有意义的**重构，但它会改动 86 个模块中的大部分，需要独立轮次。**
