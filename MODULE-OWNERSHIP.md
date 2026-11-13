# 模块归属审计：`Plugins/` 下混入了内核代码（阶段 C，P3-6）

## 第 889-890 轮建立的证据链

**第 889 轮把 `Plugins` 加入 I4 的 `LAYER_OF`/`rank` 映射表后，I4 报出 `core → plugins` 5 条违规。**

**第 890 轮逐个核查了这些边，结论是**不是导入写错了，而是模块放错了**：**

| 模块 | `namespace` | 谁依赖它 |
|:--|:--|:--|
| **`Plugins/Core/Repair/Repair.lean`** | **`namespace Lattice.Core`**（第 52 行） | **`Core/Invariant.lean`、`Core/OneStepBridge.lean`** |
| **`Plugins/Core/Repair/RepairConvergence.lean`** | **`namespace Lattice.Core`** | **`Core/OneStepBridge.lean`** |
| **`Plugins/Core/Constraint/Proofs.lean`** | **`namespace Lattice.Core`** | **`Core/IR/T4Repair.lean`、`Lib`** |

**=> 这三个文件的**名字空间就是 `Lattice.Core`**。它们从来不是插件代码。**

## 它们是怎么跑到 `Plugins/` 下的

**`Plugins/Core/Repair/Repair.lean` 的文件头写着：**

> **「`# The `Core.Repair` plugin's proofs -- MOVED from `Lattice/Core/Repair.lean`」**
> **「The DECLARATIONS do not change -- same names, same statements, same proofs, same namespace.」**

**=> 这是一次**已经发生过的迁移**，方向是 `Core/ → Plugins/Core/`，而且迁移的只是文件位置，
名字空间保持 `Lattice.Core` 不变。**

**那次迁移的理由已经无从查证（相关轮次记录不在树里），但它产生了一个**可测的结果**：
内核代码位于插件层，于是内核层必须向上依赖插件层。**

## 为什么这是一次真正的分层违规

**一个被内核必需的模块，按定义就不是「可插拔」的。**
**`Repair` 的 T4 验证回路是**框架基石**：`Core/Invariant.lean` 与 `Core/OneStepBridge.lean`
直接依赖它。把基石放在 `Plugins/` 下，等于宣布「内核为了工作必须装一个插件」——
这不是插件架构，这是把名字用错了。**

## 本轮的处置

**把这三个文件（连同同属 `Plugins/Core/Repair/` 的 `RepairAtomicity`、`RepairMultistep`、`RepairWF`，
它们同样是 `namespace Lattice.Core`）下沉回 `Lattice/Core/Repair/`，并把所有导入方改指。**

**`Plugins/Core/Repair/` 与 `Plugins/Core/Constraint/` 保留 `Manifest.lean` 与 `Plugin.lean`——
那两个的 namespace 是 `Lattice.Plugins.Core.*`，它们是**真正的**插件（声明插件的义务与清单），
而不是内核证明。**

## 判据（可复用的规则）

**判断一个模块属于哪个层，看它的 `namespace`，不看它的目录：**

- **`namespace Lattice.Core` 的实现 ⇒ 属于 `Core/`；**
- **`namespace Lattice.Plugins.X` 的清单/义务 ⇒ 属于 `Plugins/`。**

**=> 目录是**位置**，namespace 是**身份**。两者不一致时，以 namespace 为准，
因为所有**引用**都是按 namespace 写的。**

## 这不解决的那一半

**`plugins → reference` 的 19 条边与它无关**，那是 `LAYER-CYCLE.md` 记录的定义归属问题
（`Expr`/`Constraint`/`Dist`/`Lipschitz` 住在 `Reference` 里）。**本轮只处理 `core → plugins`。**
