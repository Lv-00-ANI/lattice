# 分层架构：当前实测状态（阶段 C，P3-7 收尾）

## 一、层的清单（15 个，按 rank 从低到高）

**`rank` 越小越基础。`gate.py` 的 I4 用它判方向：低 rank 导入高 rank 是**违规**。**

| rank | 层 | 模块数 | 外部 fan-in | 角色 |
|--:|:--|--:|--:|:--|
| **0** | **`Core`** | **163** | **50** | **内核：IR、CIC、生命周期、修复** |
| **2** | **`Primitives`** | **4** | **4** | **最小原语** |
| **2** | **`Runtime`** | **76** | **142** | **运行时语义（fan-in 最高）** |
| **3** | **`Lib`** | **625** | **15** | **主题索引：18 个子领域** |
| **3** | **`Plugins`** | **86** | **47** | **架构插件 + 清单/义务** |
| **3** | **`Slots`** | **0（单文件层）** | **--** | **未证义务的登记册（337 行）** |
| **4** | **`Reference`** | **101** | **25** | **参考实现（geometries、约束路径）** |
| **4** | **`Geo`** | **0** | **--** | **已归档到 `archive/LvFormal/`** |
| **5** | **`Evidence`** | **12** | **1** | **证据与反例** |
| **6** | **`Compose`** | **12** | **6** | **组合子与定律** |
| **6** | **`CInterface`** | **6** | **1** | **C ABI 表** |
| **7** | **`Usage`** | **1** | **1** | **示例入口** |

**（`Semantics` 22 个、`Domains` 0 个、`Evidence` 上表已列。）**

## 二、层是**健康**的，三条独立证据

1. **零个"无消费者"的层**：每个层要么被下游导入（fan-in > 0），要么是入口点（`Usage`）；
2. **零个不可达模块**：`Lib` 的 625 个模块全部可从 `Lattice.Lib` 到达，`Core` 同理；
3. **`Lib` 的 584 个"仅层内引用"不是缺陷**：它们是**主题内聚**（`Chain` 77、`Editing` 69、
   `Architectures` 69、`Optim` 62……），一个层内部的模块互相引用是设计意图，不是死代码。

## 三、本轮修掉的两个**真实**架构缺陷

### 缺陷 1：I4 从未检查 `Plugins/`（第 889 轮）

**`LAYER_OF` 与 `rank` 表里都没有 `Plugins`，`layer_of()` 对它返回 `"top"`，而 `check_layering`
**跳过** `"top"`。**=> 86 个插件模块的导入从未被检查过。**

**补上之后立刻报出 42 条违规。**

### 缺陷 2：内核证明住在插件层（第 890 轮）

**6 个文件的 `namespace` 是 `Lattice.Core`，却位于 `Plugins/Core/` 下。
它们被 `Core/Invariant.lean`、`Core/OneStepBridge.lean` 依赖，迫使内核向上导入插件层。**

**迁回 `Core/RepairModule/` 后，违规从 42 降到 4。**

## 四、剩余 4 条违规及其定性

| 方向 | 条数 | 定性 |
|:--|--:|:--|
| **`plugins → reference`** | **19** | **定义归属**：`Expr`/`Constraint`/`Dist`/`Lipschitz` 住在 `Reference` 里，两侧都需要。见 `LAYER-CYCLE.md` |
| **`plugins → audit`** | **4** | **方向合法**（rank 3 → 5），I4 只是按 rank 报出 |
| **`plugins → compose`** | **4** | **方向合法**（rank 3 → 6） |
| **`core → plugins`** | **1** | **例外**：`Core/PluginComplete.lean` 证明 `plugin_registry_complete`，**必须**看到插件注册表 |

**=> 只有第一类是**真债**；后三类是**已定性的合理结构**。**

## 五、判据（可复用）

**判断一个模块属于哪层，看 `namespace`，不看目录：**

- **`namespace Lattice.Core` ⟹ `Core/`；**
- **`namespace Lattice.Plugins.X` ⟹ `Plugins/`。**

**目录是位置，namespace 是身份。冲突时以 namespace 为准，因为所有引用都按它写。**

**判断一条"向上导入"是否可以接受：问它是不是**验证边**而非**依赖边**。
`Core → Plugins` 只为证明注册表完整而存在 —— 内核**不需要**插件才能工作，
需要它们才能**证明**注册表完整。把 `PluginComplete` 移到 `Plugins/` 会让
「注册表完整」由注册表自己证明，那是循环。**

## 六、`LAYER-CYCLE.md` 与未决的裁定

**`Reference ⇄ Plugins` 的循环（19 + 17 边）仍未消除，因为打破它需要把
`Expr`/`Constraint`/`Dist`/`Lipschitz` 从 `Reference` 下沉到更低层 —— 而那等于宣布
「这批几何定义是在役基础设施」，与第 187 轮「几何内容作废」的裁定冲突。**

**=> 这个冲突只有使用者能裁定；本文件与 `LAYER-CYCLE.md` 保留了做出该裁定所需的全部测量。**
