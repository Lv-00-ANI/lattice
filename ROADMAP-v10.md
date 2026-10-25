# LATTICE 第七轮规划（ROADMAP-v10）

> 生成时点：2026-10-25，第 38 轮。
> 前置：`ROADMAP-v9` 完成；欠账 4 条；文档 14 份。

---

## 0. 本轮做的事：文档数字的**整体复测**

前几轮逐项测量了代码。**本轮测量的对象是文档本身**：14 份文档里的数字性断言，
是否仍然与树一致？

### 0.1 复测结果

| 文档 | 断言 | 树 | 判定 |
|:--|--:|--:|:--|
| `README` 层计数（Core/Lift/Geo/Lib） | 16 / 35 / 65 / 588 | 同 | ✅ |
| `README` 检查器数 | 39 | 39 | ✅ |
| `REFUTATION-CENSUS` 否证数 | 387 | 387 | ✅ |
| `REPAIR-CENSUS` A 类 | **6 文件 / 27 声明** | **9 文件 / 28 声明** | ❌ **漂移** |

**一处漂移**，来自本会话第 22、28、36 轮新增的三个文件。

### 0.2 一处我自己制造的二次错误

发现漂移后，我先写「9 文件 / **30** 声明」——**没有实测**，是推算的。

实测后正确值是 **28**：

| 文件 | fix/repair 命名声明 |
|:--|--:|
| `Geo/Loop` | 10 |
| `Geo/LoopPerp` | 4 |
| `Geo/ConjRepair` | 3 |
| `Core/Repair` | 3 |
| `Lib/Linear/Residual` | 5 |
| `Lib/Linear/Multivar` | 2 |
| `Core/RepairMultistep` | **0**（定义的是 `countdown`） |
| `Core/RepairAtomicity` | **0**（定义的是 `mkWithAtomic`） |
| `Usage/Examples` | 1（`natRepair`） |

**文件数 +3，声明数 +1。** 这个区别本身写进了清册——
它正是 `REPAIR-CENSUS §4` 自己警告过的事：**名字过滤不等于测量**。

---

## 1. 本轮结论：文档与代码的同步是**持续**工作，不是一次性

`CONVENTIONS §7` 已记录过一次「数字全部漂移」。
本轮证明：**即使有了记录，漂移仍会发生**——因为记录本身不会自动更新。

### 1.1 已有机制，以及它的覆盖面

| 机制 | 覆盖 | 能失败？ |
|:--|:--|:--|
| `audit_counts.py` | README 的 7 项计数 | ✅ 是门禁 |
| `check_proof_chain_rung.py` | 证明链文档的实例普查 | ✅ |
| `check_chain_deps.py` | 12 条定理的依赖数 | ✅ |
| **其余文档的数字** | `REPAIR-CENSUS`、`REFUTATION-CENSUS`、`USAGE` | ❌ **无守卫** |

⇒ **漂移发生在无守卫的地方**，这与预期一致。

---

## 2. 新规划

### 2.1 第一优先：把 `REPAIR-CENSUS` 的数字变成可判定

**做什么**：新增 `gov/check_repair_census.py`，测量 A/B/C 三类的文件数与声明数，
与清册中的数字比对，不一致即失败。

**规模**：S。**为什么第一**：它把本轮手工发现的漂移变成**自动发现**，
从此这个数字有守卫。

### 2.2 第二优先：`REFUTATION-CENSUS` 的守卫

同理：387 这个数字目前靠 `build_census2.py` 手工跑。
把它接进门禁，数字变化时失败并要求更新。

**规模**：S。

**注意**：本轮的复测显示 387 仍正确（本轮新增的否证定理已计入）。
但**下轮新增定理时就会漂移**。

### 2.3 第三优先：一份「数字来源」总表

**问题**：14 份文档、几十个数字，每个都来自不同脚本。
一个读者无法知道「这个数字谁负责保证」。

**做什么**：在 `CONVENTIONS §6`（已有的「数字口径」）扩写成一张表：

| 数字 | 出现在 | 由谁保证 | 能否失败 |
|:--|:--|:--|:--|

**规模**：S。**价值**：它让「哪个数字可信」变成可查的，而不是靠信任。

### 2.4 不做的

| 事项 | 理由 |
|:--|:--|
| 更新 `ROADMAP-v3`–`v9` 的数字 | 它们是**历史记录**，数字描述的是当时的树；改它们就是篡改历史 |
| 继续加定理 | 7883 条已足够 |
| 4 条欠账 | 性质已定 |

---

## 3. 验收基线

1. `lake build Lattice` 0 error
2. 门禁 I1–I8 全绿
3. **`check_repair_census.py` 与 `check_refutation_census.py` 注册进门禁且能失败**
4. `CONVENTIONS §6` 有完整的数字来源表
5. `audit_counts` 全匹配

---

## 附：本轮树的实际数字（供后续核对）

```
Core   16 files    62 theorems
Lift   35 files   225 theorems
Geo    65 files   358 theorems
Lib   588 files  7219 theorems
Audit   5 files    17 theorems
Usage   1 file      0 theorems
(root)  7 files     2 theorems
TOTAL 717 files  7883 theorems
```
