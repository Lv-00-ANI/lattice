# `Primitives` 的 rank 冲突：测量、结论、三条路线

> **状态**：分析，不是执行。**本轮没有搬任何文件。**
> **背景**：`DIRECTORY-DESIGN.md` §9 的链路是 `lib 0 < kernel 1 < runtime 2 < domains 3 < primitives 4`，
> §10 把 `NetLoss`/`ConstraintDescent`/`WeightDescent` 划给 `Primitives/Train`，
> 把 `Repair*`/`Loop*`/`Reinjection*` 划给 `Primitives/Repair`。

---

## 0. 一句话结论

**§9 把「被调用的基础调用」放在了「调用它们的领域实例」之上，而依赖图的方向正好相反。**
所以 `Primitives` **不能**在 rank 4。这不是偏好问题，是四组测量。

---

## 1. 测量：§10 想放进 `Primitives` 的模块，全部被留在 `Domains` 的模块依赖

`Domains/` 被子划分成 `Constraints`（28）与 `Geometry`（71），下表的 in-degree 是**在 `Domains` 内部**的。

### `Primitives/Train`（§10 的 4 个）

| 模块 | in-degree | 依赖它的模块 |
|:--|--:|:--|
| `PenaltyLoss` | **2** | `ConstraintDescent`, `NetLoss` |
| `NetLoss` | **1** | `ConstraintDescent` |
| `ConstraintDescent` | 0 | — |
| `WeightDescent` | 0 | — |

### `Primitives/Repair`（§10 的 16 个）

| 模块 | in-degree | 依赖它的模块（部分） |
|:--|--:|:--|
| **`Loop`** | **8** | `ClosedLoop`, `ConjRepair`, `LoopRate`, `Reinjection`, `RepairBridge`, `RepairPenalty` … |
| `LoopPerp` | 6 | `ConjRepair`, `IRRepair`, `ReinjectionGeneral`, `RepairCoverage`, `RepairQuality`, `Unified` |
| `RepairPerp` | 4 | `ConjRepair`, `LoopPerp`, `MissingRepairs`, `RepairCoverage` |
| `Reinjection` | 3 | `ClauseComposition`, `PartialReinjection`, `ReinjectionGeneral` |
| `RepairCoverage` | 3 | `EqualLengthRepair`, `ParallelRepair`, `PolyRepair` |
| `ConjRepair` | 2 | `ClosedLoop`, `IRRepair` |
| 其余 10 个 | 0–1 | — |

### `Primitives/Verify`（3 个）与 `Primitives/Model`（3 个）

`ExecutableCheck` 1（`ExecutableGeoCheck`）、`GeoSampledBound` 1（`ClauseComposition`）、
`GeoLadder` 1（`WeightSideLadder`）；其余 0。

**四行里没有一行是全 0。** 把任何一行移到 rank 4，那 1–8 条「来自 rank 3 的 import」就变成向上依赖，
**I4 会直接报错**。

---

## 2. 更根本的测量：只有 4 个模块**可能**是一个更低的层

一个模块要当「被领域实例调用的基础调用」，它自己就**不能**依赖那些实例。
所以判据是：**在 `Domains` 内部 in-degree = 0 且不 import 任何 `Domains` 模块**。

| 模块 | 它 import 的层 | 需要的 rank |
|:--|:--|--:|
| `MultistepLoop` | `Core` | 0 |
| `TokenizeStrategy` | 只有 Mathlib | 0 |
| `TokenizerPattern` | 只有 Mathlib | 0 |
| `WeightDescent` | `Core` | 0 |

**99 个里只有这 4 个。其余 95 个都是消费者**——`Constraint` in-degree 25、`Loss` 20、`Expr` 12、
`Dist` 8、`Loop` 8。**它们不再是「primitive」，它们是「被别的模块用的模块」。**

**这就是关键**：§10 的分组依据是**用途的想象**（「训练」「修复」「验证」），
而 rank 的依据是**依赖方向**。**两者在 `Geo` 这一层上不一致。**

---

## 3. 三条路线

### 路线 A：`Primitives` 放在 **rank 2**，只装那 4 个

- **做什么**：建 `Lattice/Primitives`（rank 2），把 `MultistepLoop`、`TokenizeStrategy`、
  `TokenizerPattern`、`WeightDescent` 搬进去。
- **合法**：四个都需要 rank 0，而 `Domains`(3) import `Primitives`(2) 是向下的。
- **代价**：1 个批次、4 个文件；`PATH_MAP` 4 条；**全量验证一遍**。
- **收益**：一个**真正的**底层，而不是名义上的。
- **不满足**：§10 的分组（`Train`/`Repair`/`Verify`/`Model` 都装不进去）。

### 路线 B：`Primitives` 放在 **rank 3**，与 `Domains` 同级，装 §10 的全部

- **做什么**：99 个路径搬迁（`Domains/Constraints/X` → `Primitives/Constraints/X` 之类）。
- **合法**：同级之间互相 import 都合法，所以 **I4 不再提供任何保证**。
- **代价**：99 个文件、约 183 条边；`PATH_MAP` 99 条；一次全量重建。
- **收益**：目录名与 §10 一致。
- **代价的另一半**：**分层保证消失**。`Domains → Primitives` 与 `Primitives → Domains` 同时合法，
  于是「primitives 在下」这句话**没有任何检查在支撑**——而本项目刚刚才把「不能失败的门禁不是门禁」
  当成原则。

### 路线 C：把 §10 的 `Primitives` 分组理解为**`Domains` 的子划分**（**现状**）

- **做什么**：什么都不做。`Domains/Constraints`（28，对 `Geometry` **零反向边**）已经是
  「底半」；`Domains/Geometry`（71）已经是「上层」。
- **代价**：0。
- **收益**：分层保证是**测量出来的**（0 条反向边），不是声明的。
- **不满足**：目录**名字**不叫 `Primitives/Train`。

---

## 4. 建议

**A + C 组合**：

1. **做路线 A**：把 4 个真正自由的模块搬到 rank-2 的 `Primitives/`。
   这让「基础调用」这个名字第一次有依赖方向的支撑。
2. **把路线 C 写进 §10**：`NetLoss`/`PenaltyLoss`/`ConstraintDescent`/`Repair*`/`Loop*` **留在
   `Domains/Geometry`**，并说明理由（它们是消费者，不是基础调用）。
3. **改 §9 的链路**：`primitive` 应在 `domains` **之下**，而不是之上。

**不建议路线 B**：它花 99 次搬迁换来一个**会拆掉分层保证**的目录名。
本项目已经因为「静默的空洞」栽过四次（`zero.Geo`、`Lift` 空目录、`Domains` 非递归、`mod_of` 的基名），
**不该再主动制造一个「合法但无保证」的层级**。

---

## 5. 这条分析没有做的事

- **没有搬任何文件。**
- **没有改 §9 或 §10**——两处都是设计决策，本节给测量与三条路线。
- **没有量「路线 A 之后 rank 需求是否变化」**：搬 4 个模块会改变图，**每批之后要重算**。
- **没有检查 §2.6**（「primitives 之间零 import」）：`Domains/Constraints` 内部有 28 个模块、
  边不为零（`Constraint → Dist → Expr`），**所以 §2.6 在这个粒度上也不成立**，
  但它属于另一份分析。
