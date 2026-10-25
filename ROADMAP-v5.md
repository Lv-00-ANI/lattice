# LATTICE 第三轮规划（ROADMAP-v5）

> 生成时点：2026-10-25，第 22 轮。
> 前置：`STATE-2026-10.md`（5 项完成）、`ROADMAP-v4.md`（4 项完成，1 项被阻塞）、
> `REPAIR-CENSUS.md`。
>
> **本轮换了测量对象**：不再数「某类声明有多少个」，而是读 **`Lattice.Slots`——
> 项目自己的欠账登记表**。它由门禁 I6 校验，所以它就是权威的待办清单。

---

## 0. 权威事实：6 条欠账（可判定，已用 `#eval` 核实）

`Lattice.Slots.fullRegistry` 有 8 个 slot，其中 6 个未清：

```
#eval Slot.owedCount fullRegistry
6
#eval (Slot.owed fullRegistry).map (fun s => s.name)
["lift.compile.single_item_sound", "lift.embed.local_minimiser_exact",
 "lift.extract.roundtrip", "core.repair.atomic",
 "core.semantics.external_bridge", "geo.loop.convergence_is_single_step"]
```

这个数字由 `example : Slot.owedCount fullRegistry = 6 := by decide` 钉住，
**不是散文里的自述**。

### 0.1 按可做性分类（本轮实测）

| # | 欠账 | 性质 | 能否现在推进 |
|--:|:--|:--|:--|
| 1 | `lift.compile.single_item_sound` | 逐编译器的义务 | ✅ **可做** |
| 2 | `lift.embed.local_minimiser_exact` | 一般命题**已被否证**（`sound_not_exact`） | ❌ 已在最弱意义上关闭 |
| 3 | `lift.extract.roundtrip` | 逐表示的义务 | ✅ **可做** |
| 4 | `core.repair.atomic` | 逐算子的义务 | ✅ **可做** |
| 5 | `core.semantics.external_bridge` | **工具链**（需 Lean ≥ 4.26） | ❌ **外部阻塞** |
| 6 | `geo.loop.convergence_is_single_step` | 需「一步不解决问题」的算子 | ✅ **可做** |

**3 条可做、1 条结构上关闭、1 条外部阻塞、1 条与另一条同源。**

---

## 1. 第一优先：多步修复算子（同时化解第 4、6 条）

### 1.1 问题

`geo.loop.convergence_is_single_step` 的 note 原文：

> "Iterated convergence needs an operator whose step does not settle the predicate."

而 `core.repair.atomic` 的 note 说它「per operator 关闭，办法是选一个在目标上为零的测度」。

**这两条是同一件事的两面**：库中现有全部修复算子的测度值域是 `{0,1}`，
所以它们一步到站，既不能展示多步收敛，也不能展示 `atomic` 的必要性。

### 1.2 要做成什么

构造一个 `Repair` 实例，其测度**值域无界**，并且**每一步只降 1**：

```
stepsToZero n : Nat          -- 一个需要 n 步的算子
μ x = x                       -- 测度就是距离目标的距离
decreases: x ≠ 0 → μ (fix x) = μ x - 1
```

于是：
- `Repair.progress` 对它给出 `∃ k, Sat`（存在性）；
- **第 17 轮的 `converges_within` 给出「恰好 `μ x` 步」**——这是新的定量内容；
- `loop_converges_in_one` 的**反面**：这个算子**不存在**一步界（用 `μ` 无界证明）。

### 1.3 为什么可做

- `Repair` 已在 `Nat` 上陈述测度，结构无需改动；
- 第 17 轮已证 `converges_within`（对任意 `Repair`），本项是给它一个**非平凡的实例**；
- 不需要新理论，只需要构造与验证。

**规模**：S–M。

---

## 2. 第二优先：`encode ≠ id` 的编译器实例（第 1 条）

### 2.1 问题

`lift.compile.single_item_sound` 的 note：

> "Open as a *scheme* because no single instance covers every backend."

但更强的说法是：**库中唯一的 `Compiler` 实例 `geoCompiler` 的 `encode := id`**，
所以「编译」这一步在实例上其实是恒等，`sound` 因此近乎自动。

### 2.2 要做成什么

一个 `encode` **不是**恒等的 `Compiler` 实例，且 `sound` 需要**真证明**。

最直接：设符号侧输入是 `LinearForm R n`，权重侧输入是它的**扁平向量**
（`flatten` 去掉一个维度或重排坐标），`encode` 做这个变换，
`sound` 需要证明「变换后的点仍满足原约束」。

### 2.3 为什么可做

`Flatten`/`FlattenAgreement` 已给出扁平化的一致性质（第 22 轮调查所见），
所以 `encode` 的非恒等变换已有载体。**不需要 TorchLean。**

**规模**：M。

---

## 3. 第三优先：非双射编码的提取往返（第 3 条）

`lift.extract.roundtrip` 的 note：

> "Degenerate for field renaming; substantive for any backend whose encoding is not the identity."

所以它与第 2 条**同源**：一旦有了 `encode ≠ id` 的编译器，
它的 `Representation` 侧往返就是这条欠账的实质内容。

⇒ **合并到第 2 条执行**，不单独立项。

---

## 4. 不做的（及理由）

| 事项 | 理由 |
|:--|:--|
| `core.semantics.external_bridge` | 工具链：TorchLean 需 Lean ≥ 4.26，本项目钉 4.14 |
| `lift.embed.local_minimiser_exact` | 一般命题**已被 `sound_not_exact` 否证**；已在最弱意义上关闭，再推进就是试图证伪命题 |
| `Lib` 内部层序（选项 b/c） | 需先测 588 文件依赖图；`CONVENTIONS §2b` 已登记 |
| `δ` 收敛率 | 数值分析，与已完成的多步收敛率是两件事 |

---

## 5. 关于「288 个文件自述有未做项」

本轮调查发现 288 个文件正文提到 owed / 未做 / 超出范围之类的措辞。
**这个数字不能当作待办清单**：其中大量是「本文件不处理 X（属 Y 的职责）」
这类**范围声明**，不是欠账。真正的欠账清单是 `Slots` 的 6 条。
这个区分本身值得记录，否则下轮会再次被大字吓到。

---

## 6. 验收基线

1. `lake build Lattice` 0 error
2. 门禁 I1–I8 全绿
3. **`Slot.owedCount` 从 6 降到 4**（多步算子 + 非恒等编译器各清一条），
   且 `Slots.lean` 的 `example` 随之更新——**这个数字是可判定的，改不了假**
4. 新算子**不存在**一步界（这是与现有算子的实质区别，需显式陈述）
5. `audit_counts` 7 项全匹配

---

## 附：测量口径

- 欠账清单：`Lattice.Slots.fullRegistry`，用 `#eval Slot.owedCount` 读取（实质检查，非散文）。
- 可做性分类：读每个 slot 的 `note` 字段原文，判断阻塞是内部的（缺证明）还是外部的（缺工具链）。
- 「288 个文件」：正则扫正文，**仅作参考**，见 §5 的警告。
