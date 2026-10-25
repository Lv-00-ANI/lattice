# LATTICE 第二轮规划（ROADMAP-v4）

> 生成时点：2026-10-25，第 19 轮。前置：`STATE-2026-10.md`（五个优先级已完成）。
>
> **本文件不是在旧规划上加项，而是按目标的五个分句重新测量后的新一期。**
> 每条都附实测，不附印象。

---

## 0. 测量结果（**初版方法有误，此处为更正后的版本**）

### 0.1 初版错在哪

初版按**声明名**搜索关键词（`synth`、`augment` 等）统计。这个方法有根本缺陷：

> 主题写在**文件名**里，而定理名用的是另一套词汇。

具体例子：`Geo/Synthesis.lean` 是数据合成的实现，但它的核心定理叫
`samples_sound`、`synthesize_perpendicular_samples`——按 `synth` 搜**搜不到**。
于是初版报告「数据合成 6 个声明」，而实际是一个 **11 个声明的模块，
带端到端认证生成器**。

### 0.2 更正后的方法

按**文件**测量：读每个 `Geo` 文件的模块标题（`# \`Lattice.Geo.X\` -- ...`），
标题陈述的就是该文件要做什么。脚本 `agent-tmp/measure_geo_by_file.py`。

### 0.3 更正后的结论

`Geo` 层共 **64 个文件**，覆盖的比初版描述的完整得多：

| 目标分句 | 实际载体（实测） |
|:--|:--|
| 符号引擎（不设中间层） | `Expr`、`Constraint`、`Engine`、`Exec`、`Rules`、`Derive`、`Eval` |
| 约束损失 | `Loss`、`Square`、`Exterior`、`LayerExact`、`PenaltySmooth` |
| **数据合成** | **`Synthesis`（6 定理 / 5 定义）、`Invariant`（12/2）、`Initialise`（9/1）** |
| 提取 | `Extract`、`Semantic`、`Flatten`、`FlattenAgreement`、`SeqRepresentation` |
| 验证 | `GeoSampledBound`、`DistLipschitz`、`Lipschitz`、`PolyAssemble`、`PolyConstants` |
| 修正 | `Repair`、`RepairBridge`、`RepairPerp`、`RepairQuality`、`RepairPenalty`、`LoopPerp` |
| 再注入 | `Reinjection`（第 19 轮新增） |
| 闭环 | `Loop`、`LoopRate`、`ClosedLoop`、`ConjRepair`、`Unified` |
| 端到端 | `Pipeline`、`Compile`、`IRBridge`、`LadderInstance`、`ApproxEmbedding` |

**所以「数据合成」不是空白**：`Synthesis` 已经实现了「种子 + 变换族 → 认证样本列表」，
并给出 `samples_sound`（每条样本都满足约束）与 `synthesize_from_initialisation`
（接上初始化）。初版把它列为「第二优先：要做」是错的。

**这次错误的价值**：它说明**按名字搜索不能当作覆盖度测量**。本仓此前记录过
「不剥注释会误报」，这次是同一类错误的另一种形态。

## 1. 第一优先：把「再注入」做成真命题

### 1.1 问题（实测）

`Geo/Loop.lean` 的两条再注入定理：

```lean
theorem reinject_sound (a b : ℕ) (pts : ℕ → Pt n) :
    GeoConstraint.Holds (.samePoint a b) ((samePointRepair a b).iterate 1 pts) :=
  loop_converges_in_one a b pts          -- 证明体就是上一条定理

theorem reinject_entails (a b : ℕ) :
    EntailsGeo [GeoConstraint.samePoint a b] (GeoConstraint.samePoint a b) :=
  entailsGeo_refl _                      -- 自反性
```

**两条都不是再注入**（以下经实测，脚本 `agent-tmp/chk_reinject.lean`）：

```lean
-- 两个陈述：
--   loop_converges_in_one : (samePointRepair a b).Sat        (iterate 1 pts)
--   reinject_sound        : (GeoConstraint.samePoint a b).Holds (iterate 1 pts)
--
-- 它们【定义相等】：
example : (samePointRepair a b).Sat pts = GeoConstraint.Holds (.samePoint a b) pts := rfl
```

所以 `reinject_sound` 是 `loop_converges_in_one` 的**同一命题换了一种写法**
（`Sat` 与 `Holds` 展开后相同），证明体就是直接引用上一条定理。
**不是「逐字相同」，而是「定义相等」**——这个区别重要，因为它意味着
第一条再注入定理没有增加任何信息。

`reinject_entails` 陈述的是「一个约束蕴含它自己」（`entailsGeo_refl`），与修正无关。

而目标的原文是「**修正、再注入**」：修正之后要把结果**写回符号模型**，
再走一遍编译。这一步在库中不存在。

### 1.2 要做成什么

一条真正的再注入定理，其形状应当是：

```
repair 之后  ⟹  compile 之后的损失在修正点为零
```

即把 `Repair` 的 `Sat`、`Compiler` 的 `sound`、`EqConstraint.loss` 三者串起来：

```lean
theorem reinject_compiles_to_zero
    (c : EqConstraint n) (pts' : ℕ → Pt n)
    (h : GeoConstraint.Holds (.eqZero ...) pts') :
    EqConstraint.loss c pts' = 0
```

其中 `h` 由 `reinject`（修正后满足）供给，结论是「再编译得到的惩罚在修正点确实为零」。
这才是闭环：**验证 → 修正 → 写回 → 再编译 → 新惩罚在修正点为零**。

### 1.3 为什么可做

三块料都已存在：

| 料 | 位置 |
|:--|:--|
| 修正后满足（`loop_converges_in_one`） | `Geo/Loop.lean` |
| 损失定义 `loss = poly²` | `Geo/Loss.lean` |
| `poly = 0 ⟹ loss = 0` | `Geo/Loss.loss_eq_zero_*` 系列 |

所以这是**组合**，规模 S–M，不是新理论。

**规模**：S。

---

## 2. ~~第二优先：数据合成~~ —— **撤回（已存在）**

**撤回理由**：§0.1 记录了初版测量的错误。`Geo/Synthesis.lean` 已实现该路径：
`samples`（生成器）、`samples_sound`（每条样本认证）、
`synthesize_perpendicular_samples`（5 条端到端样本）、
`synthesize_from_initialisation`（接上初始化）。

**它真正的缺口**（读代码得出，不是测名字）：

1. `samples` 只沿**一条轨道**生成（平移/缩放同一个种子），
   文件头自己写明「Genuine diversity needs *several seeds*」；
2. 只对 `perpendicular` 与 `samePoint` 给了端到端的合成定理；
   `distEq`、`collinear`、`parallel` 等未接。

⇒ 若要继续这条路，正确的下一步是**多种子**与**逐约束补全**，
而不是「实现数据合成」。规模 M。

## 3. 第三优先：`Lib` 中「修正」的语义澄清 —— ✅ **已完成（第 21 轮）**

**原计划**：把 278 个「修正」相关声明分类。**测量方法同样需要更正**：
278 是按名字搜出来的，实际只有 **27 个**是修复算子。

**结果**（`REPAIR-CENSUS.md`）：

| 类 | 判据 | 文件 | 声明 |
|:--|:--|--:|--:|
| A. 定义 `Repair` 实例 | `: Repair … where` | 6 | **27** |
| B. 使用结构 | 提到 `Repair` | 12 | 30 |
| C. 字面命中 | 无 `Repair` | 48 | **237** |

**A 类的 6 个文件**：`Geo/Loop`、`Geo/LoopPerp`、`Geo/ConjRepair`、
`Core/Repair`、`Lib/Linear/Residual`、`Lib/Linear/Multivar`。

**已知缺口**：`distEq`、`collinear`、`parallel` 等约束**没有修复算子**，
所以 `Geo/Reinjection` 的再注入定理目前只覆盖 `samePoint`。这与该文件头记的边界一致。

## 4. 第四优先：`PROOF-CHAIN-RUNG.md` 的 ⚠️ 条目

### 4.1 现状

四跳的状态表中仍有若干 ⚠️（条件成立但实例弱）。逐条核：

| 跳 | 当前 ⚠️ 的理由 | 能否升级 |
|:--|:--|:--|
| L2→L3 | `Compiler` 唯一实例 `geoCompiler` 的 `encode := id` | 需要 encode ≠ id 的实例 |
| L3→L2 | `Representation` 的一个实例由双射构造 | 需要非可逆编码的实例 |
| 端到端 | `linearLadder` 的 `W := ℝ` 是损失值 | 需要 `W` 是真权重的实例 |

三者都需要**真权重类型**，而那与 `Slots.lean` 的 `core.semantics.weight_exists`
（工具箱债：TorchLean 需 Lean ≥ 4.26）相连。

**规模**：L，且**被外部工具链阻塞**。登记为边界，不排期。

---

## 5. 不做的（及理由）

| 事项 | 理由 |
|:--|:--|
| `δ` 收敛率（采样密度趋零的速度） | 数值分析，与已完成的**多步收敛率**是两件事；无外部需求 |
| `Lib` 内部层序（选项 b/c） | 需要先测 588 文件的依赖图；`CONVENTIONS §2b` 已登记 |
| 修 `RepairWF` 的步数界 | **原理上不可能**：良基序可有无穷长下降链 |
| 真权重类型的实例 | 被 TorchLean 工具链（Lean ≥ 4.26）阻塞 |

---

## 6. 验收基线（本轮完成时须同时满足）

1. `lake build Lattice` 0 error
2. 门禁 I1–I8 全绿，且每条不变量的反应性测试存在
3. **再注入是真命题**：`reinject_*` 的陈述不与 `loop_converges_in_one` 重复
4. **数据合成有生成器 + 正确性定理**
5. 修正清单产出，278 个声明分类完毕
6. `audit_counts` 的 7 项计数全匹配

---

## 附：本文件的测量口径

- 声明计数：剥注释后按行首匹配 `theorem|lemma|def|structure|abbrev|inductive`。
  脚本 `agent-tmp/round19_survey.py`。
- **关键词匹配是初筛，不是结论**：`修正` 的 278 中有大量 `fixed` 字面命中；
  `数据合成` 的 6 个里有 4 个是 `augmentedLagrangian`（与数据合成无关）。
  本文件据此把「逐项核实」列为第三优先。
