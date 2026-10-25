# LATTICE 第二轮规划（ROADMAP-v4）

> 生成时点：2026-10-25，第 19 轮。前置：`STATE-2026-10.md`（五个优先级已完成）。
>
> **本文件不是在旧规划上加项，而是按目标的五个分句重新测量后的新一期。**
> 每条都附实测，不附印象。

---

## 0. 测量结果：目标五句 vs 实际覆盖

| 目标分句 | 相关声明数 | 判定 |
|:--|--:|:--|
| 正向：**约束损失** | 153 | ✅ 充足 |
| 正向：**数据合成** | **6** | ❌ **几乎为零** |
| 正向：**结构化初始化** | 67 | ⚠️ 多为「初始化」字面命中，需逐个核 |
| 逆向：**提取** | 106 | ✅ 充足 |
| 逆向：**验证** | 41 | ✅ 够用（`SampledVerified` + 采样界已打通） |
| 逆向：**修正** | 278 | ✅ 充足（但多为「fixed point」字面命中） |
| 逆向：**再注入** | **2** | ❌ **只有 2 条，且其中一条是同义重复** |
| 闭环：回路 / 收敛 | 44 / 49 | ✅ 收敛率已证（第 17 轮） |
| 符号引擎：`GeoExpr`/`GeoConstraint`/`poly` | 全部存在 | ✅ 无中间层 |
| 边界：不实现引擎 | torch 0、GPU 0、tensor 12（抽象） | ✅ 未越界 |

**结论**：链路的**中间环节很实**（损失、提取、修正、收敛），**两端很虚**：
「数据合成」（6）与「再注入」（2）。

---

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

## 2. 第二优先：数据合成（当前 6 个声明）

### 2.1 问题

目标的「正向」第二件事是**数据合成**（从符号约束生成训练数据）。
库中相关声明只有 6 个，且多是 `augmentedLagrangian`（增广拉格朗日，与数据合成无关）。

### 2.2 要做成什么

最小有意义的形式：**从一个约束 `c` 生成一组满足/违反它的样例点**，
并证明生成器的正确性：

```
(symbolicToData c : List (ℕ → Pt n))
theorem symbolicToData_sound : ∀ pts ∈ symbolicToData c, Holds c pts
```

（或生成「违反」的样例，用于负样本。）

### 2.3 为什么可做

`Geo/Expr.evalPts` 是可计算的（`GeoExpr` 是显式归纳类型），
所以「解出满足 `poly = 0` 的点」对**线性**约束是初等代数。
对一般约束需要求解器，超出「不实现引擎」的边界，应登记为边界。

**规模**：M。

---

## 3. 第三优先：`Lib` 中「修正」的语义澄清

### 3.1 问题

`修正` 相关声明有 **278** 个，但大量是 `fixed`（不动点）的字面命中，
与「修正」这个动作无关。首次统计被字面匹配误导过一次（第 19 轮）。

### 3.2 要做成什么

不新增证明，而是**区分**：

- 真正的修复算子（`Core.Repair` 的实例，逐个列出）；
- 「fixed point」性质的定理（与修复无关）。

产出一份清单，避免下轮再次被字面命中误导。

**规模**：S（纯审计）。

---

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
