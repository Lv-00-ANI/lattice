# LATTICE 第六轮规划（ROADMAP-v8）

> 生成时点：2026-10-25，第 34 轮。
> 前置：`ROADMAP-v7` 全部完成。欠账 4 条（性质均已确定，无可做项）。

---

## 0. 本轮测量的核心事实：97 条否证

全库 **97 条否定命题**（`theorem` 级，结论形如 `¬…` 或 `→ False`）。
这是**唯一可以完整测量**的类别——不依赖关键词、不依赖抽样。

| 层 | 条数 |
|:--|--:|
| `Lib` | 90 |
| `Lift` | 4 |
| `Core` | 3 |
| `Geo` / `Audit` | 0（`Audit` 本轮新增 2 条） |

**链层原有的 7 条**：

| 定理 | 否证的是什么 |
|:--|:--|
| `Core/Net.relu_not_injective` | ReLU 单射 |
| `Core/Repair.down_no_progress` | 「absorbs + decreases 足以收敛」 |
| `Core/RepairMultistep.no_uniform_bound` | 统一步数界 |
| `Lift/PenaltyEmbedding.const_not_levelB` | 常数项属于某层 |
| `Lift/RealTokenization.tokenize_not_injective` | 分词单射 |
| `Lift/RoundingBackend.compileZ_not_injective` | 取整单射 |
| `Lift/SymbolToWeight.encode_necessary` | `encode` 可省略 |

---

## 1. 第一优先：补齐缺失的否证 —— `Repair.absorbs`

### 1.1 问题

`Repair` 三条义务中，**只有 `atomic` 被证明不可导出**（`down_no_progress`）。
`absorbs` 的可导出性**从未被问过**。

若它可导出，那个字段就是装饰；若不可，应当有反例。

### 1.2 结果（本轮已完成）

**不可导出**，反例是 `Audit.destructiveFix`：

```
Sat n := n = 0,  fix 0 = 5,  fix n = n - 1 (n > 0),  μ n := n
```

| 义务 | 成立？ |
|:--|:--|
| `decreases` | ✅ |
| `atomic` | ✅ |
| `absorbs` | ❌（`0` 满足却被改成 `5`） |

**意义**：没有 `absorbs`，一个满足收敛性保证的「修复」可以把**已通过的配置改坏**。
验证回路中这正是该字段要防的失败。

### 1.3 仍缺的一条

`decreases` 的不可导出性**尚未证明**。需要一个满足 `absorbs` + `atomic`
但 `decreases` 失败**且仍收敛**的算子。

**注意**：若算子仍收敛，`decreases` 显然不是收敛的必要条件——
但那正是要证的。这是一个**真实缺口**，登记为下一优先。

---

## 2. 第二优先：`decreases` 的独立性

### 2.1 要证什么

```
¬ (∀ Sat fix μ, absorbs … → atomic … → ∀ n, ¬ Sat n → μ (fix n) < μ n)
```

即：存在一个算子，保持满足、测度为零即满足，但在未满足点**测度不降**，却仍然收敛。

### 2.2 构造思路

取 `μ` 恒为 `1`（除目标外）：则 `decreases` 要求在 `0 < 1` 处下降，
但 `μ (fix n) = 1` 不 `< 1`，所以 `decreases` 失败；
而 `atomic` 要求 `μ n = 0 → Sat n`，`μ` 恒为 `1` 时它**空洞为真**；
`absorbs` 只要在满足点不动即可。

收敛性：`fix` 一步到目标，所以收敛。

### 2.3 为什么值得做

三条义务全部被证明独立 ⟹ `Repair` 的结构是**最小完备**的，
没有一条可删。这是对一个核心结构的完整刻画。

**规模**：S。

---

## 3. 第三优先：把「97 条否证」变成可核对的清册

**问题**：97 条否证是库中最强的证据，但**没有清单**。
一个读者无法知道「哪些不可能的结论已被证明」。

**做什么**：在 `Audit` 下建一份否证清册，按「否证的是什么」分类，
如同 `REPAIR-CENSUS` 对修复算子所做。

**规模**：S。

**价值**：这正是项目定位「通用基础设施」的证据面——一个基础设施的可信度，
很大程度上取决于它**明确知道什么做不到**。

---

## 4. 不做的

| 事项 | 理由 |
|:--|:--|
| 继续增加正向定理 | 数量已足够（~7,870）；否证与承重性更能说明强度 |
| 修 35 条 camelCase 定理 | 需逐条判断命名意图，P11 后续工作 |
| `external_bridge` 等 4 条欠账 | 性质已定：1 被否证 / 2 到成本下限 / 1 工具链 |

---

## 5. 验收基线

1. `lake build Lattice` 0 error
2. 门禁 I1–I8 全绿
3. **`decreases` 的独立性有结论**（能证则证，不能证则说明为何不能）
4. **否证清册产出**，97 条按类别归入
5. `audit_counts` 7 项全匹配

---

## 附：测量口径

- 否定命题：`theorem`/`lemma` 的结论形如 `¬…` 或 `→ False`，
  正则 `:\s*(?:¬|not )` 或 `-> False`。脚本 `agent-tmp/survey_negatives.py`。
- **这是唯一完整的测量**：它不依赖「主题词」，只依赖逻辑形式。
- 其余数字（文件数、定理数）按行首正则计，同样完整。
