# 评估核对备忘（第 25 轮）：哪些数字要更新、哪些路径已失效、哪些项已关闭

> **目的**：上一份正式评估以 `acbdf6b`（344 提交）为基线。本备忘把它与
> **`8d5f8ed`（348 提交）** 对齐，并列出**已失效的路径**——因为三次搬迁
> （`Lift`→`Runtime`、`Geo`→`Domains`、`Audit`→`Evidence`）之后，评估里带 `Geo/`、`Lift/` 的引用
> **在树里已经不存在**。

---

## 1. 数字：三项要更新

| 指标 | 相对评估的增量 | 说明 |
|:--|--:|:--|
| 提交 | **+4** | 评估的基线之后合并了 L0-1/L0-2 与备忘录 |
| 定理 / 引理 | **+8** | 评估把 L0-1/L0-2 列为未做，它们现在已证 |
| 检查器 | **+7** | 新增均为门禁 + 自检配对 |
| 模块 | 0 | 与评估一致 |
| 欠账 / 永久边界 | 0 / 0 | 与评估一致（0 / 4） |
| 证明债判定 | 0 | `delete` 44、`strengthen` 24、`downgrade` 0、`register` 95，**全部一致** |
| 承重覆盖 | 0 | 682/872 = 78.2%，一致 |
| 零入度覆盖 | 0 | 383/7,537 = 5.1%，一致 |

**当前绝对值以 `README.md` 的计数行为准**（`audit_counts.py` 核对它）；
本表只记**相对评估基线的增量**，避免与主文档的实测值构成「两处不一致」。

---

## 2. ⭐ 已关闭：评估把 P0 的头两项列为未做，而它们现在**已证**

| ID | 评估写的状态 | **现在** |
|:--|:--|:--|
| **L0-1** `layerWords` 单射性 | 「工作树只差一个 `omega`」 | ✅ **`layerWords_injective` 已证**（`8d5f8ed`） |
| **L0-2** 解码器 + 往返 | 「无 decoder」 | ✅ **`wordsLayer_layerWords` 已证**（`8d5f8ed`） |

**所以「C 核心规格 70–75%」这条要重算**：评估的 P0 是 7 项，其中 **L0-1、L0-2 已完成**，
剩下 **L0-3（字节模型）、L0-4（布局/所有权，被测量挡住）、L0-5（向量充分性）、
L0-6（`Float`/`ℝ` 一致）、L0-7（类型级组合）**。

**关键**：**L0-1 与 L0-2 合起来**使词级格式成为**完整、无损、可解码**的规格——
「单射性差一个 `omega`」那句话已经过期。

---

## 3. 失效路径：评估里带 `Geo/`、`Lift/` 的引用要改

三次搬迁之后，下列引用**在树里不存在**（括号内是现在的路径）：

| 评估里的引用 | 现在的路径 |
|:--|:--|
| `Lattice/Geo/ConstraintDescent.lean` | `Lattice/Domains/Geometry/ConstraintDescent.lean` |
| `Lattice/Geo/NetLoss.lean` | `Lattice/Domains/Constraints/NetLoss.lean` |
| `Lattice/Geo/PenaltyLoss.lean` | `Lattice/Domains/Constraints/PenaltyLoss.lean` |
| `Lattice/Geo/GeoLadder.lean` | `Lattice/Domains/Geometry/GeoLadder.lean` |
| `Lattice/Lift/ProgramAST.lean` | `Lattice/Runtime/ProgramAST.lean` |
| `Lattice/Audit/*` | `Lattice/Evidence/*`（12 个模块） |
| `Lattice/Geo/*`（其余） | `Lattice/Domains/{Constraints,Geometry}/*` |

⚠ **namespace 未改**（§2.8 的零轮规则），所以**定理名一律不变**——
只有**模块路径**搬了。所以「`Geo/ConstraintDescent` 的 `9d1291e`」这条**内容仍然成立**，
只是路径要按上表替换。

**建议**：评估文档里凡引用 `Lattice/Geo/` 或 `Lattice/Lift/` 的地方，**用 `PATH_MAP`
（`gov/_debt_path_map.py`）机械替换**，不要手改——那是本会话十次路径事故的教训。

---

## 4. 与评估一致、无需改动的判断

以下是评估里**已经准确**的部分，本备忘不重复论证，只确认：

- **S9 只 2/12 构造子**（`samePoint`/`midpoint`），其余 10 个已分类为不可仿射；
- **S10 只在解处**成立（`Semantics/PostTrain.lean`）；
- **S20 阻塞**：`MergeSound` 不含词表类型；
- **训练数学缺 AD / data / SFT / DPO / RLHF**；
- **零入度 7,537 条只审了 5.1%**——这是**已登记的边界**，不是「会全审」；
- **I5 按名字只覆盖 0.4%**，而 `check_endtoend_content` 的内容普查覆盖 **1,763 条跨 ≥2 层**；
  **两者是不同的仪器**，评估把前者的 0.4% 当作 I5 的全部覆盖是**偏保守的读法**。

---

## 5. 本备忘**没有**做的事

- **没有重算百分比**。评估给的 70–75% / 50–55% / 30–35% 是**人工估计**，
  而本项目的判据一直是「能给数字就给数字」。**L0-1/L0-2 关闭后 P0 完成 2/7**，
  这个比例是**可数的**；而「C 核心规格到闭环的百分比」**没有定义**，所以本文不改它。
- **没有改评估文档本身**（它不在树里，是外部输入）。
- **没有开始 L0-3 至 L0-7**：L0-4 被测量挡住（三个类型不存在），L0-3 需要 IEEE-754 舍入模型。
