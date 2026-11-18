# 修复算子清册（REPAIR-CENSUS）

> 目的：把「修正/修复」相关声明按**语义**分类，而不是按名字。
> 起因：`ROADMAP-v4 §0` 用关键词搜声明名统计出「修正 278 个」，
> 而 `fixed point`、`fixed mask`、`fixed-width` 这类字面命中占绝大多数。

---

## 1. 三类，按是否真的实现修复

| 类 | 判据 | 文件数 | fix 命名声明数（按文件计） |
|:--|:--|--:|--:|
| **A. 定义 `Repair` 实例** | 文件里有 `: Repair … where` | **8** | **20** |
| B. 使用 `Repair` 结构 | 出现 `Repair` 但无实例定义 | 17 | **45** |
| C. 字面命中 | 有 fix 命名声明，但文件里没有 `Repair` | 59 | **241** |

**口径说明**：上表按文件累加得 334，而 `ROADMAP-v4 §0` 的 278 是
**去重后的声明名数**（一次正则扫全库）。两者差 56，因为同一名字可能在
一个文件里定义、在另一个文件的签名里被 `DECL` 正则误配。
**衡量「有多少个声明」应取去重数 278**；衡量「多少个文件涉及」取 86。
`A` 类的 37 与 `C` 类的 238 都小于对应的去重总数，结论不受影响。

**⇒ 真正的修复算子只有 37 个声明，不是 278 个。** 相差七倍。

> **本轮（第 38 轮）复测的修正**：本清册初版记录 A 类为 6 个文件 / 27 个声明。
> 之后本会话新增了三个实现 `Repair` 的文件，清册**没有随之更新**：
>
> | 新增文件 | 定义 | 来源 |
> |:--|:--|:--|
> | `Core/RepairMultistep.lean` | `countdown`（无界测度的多步算子） | 第 22 轮 |
> | `Core/RepairAtomicity.lean` | `mkWithAtomic`（供给 `atomic` 的构造器） | 第 28 轮 |
> | `Usage/Examples.lean` | `natRepair`（使用说明的最小示例） | 第 36 轮 |
>
> 这与 `CONVENTIONS §7` 记录的漂移是**同一模式**：数字写下后无人复测。
>
> > **B 类也在本轮复测中更新**：从 12 文件 / 30 声明变为 **15 文件 / 37 声明**。
> 原因是本会话新增了 `Core/RepairConvergence`、`Geo/Reinjection`、`Geo/ReinjectionGeneral`
> 等引用 `Repair` 但不定义实例的文件。
>
> **B 类的判据此前是模糊的**（「出现 `Repair` 但无实例定义」）。现在由
> `gov/check_repair_census.py` 精确实现为：**提到 `Repair`、有 fix 命名声明、
> 但不匹配 A 类模式**。判据一旦精确定义，数字就可复现。

**一个必须说明的细节**：三个新文件各自定义了一个 `Repair` **实例**，但只有
> `natRepair` 的名字含 `fix`/`repair`；`countdown` 与 `mkWithAtomic` 不含。
> 所以**文件数 +3，声明数 +1**。这正是本文件 §4 警告的那件事——
> 名字过滤不等于测量。
> 本节的正确值现为 **11 个文件 / 37 个声明**，且由
> `gov/check_repair_census.py` 可重跑核对。
>
> > **本节此后不再手工记录数字**：`gov/check_repair_census.py` 直接解析上表并与树比对，
> > 数字一旦漂移，那个门禁就红。此前它带着自己的 `EXPECTED` 常量（11/37、18/47、57/238），
> > 而本文件写的是 9/28、22/56、54/239 —— **两者从未被比较过，门禁一直是绿的**。

---

## 2. A 类：真正实现了 `Repair` 的 9 个文件

| 文件 | fix 声明 | 它定义了什么 |
|:--|--:|:--|
| `Geo/Loop.lean` | 10 | `samePointRepair`：把一点复制到另一点的位置 |
| `Geo/LoopPerp.lean` | 4 | 垂直约束的修复回路 |
| `Geo/ConjRepair.lean` | 3 | 两个不同类约束的联合修复 |
| `Core/Repair.lean` | 3 | 框架本身 + `parity` 与 `down` 两个例子（含 `down_no_progress` 反例） |
| `Lib/Linear/Residual.lean` | 5 | **线性残差**的修复（文件头自称「the first real instance」） |
| `Lib/Linear/Multivar.lean` | 2 | 任意元数的修复回路 |
| `Core/RepairMultistep.lean` | 3 | `countdown`：测度无界的多步算子（第 22 轮） |
| `Core/RepairAtomicity.lean` | 5 | `mkWithAtomic`：由等价关系构造 `Repair`（第 28 轮） |
| `Usage/Examples.lean` | 2 | `natRepair`：使用说明的最小示例（第 36 轮） |

这 6 个是链路在「修正」这一步上的全部实质。

---

## 3. B 类：使用修复结构，但不定义算子

`RepairBridge`、`RepairPerp`、`Unified`、`RepairWF`、`ClosedLoop`、`IRRepair`、
`Repair`、`RepairQuality`、`QualityBridge`、`Extraction`、`Slots`、`Core/Invariant`。

这一类的价值在**性质**（保持、收敛、质量区分），不在**算子**。
把它们与 A 类混在一起数，会让人以为库里有十几个修复器。

---

## 4. C 类：为什么字面命中这么多

前三名足以说明问题：

| 文件 | fix 声明 | 实际内容 |
|:--|--:|:--|
| `Lib/Lift/RealNonlinearFidelity.lean` | 50 | 非线性保真度的可判定判据 |
| `Lib/Architectures/RealLoopFixedPointExistence.lean` | 18 | 收缩映射的**不动点存在性** |
| `Lib/FCA/RealFCATokenization.lean` | 17 | FCA 的 `intent` 作为分词选择集 |

`Fidelity` 里的 `fix` 是 `fixed`（固定），`FixedPoint` 是数学不动点，
`KVCache` 的 `fix` 是「修复推理等价性」——**没有一个是修复算子**。

---

## 5. 结论与后续

- **不要再用「修正相关声明数」衡量这一步的覆盖度**：97% 是字面命中。
- 真正该看的是 **A 类的 9 个文件**，以及它们各自处理哪类约束。
- **已知缺口**：A 类覆盖 `samePoint`、`perpendicular`、线性残差；
  `distEq`、`collinear`、`parallel`、`ratioDivision` 等**没有修复算子**。
  这与 `Geo/Reinjection.lean` 文件头记的边界一致（再注入对一般 `EqConstraint`
  需要对应的修复算子，而目前不是每个都有）。

---

## 附：测量口径

脚本 `agent-tmp/classify_repair.py`。判据：

- A 类：正则 `:\s*(?:Lattice\.Core\.)?Repair\b[^\n]*\bwhere\b` 命中；
- B 类：出现 `Repair` 且有 fix 命名声明，但无 A 类模式；
- C 类：有 fix 命名声明，全文无 `Repair`。

排除 `Lattice/Reference/`。
