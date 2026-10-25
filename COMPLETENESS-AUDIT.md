# 完整性终审（COMPLETENESS-AUDIT）

> 第 43 轮。**逐条对照目标原文**，确认每一条都有对应物，或已有明确的「不做」理由。
> 方法：把目标拆成可检验条款，每条给出**声明名**或**文档名**或**理由**。
> 脚本 `agent-tmp/completeness_audit.py`。

---

## 0. 结论

**目标原文的 16 条可检验条款，全部有对应物。零缺失。**

| 类别 | 条款数 | 状态 |
|:--|--:|:--|
| 链路与三个正向环节 | 4 | ✅ |
| 逆向三个环节 + 再注入 | 4 | ✅ |
| 闭环、符号引擎 | 2 | ✅ |
| 定位边界（不实现引擎/模型/框架、不绑定厂商） | 2 | ✅ |
| 形式化保证、证明链、语言、分文件命名 | 4 | ✅ |

---

## 1. 逐条对照

### 1.1 链路与正向

| 条款 | 载体（实测声明） |
|:--|:--|
| **数据 ⇄ token ⇄ 符号 ⇄ 权重** | `encodeForm`、`decodePayload`、`decodePayload_encodeForm`、`ladder_forward`、**`weightLadder`** |
| 正向：约束损失 | `EqConstraint`、`loss`（= `poly²`）、`poly` |
| 正向：数据合成 | `samples`、`samples_sound`、`samplesOf_sound`（多种子） |
| 正向：结构化初始化 | **`compileToLayer`**、`compileToLayer_sound`、`allSame` |

`compileToLayer` 是第 42 轮新增的：把符号的系数/常数直接写成权重矩阵/偏置，**不经训练**。

### 1.2 逆向

| 条款 | 载体 |
|:--|:--|
| 提取 | `Representation`、`extract_compile`、**`roundingLossy`**（非可逆编码） |
| 验证 | `geo_sampled_bound`、`residual_le_of_zero_on_dense(_of_d)` |
| 修正 | `Repair`、`samePointRepair`、`perpRepair`、`countdown` |
| **再注入** | `reinject_loss_eq_zero`、`reinject_generic`、`reinject_of_hold` |

### 1.3 闭环与符号引擎

| 条款 | 载体 |
|:--|:--|
| 验证回路 | `loop_converges`、`converges_within`（**精确界**）、`progress` |
| **符号模型直接跑在符号引擎上，不另设中间层** | `GeoExpr`、`GeoConstraint`、`Holds`、`evalPts`，以及 `Geo/Engine.lean` 的 `Rule`、`EntailsGeo`、`Closed`、`step_sound`、`derivation_sound` |

**「不另设中间层」这一条**：`GeoExpr` 是**可直接求值**的归纳类型（`evalPts`），
约束的满足关系 `Holds` 直接定义在它上面，推理规则 `Rule` 也直接作用于它。
中间没有「先编译成另一种表示」的步骤。

### 1.4 定位边界

| 条款 | 实测证据 |
|:--|:--|
| 不绑定厂商/框架 | 文件名含厂商/模型：**0**（`REFUTATION-CENSUS` 附录已记录 3 个正文提及，均为引用场景） |
| 不实现引擎、模型、训练框架 | 标题含 torch/cuda/tensor/autograd/pytorch/jax：**0** |
| 通用基础设施 | `USAGE.md`：四个结构的最小实例，每个代码块可编译 |

### 1.5 形式化与工程

| 条款 | 载体 |
|:--|:--|
| 正确性由 Lean 4 保证 | 7,886 条定理；门禁 **I1** 禁 `axiom`/`opaque`，**I2** 禁 `sorry`/`admit` |
| 证明链梳理干净 | `PROOF-CHAIN-RUNG.md`：六跳全部有承重载体，**零 ⚠️** |
| 语言学术化专业化 | `CONVENTIONS §5` 术语表；文档用「否证」「承重」「义务」而非口语 |
| 该分文件的分文件 | `CONVENTIONS §F1`：≤60 声明/文件；**超限文件 10 个，全在 `Lib`，承重层 0** |
| 命名标注 | `CONVENTIONS §N1–N8`；N4 撇号违规 **3**（全为上游强制例外） |

---

## 2. 那条唯一的 ⚠️ 是如何消失的

第 41 轮的状态表还有一处 ⚠️：`linearLadder` 的 `W := ℝ` 是损失值。

判断是「需要 TorchLean（Lean ≥ 4.26）」。**第 42 轮核实后推翻了它**：
`Lattice.Core` 已有 `AffineLayer`、`netAct`、`WeightSemantics`，都不依赖 TorchLean。
于是 `weightLadder` 给出 `W := List (AffineLayer (Fin 1))`——**真权重栈**。

⇒ **「六跳全有载体」不是靠放宽标准得到的，是靠核实一个过强的阻塞理由得到的。**

---

## 3. 仍然开放的事项（**不是缺口，是范围**）

| 事项 | 性质 | 为什么不做 |
|:--|:--|:--|
| `core.semantics.external_bridge` | 工具链 | 类型化张量 / autograd / IEEE-754 需要 TorchLean（Lean ≥ 4.26）。目标明确说**不实现引擎与框架** |
| `lift.embed.local_minimiser_exact` | 数学上已否证 | 一般命题被 `sound_not_exact` 否证；已在最弱意义上关闭 |
| `core.repair.atomic` | 逐算子义务 | 成本已降到一行（`mkWithAtomic`）；无新内容可做 |
| `geo.loop.convergence_is_single_step` | 已有见证 | `countdown` 已是多步算子 |
| 35 条 camelCase 定理 | 命名规范 | 需逐条判断命名意图，属 P11 后续 |
| `Lib` 内部层序 | 架构 | 需先测 588 文件依赖图；`CONVENTIONS §2b` 已登记 |

**欠账 4 条中：1 条被否证、2 条已到成本下限、1 条是工具链。**
**没有一条是「缺一个证明」。**

---

## 4. 这份终审的边界

1. **它检查「有对应物」，不检查「对应物是否足够强」。** 后者由
   `REFUTATION-CENSUS`（387 条否证）、承重性审计（10 条无冗余）、
   `check_chain_deps`（12 条依赖数）分别负责。
2. **条款是我从目标原文拆的**，不是目标原文的自带编号。
   拆法见脚本，可被质疑与重拆。
3. **`allSame` 等辅助声明**的存在不等于「数据合成可以做多样本」；
   后者由 `samplesOf_sound` 负责。

---

## 5. 怎么复现这份终审

```bash
python agent-tmp/completeness_audit.py     # 16 条条款的声明存在性
cd gov && python gate.py                   # I1-I8
python check_chain_table.py                # 六跳载体存在
python check_refutation_census.py          # 387 条否证
```
