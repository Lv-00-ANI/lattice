# LATTICE 宏观认知与后续规划（第 125 轮独立盘点）

**生成时间：第 125 轮**
**HEAD：`7f3373f`，830 提交**
**本文件不依赖既有 ROADMAP/STATE 文档，仅依据树中实测数据重新建立认知。**

---

## 1. 项目目标（复述，作为判定基准）

**做一条端到端的表示链路：数据 ⇄ token ⇄ 符号模型 ⇄ 权重。**
**正向：符号知识 → 权重（约束损失、数据合成、结构化初始化）。**
**逆向：权重行为 → 符号（验证、修正、再注入）。**
**闭环：验证回路。**
**符号模型直接跑在符号引擎上，不另设中间层。**
**真正的难点只有 符号⇄权重 这一跳。**
**定位：通用基础设施，不绑定厂商/框架，不实现引擎、模型与训练框架。**
**正确性由 Lean 4 形式化保证。**

---

## 2. 实测规模

| 层 | 模块 | 定理 |
|:--|--:|--:|
| `Lib` | **625** | **7,251** |
| `Reference` | 121 | 1,391 |
| `Plugins` | 74 | 786 |
| `Domains` | 104 | 630 |
| `Runtime` | 74 | 458 |
| `Semantics` | 17 | 96 |
| `Core` | 26 | 84 |
| `Evidence` | 12 | 72 |
| `Compose` | 12 | 52 |
| `CInterface` | 5 | 41 |
| `Primitives` | 4 | 31 |

**合计：1094 模块 / 9,651 定理 / 12,1061 声明。**
**gov 脚本 137 个，`verify_all` 126 项检查（99 门禁 + 21 报告）。**
**否证清册 318 条；修复清册 B 层 63 / C 层 265。**

**观察：`Lib` 占比 75%，`Semantics` 仅 17 模块。**
**这个比例本身是一个信号：主体工作量在具体领域与架构实例，而非语义主线。**

---

## 3. `ProofComplete` 的 22 个合取项（全部已解除）

**注册表 + 清册 + 迁移 + T1..T4 + T5..T8 + 梯子 + 闭环 + C 阶段 + D 阶段。**

**逐项内容：**

| 编号 | 合取项 | 性质 |
|:--|:--|:--|
| 1-3 | `PluginRegistryComplete` / `¬ pluginCensusPending` / `RegistryMigratedFor` | **注册表** |
| 4-6 | `t1_compile_sound_instance` / `t1_merge_sound_unrejected` / `t1_compile_sound_general` | **T1 编译可靠性** |
| 7-8 | `t2_penalty_exact` / `t2_penalty_modulus` | **T2 惩罚** |
| 9-12 | `t3_parameter_roundtrip` / `t3_compile_injective` / `t3_semantic_not_injective` / `t3_no_faithful_extractor` | **T3 逆向** |
| 13-14 | `t4_repair_progress` / `t4_loop_converges` | **T4 修复** |
| 15-18 | `t5_recovery` / `t6_spatial` / `t7_confluence` / `t8_failure_isolation` | **T5-T8 时空与容错** |
| 19-20 | `ladder_end_to_end` / `verification_loop_closes` | **端到端与闭环** |
| 21 | `CPhaseAdditions` | **C-1..C-6** |
| 22 | `DPhaseAdditions` | **D-1/D-2/D-5/D-6** |

---

## 4. **本轮发现的关键问题：文档-实现脱节（M5）**

### 4.1 `ARCHITECTURE-CARRIERS.md` 声称三个不存在的载体

**该文档第 5 行说：**

> Conv / Attention / Norm / DAG 是 **L3 载体插件**

**第 12-15 行列出目录：**

```
Lattice/Plugins/Architectures/Conv/
Lattice/Plugins/Architectures/Attention/
Lattice/Plugins/Architectures/Norm/
Lattice/Plugins/Architectures/DAG/
```

**第 44 行起为每个载体列出证明名（如 `compile_conv_sound`、`extract_conv_sound`、`conv_equivariance`）。**

**实测：**

| 项目 | 文档声称 | 磁盘实际 |
|:--|:--|:--|
| `Plugins/Architectures/` 下的目录 | **Conv, Attention, Norm, DAG** | **GNN, Norm** |
| `compile_conv_sound` | **存在** | **0 处** |
| `extract_conv_sound` | **存在** | **0 处** |
| `conv_equivariance` | **存在** | **0 处** |

**=> 三个载体（Conv、Attention、DAG）与其全部证明在树中不存在。**

### 4.2 形态判定

**按 `incomplete-implementation` 的六形态：这是 M5「声称与实现脱节」。**
**影响级别：P0（会误导读者与后续规划——把不存在的能力当作已有）。**

### 4.3 为什么这不是「有意简化」

**有意简化需要边界原因（性能、外部契约、产品取舍）。**
**此处没有：文档不是标注「计划中」，而是**逐目录、逐证明名列出**，与 `Norm` 并列，而 `Norm` 确实存在。**
**=> 读者无法从文档区分「已有」与「未做」。**

### 4.4 相关但不相同的事实

**`Lib/Attention.lean` 存在，但只有 43 行，且不在 `Plugins/Architectures` 下。**
**`Lib` 层的 `Conv`/`DAG` 匹配全是 `Convex`/`Convergence`/`Conversion` 的误命中。**
**=> 三者均无对应实现，`Lib/Attention.lean` 不是 Attention 载体。**

---

## 5. 已完成 vs 未完成的诚实清单

### 5.1 已完成（有 `ProofComplete` 承载）

- **T1-T8 全部**（编译可靠性、惩罚、逆向、修复、时空、容错）。
- **端到端链与验证闭环。**
- **C 阶段 6 项**：求解器读规格、T1 结论含 `R`、`g(δ)` 模数、T3 实例、T3 非空真、T4 第三义务。
- **D 阶段 4 项**：两个语义域、`V` 桥、非平凡语境几何、`sound` 非 `rfl`。
- **8 个插件全部迁移，注册表完整。**

### 5.2 未完成（明确未做）

| 缺口 | 性质 | 出处 |
|:--|:--|:--|
| **`meaningTypesDiffer`** | **已提出、四条路线被否证、仍未证** | 第 126 轮 |
| **Conv / Attention / DAG 三个载体插件** | **文档声称存在，实际不存在** | **本轮发现** |
| **`sound` 只有 1 个非平凡实例** | 编译 = 展平，非数值 | 第 123 轮 |
| **`Pt n → Fin n → ℝ` 载体对** | 未覆盖 | 第 110 轮 |
| **`leZero`/`ltZero`/`gtZero`/距离的模数** | 未做 | 第 109 轮 |
| **S7-S20 的语义条目** | 部分 | D 阶段 |

---

## 6. 重新规划：后续优先级

### P0：修正误导性文档（本轮完成）

**`ARCHITECTURE-CARRIERS.md` 必须区分「已有」与「计划中」。**
**这是正确性问题：一份把不存在的能力描述为已有的文档，会让后续规划建立在错误前提上。**

### P1：补齐三个载体（F 阶段的实际工作）

**按现有 GNN / Norm 的插件形状建立：**

1. **`Plugins/Architectures/Conv/`** —— **卷积的权重共享约束**：
   - `Manifest.lean`、`Semantics.lean`、`Soundness/`、`Equivariance/`、`Plugin.lean`
   - **核心定理：`compile_conv_sound`（编译到权重保持卷积语义）、`conv_equivariance`（平移等变）**
2. **`Plugins/Architectures/Attention/`** —— **注意力的置换等变**：
   - **核心定理：`attention_perm_equivariant`（对 token 置换等变）**
3. **`Plugins/Architectures/DAG/`** —— **有向无环图的计算顺序**：
   - **核心定理：`dag_confluence`（拓扑序无关性）**

### P2：语义主线的剩余条目（D-8 起）

- **S7-S20 的逐条形式化。**
- **`meaningTypesDiffer` 的持续攻关（已知四条路线不通）。**

### P3：模数的构造子扩展

- **`leZero`/`ltZero`/`gtZero`/距离的 `g(δ)`。**

---

## 7. 本轮结论

**项目的**主线**（符号⇄权重 的 T1-T8 + 端到端 + 闭环）是完整的，且有 22 项 `ProofComplete` 承载。**
**C 与 D 两个阶段的强化成果均已进入判据。**

**但 F 阶段（架构载体）存在**实质缺口**，且被文档掩盖。**
**=> 后续应优先补齐三个载体，而不是继续在语义层深挖——因为语义层的主干已由 D 阶段收口。**

**同时，`meaningTypesDiffer` 是已知的开放问题，不应阻塞主线。**
