# 语义信息主攻方向（SEMANTICS-MAINLINE）

> **状态**：方向文档，不是完成声明。
> 本文定义「语义信息」在 LATTICE 里的含义、形式化骨架、证明义务与三阶段路线。
> 它与 `PARADIGM.md` 的关系是：`PARADIGM` 定义「表示格」这一层；本文定义「语义信息」这一层，并把后者定为**主攻方向**。
> 本文不写数字；所有可漂移的计数交给 `gov/` 守卫。

---

## 0. 一句话

**语义信息 = 在某个语义域 `D` 上，模型行为与符号指称之间可证明的对应关系。**

主攻方向不是「给权重写注释」，而是把这句话拆成三层可证对象：

1. **约束几何语义**：语义 = 约束解集；几何 = 解集；标注 = 约束集。可精确证明。
2. **程序语义**：语义 = 程序 AST 的指称；几何 = 程序结构；标注 = 程序片段到约束/功能的映射。可证明，但需要非线性原语与模型级 `Representation`。
3. **隐空间几何语义**：语义 = 对激活/隐空间的解释函数。这是经验科学；只能证**条件性**定理，不能假装它是已证的。

**先做第 1 层，再做第 2 层；第 3 层是研究赌注，不作为近期承诺。**

---

## 1. 背景设定

目标用法（本文的形式化对象）：

1. **多个专业基础模型**：每个模型在极端特化的结构化语料上常规预训练，避免数据冲突。
2. **权重 → 符号**：把每个模型的权重/结构映射成符号画像（profile）。
3. **人工整合**：由人决定专家之间如何合并、冲突如何裁决、优先级如何排。
4. **LATTICE 做后训练与精细编辑**：约束损失、验证、修复、编辑、回滚。
5. **C 实现**：Lean 出规范/证明，C 出可执行运行时。

本文只讨论 **Lean 侧的语义层**与它对 C 的接口；C 代码独立实现。

---

## 2. 三个命题的精确化

### 2.1 「词表可以携带语义」

精确说法：存在一个**指称函数**

```lean
structure Vocab where
  Token : Type
  denote : Token → Meaning
```

`denote` 是**约定**，不是从权重里学出来的。词表提供的是**符号接口**：人类可读、可标注、可编辑。它本身不保证模型「按这个指称使用 token」；后者是行为语义，需要另证。

### 2.2 「权重 + 词表可以携带语义信息且完整」

必须区分两种「完整」：

| 完整性 | 陈述 | 性质 |
|:--|:--|:--|
| **行为完整** | 给定 `W` 与 `Vocab`，`behavior : List Token → Meaning` 被唯一决定 | 同义反复，没有信息量 |
| **符号完整** | `∀ m ∈ D, ∃ W, behavior W = m` | 非平凡；只对受限语义域 `D` 可能成立 |

⇒ 本文只承诺**相对语义域 `D` 的符号完整**，并要求给出：

- `D` 的定义（约束、程序、有限事实库、几何对象……）；
- `behavior` 的定义；
- 覆盖定理 `complete_on D`；
- 反例/边界：`D` 之外不声称。

**「所有 LLM 的语义」不在 `D` 内**；这是一条明确的非声称。

### 2.3 「几何结构继承语义信息」

「几何」有两种，必须分开：

| 几何 | 语义 | 能否证明 |
|:--|:--|:--|
| **约束几何**：`{ x | constraints }` | 约束集本身 | **能**：`Holds` 就是 `label`，继承是定义级 |
| **程序几何**：AST / 计算图 | 程序指称 | **能**：`eval` 定理；`l2l3_sound` 是桥 |
| **隐空间几何**：激活流形/度量/曲率 | 解释函数 `label` | **只能条件性**：假设 `label` sound，证编辑局部性；不能证 `label` 本身 |

本文的「几何继承」默认指**约束几何/程序几何**；隐空间几何单列为研究阶段。

### 2.4 「直接标注继承内容就可以编辑」

标注不是注释，是**结构上的补丁 + 定理**。一个可编辑的标注至少要有：

```lean
structure Annotation where
  target : Region
  meaning : Meaning
  provenance : Provenance        -- 来自哪个专家/约束/编辑
  priority : Priority

structure Edit where
  apply : Structure → Annotation → Delta → Structure
  realizes : ∀ a, label (apply S a δ) a.target = a.meaning
  frame : ∀ x ∉ a.target, label (apply S a δ) x = label S x
  reversible : apply (apply S a δ) (inverse δ) = S
```

没有 `realizes`，标注是假的；没有 `frame`，编辑会破坏无关知识；没有 `reversible`，不能回滚。

---

## 3. 形式化骨架（Lean）

以下是**目标结构**，不是当前已实现的声明；实现时逐条落到 `Lattice/` 的模块里。

```lean
-- 语义域：必须先选一个可形式化的 D
structure SemanticDomain where
  Meaning : Type
  equiv : Meaning → Meaning → Prop

-- 词表：token 到语义的约定
structure Vocab (D : SemanticDomain) where
  Token : Type
  denote : Token → D.Meaning

-- 模型：权重 + 行为
structure Model (D : SemanticDomain) where
  Weights : Type
  behavior : List Token → D.Meaning

-- 几何：载体 + 标注
structure Geometry (D : SemanticDomain) where
  Carrier : Type
  label : Carrier → D.Meaning

-- 继承：几何标注与模型行为一致
structure Inherits (D) (G : Geometry D) (M : Model D) where
  embed : M.Weights → G.Carrier
  sound : ∀ w x, G.label (embed w x) = M.behavior w x
  complete : ∀ m : D.Meaning, ∃ w x, G.label (embed w x) = m
```

**关键设计**：`Inherits` 是**结构**，不是假设。`sound`/`complete` 是字段，必须由实例填充；没有实例就没有继承。

### 3.1 编辑的五个义务

| 义务 | 陈述 |
|:--|:--|
| `realizes` | 编辑后目标区域的标注等于意图 |
| `frame` | 目标区域外的标注不变 |
| `reversible` | 存在逆编辑，回到原结构 |
| `idempotent` | 重复同一编辑不改变结果（或显式记录非幂等） |
| `conflict_free` | 多标注编辑不引入未登记的冲突；冲突可检测/可修复 |

### 3.2 整合证书（人工整合的可检查记录）

人工整合必须留下**可检查的记录**，否则不可复现：

```lean
structure MergeRecord where
  experts : List Expert
  constraints : List Constraint
  priority : Priority
  decisions : List Decision          -- 人做出的取舍
  provenance : Provenance

structure MergeSound (R : MergeRecord) (M : Model) where
  per_domain : ∀ e ∈ R.experts, ...   -- 专家域内保持
  global : ...                        -- 全局约束满足
  conflict_free : ...                 -- 冲突已裁决或已修复
```

`MergeRecord` 是**数据**；`MergeSound` 是**证明**。人只填数据，机器检查证明。

---

## 4. 流程（与 LATTICE 的接口）

```
专家模型 W_i
   │  extract（结构符号/约束画像；标注 exact / approx / unknown）
   ▼
Profile P_i
   │  人工整合（MergeRecord：约束、优先级、冲突裁决）
   ▼
Merged Profile P
   │  compile（符号→程序/权重）
   ▼
Model/Program M
   │  后训练（约束损失 + 验证 + 修复；LATTICE 提供约束层）
   ▼
Post-trained M'
   │  Edit（Annotation + Delta + frame/reversible）
   ▼
Edited M''
```

每一步的 Lean 义务：

| 步骤 | 义务 |
|:--|:--|
| `extract` | `extract_sound`：抽出的 profile 在专家域内与行为一致；`exact/approx` 显式标注 |
| `merge` | `MergeSound`：专家域保持 + 全局约束 + 冲突裁决 |
| `compile` | `compile_sound`：编译后的程序/权重满足 merged profile |
| `post-train` | `preserves_constraints`：后训练步骤后约束仍成立（或由 repair 恢复） |
| `edit` | `realizes` + `frame` + `reversible` + `conflict_free` |

---

## 5. 三阶段路线

### 阶段 1：约束几何语义（近期，优先）

- `SemanticDomain` = 约束集；`Meaning` = `ConstraintSet`；
- `Vocab.denote`：token → 约束的约定；
- `Geometry.label` = 约束集；`Inherits.sound` = `Holds` 定理；
- `Annotation`/`Edit`：加/删/改约束 + `Repair`；
- 证明：`realizes`/`frame`/`reversible`/`conflict_free`；
- C 接口：profile、check、compile、edit、rollback。

**交付标准**：一个结构化专家域（如线性/几何约束）上，端到端演示「抽取 → 人工整合 → 编译 → 约束后训练 → 标注编辑 → 回滚」，并给出 `frame` 定理。

### 阶段 2：程序语义（中期）

- `SemanticDomain` = 程序 AST 的指称；
- 扩展 `Program`/`CExpr`/`StackOp` 的非线性原语（`div/sqrt/exp/log/relu/softmax/layernorm`）；
- 定义 `attention`/`block`/`model` 的 AST 与 `eval`；
- `Representation`：`P`（符号规格）⇄ `W`（程序 + 参数），语法精确往返，语义由 `eval` 定理给；
- `Edit`：程序补丁 + 局部性。

**交付标准**：一个 Transformer block 作为程序可编译、可执行、可编辑；`l2l3_sound` 非重言；C 解释器可运行。

### 阶段 3：隐空间几何语义（研究）

- `label` 由探测/SAE/因果干预给出；
- 只能证**条件性**定理：给定 `label` 的 soundness 假设，证编辑局部性/副作用界；
- 不承诺「隐空间几何自动继承语义」；这是经验假设。

**交付标准**：一个可复现的标注协议 + 条件性定理 + 副作用评估；不声称普遍性。

---

## 6. 证明义务清单

| ID | 义务 | 验收 |
|:--|:--|:--|
| S1 | `vocab_denote_sound` | 词表指称与行为在词表上的限制一致 |
| S2 | `complete_on D` | 对语义域 D 的覆盖定理；D 外有反例/边界 |
| S3 | `geometry_inherits` | `label ∘ embed = behavior`（约束/程序几何） |
| S4 | `annotation_realizes` | 编辑后目标语义成立 |
| S5 | `edit_frame` | 目标外不变 |
| S6 | `edit_reversible` | 逆编辑回到原结构 |
| S7 | `edit_conflict_free` | 冲突检测/修复；无未登记冲突 |
| S8 | `merge_record_sound` | 专家域保持 + 全局约束 |
| S9 | `compile_sound` | 编译结果满足 merged profile |
| S10 | `post_train_preserves` | 后训练后约束保持/可修复 |
| S11 | `program_representation_roundtrip` | 程序语法精确往返 |
| S12 | `transformer_eval` | block/model 的 `eval` 语义 |
| S13 | `float_refinement` | 若 C 用 double，给出误差界；否则显式信任边界 |

**S1–S8 是阶段 1 的核心；S9–S12 是阶段 2；S13 是 C 正确性的前置。**

---

## 7. C 运行时接口（描述，不实现）

Lean 侧只需要给**数据格式 + 定理**；C 侧独立实现。

| 接口 | 输入 | 输出 | 对应 Lean |
|:--|:--|:--|:--|
| `profile_load` | 权重/程序 | `Profile`（约束、标注、provenance） | `extract` |
| `merge_check` | 多 `Profile` + `MergeRecord` | 通过/冲突报告 | `MergeSound` |
| `compile` | `Merged Profile` | 程序/权重 | `compile_sound` |
| `check` | 约束 + 点/输入 | 判定 | 12/12 可执行判定 |
| `train_hook` | 约束损失/验证/修复 | 约束满足 | `post_train_preserves` |
| `edit` | 结构 + `Annotation` + `Delta` | 新结构 | `realizes/frame/reversible` |
| `rollback` | 编辑记录 | 原结构 | `reversible` |

**信任边界**：若不做 S13，C 的 `double` 路径只能标为「受信任实现」，不能声称「证明保证 C 正确」。整数/定点路径（token、量化、索引）可精确，优先。

---

## 8. 评价指标（不是定理，但决定方向是否成立）

| 指标 | 定义 |
|:--|:--|
| 抽取保真度 | `extract` 在专家域内与行为一致的比例；exact/approx/unknown 分类 |
| 约束满足率 | 合并/编辑后，约束在测试输入上的满足比例 |
| 编辑局部性 | 目标区域变化 / 非目标区域变化 |
| 回滚精确度 | `rollback(edit(S))` 与 `S` 的行为差 |
| 冲突检测率 | 人工标注的冲突中被 `MergeSound` 检出的比例 |
| 端到端任务保持 | 专家域任务分数在整合/编辑后的下降 |

**只证定理不做这些指标，方向无法被外部接受；只做指标不证定理，则退化为普通 model merging。**

---

## 9. 非目标与非声称

- **不声称**「权重 + 词表对所有语义完整」；只对显式语义域 `D` 声称。
- **不声称**「隐空间几何自动继承语义」；这是阶段 3 的研究假设。
- **不声称**「标注即编辑」；标注必须配 `Edit` 的 `realizes/frame/reversible`。
- **不声称** LATTICE 替代优化器/后训练算法；它提供约束/验证/修复层。
- **不声称** 任意常规预训练权重都可精确抽取成语义符号；`extract` 的保真度必须逐域标注。
- **不声称** 本文是完成声明；它是主攻方向与义务清单。

---

## 10. 与现有文档的关系

| 文档 | 关系 |
|:--|:--|
| `PARADIGM.md` | 定义表示格与 8 维记分卡；本文是其上的语义层 |
| `OBJECTIVE-MAP.md` | 14 条目标条款的载体；本文的 S1–S13 是新增语义义务，暂不计入既有 14 条 |
| `OBJECTIVE-AUDIT.md` | 「定理/检查/定位」三分法；本文每条也应按这三类标注 |
| `STATE-FINAL.md` / `DELIVERY.md` | 交付状态；本文不修改其数字，只新增方向 |
| `Slots.lean` | 新义务若承重，应登记为 slot；未登记前不得声称「owed 0 覆盖本文」 |

**治理规则**：本文每一条陈述必须落为以下三类之一：

1. **theorem**：有 Lean 声明与证明；
2. **check**：有 `gov/` 可执行检查；
3. **hypothesis**：显式标为研究假设，不进入交付声明。

没有第四类「散文默认成立」。

---

## 11. 近期执行顺序

1. **写 `SemanticDomain`/`Vocab`/`Geometry`/`Inherits` 的最小定义**（阶段 1，约束几何）。
2. **把 `Annotation`/`Edit` 的五个义务写成 structure 字段**，先对几何约束实现。
3. **`MergeRecord`/`MergeSound`**：人工整合证书的最小版本。
4. **一个端到端 MVP**：2–3 个结构化专家域，抽取→整合→编译→编辑→回滚。
5. **阶段 2 的原语与 AST**：非线性算子、Transformer block、程序级 `Representation`。
6. **阶段 3 只在阶段 1/2 有论文级结果后启动**；在此之前只写研究假设，不写承诺。

---

## 12. 一句话总结

**语义信息不是「权重里藏着可以被读出的意义」，而是「在显式语义域上，行为、符号、几何三者之间可证明的对应关系」。**
**主攻方向 = 约束几何语义（可证）→ 程序语义（可证，需非线性/Transformer）→ 隐空间几何语义（条件性，研究）。**
**标注只有在带上 `realizes/frame/reversible` 时才等于编辑；否则它只是注释。**
