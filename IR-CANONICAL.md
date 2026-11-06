# IR-CANONICAL —— 结构语义表示规范形 IR

> **状态：** 设计规格（2026-11-07）。实现未开始。
> **定位：** 这不是新载体，不是新语言，是**规范形 IR**：
> 模型权重的**结构语义表示**，正逆统一，唯一。
> **不实现：** LLM 前端、语言实现、大规模验证、训练、格式 I/O、C、自回归、MoE 执行。

---

## 0. 一句话

**IR = 权重的结构语义表示规范形。**
权重与 IR 之间有两个方向：`compile`（IR → 权重）与 `extract`（权重 → IR）；
`extract` 唯一，因此 IR 是**规范形**；`roundtrip` 把两个方向统一。

---

## 1. 定位

### 1.1 三个词各自的含义

| 词 | 含义 | 不是什么 |
|:--|:--|:--|
| **结构** | 权重内部的关系网（张量 + 高维超边） | 不是语法树 |
| **语义** | 结构自带的全部信息（九项） | 不是外部投影 |
| **规范形** | 唯一的标准表示 | 不是某种分解选择 |

### 1.2 与已有概念的区别

| 概念 | 与本 IR 的关系 |
|:--|:--|
| CIC term | CIC 是**符号载体**；IR 是**结构表示**。两者可以互相编码，但不是同一个东西 |
| `HyperStructure` | 同一对象的技术名；IR 是它在文档中的正式名 |
| `Ladder` | `Ladder` 是接口形状；IR 是 `l2l3` 的输入 |
| `ModelArtifact` | 产物；IR 是产物的结构描述 |
| `Program`（旧设计） | 被 IR 取代；程序是 IR 的一种渲染 |
| 几何 | 待归档；IR 是它的替代品 |

### 1.3 不是新载体

**载体是“符号用什么表达”**：几何、CIC、DSL。
**IR 是“权重用什么描述”**：关系网。

两者正交：

```text
符号载体（CIC / 几何 / DSL）
        │ compile
        ▼
      权重
        │ extract
        ▼
  IR（结构语义表示规范形）
```

IR 不替代载体，它替代“逆向只读回程序”这种弱形态。

### 1.4 为什么需要 IR

| 现状 | 问题 |
|:--|:--|
| `Ladder.satW := netAct w 0 = 0` | 只约束一个点，退化 |
| 逆向只读回 `Program` | 只证“读回同一个程序”，不证“这个程序是那个模型” |
| `Vocab.denote` 是约定 | 语义外挂，不从结构来 |
| 权重有低秩/共享/对称/路由 | 二元图表达不了 |

**IR 解决这四条。**

---

## 2. 核心对象

### 2.1 `Tensor`

```lean
structure Tensor where
  id    : TensorId
  shape : List Nat
  data  : Fin (shape.product) → ℝ
```

- `shape` 是多轴（`[d₁, d₂, …]`）；
- 张量集由权重唯一决定。

### 2.2 `Relation`（高维超边）

```lean
structure Relation where
  kind : RelKind
  args : List (TensorId × List Nat)   -- 每个参数带多轴索引
  hold : Holds kind args
  part : Option PartKind              -- 视图标注，不影响唯一性
```

```lean
inductive PartKind where
| vocab      -- 词表部分
| arch       -- 架构部分
| shared     -- 两者共享
```

- **不投影到二元边**；
- 轴是参数的一部分；
- 一条关系可有 n 个参数；
- `part` 只是标注，不是结构的一部分。

### 2.3 `IR`

```lean
structure IR where
  tensors   : List Tensor
  relations : List Relation
```

- 张量集 + 关系集；
- **词表信息已展开为关系，IR 自包含**；
- 由权重唯一决定（见 §5）。

### 2.4 关系种类（初始集）

#### 架构关系

| 种类 | 含义 | 唯一性来源 |
|:--|:--|:--|
| `equal` | 两处相等 | 相等与否唯一 |
| `zero` | 某位置为零 | 零位置唯一 |
| `lowRank` | 秩 ≤ r | 秩唯一 |
| `block` | 分块 | “最细”边界唯一 |
| `symmetry` | 在群下不变 | “最大”群唯一 |
| `depends` | 输出依赖输入 | 由计算图唯一 |
| `ordered` | 顺序 | 由依赖唯一 |
| `scaled` | 成比例 | 比例唯一 |
| `transposed` | 转置 | 由索引唯一 |
| `shared` | 共享参数 | 由相等唯一 |

#### 词表关系

| 种类 | 含义 | 参数形态 | 唯一性来源 |
|:--|:--|:--|:--|
| `tokenOf` | 索引 `i` 的 token 是 `s` | `(E, i)`, `s` | 由 id 唯一 |
| `merges` | `c = a ++ b` | `a`, `b`, `c` | 由规则唯一 |
| `specialToken` | `i` 是特殊 token `s` | `(E, i)`, `s` | 由 id 唯一 |
| `contiguous` | 某范围同属一族 | `(E, [lo,hi])` | 可选结构信息 |
| `sorted` | 某范围按频率排序 | `(E, [lo,hi])` | 可选结构信息 |

**前三条是必须的；后两条是可选的。**

**初始集，可随插件扩展（见 §4.4）。**

---

## 3. 权重的内部关系

### 3.1 为什么不是简单图

| 维度 | 内容 |
|:--|:--|
| **张量维** | 权重是 `d₁ × d₂ × …`，关系作用在多个轴上 |
| **层维** | 同一关系跨层（层 `i` 与层 `j` 共享） |
| **头维** | 注意力头之间的关系 |
| **专家维** | MoE 专家之间的关系 |
| **时间维** | 序列位置之间的关系（`t` 与 `t+k`） |
| **类型维** | 不同原语类型之间的关系 |
| **约束维** | 等式、不等式、秩、稀疏 |

**关系不是“节点之间的边”，而是“多维索引之间的关系”。**

### 3.2 高维结构的表现

| 现象 | 高维性 |
|:--|:--|
| 层间共享 | `(layer, head, dim)` 的相等 |
| 低秩 | `(dim_out, dim_in)` 上的秩约束 |
| MoE | `(token, expert)` 的路由 |
| 位置编码 | `(position, dim)` 的周期关系 |
| 分块 | `(block_id, offset)` |

### 3.3 为什么不投影

| 投影 | 问题 |
|:--|:--|
| 二元边 | 丢轴 |
| 线性列表 | 丢无序性 |
| 规范形（外部规则） | 需额外规则，非内在 |

**投影是低维工具的限制，不是问题本身；直接拿高维结构，唯一性就落在关系集上。**

### 3.4 投影造成的不唯一

| 担心 | 原因 | 消除 |
|:--|:--|:--|
| 轴置换 | 投影到不同轴 | 不投影，轴是参数 |
| 分解顺序 | 线性列举 | 关系是集合，无序 |
| 等价重写 | 图重写 | 超边不可重写 |

---

## 4. 原语

### 4.1 原语是关系的名字

```lean
structure Primitive where
  key      : ServiceKey
  plugin   : PluginName        -- 提供者
  relKind  : RelKind
  name     : String            -- 可读名
  arity    : Nat               -- 参数个数
  shape    : ShapeSpec         -- 形状规则
  build    : Params → Weights  -- 构造
  contract : Contract          -- 契约
```

- 一个 `Primitive` 对应一种 `RelKind`；
- 不是“分解单位”，而是“关系的名字”；
- **互斥性不需要成立**。

### 4.2 原语的职责

| 职责 | 说明 |
|:--|:--|
| **形状** | 输入/输出形状 |
| **构造** | 从参数构造权重片段 |
| **逻辑关系** | 与其他片段的连接方式 |
| **契约** | 符号侧与权重侧的要求 |

### 4.3 原语分类（从权重分析，非枚举）

> **以下分类是从权重实际数学结构分析得到的，不是举例。**

| 类别 | 原语 | 覆盖 |
|:--|:--|:--|
| **计算** | `matmul` / `add` / `mul` | 线性运算 |
| **激活** | `relu` / `gelu` / `silu` / `swiglu` | 非线性 |
| **归一化** | `layernorm` / `rmsnorm` | 统计依赖 |
| **注意力** | `attention` / `causal` / `multihead` | 路由加权 |
| **位置** | `rope` / `alibi` / `absolute` | 位置结构 |
| **结构** | `seq` / `par` / `residual` / `branch` | 组合 |
| **路由** | `moe` / `topk` / `shared` | 条件分支 |
| **参数关系** | `tie` / `lowRank` / `block` / `symmetry` | 约束 |
| **词表** | `embed` / `unembed` / `tie` | 映射 |
| **生成** | `sample` / `kv_cache` | 自回归 |
| **数值** | `quantize` / `dequantize` | 精度 |

**十一类是从实际权重能想到的；是否完整需“缺失分析”判定（见 §12）。**

### 4.4 原语集随插件扩展

```lean
def primitiveCatalog (reg : List VerifiedPlugin) : List Primitive :=
  reg.flatMap (fun p => p.primitives)
```

| 插件 | 提供的原语 |
|:--|:--|
| `Architectures.Norm` | `layernorm` / `rmsnorm` |
| `Architectures.Attention` | `attention` / `causal` / `multihead` |
| `Architectures.Conv` | `conv` / `toeplitz` |
| `Architectures.GNN` | `messagepass` |
| `Architectures.DAG` | `seq` / `par` / `residual` |
| 新增 SSM 插件 | `scan` / `selective` |
| 新增 MoE 插件 | `moe` / `topk` |

**插件 = 原语的提供者；原语集 = 所有插件的并集。**

### 4.5 原语不是互斥划分

| 性质 | 是否成立 |
|:--|:--|
| 覆盖性 | ✅ 可以 |
| 互斥性 | ❌ **不成立** |
| 可组合 | ✅ 可以 |
| 可扩展 | ✅ 可以 |
| 可验证 | ✅ 可以 |

**互斥性不成立的原因：**

| 原因 | 说明 |
|:--|:--|
| 粒度不同 | `attention` 包含 `matmul` + `softmax` + `matmul` |
| 约束可叠加 | `matmul` + `lowRank` 不是互斥，是叠加 |
| 多重解释 | 同一 `W` 可同时满足多种原语 |

**唯一性不来自原语互斥，而来自结构（见 §5）。**

### 4.6 原语的偏序（非划分）

```text
moe ⊐ block ⊐ attention ⊐ matmul ⊐ ...
```

- `⊐` 表示“包含”；
- 粗粒度可展开为细粒度；
- 细粒度可收缩为粗粒度；
- **这是偏序，不是划分。**

---

## 5. 唯一性

### 5.1 关系集唯一

```lean
theorem relations_unique (w : Weights) :
  ∃! R, IsRelationSet R w
```

`IsRelationSet` 要求：

| 性质 | 含义 |
|:--|:--|
| 覆盖 | 每个非零/非平凡位置都有关系 |
| 极大 | 没有可加的关系 |
| 精确 | 关系的 `hold` 真 |

**唯一性来源：**

| 项 | 唯一 |
|:--|:--|
| 张量形状 | ✅ |
| 相等 | ✅ |
| 零位置 | ✅ |
| 秩 | ✅ |
| 块边界 | ✅ “最细” |
| 对称群 | ✅ “最大” |

### 5.2 IR 唯一

```lean
theorem ir_unique (w : Weights) :
  ∃! S, IsIR S w
```

- 张量集唯一；
- 关系集唯一；
- **所以 IR 唯一。**

### 5.3 三个需要定义的对象

| 对象 | 需要定义 | 唯一性定理 |
|:--|:--|:--|
| **最细块** | 不可再分的非零块 | `finest_block_unique` |
| **最大不变群** | 对 `w` 不变的最大群 | `maximal_symmetry_unique` |
| **最小依赖** | 生成 `w` 的最小依赖集 | `minimal_dependency_unique` |

**这三个是“唯一性”的核心研究对象。**

### 5.4 若某个不唯一

| 情形 | 处理 |
|:--|:--|
| 给出反例 | 证否 |
| 给出更细定义 | 替代 |
| 承认不唯一 | 给等价类 |

---

## 6. 正逆统一

### 6.1 同一个结构，两个方向

```text
           ┌─────────┐
           │   IR    │   ← 本体（唯一）
           └────┬────┘
      compile │      │ extract
              ▼      ▼
           ┌─────────┐
           │ Weights │
           └─────────┘
```

### 6.2 正向

```lean
def compile (S : IR) : Weights

theorem compile_sound (S : IR) (hS : WellFormed S) :
  Satisfies (compile S) (semantics S)
```

### 6.3 逆向

```lean
def extract (w : Weights) : IR

theorem extract_sound (w : Weights) :
  Satisfies w (semantics (extract w))
```

### 6.4 往返

```lean
theorem roundtrip (w : Weights) :
  compile (extract w) = w

theorem roundtrip_semantic (w : Weights) :
  semantics (compile (extract w)) = semantics w
```

**`extract` 唯一且 `compile` 确定 ⇒ 往返成立。**

### 6.5 与已证定理不冲突

| 已证 | 是否冲突 | 原因 |
|:--|:--|:--|
| `semantic_not_injective` | ❌ | 约束语义层；这里可逆的是结构层 |
| `no_extractor_preserves_both` | ❌ | 约束参数层+语义层同时；这里只承诺结构层 |
| `reversibility_boundary` | ❌ | 约束参数层；结构层可逆 |

**三层可逆性分明：**

| 层 | 可逆 |
|:--|:--|
| 结构层（IR） | ✅ 可逆 |
| 参数层 | ❌ 单射非同构 |
| 语义层 | ❌ 不可逆 |

---

## 7. 契约

```lean
structure Contract where
  sym    : Sym → Prop        -- 符号侧
  weight : Weights → Prop    -- 权重侧
  sound  : ∀ s, sym s → weight (build s)
```

- 契约保证“构造的权重满足符号侧要求”；
- 这是 `l2l3_sound` 的来源；
- 契约是 `Obligation` 在语义侧的对应。

---

## 8. 语义

### 8.1 语义是结构自带的

```lean
def semantics (S : IR) : Semantics
```

`Semantics` 包含九项：

| # | 内容 | 说明 |
|--:|:--|:--|
| 1 | 形状 | 每片段的输入/输出形状 |
| 2 | 参数 | 每片段的权重 |
| 3 | 关系 | 连接、共享、依赖 |
| 4 | 类型 | 线性/非线性/路由 |
| 5 | 组合方式 | 序列/并行/残差/分支 |
| 6 | 约束 | 组合后的等式/不等式 |
| 7 | 不变量 | 在什么变换下不变 |
| 8 | 来源 | 从什么构造出来 |
| 9 | 行为 | 由 1–5 决定 |

**九项合起来才是语义；任一单项只是语义的一个投影。**

### 8.2 语义不是投影

| 我之前错误的说法 | 正确 |
|:--|:--|
| 语义 = 六个投影 + coherence | **语义 = 结构自带的九项** |
| 语义 = 结构 + 词表生成 | **结构是本体；词表是命名** |
| 词表是语义来源 | **词表只是解释的词汇** |

### 8.3 词表：直接读入 IR

#### 8.3.1 词表是什么

词表 = **大模型自带的 tokenizer 词表文件**（`vocab.json` / `merges.txt` / `tokenizer.model` / `tokenizer.json`）。

**格式由工程侧的解析器处理**；LATTICE 只消费解析后的抽象结构：

```lean
structure ParsedVocab where
  tokens  : List String                          -- 按 id 排序
  merges  : List (String × String × String)      -- (a, b, c) 表示 c = a ++ b
  special : List (String × Nat)                  -- 特殊 token
```

**这是工程侧的输出；LATTICE 不解析文件。**

#### 8.3.2 抽象覆盖大多数厂商

不看格式，只看结构：

| 共性 | 抽象 | 覆盖 |
|:--|:--|:--|
| token 到 id 的映射 | `tokenOf(i, s)` | 全部 |
| id 到 token 的映射 | `tokenOf` 反向 | 全部 |
| 特殊 token | `specialToken(i, s)` | 全部 |
| 子词合并 | `merges(a, b, c)` | BPE / WordPiece / Unigram |
| 词表大小 | `Tensor E` 的行数 | 全部 |
| 嵌入向量 | `Tensor E` 的数据 | 全部 |

**六项足以覆盖大多数厂商。**

#### 8.3.3 映射进 IR

```lean
def vocabRelations (v : ParsedVocab) (E : TensorId) : List Relation
```

- 生成 `tokenOf`、`merges`、`specialToken` 关系；
- 参数带 `E` 与索引；
- `part := some .vocab`。

**词表信息在 `relations` 里，IR 自包含。**

#### 8.3.4 词表部分与架构部分的区分

| 部分 | 关系 | `part` |
|:--|:--|:--|
| **词表部分** | `tokenOf` / `merges` / `specialToken` | `.vocab` |
| **架构部分** | `lowRank` / `block` / `depends` / `transposed` | `.arch` |
| **共享部分** | `tie(E, U)`（既是词表也是架构） | `.shared` |

**`part` 是视图标注，不影响 `ir_unique`。**

#### 8.3.5 实际语义信息怎么看

三步：

| 步 | 内容 | 产出 |
|--:|:--|:--|
| 1 | `extract w = IR` | 结构 |
| 2 | 按 `part` 分组遍历关系 | 词表部分 / 架构部分 / 共享部分 |
| 3 | 每条关系用词表查名字 | 可读文本 |

**示例：**

IR：

```
tensors:
  E (32000 × 4096)   -- 词表嵌入
  U (4096 × 32000)   -- 输出头

relations:
  tokenOf(E, 0, "<pad>")        part=vocab
  tokenOf(E, 1, "<s>")          part=vocab
  tokenOf(E, 2, "的")            part=vocab
  merges("的", "话", "的话")     part=vocab
  specialToken(E, 0, "<pad>")    part=vocab
  transposed(E, U)              part=arch
  lowRank(E, r=?)               part=arch
  tie(E, U)                     part=shared
```

渲染：

```
vocab:
  E: 词表嵌入 32000 × 4096
    token 0 = "<pad>"  (特殊)
    token 1 = "<s>"
    token 2 = "的"
    ...
    merges: "的" + "话" → "的话"

arch:
  E: 低秩
  U: 是 E 的转置

shared:
  U 与 E 共享行
```

**这就是“实际语义信息”——能看见每个 token 对应哪一行、哪些是架构关系。**

#### 8.3.6 词表关系也参与唯一性

| 关系 | 唯一性 |
|:--|:--|
| `tokenOf` | ✅ 由 id 唯一 |
| `merges` | ✅ 由规则唯一 |
| `specialToken` | ✅ 由 id 唯一 |
| `contiguous` / `sorted` | ⚠️ 可选，不参与 |

**词表关系不影响唯一性，反而增加确定性。**

#### 8.3.7 词表格式不在本仓库

| 项 | 归属 |
|:--|:--|
| `vocab.json` 解析 | **工程侧** |
| `merges.txt` 解析 | **工程侧** |
| `tokenizer.model` 解析 | **工程侧** |
| `ParsedVocab` | LATTICE 消费 |
| `vocabRelations` | LATTICE 提供 |
| 词表编辑 | 见 §9 |

### 8.4 语义的“解释”

| 解释 | 不是 |
|:--|:--|
| 把结构的形状说出来 | 给结构加形状 |
| 把结构的连接说出来 | 给结构加连接 |
| 把结构的行为说出来 | 给结构加行为 |
| 把结构的不变量说出来 | 给结构加不变量 |

**解释是“读出来”，不是“写进去”。**

### 8.5 词表编辑 = 结构编辑

> **词表在 IR 里就是关系；所以改词表就是改结构中的一部分关系。**

```text
tokenOf(E, 2, "的")          -- 词表关系
merges("的", "话", "的话")     -- 词表关系
specialToken(E, 0, "<pad>")  -- 词表关系
lowRank(E, r=8)              -- 架构关系
tie(E, U)                    -- 架构关系
```

**它们都是 `Relation`；`part` 只是视图标注。**

因此：

| 想做的 | 实际是 |
|:--|:--|
| 改 token 名 | 改一条 `part := .vocab` 的关系 |
| 加 token | 加一条 `tokenOf` 关系 + 扩 `E` |
| 改合并规则 | 改一条 `merges` 关系 |
| 改架构关系 | 改一条 `part := .arch` 的关系 |

**统一为 `Edit`，见 §9。**

### 8.6 `part` 只用于渲染分组

| 用途 | 是否用 `part` |
|:--|:--|
| 决定是否传播 | ❌ 不用 |
| 决定渲染分组 | ✅ 用 |
| 决定一致性检查 | ❌ 不用 |
| 决定 `ir_unique` | ❌ 不用 |

**`part` 不影响编辑语义；它只影响“渲染时怎么分组显示”。**

### 8.7 旧的抽象 `Vocab`

> **此前设计的 `Vocab { Name, Meaning, denote }` 是展示层的命名系统，不是模型词表。**

| 对象 | 作用 |
|:--|:--|
| `ParsedVocab` | 模型词表（工程侧解析） |
| `vocabRelations` | 词表 → IR 关系 |
| `Vocab { Name, Meaning }` | **展示层**：给关系起可读名 |

**两者不同：模型词表是数据；展示词表是命名。**

---

## 9. 编辑：统一模型

### 9.1 只有一个操作

```lean
inductive EditTarget where
| tensor     : TensorId → EditTarget
| relation   : RelationId → EditTarget
| value      : TensorId → List Nat → EditTarget
| subgraph   : List RelationId → EditTarget

inductive Change where
| setValue    : ℝ → Change
| rename      : String → Change
| setParam    : Nat → Change
| addRelation : Relation → Change
| delRelation : RelationId → Change
| replace     : IR → Change

inductive EditMode where
| relational   -- 关系编辑：传播到所有受影响处
| hard         -- 硬编辑：直接改，不传播

structure Edit where
  target : EditTarget
  change : Change
  mode   : EditMode
```

**词表编辑、结构编辑、数值编辑都是 `Edit` 的不同 `target`。**

### 9.2 关系编辑（`mode := relational`）

```lean
def applyRelational (e : Edit) (S : IR) : IR
```

- 改一条关系；
- **沿依赖边传播到所有受影响的关系**；
- 不区分 `part` 是 `.vocab` 还是 `.arch`。

**传播规则：沿依赖边传。**

| 编辑 | 传播到 |
|:--|:--|
| 改 `tokenOf` | 所有引用该 token 的关系 |
| 改 `lowRank` | 所有依赖该分解的关系 |
| 改 `tie(E,U)` | `E` 与 `U` 同步 |
| 改 `merges` | 所有引用合并结果的 token |

### 9.3 硬编辑（`mode := hard`）

```lean
def applyHard (e : Edit) (S : IR) : IR
```

- 直接改一个数值；
- **不更新关系**；
- 可能破坏 `Consistent`；
- **这是有意的“关闭传播”**。

**硬编辑的合法性：**

| 项 | 处理 |
|:--|:--|
| 硬编辑后 IR 不一致 | 允许，但要标注 |
| `compile` 遇不一致 | 拒绝或给 ε |
| 硬编辑后的 `roundtrip` | 可能不成立 |

### 9.4 一致性

```lean
def Consistent (S : IR) : Prop :=
  ∀ r ∈ S.relations, r.hold
```

| 编辑 | `Consistent` |
|:--|:--|
| 关系编辑 | 保持 |
| 硬编辑 | 可能破坏 |

**硬编辑后需要显式修复，或者接受不一致。**

```lean
def repair (S : IR) : Option IR
```

### 9.5 交换性

```lean
structure Commutes (e₁ e₂ : Edit) (S : IR) where
  commutes : apply e₁ (apply e₂ S) = apply e₂ (apply e₁ S)
```

- 两个编辑可交换；
- 也可以写成语义一致：`semantics (apply e₁ (apply e₂ S)) = semantics (apply e₂ (apply e₁ S))`。

### 9.6 与已有三件套的关系

| 旧三件套 | 统一后 |
|:--|:--|
| `VocabEdit V V'` | `Edit` on `.vocab` relations |
| `WeightTransform M M'` | `Edit` on `.arch` relations 或 values |
| `VocabCompat σ T` | 两个 `Edit` 的 `Commutes` |

**三者只是 `Edit` 的不同实例。**

### 9.7 编辑的语义

| 想要的修改 | 实际要改 | 权重变 | 语义变 |
|:--|:--|:--|:--|
| 改模型行为 | 改架构关系（`relational`） | ✅ | ✅ |
| 改 token 名 | 改词表关系（`relational`） | ❌ | ❌ |
| 直接改数值 | 硬编辑（`hard`） | ✅ | ⚠️ 可能不一致 |
| 加 token | 加关系 + 扩 `E` | ✅ | ✅ |

**“改命名”也是改关系，只是那条关系恰好属于 `.vocab`。**

---

## 10. 渲染

### 10.1 `Rendered`

```lean
structure Rendered where
  vocabPart : String                       -- 词表部分文本
  archPart  : String                       -- 架构部分文本
  sharedPart: String                       -- 共享部分文本
  bindings  : List (Name × RelationId)
  numerals  : List (RelationId × ℝ)
  sound     : semantics (unrender text) = semantics S
```

- 三部分分开：**词表 / 架构 / 共享**；
- `text` 是给人读的；
- `bindings` 是展示层命名；
- `numerals` 是无法命名的数值；
- `sound` 保证 `render`/`unrender` 不引入新语义。

### 10.2 渲染不是本体

- 同一 IR 可有多种文本；
- **IR 唯一，文本不唯一**；
- 文本是“给人看和改的产物”。

### 10.3 可读性

| 标准 | 可判定 |
|:--|:--|
| 每条关系有名字 | ✅ |
| 关系序列合法 | ✅ |
| 无冗余关系 | ⚠️ 需分析 |
| 结构可命名 | ⚠️ 启发式 |

**“可读”不能完全形式化；可证的是“关系合法 + 语义正确”。**

### 10.3bis 三部分显示

| 部分 | 内容 | 示例 |
|:--|:--|:--|
| **词表部分** | `tokenOf` / `merges` / `specialToken` | `token 2 = "的"`、`"的"+"话" → "的话"` |
| **架构部分** | `lowRank` / `block` / `depends` / `transposed` | `E: 低秩`、`U: E 的转置` |
| **共享部分** | `tie(E, U)` | `U 与 E 共享行` |

**分开显示，人一眼能看出“哪些是词表、哪些是架构”。**

### 10.4 逆向的层次

| 层 | 内容 | 状态 |
|:--|:--|:--|
| L1 结构逆向 | `Arch` / 图 | ✅ 可做 |
| L2 程序逆向 | 关系序列 | ✅ 可做 |
| L3 语义逆向 | `Semantics` | ✅ 可做（随 §8） |

**语义逆向是必须的：只有程序层，等于只证“读回同一个程序”，不证“这个程序是那个模型”。**

---

## 11. 与已有工作的关系

| 已有 | 关系 |
|:--|:--|
| `Ladder` | `l2l3` 的输入可以是 IR；`satW` 由契约合成 |
| CIC | IR 可以由 `Term` 解析；CIC 是符号载体，IR 是结构表示 |
| `VocabEdit` / `WeightTransform` / `VocabCompat` | 修改三件套 |
| `PARAMETERIZATION-AUDIT` | 第 1（`Weights` 索引）、第 5（`Obligation` 内嵌）已做 |
| `Plugins` | 原语由插件提供；契约是 `Obligation` |
| 几何 | 待归档；IR 是它的替代 |

---

## 12. 与 T0–T8 的关系

| 目标 | 关系 |
|:--|:--|
| T0 构造 | `compile : IR → Weights` |
| T1 编译保语义 | `compile_sound` |
| T2 罚 | 契约可以是罚 |
| T3 提取 | `extract : Weights → IR` |
| T4 修复 | IR 不满足契约时修复 |
| T5–T8 | IR 可以带 effect |

---

## 13. 不实现的高级部分

| # | 高级部分 | 原因 |
|--:|:--|:--|
| 1 | LLM 前端（写规格） | 用户/工程 |
| 2 | 语言实现（parser / elaborator） | 已立项，工程侧 |
| 3 | 大规模验证（671B） | 工程 |
| 4 | 训练/搜索 | 外部框架 |
| 5 | 格式 I/O | 工程侧 |
| 6 | C 实现 | 不写 |
| 7 | 自回归生成 | 高级部分 |
| 8 | MoE 路由执行 | 高级部分 |

**本仓库只提供：IR、`compile`、`extract`、往返定理、语义、契约、渲染。**

---

## 14. 最小验证

| 步 | 内容 | 验收 |
|--:|:--|:--|
| 1 | `Tensor` / `Relation` / `IR` / `PartKind` | 类型落地 |
| 2 | 三种架构关系：`equal` / `zero` / `depends` | 判据 |
| 3 | **三种词表关系：`tokenOf` / `merges` / `specialToken`** | 判据 |
| 4 | `extract` 一个最简单权重（含 `E` + 词表） | 能提取 |
| 5 | `extract_unique`（六种关系下） | 唯一性 |
| 6 | `compile` | 能构造 |
| 7 | `roundtrip` | 往返成立 |
| 8 | `render` / `unrender`（三部分） | `sound` 成立 |

**不做**：十类关系全做、MoE、自回归、大规模、词表文件解析。

---

## 15. 开放问题

| # | 问题 | 性质 |
|--:|:--|:--|
| 1 | 关系种类是否完整 | 需缺失分析 |
| 2 | “最细块”定义 | 需研究 |
| 3 | “最大群”定义 | 需研究 |
| 4 | 聚合规则完备性 | 需研究 |
| 5 | `Semantics` 具体字段 | 需设计 |
| 6 | `Rendered` 格式 | 需设计 |
| 7 | 与 CIC 的接口 | 需设计 |
| 8 | 大规模验证边界 | 需评估 |
| 9 | **词表抽象是否覆盖所有厂商** | 需厂商调研 |
| 10 | **`merges` 是否足以表达 WordPiece / Unigram** | 需验证 |
| 11 | **特殊 token 的 `part` 归属** | 需设计 |

---

## 16. 一句话

**IR 是权重的结构语义表示规范形：正逆统一，`extract` 唯一，`roundtrip` 统一。**
**它不是新载体，不是新语言；载体仍是 CIC，IR 是权重的结构描述。**
**唯一性来自关系集（相等/零/秩/最细块/最大群），不来自原语互斥，也不需要投影。**
**语义是结构自带的九项；模型词表（`ParsedVocab`）直接读入为关系；`part` 只用于渲染分组。**
**编辑统一为一个 `Edit`：`relational` 传播，`hard` 不传播；词表编辑与结构编辑是同一个操作。**
**词表格式解析是工程侧的事情，LATTICE 只消费 `ParsedVocab`。**
