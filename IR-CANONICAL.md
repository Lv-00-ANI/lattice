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
| `HyperStructure` | 同一对象的不同称呼；IR 是它在文档中的正式名 |
| `Ladder` | `Ladder` 是接口形状；IR 是 `l2l3` 的输入 |
| `ModelArtifact` | 产物；IR 是产物的结构描述 |
| `Program`（旧设计） | 被 IR 取代；程序是 IR 的一种渲染 |

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

---

## 2. 核心对象

### 2.1 `Tensor`

```lean
structure Tensor where
  id    : TensorId
  shape : List Nat
  data  : Fin (shape.product) → ℝ
```

- `shape` 是多轴；
- 张量集由权重唯一决定。

### 2.2 `Relation`（高维超边）

```lean
structure Relation where
  kind : RelKind
  args : List (TensorId × List Nat)   -- 每个参数带多轴索引
  hold : Holds kind args
```

- **不投影到二元边**；
- 轴是参数的一部分；
- 一条关系可有 n 个参数。

### 2.3 `IR`

```lean
structure IR where
  tensors   : List Tensor
  relations : List Relation
```

- 张量集 + 关系集；
- 由权重唯一决定（见 §4）。

### 2.4 关系种类（初始集）

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

**初始集，可随插件扩展。**

---

## 3. 正向：`compile`

```lean
def compile (S : IR) : Weights

theorem compile_sound (S : IR) (hS : WellFormed S) :
  Satisfies (compile S) (semantics S)
```

- 从张量集与关系集构造权重；
- 关系决定张量如何组合；
- 良构性要求关系一致。

### 3.1 契约

```lean
structure Contract where
  sym    : Sym → Prop
  weight : Weights → Prop
  sound  : ∀ s, sym s → weight (build s)

structure Primitive where
  key      : ServiceKey
  relKind  : RelKind
  build    : Params → Weights
  contract : Contract
```

- 原语是关系种类的命名；
- 契约保证“构造的权重满足符号侧要求”；
- 原语集 = registry 里所有插件的原语并集（随插件扩展）。

---

## 4. 逆向：`extract`

```lean
def extract (w : Weights) : IR

theorem extract_sound (w : Weights) :
  Satisfies w (semantics (extract w))
```

### 4.1 唯一性

```lean
theorem extract_unique (w : Weights) :
  ∃! S, IsIR S w
```

`IsIR` 要求：

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

### 4.2 为什么不投影

| 投影 | 问题 |
|:--|:--|
| 二元边 | 丢轴 |
| 线性列表 | 丢无序性 |
| 规范形（外部规则） | 需额外规则，非内在 |

**直接拿高维结构，唯一性落在关系集上。**

---

## 5. 往返

```lean
theorem roundtrip (w : Weights) :
  compile (extract w) = w

theorem roundtrip_semantic (w : Weights) :
  semantics (compile (extract w)) = semantics w
```

**`extract` 唯一且 `compile` 确定 ⇒ 往返成立。**

### 5.1 与已证定理不冲突

| 已证 | 是否冲突 |
|:--|:--|
| `semantic_not_injective` | ❌ 它约束语义层；这里可逆的是结构层 |
| `no_extractor_preserves_both` | ❌ 它约束参数层+语义层同时；这里只承诺结构层 |
| `reversibility_boundary` | ❌ 它约束参数层；结构层可逆 |

---

## 6. 语义

### 6.1 语义是结构自带的

```lean
def semantics (S : IR) : Semantics
```

`Semantics` 包含九项：

| # | 内容 |
|--:|:--|
| 1 | 形状 |
| 2 | 参数 |
| 3 | 关系 |
| 4 | 类型 |
| 5 | 组合方式 |
| 6 | 约束 |
| 7 | 不变量 |
| 8 | 来源 |
| 9 | 行为 |

**九项合起来才是语义；任一单项只是投影。**

### 6.2 词表是命名的词汇

```lean
structure Vocab where
  Name    : Type
  Meaning : Type
  denote  : Name → Meaning
```

- 只是命名；
- 不增加语义；
- 换词表，语义不变。

### 6.3 修改

| 想要的修改 | 实际要改 |
|:--|:--|
| 改模型行为 | **改 IR（结构）** |
| 改命名 | **改词表** |
| 两者 | 都改，并证 `commutes` |

```lean
structure VocabCompat (σ : VocabEdit) (τ : IREdit) where
  commutes : semantics (τ.apply S) = f (semantics S)
```

---

## 7. 渲染

```lean
structure Rendered where
  text     : String
  bindings : List (Name × RelationId)
  numerals : List (RelationId × ℝ)
  sound    : semantics (unrender text) = semantics S
```

- 同一 IR 可有多种文本；
- **IR 唯一，文本不唯一**；
- 文本是给人看和改的产物。

---

## 8. 不实现的高级部分

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

## 9. 与已有工作的关系

| 已有 | 关系 |
|:--|:--|
| `Ladder` | `l2l3` 的输入可以是 IR |
| CIC | IR 可以由 `Term` 解析；CIC 是符号载体，IR 是结构表示 |
| `VocabEdit` / `WeightTransform` / `VocabCompat` | 修改三件套 |
| `PARAMETERIZATION-AUDIT` | 第 1（`Weights` 索引）、第 5（`Obligation` 内嵌）已做 |
| `Plugins` | 原语由插件提供；契约是 `Obligation` |
| 几何 | 待归档；IR 是它的替代 |

---

## 10. 与 T0–T8 的关系

| 目标 | 关系 |
|:--|:--|
| T0 构造 | `compile : IR → Weights` |
| T1 编译保语义 | `compile_sound` |
| T2 罚 | 契约可以是罚 |
| T3 提取 | `extract : Weights → IR` |
| T4 修复 | IR 不满足契约时修复 |
| T5–T8 | IR 可以带 effect |

---

## 11. 最小验证

| 步 | 内容 | 验收 |
|--:|:--|:--|
| 1 | `Tensor` / `Relation` / `IR` | 类型落地 |
| 2 | 三种关系：`equal` / `zero` / `depends` | 判据 |
| 3 | `extract` 一个最简单权重 | 能提取 |
| 4 | `extract_unique`（三种关系下） | 唯一性 |
| 5 | `compile` | 能构造 |
| 6 | `roundtrip` | 往返成立 |
| 7 | `render` / `unrender` | `sound` 成立 |

**不做**：十类关系全做、MoE、自回归、大规模。

---

## 12. 开放问题

| # | 问题 |
|--:|:--|
| 1 | 关系种类是否完整（需缺失分析） |
| 2 | “最细块”与“最大群”的定义 |
| 3 | 聚合规则 |
| 4 | `Semantics` 的具体字段 |
| 5 | `Rendered` 的格式 |
| 6 | 与 CIC 的接口 |
| 7 | 大规模验证的边界 |

---

## 13. 一句话

**IR 是权重的结构语义表示规范形：正逆统一，`extract` 唯一，`roundtrip` 统一。**
**它不是新载体，不是新语言；载体仍是 CIC，IR 是权重的结构描述。**
**唯一性来自关系集（相等/零/秩/最细块/最大群），不来自原语互斥，也不需要投影。**
