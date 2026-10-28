# 目录设计思想（DIRECTORY-DESIGN）

> **状态**：Lean 侧目录设计 + C 接口规格，不是完成声明。
> **范围**：目录、`Primitive` 契约、组合方式、迁移流程、C 接口/前置。
> **C 实现最后**：C ABI、布局、序列化、conformance 的接口与前置现在定义；C 代码最后写。
> **核心原则**：库只提供基础 `Primitive`，不打包任何能力；组合是用户的事。

---

## 0. 一句话

**顶层按基础调用分组，不按证明层、不按固定流程；每个 `Primitive` 只做一件事，互不 import；共享类型与链定律收进 `Kernel`；任意组合由 `Compose` 的组合子完成；用户自己决定怎么用。**

---

## 1. 当前目录

```
Lattice/
  Core/          -- 语言/语义/修复/权重
  Lift/          -- 表示/编译/量化/代码生成/tokenizer
  Geo/           -- 几何约束、损失、修复、检查、实例
  Lib/           -- 数学库（优化/学习理论/集中不等式/架构…）
  Semantics/     -- 语义域/词表编辑/标注/合并
  Audit/         -- 组合代数/债务/否证
  Usage/         -- 示例
  Reference/     -- 冻结参考区
```

### 1.1 当前目录的问题

| 目录 | 问题 |
|:--|:--|
| **Geo** | 约束定义、损失、下降、检查、修复、实例混在一起；是最大的杂物间 |
| **Lift** | 表示、编译、量化、codegen、tokenizer、示例混在一起；是第二个杂物间 |
| **Semantics** | 只有少量模块，但它是语义核心；词表编辑与语义编辑没有在目录上分开 |
| **Core** | 小但混合了网络语义、修复、逻辑 |
| **Lib** | 数学库，本身不是杂物间；但 `Lib/Chain` 等模块方向混杂 |
| **Audit** | 组合代数、债务、否证混在一起 |
| **Usage** | 示例与产品边界不清 |
| **没有 Primitive 面** | 只有 `Lattice.lean` 全量 import；用户看不到“基础调用” |

**结论**：不是把整个仓库推倒重来，而是**以当前目录为基础，先拆 `Geo`/`Lift`，再把基础调用沉淀到 `Primitives/`，把语义核心分成 `Kernel/Semantics` + `Primitives/Vocab` + `Primitives/Semantics`。**

---

## 2. 设计原则

### 2.1 只提供基础 `Primitive`，不打包能力

- 不提供 `Import`、`Construct`、`PostTrain`、`Merge`、`QuantizeModel`、`EvaluateModel` 这类入口。
- 只提供最小可调用操作：
  - `weightsCheck`、`bindVocab`、`programAssemble`
  - `tokenMap`、`applyTokenMap`、`embeddingPermute`
  - `applyDelta`、`semanticCheck`、`frameCheck`、`undo`
  - `lossTask`、`grad`、`sgdStep`
  - `constraintUnion`、`conflictDetect`、`conflictResolve`
  - `lowerAffine`、`checkConstraint`
- 一个 `Primitive` 只做一件事；如果内部串了两步，就拆。

### 2.2 组合是用户的事

库只提供通用组合子：

```lean
compose   -- 串联，需要 post → pre 的兼容性证明
parallel  -- 并行
choice    -- 二选一
optional  -- 条件跳过
iterate   -- 循环，需要 measure
```

不提供：

- `importModel`
- `trainStep` / `trainLoop`
- `mergeExperts`
- `quantizeModel`
- `verifyModel`
- `semanticEdit`

用户自己组合。

### 2.3 语义是核心，词表编辑与语义编辑分开

| 编辑 | 改什么 | 纯权重变换？ |
|:--|:--|:--|
| 词表-句法编辑 | token ID/集合、embedding 行、输出头列 | 有 `T(σ)` |
| 词表-语义编辑 | `denote : Token → Meaning` | 没有 |
| 模型-行为编辑 | 权重/程序/约束 | 通过 Train/Repair |

- `Primitives/Vocab`：句法编辑；置换/未用增删精确，merge/split 有损。
- `Primitives/Semantics`：语义编辑；`applyDelta` 只改记录，实现由用户组合 Train/Repair。

### 2.4 一条依赖方向

```
Lib（数学）
  ↑
Kernel（类型/定律）
  ↑
Runtime（Lean 操作语义）
  ↑
Domains（领域实例）
  ↑
Primitives（基础调用）
  ↑
Compose（组合子）
  ↑
Usage（用户示例）
```

`Evidence` 是旁路，产品不得 import。

### 2.5 共享类型集中在 `Kernel`

`Model`、`Profile`、`Program`、`Weights`、`Spec`、`Vocab`、`ConstraintSet`、`Param`、`Loss`、`Grad`、`Annotation`、`Delta`、`EditRecord`、`Violation`、`Operator`、`Certificate`、`QuantParams`、`QuantizedWeights`、`Metrics`、`Data`、`Batch`、`TokenMap`、`MergeRecord` 全部在 `Kernel/Types.lean`。

### 2.6 Primitive 不互相 import

- `Primitives/Train/Grad.lean` 不 import `Primitives/Train/SGDStep.lean`；
- `Primitives/Semantics/ApplyDelta.lean` 不 import `Primitives/Semantics/SemanticCheck.lean`；
- 只 import `Kernel`/`Runtime`/`Domains`。

组合只在 `Compose` 与用户代码里。

### 2.7 强度与覆盖是契约的一部分

每个 `Primitive` 带：

```
strength: exact | approx(ε) | conditional | existence | negative
coverage: all | 12/12 | n=2 | single-point
```

组合时：强度取最小，覆盖取交集。不允许把 `approx` 静默升级成 `exact`。

### 2.8 迁移不改声明名，旧路径保留别名

- `git mv` 只改模块路径，不改 `namespace`；
- 旧路径留 `import` 别名一个周期；
- `PROOF-DEBT` 用 `PATH_MAP` 重生成，条目数不变。

---

## 3. 目标目录

```
Lattice/
  Kernel/                       -- 共享类型 + 链的定律
    Types.lean
    Semantics/
      SemanticDomain.lean
      Vocab.lean
      Geometry.lean
      Inherits.lean
      Delta.lean
    Constraints/
    Representations/
    Repair/
    Algebra/
    Obligations.lean
  Runtime/                      -- Lean 操作语义，不是 C
    Program.lean
    Eval.lean
    Codegen.lean
    Quantization.lean
    Float.lean
  Domains/                      -- 具体领域实例
    Geometry/
    Linear/
    Transformer/
  Primitives/                   -- 所有基础调用；分组只是组织，不是打包能力
    Model/
    Vocab/                      -- 词表-句法编辑
    Semantics/                  -- 语义编辑
    Extract/
    Align/
    Merge/
    Compile/
    Train/
    Repair/
    Verify/
    Quantize/
    Evaluate/
  Compose/                      -- 只有组合子，没有流程
    Primitive.lean
    Combinators.lean
    Laws.lean
    Matrix.lean
    Registry.lean
  CInterface/                   -- Lean 侧 C 契约（现在定义）
    ABI.lean                    -- 函数签名/错误码/所有权
    Layout.lean                 -- Model/Profile/Program 内存布局
    Serialization.lean          -- token/weight/profile 字节格式
    Conformance.lean            -- Lean #eval 向量与 C 对照格式
  C/                            -- C 实现（最后；现在不建）
  Lib/                          -- 数学库，保持独立
  Evidence/                     -- Audit / PROOF-DEBT / census / negative
    Debt/
    Census/
    Negative/
    Audits/
  Usage/                        -- 用户组合示例，不是库提供的流程
  Compat/
    Deprecated/
    Reference/
  Lattice.lean                  -- 只 import Kernel + Primitives + Compose
  Lattice/All.lean              -- 内部全量聚合
```

**没有** `Import/`、`Construct/`、`PostTrain/`、`Edit/` 这种打包目录。
`Primitives/Semantics` 与 `Primitives/Vocab` 是分组，不是“能力包”。

---

## 4. `Primitive` 契约

```lean
structure Primitive where
  Input  : Type
  Output : Type
  pre    : Input → Prop
  post   : Input → Output → Prop
  run    : Input → Option Output
  sound  : ∀ x, pre x → ∃ y, run x = some y ∧ post x y
  strength : Strength
  coverage : Coverage
  frame    : Input → Output → Prop
```

### 4.1 每个 primitive 的目录模板

```
Primitives/<Group>/<Name>.lean
```

一个文件放一个 `Primitive`（或一组紧密相关的纯函数）；必须包含：

1. `Input/Output`；
2. `pre/post`；
3. `run`；
4. `sound`；
5. `strength/coverage`；
6. `INDEX.md` 条目。

### 4.2 示例：`applyTokenMap`

```lean
namespace Lattice.Primitives.Vocab

def Input  := Model × TokenMap
def Output := Model

def pre (x : Input) : Prop :=
  x.2.wellFormed ∧ x.2.source = x.1.vocab

def post (x : Input) (y : Output) : Prop :=
  (x.2.kind = .permute → behavior y (map x.2 tokens) = behavior x.1 tokens)
  ∧ (x.2.kind = .merge ∨ x.2.kind = .split →
      vocabError y x.2 ≤ x.2.ε)

def run (x : Input) : Option Output := ...

theorem sound ... := ...

end Lattice.Primitives.Vocab
```

### 4.3 示例：`applyDelta`

```lean
def Input  := Model × SemanticDelta
def Output := Model

def post (x : Input) (y : Output) : Prop :=
  y.record = x.1.record ++ [x.2]
  ∧ frame x.1 y x.2
  -- 不保证 behavior y 实现 x.2.meaning
```

`applyDelta` 只改记录/结构；语义实现由用户组合 Train/Repair + `semanticCheck`。

---

## 5. Primitive 分组

> 分组是组织方式，不是打包能力；每个 primitive 独立调用、独立证明。

### 5.1 Model

`weightsCheck`、`weightsShape`、`bindVocab`、`unbindVocab`、`modelCheck`、`programAssemble`、`modelToProgram`、`modelParams`、`paramToModel`、`specCheck`、`synthesize`。

### 5.2 Vocab（词表-句法编辑）

`vocabCheck`、`tokenMap`、`applyTokenMap`、`embeddingPermute`、`headPermute`、`embeddingAdd`、`embeddingDelete`、`embeddingMerge`、`embeddingSplit`、`headMerge`、`headSplit`、`vocabCompat`、`vocabError`。

### 5.3 Semantics（语义编辑）

`label`、`inheritsCheck`、`denoteCheck`、`annotate`、`applyDelta`、`semanticCheck`、`frameCheck`、`undo`、`meaningUnion`、`semanticDiff`、`conflictDetect`、`conflictResolve`。

### 5.4 Extract

`extractStructural`、`extractBehavioral`、`profileCheck`。

### 5.5 Align

`vocabMap`、`applyVocabMap`、`embeddingPermute`、`widthProject`、`layerPermute`、`alignCheck`。

### 5.6 Merge

`constraintUnion`、`conflictDetect`、`conflictResolve`、`embeddingMerge`、`headMerge`、`weightCombine`、`applyMergeRecord`、`mergeCheck`。

### 5.7 Compile

`lowerAffine`、`lowerGeneral`、`programCheck`、`compileValidate`。

### 5.8 Train

`lossTask`、`lossConstraint`、`lossTotal`、`grad`、`gradCheck`、`sgdStep`、`momentumStep`、`adamStep`、`schedule`、`constraintProject`、`batch`、`sample`。

### 5.9 Repair

`violationDetect`、`operatorSelect`、`repairApply`、`repairCheck`。

### 5.10 Verify

`checkConstraint`、`sampleBound`、`certificateBuild`、`certificateCheck`。

### 5.11 Quantize

`calibrate`、`quantizeWeights`、`quantizeActivations`、`dequantizeWeights`、`quantError`。

### 5.12 Evaluate

`metricConstraint`、`metricTask`、`metricEdit`、`metricAggregate`。

---

## 6. `Compose`：唯一的组合机制

```lean
def compose (f g : Primitive)
    (h : ∀ x y, f.post x y → g.pre y) : Primitive

def parallel (f g : Primitive) : Primitive
def choice   (f g : Primitive) : Primitive
def optional (p : Input → Bool) (f : Primitive) : Primitive
def iterate  (measure : Input → ℕ) (f : Primitive) : Primitive
```

- `compose` 必须提供 `post → pre` 的兼容性证明；
- `choice` 用于 `bindVocab`/`synthesize` 等替代入口；
- `iterate` 用于训练/修复循环，必须带 measure；
- 强度 = min；覆盖 = 交集；失败用 `Option` 传播。

**没有 `Flows/`、`Workflow/`、`Pipeline/`。**

---

## 7. 如何保证所有基础都能组合

1. 所有 `Input/Output` 都是 `Kernel` 类型；
2. `Primitives/**` 不 import 另一个 `Primitives/**`；
3. `Compose/Registry` 列出所有已注册 primitive；
4. `Compose/Matrix` 对每个合法 pair 写 `example`，不兼容 pair 编译失败；
5. 缺边用显式适配器（`programAssemble`、`dequantizeWeights`、`paramToModel`）；
6. 守卫 `gov/check_primitive_independence.py`；
7. 每个 primitive 至少有独立示例或一个组合示例。

---

## 8. 语义核心在目录中的位置

- `Kernel/Semantics`：`SemanticDomain`、`Vocab`、`Geometry`、`Inherits`、`SemanticDelta` 的定义与定律。
- `Primitives/Vocab`：词表-句法编辑；置换/未用增删精确，merge/split 有损。
- `Primitives/Semantics`：语义编辑；`applyDelta` 只改记录，`semanticCheck`/`frameCheck`/`undo` 分开。

**不存在 `Lattice/Semantics` 打包能力目录。** `Semantics` 只是 `Kernel/Semantics` + `Primitives/{Vocab,Semantics}`。

细节见 `SEMANTICS-MAINLINE.md`。

### 8.1 CInterface（现在）与 C 实现（最后）

`CInterface/` 是 **Lean 侧 C 契约**，不是 C 代码：

| 文件 | 内容 |
|:--|:--|
| `ABI.lean` | 每个 `Primitive` 一个 C 函数签名、错误码、所有权 |
| `Layout.lean` | `Model`/`Profile`/`Program`/`Certificate` 的内存布局 |
| `Serialization.lean` | token/weight/profile 的字节格式 |
| `Conformance.lean` | Lean `#eval` 向量与 C 对照格式 |

**C 接口原则**：

- 一个 `Primitive` 一个 C 函数；没有 `importModel`/`trainLoop` 打包函数；
- C 侧组合由用户写；
- 失败用 status/`Option` 传播；
- 每个函数返回输出 + certificate（如适用）；
- S13 的 Lean 侧 Float 模型/误差界是 C 的 `double` 路径前置；未做前 C 是信任边界。

**C 实现最后**：在 `Primitive`/`Sound`/`Compose` 稳定后再写 `C/`；当前只定义接口与前置，不写 C 代码。

---

## 9. 依赖与门禁

```
core 0
lift 2           （slots 1 保留在 core 与 lift 之间）
lib 3
geo 4
audit 5
compose 6
top 99
```

### ⚠ 第 228 轮修订：`lib` **不放在 0**，**保持今天的 rank 3**

原表把 `lib` 放在 **0**，理由是「`Lib` 是数学库，保持独立」。**这条与本树冲突**：
实测 **244 个 `Lib` 文件 import `Lift`，16 个 import `Core`**（`grep '^import Lattice\.'`）。
按原表（`lib 0` < `lift 2`）这 260 个 import 全部变成向上依赖。

**裁决（第 228 轮）：`Lib` 保持 rank 3 —— 沿用今天的 `core < lift < lib`。**

**理由不是「搬家太贵」，而是职责**：`Lib` 要负责**两类**内容——

1. **无法迁移的**：依赖 `Core`/`Lift` 多个层、又无法干净切分的（`Lib/Chain`、`Lib/Editing`、
   `Lib/Linear` 等，即上面那 244 + 16 个文件）；
2. **后续新增的同类**：将来新写的、需要同时看见 `Kernel`/`Runtime` 的内容。

把 `Lib` 钉在**最底层**会逼这些内容要么被硬塞进某一层、要么被拆碎——**那是有损的**，
而且「新东西该放哪」会没有答案。**保留 rank 3，这个问题才有归宿。**

**为什么不是更上面的 9**：本节第一版把 `lib` 移到 **9**，结果 I4 立刻报 **14 处**违规——
`Geo` 依赖 `Lib`（`Geo/Derivative`、`Geo/Unified`、`Geo/QualityBridge`、`Geo/RepairPerp`），
把 `lib` 抬到 `geo` 之上就把那些依赖变成向上依赖。
**而实测 `Lib` 不 import 任何 `Geo`**，所以 `lib 3`（低于 `geo`）**两边都不冲突**。

**代价（必须记账）**：`Lib` 可以 import `Core` 与 `Lift`，所以 **`Lib` 里的定理不能一律当作
「独立于架构的数学」**——其中相当一部分依赖 `Lift` 的定义。强度审计里 `Lib` 的定理按它
**实际 import 的层**计，不按「数学库」计。

- `Primitives` 只能 import `Kernel`/`Runtime`/`Domains`；
- `Primitives` 之间零 import；
- `Compose` 可以 import `Primitives`；
- `Usage` 可以 import `Compose`；
- `Evidence` 可以 import 全部，但产品不得 import `Evidence`；
- `Compat` 是别名/冻结区，产品不得依赖。

新增守卫：

- `gov/check_primitive_independence.py`：检查 primitive 之间无 import；
- `gate.py` 的 `LAYER_OF` 增加 `Lattice/Primitives`、`Lattice/Compose`；
- `check_registry`/`check_doc_consistency` 更新路径。

---

## 10. 当前目录 → 目标目录

| 当前 | 目标 |
|:--|:--|
| `Core/Net`、`Core/Activation`、`Core/Weight*` | `Kernel/Types` + `Runtime` |
| `Core/Repair*` | `Kernel/Repair` |
| `Lift/WeightSymbolRepresentation`、`Rectangular*`、`WeightLadder*` | `Kernel/Representations` + `Primitives/Model` |
| `Lift/ProgramAST`、`StackCodegen` | `Runtime/Program`、`Runtime/Codegen` |
| `Lift/LayerQuantization*`、`Saturation*`、`QuantErrorPropagation` | `Runtime/Quantization` + `Primitives/Quantize` |
| `Lift/Approx*`、`ExtractionStrength` | `Kernel/Representations`（approx） |
| `Geo/Constraint`、`Expr`、`Loss`、`PenaltyLoss`、`ConstraintSet` | `Kernel/Constraints` |
| `Geo/GeoLadder`、`WeightSideLadder`、`LadderInstance` | `Domains/Geometry` + `Primitives/Model` |
| `Geo/Repair*`、`Loop*`、`Reinjection*` | `Primitives/Repair` + `Domains/Geometry/Repairs` |
| `Geo/Executable*Check`、`GeoSampledBound` | `Primitives/Verify` |
| `Geo/NetLoss`、`ConstraintDescent`、`WeightDescent` | `Primitives/Train` |
| `Semantics/Stage1` | `Kernel/Semantics` |
| `Semantics/VocabEdit` | `Primitives/Vocab` |
| `Semantics/Annotations` | `Primitives/Semantics` |
| `Semantics/Merge` | `Primitives/Merge` + `Primitives/Semantics/Conflict*` |
| `Lift/Verification*`、`VerifierRate` | `Primitives/Verify` |
| `Lib/*` | 保持 `Lib`（数学） |
| `Audit/*` | `Evidence` |
| `Usage/*` | `Usage` |
| `Slots.lean` | `Kernel/Obligations` |
| `Reference/*` | `Compat/Reference` |

---

## 11. 执行流程

| 阶段 | 时间 | 工作 | 出口 |
|:--|--:|:--|:--|
| **P0 骨架** | 3–5 天 | `Kernel/Types`、`Compose/Primitive`、少量 primitive 骨架 | 类型/契约编译；不注册无 `sound` 的 primitive |
| **P1 证明与注册** | 1–2 周 | 逐 primitive `Sound`；`Compose/Laws`；`Matrix`；`Registry` | 已注册 primitive 全有 `sound`；合法 pair 可组合 |
| **P2 拆 Lift/Geo** | 2–4 周 | `Kernel/Runtime/Domains`；旧路径别名；`PATH_MAP` | 构建通过；`PROOF-DEBT` 条目数不变 |
| **P3 Core/Audit** | 1–2 周 | `Core→Kernel`、`Audit→Evidence`、gate rank、独立性守卫 | 无 primitive 互相 import |
| **P4 清理** | 1 周 | `PRIMITIVE-INDEX`、删别名、文档 | 61 检查绿；构建时间 +≤20% |
| **P5 C 接口规格** | 1 周 | `CInterface/ABI`、`Layout`、`Serialization`、`Conformance` | 每个 primitive 有 C 签名/布局/字节格式/测试向量；无 C 代码 |
| **P6 C 实现** | 最后，另行排期 | `C/` 实现 | 与 `CInterface` 一致；不在 Lean 阶段 |

**Lean 阶段总工作量**：约 6–10 周（1–2 人）；C 接口规格 +1 周；C 实现最后。

### 11.1 迁移机制

- `git mv` 只改路径，不改 `namespace`；
- 旧路径留别名 `import`；
- `gen_proof_debt.py` 加 `PATH_MAP`，生成失败即停；
- 一次只搬一个 primitive 组，搬完即 `lake build`；
- 每个阶段独立分支/合并点，可单独回滚。

### 11.2 P0 细节

1. `Kernel/Types.lean`：先 `abbrev`/`structure` 指向现有类型。
2. `Compose/Primitive.lean` + `Combinators.lean`。
3. `Primitives/` 只建少量骨架（Model/Extract/Verify）。
4. `Lattice.lean` 暴露 primitives；不建打包能力。
5. 不写 `Sound` 的 primitive 不注册；不用 `True`/`sorry`。

### 11.3 P1 细节

1. 每个 primitive 补 `Sound.lean`；缺证明的保留 `Contract`+`Impl`，不注册。
2. `Compose/Laws.lean`：`compose_sound`、`assoc`、`identity`、`parallel`、`choice`、`optional`、`iterate`。
3. `Compose/Matrix.lean`：所有已注册 primitive 对。
4. `Usage` 写 3 个用户组合示例。

### 11.4 P2 细节

1. `Kernel/Types` → `Kernel/Semantics` → `Kernel/Constraints`/`Representations`。
2. `Runtime/Program`/`Eval`/`Codegen`/`Quantization`/`Float`。
3. `Domains/Geometry`/`Linear`/`Transformer`。
4. `Primitives` 的 `Impl` 改为直接调用新模块。
5. 旧路径别名；`PROOF-DEBT` 路径映射。

### 11.5 P3 细节

1. `Core` → `Kernel`。
2. `Audit` → `Evidence`。
3. `Slots.lean` → `Kernel/Obligations`（或别名）。
4. `gate.py` 更新 rank。
5. 新增 `check_primitive_independence.py`。

### 11.6 P4 细节

1. 生成 `PRIMITIVE-INDEX.md`/`THEOREM-INDEX.md`。
2. 删除旧别名（或 `@[deprecated]` 保留一版）。
3. 更新 `README`/`PROOF-DEBT`/`MACRO-STATUS`。
4. 全量 `lake build` + 61 检查。

### 11.7 P5 细节：C 接口规格

1. `CInterface/ABI.lean`：每个 `Primitive` 一个 C 函数签名、错误码、所有权。
2. `CInterface/Layout.lean`：`Model`/`Profile`/`Program`/`Certificate` 的内存布局。
3. `CInterface/Serialization.lean`：token/weight/profile 字节格式。
4. `CInterface/Conformance.lean`：Lean `#eval` 向量与 C 对照格式。
5. S13 的 Lean 侧 Float 模型/误差界；C 的 `double` 路径以此标注信任边界。

### 11.8 P6 细节：C 实现（最后）

- 在 `Primitive`/`Sound`/`Compose`/`CInterface` 稳定后开始；
- 一个 primitive 一个 C 函数；不提供 `importModel`/`trainLoop` 打包函数；
- C 侧组合由用户写；
- 与 `CInterface`/conformance 对齐后，才能声称 C 实现符合 Lean 规格。

---

## 12. 验收标准

1. 顶层 = `Kernel / Runtime / Domains / Primitives / Compose / CInterface / Lib / Evidence / Usage / Compat`。
2. `Primitives/**` 每个文件是基础调用；没有 `Import`/`PostTrain`/`Merge` 打包能力。
3. 每个 primitive 有 `sound`；无 `True`/`sorry`/`:= h`。
4. **Primitive 之间零 import**（守卫）。
5. `Compose/Registry` 列出所有 primitive；`Matrix` 覆盖合法 pair。
6. `compose_sound`/`assoc`/`identity`/`parallel`/`choice`/`iterate` 有定理。
7. 强度/覆盖组合规则有定理；不允许静默升级。
8. `lake build` 通过，61 检查绿；`PROOF-DEBT` 条目数不变。
9. `Usage` 至少三种用户自组合示例；库不提供固定流程。
10. `CInterface/` 的 ABI/Layout/Serialization/Conformance 规格存在；**C 实现最后**，不要求现在有 C 代码。

---

## 13. 非目标

- 不提供打包能力；
- 不提供固定使用链；
- 不搬 `Lib`；
- 不在迁移中改声明名；
- **C 实现最后**；C 接口/前置现在定义；
- 不声称本设计等于证明完成（S9/S10/S20、PROOF-DEBT 是并行任务）。

---

## 14. C 接口（现在）与 C 实现（最后）

**现在定义**：

- `CInterface/ABI.lean`：每个 primitive 的 C 函数签名、错误码、所有权；
- `CInterface/Layout.lean`：`Model`/`Profile`/`Program`/`Certificate` 内存布局；
- `CInterface/Serialization.lean`：token/weight/profile 字节格式；
- `CInterface/Conformance.lean`：Lean `#eval` 向量与 C 对照格式；
- S13 的 Lean 侧 Float 模型/误差界（C `double` 的信任边界依据）。

**最后写**：

- `C/` 实现：ABI、序列化、conformance、runtime、trainer、性能/部署；
- 在 `Primitive`/`Sound`/`Compose`/`CInterface` 稳定后开始；
- 一个 primitive 一个 C 函数；不提供打包入口；C 侧组合由用户写。

**未实现前**：C 是信任边界，不能声称“证明保证 C 正确”。

---

## 15. 一句话总结

**顶层只放基础调用；`Kernel` 放共享类型与链定律；`Compose` 只给组合子；`CInterface` 定义 C 契约与前置；没有打包能力、没有固定流程；C 实现最后；每个 primitive 独立、可证明、可组合；语义编辑拆成 `Primitives/Vocab` 与 `Primitives/Semantics`。**
