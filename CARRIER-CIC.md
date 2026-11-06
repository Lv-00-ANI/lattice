# CARRIER：从几何到 CIC

> **状态：** 设计决定已采纳（2026-11-05）。实施未开始。
> **范围：** 本文件说明 LATTICE 的**主符号载体**为什么从 `GeoConstraint n` 改为 **CIC term**，
> 以及几何如何作为**一个编码实例**保留下来。
> **不覆盖：** 语言本身的实现（工程侧，已单独立项）、C 代码、格式解析。


> **[待移除] 几何归档通知（2026-11-06）**：
> **`Domains/Geometry` 与 `Domains/Constraints` 已标记待移除，将移入 `Lattice/Reference/Geometry`。**
> **因此本文§3 的 `Encode/Geometry` 映射是**不承诺**的——它的见证结构不可比：**
> **`Holds` 的见证是点配置 `Φ : ℕ → Pt n`，`Typable` 的见证是构造项 `t : Term`，两者之间没有自然的桥。**
> **主线在 `Lattice/Core/CIC/`。**

---

## 0. 一句话

LATTICE 的主符号载体从 `GeoConstraint n` 改为 **CIC term**；
几何**不是被删除**，而是被**编码进 CIC**（`Encode/Geometry`），降为 `Domains/Geometry` 的一个实例。
因此 T0–T8 在 CIC 上重新陈述，几何上的旧定理保留为 **Domain 级证据**。

---

## 1. 为什么换

### 1.1 七个同根症状

2026-11 的三路只读审计（层归属 / 剩余任务 / 证明重组）在 `e0b3c06`…`1c0a787` 上发现的缺陷，
有一大批可以归到同一个根因上。

| # | 症状 | 证据（HEAD 行号） |
|--:|:--|:--|
| 1 | **T0 不可实例化** | `no_specSolver`（`Plugins/Targets/SolverBoundary.lean:78-90`）证明 `SpecSolver n` **为空**；`[rightAngle 0 1 2]` 与退化配置冲突 |
| 2 | **T1 结论不含编译输入** | `compile_sound`（`Semantics/CompileSound.lean:100-107`）结论不出现 `R`；`WeightSideLadder.lean:156` 的 `l2l3 := fun _ => [samePointLayer enc a b]` **丢弃参数** |
| 3 | **T2 的 `g(ε)` 不存在** | `T2Min.lean:55-58` 自认「`ε` 是空洞的，因为结论是精确的」；`violation` 只对 `eqZero` 有定义 |
| 4 | **T3 参数层是字段投影** | `t3_parameter_roundtrip` 就是 `Representation.roundtrip`（`Runtime/Extraction.lean:80`）这个**结构字段**；`t3_compile_injective` 是它的左逆推论 |
| 5 | **T5–T8 需要玩具模型** | `Plugins/Runtime/Spatiotemporal/*` 的载体是 `RState K := K → Option ℕ`；`t8_failure_isolation` 就是 `if failing then none` 的一步 `simp` |
| 6 | **架构载体是孤岛** | `Plugins/Architectures/{Conv,Attention}/Proofs.lean` **只 `import Mathlib`**，与 `Lib/` 零连接；DAG 的 `dagPar`/`dagResid` 都定义为 `p ++ q` |
| 7 | **`Plugins/Targets` 跨四层** | 24 文件，被 `Domains`/`Runtime`/`Semantics` 的 12 个核心模块 import；`Solver.lean:30-34`、`Statements.lean:31-38` |

这七条看起来分散，但都可以用一句话解释：

> **符号模型的「标准形态」被焊死在几何上，而几何的表达力不足以支撑上述定理。**

### 1.2 几何作为载体的四个结构性限制

| 限制 | 说明 | 直接后果 |
|:--|:--|:--|
| **可满足性不可判定** | 12 个构造子（`eqZero`/`leZero`/`ltZero`/`gtZero`/`sqDistEq`/`equalLength`/`collinear`/`perpendicular`/`parallel`/`rightAngle`/`midpoint`/`samePoint`）的组合一般不可满足 | `SpecSolver` 只能为空；T0 只能退到 family 强度 |
| **编译语义缺失** | 几何侧没有「把规格 elaborates 成权重」的自然过程，`l2l3` 只能返回常量层 | T1 结论不含 `R`；「编译」名不副实 |
| **不可逆是结构性的** | 几何函数空间太大，`semantic_not_injective` 成立得**太容易** | T3 的不可逆变成「逃避」而非「刻画」 |
| **与模型结构无关** | 点云/图与 Conv/Attention/Norm 的权重结构没有同构关系 | 五个载体全部自建，无法复用 |

### 1.3 CIC 的对应能力

| 维度 | 几何 `GeoConstraint n` | CIC term |
|:--|:--|:--|
| **规格** | 12 个固定构造子 | 任意 `Prop` / `Type` |
| **构造** | `Pt n` 点配置 | 构造项（term） |
| **可满足** | 不可判定 | 类型检查可判定（`Typable`） |
| **编译** | 损失函数（弱） | elaboration（强） |
| **提取** | 不可逆 | 结构可恢复（到 `NormalForm`） |
| **误差** | 几何 Lipschitz 常数（依赖点云界 `B`） | β 归约步数 / 显式 `ε` |
| **与模型结构** | 无关 | 同构（层/张量都可编码为 term） |

---

## 2. 不换什么

| 保留 | 说明 |
|:--|:--|
| **`Domains/Geometry`** | 413 条定理**不删除、不移动**；降级为「一个 CIC 编码实例」 |
| **`Domains/Constraints`** | 344 条定理保留，同上 |
| **非几何的 8,943 条定理** | 不动 |
| **C 语言实现** | 属于工程侧，已单独立项；本仓库只负责 CIC 语义 |
| **`ProofComplete` 的边界** | 格式/I-O/C/conformance 仍不进判据（见 `ENGINEERING.md`） |

影响面：

| 集合 | 定理数 | 占比 |
|:--|--:|--:|
| 几何相关 | ≈ 757 | 7.8% |
| 非几何 | ≈ 8,943 | 92.2% |

---

## 3. 编码：几何 → CIC

### 3.1 目标

```lean
-- Lattice/Core/CIC/Encode/Geometry.lean
def encodeConstraint {n : ℕ} : GeoConstraint n → Term
```

**单向**。只要求：

```lean
theorem encode_sound {n} (c : GeoConstraint n) (Φ : ℕ → Pt n) :
    Holds c Φ → Typable (encodeConstraint c)
```

### 3.2 12 个构造子的映射（设计草案）

点坐标编码为 `Term`：设 `Pt n = ℕ → Point ℝ n`，每个坐标 `Φ i j : ℝ` 编码为一个 `Term`（常量或自由变量）。

| 构造子 | 几何陈述 | CIC 编码 |
|:--|:--|:--|
| `samePoint a b` | `Φ a = Φ b` | `Eq (pt a) (pt b)` |
| `midpoint a b c` | `2·Φ c = Φ a + Φ b` | `Eq (mul 2 (pt c)) (add (pt a) (pt b))` |
| `eqZero e` | `eval e Φ = 0` | `Eq (evalTerm e) zero` |
| `leZero e` | `eval e Φ ≤ 0` | `Le (evalTerm e) zero` |
| `ltZero e` | `eval e Φ < 0` | `Lt (evalTerm e) zero` |
| `gtZero e` | `0 < eval e Φ` | `Lt zero (evalTerm e)` |
| `sqDistEq a b d` | `sqDist (Φ a) (Φ b) = d` | `Eq (sqDistTerm a b) (const d)` |
| `equalLength a b c d` | `sqDist (Φ a) (Φ b) = sqDist (Φ c) (Φ d)` | `Eq (sqDistTerm a b) (sqDistTerm c d)` |
| `perpendicular a b c d` | `dot (Φ b - Φ a) (Φ d - Φ c) = 0` | `Eq (dotTerm ...) zero` |
| `parallel a b c d` | `cross = 0` | `Eq (crossTerm ...) zero` |
| `collinear a b c` | `cross (Φ b - Φ a) (Φ c - Φ a) = 0` | `Eq (crossTerm ...) zero` |
| `rightAngle a b c` | `dot (Φ a - Φ b) (Φ c - Φ b) = 0` | `Eq (dotTerm ...) zero` |

**注意：** 这张表是设计草案，不是实现。实现时必须逐条对照
`Lattice/Domains/Constraints/Constraint.lean` 的 `Holds` 定义（12 个分支），
不得凭记忆。

### 3.3 为什么只做单向

- **双向**会立刻撞上 `semantic_not_injective`（`Runtime/Extraction.lean:180`）：
  几何值域比 term 值域「细」，不存在保语义的完整反编码；
- 单向 `encode` 足以让几何定理在 CIC 上重放（`Typable` 的充分条件）；
- 反方向（`extract`）由 T3 在 CIC 上单独处理，它对**部分**信息可恢复，
  对全部信息不可恢复——这正是 T3 要刻画的内容。

### 3.4 几何降级后的地位

```text
Lattice/Domains/Geometry/          -- 保留，413 条定理
  ↑ 被编码
Lattice/Core/CIC/Encode/Geometry.lean
  ↑ 使用
Lattice/Core/CIC/                  -- 主载体
```

- 几何的 `Holds` 仍然是 `Prop`，仍在 `Domains` 层；
- 但**靶定理 T0–T8 不再以几何为陈述对象**；
- 几何定理的角色变成：验证 `encode` 的正确性、提供具体实例、作为反例来源。

---

## 4. 新目录

```text
Lattice/Core/CIC/
  Syntax.lean        -- Term / Level / de Bruijn 索引
  Substitution.lean  -- 变量替换
  Reduction.lean     -- β / δ / ι / ζ
  Typing.lean        -- Typable / Context / typing rules
  Normalization.lean -- 强规范化或显式 ε（见 §7.2）
  Encode/Geometry.lean
```

依赖方向：

```text
CIC.Syntax < CIC.Substitution < CIC.Reduction
                     ↑
                CIC.Typing < CIC.Normalization
                     ↑
              CIC.Encode.Geometry  -- 只 import Domains.Constraints
```

`CIC` 位于 `Core` 内，因此**下行可用**：`Runtime` / `Domains` / `Plugins` / `Lib` 均可 import 它。

---

## 5. T0–T8 在 CIC 上的重述

| 目标 | 几何版（现状） | CIC 版（目标） | 为什么不再是弱化 |
|:--|:--|:--|:--|
| **T0** | `construct : ExpressibleSpec n → Pt n`，`SpecSolver` 为空 | `construct : Typable Γ t A → Term`（构造项） | 可满足性 = 可类型性，**可判定**；不再需要「任意 spec 都可解」这个假命题 |
| **T1** | `compile_sound` 结论不含 `R` | `parse : Term → Option IR`；`compile : IR → Weights`；`compile_sound : WellFormed S → Models (compile S) (semantics S)` | 结论**必须**含 `S`；`compile` 作用于结构，不可能丢弃输入 |
| **T2** | `penalty_min_to_violation` 的 `g ≡ 0` | `modulus : WellFormed S → |denote (compile S) - denote S| ≤ size S * ε` | `ε` 来自结构规模，是**显式**的；`ε → 0` 对应 `size S → 1` |
| **T3** | 参数层 `Representation.roundtrip` 字段投影 | `extract : Weights → IR`；`extract_compile : extract (compile S) = S`（单射即逆） | 往返是**定理**不是字段；`extract` 只读回有界的 IR，不需要 fuel 解码任意 term |
| **T4** | 几何修复回路 | `repair : Term → Term`，`Sat (repair t) ∨ progress` | 修复的对象是 term，不是点配置 |
| **T5** | `undoSeq_apply`（`K → Option ℕ`） | effect = elaborator state 变换；`undo_apply` | 有真实载体（elaborator），不是玩具 |
| **T6** | `deactivate_before_unload`（纯图论） | `canActivate` + provider 解析（`Coeffect`） | 有激活门，不只有停用门 |
| **T7** | 两个单键交换 | `run trace s ≃ construct (finalSpec trace)` | 是 `CONFLUENCE.md` 的命题，不是 `Option.bind_assoc` |
| **T8** | `if failing then none` | `Fiber` / `FAILED` / `rollback` / 无证书 | 有 fiber 隔离，不只是短路 |

**注意：** 这张表是**目标陈述**。逐条实现时，每条都要重新对照
`PROOF-OBLIGATIONS.md` 与 `README.md` 的判据，不得把本表当成已完成的证明。

---

## 6. 迁移策略

### 6.1 不动几何

- `Lattice/Domains/Geometry/*` 一个文件都不删；
- `Lattice/Domains/Constraints/*` 一个文件都不删；
- 已有的 757 条定理**不重写**。

### 6.2 新增 CIC 层

- 只新增 `Lattice/Core/CIC/`；
- 不修改 `Plugins/Targets` 的旧文件（双写期）；
- 旧靶定理标注 `[domain-legacy]`。

### 6.3 靶定理双写期

| 阶段 | `ProofComplete` 里放什么 |
|:--|:--|
| 双写期 | 旧几何靶定理（现状） |
| 切换期 | 新 CIC 靶定理与旧定理**都**在合取里（更强，不是更弱） |
| 完成后 | 只放 CIC 靶定理；几何版移入 `Domains/Geometry/Obligations.lean` 作为实例证据 |

### 6.4 几何降级为 Domain 的判定标准

一条几何定理算「Domain 级证据」当且仅当：

1. 它是 `Domains/Geometry/` 或 `Domains/Constraints/` 内的文件；
2. 它**不**出现在 `Plugins.lean` 的 `ProofComplete` 合取里；
3. 它在 `Lattice/Core/CIC/Encode/Geometry.lean` 有对应的 `encode_*` 引理，
   或者被显式标注为「无 CIC 对应」。

---

## 7. 反例与边界

### 7.1 仍然不可逆的部分

- 语义层的不可逆是**结构性事实**（`semantic_not_injective`），换载体不会改变这一点；
- CIC 让「不可逆」变得**可刻画**（`NormalForm` 之外的等价类），而不是消失；
- 因此 T3 的目标不是「变得可逆」，而是「精确说明哪些可逆、哪些不可逆」。

### 7.2 强规范化是否需要

| 用途 | 是否需要强规范化 |
|:--|:--|
| T0（构造） | 不需要；只需 `Typable` |
| T1（编译保语义） | 不需要；只需 `compile_sound` |
| T2（`g(ε)`） | **需要**一个「归约步数」的界，但不一定要强规范化 |
| T3（往返） | 需要一个可判定的 `NormalForm`，可以是弱规范化 |

**结论：** 第一阶段只需要**弱规范化 + 步数界**；强规范化是充分条件，不是必要条件。

### 7.3 语言实现不在本仓库

- CIC 的**语法与类型规则**在本仓库（`Lattice/Core/CIC/`）；
- CIC 的**实现**（parser / elaborator / evaluator）属于工程侧，已单独立项；
- 本仓库的 Lean 证明只依赖语法与规则，**不依赖实现**；
- 因此实现换了，证明不失效。

---

## 8. 与现有文档的关系

| 文档 | 需要的改动 |
|:--|:--|
| `SEMANTICS-MAINLINE.md` | §2.1 语义域加 `Carrier := CIC.Term`；§2.3 三种几何加第四种「CIC 编码」；§5 的 S1–S20 标注 CIC 位置；§7 加 `Lattice/Core/CIC/` |
| `DESIGN.md` | §2 链路图的 L2 改为 CIC term；§5 的 `ModelArtifact` 来源；§11 `ProofComplete` 同步 |
| `MODEL-WEIGHT.md` | §2 的 `Arch`/`Weights` 从 CIC term 编码；§5 `construct` 改 `Typable → Term` |
| `CONSTRUCTIVE-TRAINING.md` | §1 流程改为 `Term --parse--> IR --compile--> Weights`；§2 `ExpressibleSpec` 改为 `WellFormed`；§3 四条定理的 IR 形式 |
| `PROOF-OBLIGATIONS.md` | T0–T8 全部给 CIC 版本；修正 §T5–T8 的六个幽灵名 |
| `GLOSSARY.md` | 新增 CIC / term / `Typable` / `NormalForm` / encode / elaborate；几何标注 Domain |
| `README.md` | 定位段、§1 链路图、§3 决策、§3.9 `ProofComplete`、§7 证明债 |
| `PARADIGM.md` | §1.1「转换即对象」→「CIC term ⇄ 权重」；§2 硬缺口 |
| `SPATIOTEMPORAL.md` | §2 的 `LatticeEffect` 改为 CIC effect；§4 定理名 |
| `CONFLUENCE.md` | §1 `trace`/`construct` 定义在 CIC 上 |
| `ARCHITECTURE-CARRIERS.md` | 五载体改为「CIC term 上的架构编码」 |
| `ENGINEERING.md` | 明确「语言实现属工程」 |
| `ROADMAP.md` | 阶段重排：CIC 先行 |
| `DOCS-MAP.md` | 加入 `CARRIER-CIC.md`、`CARRIER-REPLACEMENT.md` |

---

## 9. 未验证项

1. **`encode` 的可实现性**：§3.2 的 12 条映射是设计草案，未逐条对照 `Holds` 定义；
2. **`encode_sound` 的难度**：几何的 `Holds` 是 `Prop`，CIC 的 `Typable` 也是 `Prop`，
   但两者的「证明对象」不同（前者的见证是点配置，后者的见证是 term），
   这条蕴含关系可能比预期难；
3. **弱规范化是否够用**：T2 需要「归约步数」，弱规范化是否给出可用的界，未验证；
4. **CIC 的 `Term` 定义粒度**：de Bruijn 还是 named，未定；
5. **与 `ModelArtifact` 的对接**：`compile : IR → Weights` 与 `parse : Term → Option IR` 的 `Weights` 形状未定；
6. **是否影响 `Plugins/Targets` 的 24 个文件**：双写期需要保留旧文件，文件数会暂时增加。

---

## 10. 一句话

> **几何不是被换掉，是被编码进 CIC：`Encode/Geometry` 单向、`encode_sound` 一条；**
> **CIC 成为主载体后，T0 变成「可类型性即可构造」、T1 变成「`compile` 必须消费输入」、**
> **T2 变成「β 步数给出显式 ε」、T3 变成「到 `NormalForm` 的定理而非字段投影」；**
> **几何的 757 条定理保留为 Domain 级证据，不删除、不重写。**

---

## 11. CIC 化的完整范围

“只要有收益的都可以做”——本文件的范围不止 L2 与靶定理。

### 11.1 一级：直接消除已知缺陷

| 对象 | 消除的缺陷 | 依据 |
|:--|:--|:--|
| L2 语义域 | `no_specSolver`、`l2l3` 丢参数、`g ≡ 0` | §1.1 |
| 插件 `Obligation` | 幽灵名（DAG `denote_seq`/`denote_par`、Norm 路径错配） | `PROOF-OBLIGATIONS.md` §Plugin |
| `PluginProof` | 12 字段 + “非空 ⇒ 12 字段全真” | §5 T0–T8 的连带 |
| T5–T8 | 玩具 `K → Option ℕ`、无插件身份、无证书 | §5 |
| 五个架构载体 | 孤岛、未接 CIC、`⟨rfl,rfl⟩` | `ARCHITECTURE-CARRIERS.md` §7 |

### 11.2 二级：统一而非消除

| 对象 | 统一为 | 收益 |
|:--|:--|:--|
| L1 token | 与 L2 同语义域；`L1⇄L2` 变成 term 内部操作 | 消除 L1/L2 两套语义 |
| `Primitives` | term 上的操作（`SourceTerm`、`EditTerm`） | 与 L2 同构，`S1–S20` 的载体统一 |
| 五载体 | `Term` 上的架构编码（`encode : ArchSyntax → Term`） | 消除孤岛，可复用 `Typable` |

### 11.3 不做 CIC 化

| 对象 | 原因 |
|:--|:--|
| `Weights` | 数值向量，不是语法对象；CIC 化会让“权重 ⇄ 符号”退化为“符号 ⇄ 符号” |
| `ModelArtifact` | 产物，不是语法；可从它**提取** term（`archOf`），但对象本身不是 term |
| 外部训练器 | `Delegate`，证书只能是 `Imported` / `Empirical` |
| `CInterface` ABI | 依赖语言实现，工程侧未定 |
| `Lib/` 的 ≈ 8,900 条定理 | 与 L2 无直接关系 |

### 11.4 边界：LATTICE 只提供底层

> **LATTICE 只提供底层原语与证明；surface syntax、编辑器、工作流由用户在其上构建与封装。**

| 层 | LATTICE 提供 | 用户提供 |
|:--|:--|:--|
| L2 语法 | `Term` / `Level` / 类型规则（`Typing.typable`） | 自己的 surface syntax、DSL、parser |
| L2 编码 | `Encode` 接口 + `encode_sound` | 自己领域的编码器 |
| L2 检查 | 可判定的 `Typable` | 错误消息、诊断、IDE 集成 |
| L2⇄L3 | `parse : Term → Option IR` + `compile : IR → Weights` + `compile_sound` | 自己的编译策略与优化 |
| L3→符号 | `extract : Weights → Option Term` | 自己的提取启发式 |
| 插件 | `PluginManifest` / `VerifiedPlugin` / `Registry` | 自己的插件与义务 |
| 编辑 | `Effect` / `Fiber` / `undo` / `snapshot` 原语 | `VocabEdit` / `SemanticEdit` / `Import` / `PostTrain` 等打包能力 |
| 时空 | `Trace` / `construct` / `finalSpec` / `ResultEquiv` | 自己的编排与调度 |

**这与 `SEMANTICS-MAINLINE.md` 的「不提供打包能力」一致**：
`VocabEdit`、`SemanticEdit`、`Import`、`PostTrain` 都是**用户层**的封装，不是 LATTICE 提供的入口。

