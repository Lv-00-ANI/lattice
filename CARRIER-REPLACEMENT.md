# 载体替换决定（CARRIER-REPLACEMENT）

> **状态：** Accepted（2026-11-05）。
> **性质：** 架构决定记录（ADR），记录决定、备选与回滚条件。
> **配套：** 设计与实施见 `CARRIER-CIC.md`。

---

## 0. 决定

| 项 | 决定 |
|:--|:--|
| **主符号载体** | 从 `GeoConstraint n` 改为 **CIC term** |
| **几何** | 降为 `Domains/Geometry` 与 `Domains/Constraints` 的**编码实例**，不再作为主线载体 |
| **几何定理** | 全部保留（≈ 757 条），不删除、不重写；角色从「靶定理的证据」变为「Domain 级证据 + `encode` 的验证」 |
| **语言实现** | 不在本仓库；由工程侧立项实现（parser / elaborator / evaluator） |
| **C 代码** | 不写；只写 ABI / 布局 / conformance / refinement 的 Lean 侧规格 |

---

## 1. 背景

### 1.1 三路审计的结论

2026-11-05 的三路只读审计（层归属 / 剩余任务 / 证明重组），覆盖
`e0b3c06`…`1c0a787`，一致指出一批**同根缺陷**：

| 缺陷 | 证据 |
|:--|:--|
| `ProofComplete` 22 项里 T0 只以别名间接进入 | `Plugins.lean:515-536`；`Strengthened.lean:104-105` |
| 7 条自数 `rfl` + 3 条 `String` 伪证明 + 4 条 `True` 结论 | `Statements.lean:93,133,221,344,364,372,375,384,391,363`；`T4FixedPoint.lean:101-114`；`DPhaseAdditions.lean:70` |
| 硬编码 census 从 1 份变 3 份，其中 2 份已错 | `Plugins.lean:222`（11，对）/ `:482,485`（8，错） |
| `Plugins/` 是唯一不受 I4 检查的层 | `gate.py:301-337` 的 `LAYER_OF` 无 `Lattice/Plugins` |
| 19 处反向依赖（低层 import 高层） | `Core` 7 / `Domains` 5 / `Runtime` 2 / `Compose` 3 |
| T5–T8 的载体是 `K → Option ℕ` 玩具 | `Spatiotemporal/Model.lean:39-52` |

### 1.2 更深一层的诊断

这些缺陷**不是**独立的实现疏忽。它们有一个共同前提：

> **符号模型的「标准形态」被固定在几何上。**

一旦这个前提成立：

- 可满足性不可判定 ⇒ `SpecSolver` 只能为空（T0 退化为 family 强度）；
- 编译语义缺失 ⇒ `l2l3` 只能返回常量（T1 结论不含输入）；
- 不可逆是结构性的 ⇒ T3 的「不可逆」成立得太容易，失去刻画力；
- 与模型结构无关 ⇒ 五个载体全部自建、无法复用。

**几何不是错的，是「不够」的。**

---

## 2. 备选方案与取舍

### 2.1 方案 A：用 Lean 4 本身（`Expr` / `Level`）作载体

| 优点 | 缺点 |
|:--|:--|
| 最自然：符号就是 Lean 表达式 | 把 LATTICE 变成「Lean 元编程层」 |
| 无需自建 CIC | 与「符号 ⇄ 权重」的定位冲突：权重不是 `Expr` |
| 与 `Mathlib` 直接互通 | 依赖 Lean 内部 API，版本脆弱 |

**结论：** 不作为主载体。

### 2.2 方案 B：在 Lean 内建 CIC 模型

| 优点 | 缺点 |
|:--|:--|
| 完全受控：语法、归约、类型规则都在本仓库 | 需要自建 `Term` / `Typable` / `Reduction` |
| 与「符号 ⇄ 权重」定位一致（term 是符号，`Weights` 是权重） | 前期投入约 2–3 周 |
| 语言实现可换，证明不失效 | 需要自己证明 `encode_sound` |
| 几何可作为编码实例 | — |

**结论：✅ 选定。**

### 2.3 方案 C：几何继续作为主载体，补完 T0–T4

| 优点 | 缺点 |
|:--|:--|
| 零迁移成本 | `SpecSolver` 仍然为空（`no_specSolver` 已证） |
| 757 条定理直接可用 | T1 结论仍不含输入 |
| — | T5–T8 仍是玩具 |
| — | 载体仍是孤岛 |

**结论：** 不解决问题，只是推迟。

### 2.4 方案 D：几何与 CIC 并列

| 优点 | 缺点 |
|:--|:--|
| 无迁移风险 | 两套语义并行，靶定理要写两遍 |
| — | `ProofComplete` 会有两套判据 |
| — | 长期维护成本翻倍 |

**结论：** 只在**过渡期**使用（双写期），不作为终态。

### 2.5 方案 E：删除几何

| 优点 | 缺点 |
|:--|:--|
| 最干净 | 丢掉 757 条定理 |
| — | 丢掉几何反例（`no_extractor_preserves_both` 的几何版是真实反例） |
| — | 与「Domain 实例」的设计冲突 |

**结论：** 不采纳。

---

## 3. 影响面

### 3.1 定理论

| 集合 | 数量 | 处置 |
|:--|--:|:--|
| 几何相关 | ≈ 757 | **保留**；降为 Domain 级证据 |
| 非几何 | ≈ 8,943 | **不动** |
| 新增 CIC | 待定 | 新写 |
| T0–T8 | 8 组 | **双写期**：旧 + 新都在判据里 |

### 3.2 目录

| 目录 | 变化 |
|:--|:--|
| `Lattice/Core/CIC/` | **新增**（`Syntax` / `Substitution` / `Reduction` / `Typing` / `Normalization` / `Encode/Geometry`） |
| `Lattice/Domains/Geometry/` | 不变 |
| `Lattice/Domains/Constraints/` | 不变 |
| `Lattice/Plugins/Targets/` | 双写期保留；切换后旧 T0–T8 移入 `Domains/Geometry/Obligations.lean` |
| `Lattice/Plugins/Architectures/*` | 五载体改为「CIC term 上的编码」 |

### 3.3 文档

14 份（见 `CARRIER-CIC.md §8`）：

```text
README.md
DESIGN.md
MODEL-WEIGHT.md
CONSTRUCTIVE-TRAINING.md
PROOF-OBLIGATIONS.md
GLOSSARY.md
PARADIGM.md
SPATIOTEMPORAL.md
CONFLUENCE.md
ARCHITECTURE-CARRIERS.md
ENGINEERING.md
ROADMAP.md
DOCS-MAP.md
CARRIER-CIC.md          （新增）
CARRIER-REPLACEMENT.md  （本文件）
```

### 3.4 门禁

| 门禁 | 是否需要改 |
|:--|:--|
| `gate.py` 的 `LAYER_OF` | 需要加 `Lattice/Plugins`（与本决定无关，但同期修） |
| `check_carrier_claims.py` | 需要加 CIC 载体条目 |
| `check_obligation_names.py` | 需要新建（与 `theoremName` 错配相关） |

---

## 4. 回滚条件

本决定可回滚，条件是以下任一成立：

1. **C0 最小验证失败**：`typable_has_term` 或 `encode_sound` 在 CIC 模型上
   无法在合理工作量内证明；
2. **CIC 的 `Weights` 对接失败**：`compile : Term → Weights` 无法定义出
   与 `ModelArtifact` 兼容的形状；
3. **强规范化不可得**导致 T2 完全无法给出 `ε`（弱规范化也不够时）。

回滚动作：

- `CARRIER-CIC.md` 与 `CARRIER-REPLACEMENT.md` 标 `Superseded`；
- 删除 `Lattice/Core/CIC/`；
- 恢复几何为唯一主载体；
- 在 `PROOF-DEBT.md` 记录「CIC 路线回滚」条目。

---

## 5. 验收（最小验证）

本决定是否值得继续，由两条定理决定：

| ID | 定理 | 位置 | 判据 |
|:--|:--|:--|:--|
| **V1** | `typable_has_term : Typable Γ t A → ∃ v, v : A` | `Lattice/Core/CIC/Typing.lean` | `lake build` 通过；不是 `rfl` |
| **V2** | `encode_sound : Holds c Φ → Typable (encodeConstraint c)` | `Lattice/Core/CIC/Encode/Geometry.lean` | `lake build` 通过；`encode` 出现在结论 |

**只有 V1 与 V2 都通过，才进入完整规划。**

---

## 6. 不做

| 项 | 原因 |
|:--|:--|
| 删除几何域 | 757 条定理是资产 |
| 重写 9,700 条定理 | 92% 不受影响 |
| 实现 CIC 语言 | 工程侧已立项 |
| 写 C 代码 | 用户明确排除 |
| 把权重字面量当构造 | `README.md` §3.1 已禁止 |
| 声称「所有 LLM 的语义」 | `SEMANTICS-MAINLINE.md` 只承诺相对 `D` 的符号完整 |

---

## 7. 后续

| 阶段 | 内容 |
|:--|:--|
| C0 | 最小验证（V1 / V2），3 天 |
| C1 | CIC 完整层（`Reduction` / `Normalization` / `Encode`），7 天 |
| C2 | T0–T4 在 CIC 上重述，10 天 |
| C3 | T5–T8 在 CIC 上，8 天 |
| C4 | 几何降级为 Domain，4 天 |
| C5 | 文档同步 + P0 判据诚实性，并行 |

完整日程见执行规划（会话输出，不落盘）。

---

## 8. 一句话

> **决定：CIC 作主载体，几何作编码实例；757 条几何定理保留、8,943 条非几何定理不动；**
> **语言实现属工程、C 不写、只写规格；**
> **是否继续由两条定理决定：`typable_has_term` 与 `encode_sound`。**
