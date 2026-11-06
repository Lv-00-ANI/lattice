# `Lattice/Domains/Geometry` -- **[待移除]**

> **本目录待移除。仅作参考与反例来源。主线在 [`Lattice/Core/CIC/`](../../Core/CIC/)。**
> **移动时机：CIC 版 T0–T8 就绪后（规划阶段 3）。**

## 为什么待移除

**这个目录是**几何载体**的完整实现：757 条定理，覆盖约束语法、表达式求值、点配置语义、以及
`Encode/Geometry` 的一部分。**

**它之所以待移除，不是因为几何本身有错，而是因为「符号 ⇄ 权重」这一跳需要一条几何提供不了的路。**

### 两套语义之间没有自然的桥

| | 几何 | CIC |
|:--|:--|:--|
| **谓词** | **`Holds : GeoConstraint n → (ℕ → Pt n) → Prop`** | **`Typable : CICCtx → Term → Sort → Prop`** |
| **见证** | **点配置 `Φ : ℕ → Pt n`** | **构造项 `t : Term`** |
| **值域** | **`Pt n = ℕ → Point ℝ n`（无限序列）** | **`Term`（有限语法）** |

**`encode_sound : Holds c Φ → Typable (encode c)` 要做的事是：**

> **从一个点配置满足约束，推出一个 term 可类型化。**

**但两边的见证**结构不同**：`Holds` 的见证是**点配置**，`Typable` 的见证是**构造项**。**
**不存在一个自然的映射把点配置变成构造项。**

**=> 这就是 `Encode/Geometry` 一直做不出来的根本原因，而且它不是工程量问题。**

### 次生问题

| 症状 | 几何根因 | 位置 |
|:--|:--|:--|
| **`SpecSolver` 被证为空** | **几何约束集一般不可满足** | **`no_specSolver:78-90`** |
| **`l2l3` 结论不含 `R`** | **参数被丢弃** | **`WeightSideLadder.lean:156`** |
| **`g(ε)` 不存在** | **Lipschitz 常数依赖点云界 `B`** | **`T2Min.lean:55-58`** |
| **参数层是字段投影** | **`Representation.roundtrip` 是字段而非定理** | **`Extraction.lean:80`** |
| **T5–T8 需玩具模型** | **几何没有插件生命周期** | **`Spatiotemporal/Model.lean:39-52`** |

**这些问题在 CIC 载体上都有对应解法——见 `CARRIER-CIC.md`。**

## 归档而非删除的理由

| 理由 | 说明 |
|:--|:--|
| **757 条定理是资产** | **不删除、不重写；移入 `Reference/Geometry`** |
| **反例来源** | **`no_extractor_preserves_both` 的几何版是真实反例** |
| **历史可追溯** | **载体替换的决定需要证据** |
| **将来可选** | **若有人要做 `Encode/Geometry`，有完整素材** |
| **不阻塞主线** | **`Reference/` 不参与构建，不参与 `ProofComplete`** |

## 现在能做什么，不能做什么

**能：**

- **读这些定理作为几何语义的参考；**
- **从中取反例；**
- **在 `Reference/` 移过去之后继续引用（但不再参与 `lake build`）。**

**不能：**

- **在主线里新增对 `Domains/Geometry` 的 import；**
- **把 `encode_sound` 当作可达目标；**
- **让新的 `ProofComplete` 合取项依赖本目录。**

## 相关内容

- **[`CARRIER-CIC.md`](../../../CARRIER-CIC.md)** —— CIC 载体，主线
- **[`CARRIER-REPLACEMENT.md`](../../../CARRIER-REPLACEMENT.md)** —— 载体替换的决定与回滚条件
- **[`Lattice/Core/CIC/`](../../Core/CIC/)** —— 主线的实现
