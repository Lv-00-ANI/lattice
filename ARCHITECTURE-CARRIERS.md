# ARCHITECTURE CARRIERS

## 1. 定位

Conv / Attention / Norm / DAG / GNN 是 **L3 载体插件**，不是 LATTICE 主线。

> **状态（2026-11-05 实测）：**
> **五个目录都存在并已登记：`Norm`、`GNN`、`Conv`、`Attention`、`DAG`。**
> **但“存在”不等于“内容兑现”：**
> **Conv 的 `conv_eq_shared_filter` 是 `⟨rfl, rfl⟩`；**
> **Attention 的 `attention_masked_excludes` 是 `simp`；**
> **DAG 的 `dagPar` / `dagResid` 都定义为 `p ++ q`，三条 `denote_*` 是同一命题的三个名字；**
> **Norm 的 `idempotence` 由「迭代方差 ≤ 1」承载，不是 `f∘f=f`。**
> **=> 本节余下内容是**状态描述**，不是「已闭合」声明。**

LATTICE 主线是符号⇄权重转换；架构是转换的目标载体。

**在 CIC 载体下，五个载体是 `Term` 上的架构编码**：
`encode : ArchSyntax → Term`，`decode : Term → Option ArchSyntax`。
当前实现是几何/点云上的独立模型，尚未接 CIC；这是已知缺口。

## 2. 目录

```text
Lattice/Plugins/Architectures/Conv/        -- 已建（内容部分定义展开）
Lattice/Plugins/Architectures/Attention/   -- 已建（与 Lib/Attention 有重复）
Lattice/Plugins/Architectures/Norm/        -- 已建（idempotence 语义拉伸）
Lattice/Plugins/Architectures/DAG/         -- 已建（三构造子同义）
Lattice/Plugins/Architectures/GNN/         -- 已建（单群特例）
```

每个插件当前是三个扁平文件：

```text
Manifest.lean
Plugin.lean
Proofs.lean
```

**不是** `PLUGIN-PROOFS.md` 要求的 `Semantics.lean` + 语义命名子文件夹（`Soundness/` / `Equivariance/` / `Laws/` 等）。
这是已知偏离，未修正。

## 3. 接口

**目标形状（不存在于树中）：**

```lean
structure CarrierPlugin where
  key     : ServiceKey
  Arch    : Type
  encode  : ArchSyntax → Term
  decode  : Term → Option ArchSyntax
  sound   : ...
```

当前没有 `CarrierPlugin`；实际接口是 `Plugins/Registry.verify` 的 `VerifiedPlugin`。
`ARCHITECTURE-CARRIERS.md` 此前声称存在 `CarrierPlugin`，与树不符，已更正。

## 4. 五个载体

### Conv

- 符号：卷积/权重共享约束；
- 证明：`conv_translation_equivariant`（真）、`conv_eq_shared_filter`（`⟨rfl,rfl⟩`）、`conv_window_determines_output`（代入）；
- **缺口：** `conv_eq_shared_filter` 只证「不同位移用同一 filter」，**没有证「跨层共享」**；
  `Lib/LinearAlgebra/RealWeightSharing.sharedChain` 才是跨层共享的载体，两者未连接。
- CIC：未接。

### Attention

- 符号：路由/选择约束；
- 证明：`attention_perm_equivariant`（真）、`softmax_row_stochastic`（真）、`attention_masked_excludes`（`simp`）；
- **缺口：** `softmaxWeight` / `softmaxDenom_pos` / `softmax_row_stochastic`
  与 `Lib/Attention/RealAttention.lean` 的 `softmax` / `softmax_denom_pos` / `softmax_sum_one`
  **实质重复**；`Attention/Proofs.lean` 只 `import Mathlib`，未引用 `Lib`。
- CIC：未接。

### Norm

- 符号：尺度/平移约束；
- 证明：`varNormalize_unit_lipschitz`（转发）、`varOf_varNormalize_eq_one`（单向）、`bn_train_eq_infer`（假设当结论）；
- **缺口：** `.idempotence` 由 `varOf ((varNormalize^[n+1]) x) ≤ 1` 承载，
  不是 `f∘f=f`；`Plugin.lean` 自己承认 `f∘f ≠ f`。
- CIC：未接。

### DAG

- 符号：程序/约束图；
- 证明：`dag_denote_seq`（真，`p` 上归纳）、`dag_denote_par` / `dag_denote_resid`（`unfold; exact dag_denote_seq`）、`dag_confluence`（真，含 `noncommuting_counterexample`）；
- **缺口：** `dagPar` / `dagResid` 都定义为 `p ++ q`，三条 `denote_*` 是同一命题；
  「并发」退化为「串联」。
- **幽灵名：** `Manifest.lean` 的 `theoremName := "denote_seq"` / `"denote_par"`
  与树中真名 `dag_denote_seq` / `dag_denote_par` 不符（`Obligation.theoremName` 是 `String`，无检查）。
- CIC：未接。

### GNN

- 符号：图结构约束；
- 证明：`msgPass_equivariant`（真）、`readout_invariant`（真）、`sparseMsgPass_eq_msgPass`（`rfl`）、`msgPass_bound_perm`（per-row 界）；
- **缺口：** 群固定为 `Equiv.Perm ι`（对称群），**不是 `Aut(G)`**；
  `permActFeat_faithful` 与 `msgPass_eq_of_perm_invariant` 已证但**未进 manifest**。
- CIC：未接。

## 5. 依赖

```text
Carrier < Compiler < Extractor < Verifier < Repairer
```

不得反向依赖。

**当前实际状态：** 五个载体中，`Conv` / `Attention` / `DAG` 的 `Proofs.lean`
**不 import 任何仓库内模块**（只 `import Mathlib`），因此与 `Lib/` 零连接；
这是「自包含」的设计取舍，但**文档未说明**，读者会以为是疏忽。

## 6. 非目标

- 不用架构空间取代 L0–L3；
- 不要求所有架构先统一；
- 不把 Conv/Attention/Norm/DAG 当证明主线。

## 7. 状态与后续

| 载体 | 目录 | 真内容 | 定义展开 | 未接 CIC |
|:--|:--|:--|:--|:--|
| Norm | ✅ | 3 | 3 | ✅ |
| GNN | ✅ | 4 | 4 | ✅ |
| Conv | ✅ | 1 | 2 | ✅ |
| Attention | ✅ | 2 | 2 | ✅ |
| DAG | ✅ | 2 | 3 | ✅ |

后续：

1. 五载体统一 `CarrierPlugin` 接口（`encode` / `decode` / `sound`）；
2. `Norm.idempotence` 改为真 `f∘f=f` 或改 kind 为 `.invariants`；
3. `DAG` 三构造子给出区分度（或明确说明求值相同、差异在调度层）；
4. `Attention` 与 `Lib/Attention` 的重复做出决策（引用或文档说明）；
5. `GNN` 的 `permActFeat_faithful` / `msgPass_eq_of_perm_invariant` 进 manifest；
6. 五载体接 CIC。
