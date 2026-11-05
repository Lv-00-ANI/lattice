# ARCHITECTURE CARRIERS

## 1. 定位

Conv / Attention / Norm / DAG 是 **L3 载体插件**，不是 LATTICE 主线。

> **实现状态（第 125 轮实测更正）：**
> **`Norm`、`GNN`、`Conv`、`Attention` 已实现；`DAG` 未实现。**
> **`Conv`、`Attention`、`DAG` 三个目录**不存在**，本文档第 4 节列出的证明名也**不在树中**。**
> **=> 本节余下内容是**设计规格**，不是实现陈述。**
> **本段是第 125 轮补上的：此前的版本把三者与 `Norm` 并列列出，读者无法区分已有与未做。**

LATTICE 主线是符号⇄权重转换；架构是转换的目标载体。

## 2. 目录

```text
Lattice/Plugins/Architectures/Conv/        -- 已实现
Lattice/Plugins/Architectures/Attention/   -- 已实现
Lattice/Plugins/Architectures/Norm/        -- 已实现
Lattice/Plugins/Architectures/DAG/         -- 未实现
Lattice/Plugins/Architectures/GNN/         -- 已实现
```

每个插件包含：

```text
Manifest.lean
Semantics.lean
Soundness/
Equivariance/
Laws/
Idempotence/     -- Norm
Confluence/      -- DAG
Plugin.lean
```

## 3. 接口

```lean
structure CarrierPlugin where
  key     : ServiceKey
  Arch    : Type
  compile : Symbol → Arch
  extract : Arch → Symbol
  sound   : ...
```

## 4. 四个载体

### Conv（**已实现**）

- 符号：卷积/权重共享约束；
- L3：Toeplitz/循环结构；
- **证明（已存在）**：见 `Lattice/Plugins/Architectures/Conv/`——`conv_translation_equivariant`、`conv_eq_shared_filter`、`conv_window_determines_output`。

### Attention（**已实现**）

- 符号：路由/选择约束；
- L3：softmax 核；
- **证明（已存在）**：见 `Lattice/Plugins/Architectures/Attention/`——`softmax_row_stochastic`、`attention_masked_excludes`、`attention_perm_equivariant`。

### Norm（**已实现**）

- 符号：尺度/平移约束；
- L3：幂等归一化；
- **证明（已存在）**：见 `Lattice/Plugins/Architectures/Norm/`。

### DAG（**未实现**）

- 符号：程序/约束图；
- L3：顺序/并行/残差；
- **待证**：`denote_seq`、`denote_par`、`denote_resid`、`dag_confluence`——**均不在树中**。

## 5. 依赖

```text
Carrier < Compiler < Extractor < Verifier < Repairer
```

不得反向依赖。

## 6. 非目标

- 不用架构空间取代 L0–L3；
- 不要求所有架构先统一；
- 不把 Conv/Attention/Norm/DAG 当证明主线。

## 7. 状态与后续

**已实现：`Norm`、`GNN`、`Conv`（第 126 轮）、`Attention`（第 127 轮）。**
**未实现：`Conv`、`Attention`、`DAG`。**

**=> 补齐这三个载体是 F 阶段的实际工作，其优先级与形状见 `MACRO-COGNITION.md` 第 6 节。**
**本文档在第 125 轮之前把未实现项与已实现项混列，已更正；今后任何载体的增删都应同步更新本节。**
