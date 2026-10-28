# `Kernel` 层的测量：它为什么**不该**被建起来

> **第 15 轮。** 本文档只做测量与结论，**不搬任何文件**。
> 判据与第 244 轮否决 `Kernel/Constraints` 时**完全相同**：一个模块能否进 rank 1，只取决于它 import 的东西的 rank。

---

## 0. 一句话结论

**`Kernel/Types.lean` 按 `DIRECTORY-DESIGN.md` §2.5 所写不可实现**：它点名的 23 个类型里
**17 个在活树里根本不存在**，而存在的 4 个**都需要 rank ≥ 2**。而 rank 1 的 `Kernel` 层
**没有独立于 `Core` 的自然内容**——`Core` 的 18 个模块**就是**那个层。

---

## 1. §2.5 的清单 vs 活树

§2.5 原文：「`Model`、`Profile`、`Program`、`Weights`、`Spec`、`Vocab`、`ConstraintSet`、`Param`、
`Loss`、`Grad`、`Annotation`、`Delta`、`EditRecord`、`Violation`、`Operator`、`Certificate`、
`QuantParams`、`QuantizedWeights`、`Metrics`、`Data`、`Batch`、`TokenMap`、`MergeRecord`
**全部在 `Kernel/Types.lean`**。」

实测（按 `structure`/`inductive`/`def`/`abbrev`/`class` 的定义处，取 rank 最小的那一处）：

| 分类 | 个数 | 内容 |
|:--|--:|:--|
| **根本不存在** | **17** | `Profile`、`Weights`、`Spec`、`Param`、`Grad`、`Annotation`、`Delta`、`EditRecord`、`Violation`、`Operator`、`Certificate`、`QuantParams`、`QuantizedWeights`、`Metrics`、`Data`、`Batch`、`TokenMap` |
| **存在但需 rank ≥ 2** | **4** | `Program`(2)、`Vocab`(3)、`ConstraintSet`(2)、`MergeRecord`(3) |
| 存在且 rank ≤ 1 | **2** | `Model`(0)、`Loss`(0)——但都在 `Lib`，而 `Lib` 按第 228 轮裁决不动 |

**所以 §2.5 描述的是一个从未被写出来的库。** 「全部在 `Kernel/Types.lean`」这句话**没有可执行的内容**。

---

## 2. rank 1 上到底有什么可用

| 类别 | 模块数 |
|:--|--:|
| 需要 rank ≤ 1 的模块（全树） | **165** |
| 其中 `Core` | **18** |
| 其中 `Lib`（按裁决不动） | **117** |
| 其中**其他** | **30** |

那 30 个里，真正可动的候选是 **16 个 `Runtime` 模块**（`ComboN`、`ConvertVectorLinear`、`ErrorCalculus`、
`Extraction`、`L1L2`、`PenaltyAnalysis`、`PenaltyEmbedding`、`RealLinear`、`RealModLoss`、`RealNonlinear`、
`RealRandomVerify`、`RealTokenization`、`RealVerifierReliable`、`RepresentationFamilies`、`StackCodegen`……），
外加 4 个 `Primitives`、4 个 `Audit`、1 个 `Compose`、1 个 `Domains`。

**这 30 个不是一个层，是一个 rank 桶。** 把它们叫作 `Kernel` 不会让它们成为「共享类型」——
它们之间没有共同主题，只是因为「依赖浅」而被归到一起。

---

## 3. 三条路线，以及为什么只有第三条是诚实的

### 路线 A：建 `Kernel/Types.lean`，把 §2.5 的 23 个类型写出来

**代价**：17 个类型要从零设计，4 个要从 `Runtime`/`Domains`/`Semantics` **重建**（因为搬不动，
只能复制或重构依赖）。**那是设计新库，不是迁移旧库**——而本项目的目标是**重构**，不是重写。

**并且**：新建 17 个类型会让它们**没有任何证明**，而本项目的判据是「有名字、0 sorry 不算完成」。
**那会直接制造 17 条新债。**

### 路线 B：建 rank 1 的 `Kernel`，装那 30 个模块

**代价**：30 次搬迁、一次全量重建、`PATH_MAP` 30 条。
**收益**：**目录名与 §9 一致**。
**代价的另一半**：这 30 个模块**没有共同主题**，所以这个「层」**不表达任何依赖关系**——
而分层的唯一用处就是表达依赖关系。**这是第 249 轮否决 `Primitives` 路线 B 的同一条理由。**

### 路线 C：承认 `Core` **就是** `Kernel`，并把 §9 的链路改对

**做什么**：不建新层。把 `DIRECTORY-DESIGN.md` §9 的链路
`lib 0 < kernel 1 < runtime 2 < domains 3 < primitives 4`
改成测量支持的形式：

```
core (= kernel) 0  <  slots 1  <  runtime 2 == primitives 2  <  lib 3 == domains 3  <  audit 5  <  compose 6
```

**代价**：0。
**收益**：链路**与 `LAYER_OF` 完全一致**，且每一段都有实测依据（`Basic`、`Primitives`、`Domains`
三次搬迁的测量都在这份记录里）。

---

## 4. 建议

**走路线 C**，并把 §2.5 标成**愿景而非计划**：

- `Kernel/Types.lean` 若要存在，前提是**先有那 17 个类型**，而那是新设计；
- 在那之前，`Core`（18 个模块、rank 0）**承担了 §2.5 说的那个角色**——
  它是全树唯一一个「语言层：语法 / 语义 / 满足关系 / 修复 / 权重接口」的层，也正是 §9 里
  `Kernel` 想表达的东西。

⚠ **所以「`Kernel` 层未建」这句话要改**：不是「没做完」，而是**测量表明它不该作为独立层存在**。
这与 `Primitives` 不同——`Primitives` 有 4 个真正的模块（第 249 轮），而 `Kernel` **一个都没有**。

---

## 5. 这份测量**没有**做的事

- **没有搬任何文件。**
- **没有改 §9**——改动留给下一轮，因为那是设计文档的修订而非测量。
- **没有判断那 16 个 `Runtime` 模块该不该降到 `Core`**：那是**另一个**问题（「`Core` 该不该收下
  所有 rank ≤ 1 的内容」），而且它的收益同样是目录整洁而非语义保证。
- **没有尝试为那 17 个不存在的类型找替身**：`Weights`、`Grad`、`Certificate` 等可能在别的名字下存在，
  但**按名字找不到**这件事本身就是 §2.5 不可执行的证据。
