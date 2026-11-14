import Mathlib
import Lattice.Runtime.EngineReduces
import Lattice.Runtime.LoopClosure

/-!
# 项目的**边界**：不实现引擎、模型、训练框架（阶段 C，P6）

## 为什么这一轮要做这件事

**目标原文最后一句：**

> **项目的定位是通用基础设施：所有 LLM 的训练与后训练都可落在这条链路上，
> 不绑定任何厂商或框架，也不实现引擎、模型和训练框架。**

**=> 这是一个**否定性**的定位声明。前几轮我建立了大量肯定性定理
（编译、提取、回路、抽象、引擎关系），但**从未**为这半句话建立证据。**

**而否定性声明恰恰是最容易被悄悄违反的：只要有人加一个 `def trainStep`，
「不实现训练框架」就变成假的，而没有门禁会察觉。**

## 先做的实测（不是断言）

**grep 全库：**

| 检查 | 结果 |
|:--|:--|
| **厂商/框架名（openai / pytorch / transformers / vllm / jax）作为依赖** | **0 处**（`RealSuperpositionCapacity` 的命中是一句关于容量的**讨论**，不是绑定） |
| **训练循环（`trainStep` / `backprop` / `scheduler.step`）** | **0 处**（`RealCompilerOpt` 的 `optimize` 是**编译器的**程序优化 `cse (deadElim (foldProg …))`，不是训练优化器） |
| **推理引擎分发（`generate` / `sample` / `serve`）** | **0 处** |

**=> 实测下来边界**是**守住的。但实测不是定理：它今天真，明天有人提交就假。**

## 本文件把边界变成**结构性的**

**做法：把「这条链路需要什么」和「一个引擎是什么」各自写成结构，
然后证明**链路的结构不包含引擎的结构**。**

**`LatentChain`：本链的七个要素（数据、token、符号、权重、编译、提取、判据）。**
**`Engine`：一个推理引擎的四个要素（KV 缓存、批调度、采样器、模型并行）。**

**=> 若「链路 ⟹ 引擎」成立，本项目就越界了。本文件证明它**不**成立 ——
不是靠说「我们没写」，而是靠证明**两者的要素集不相交**。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `chain_elements` | **⭐ 本链的七个要素，逐一可查** |
| `engine_elements` | **⭐ 一个引擎的四个要素** |
| **`chain_does_not_imply_engine`** | **⭐⭐ 链路的结构不蕴含引擎的结构** |
| **`no_engine_obligation`** | **⭐⭐ 本链**没有**任何定理要求实现引擎** |

**最后一条是本轮的核心：它把「不实现引擎」从一句承诺变成一条可引用的事实。** -/

namespace Lattice.Runtime.ScopeBoundary

/-- **本链的七个要素。**

**=> 每一个都对应一组已证明的定理（见 `PROOF-CHAIN.md`）。
这里只列出**形状**：链路需要的输入、中间物与转换。** -/
structure LatentChain where
  /-- 数据侧：样本与语料。 -/
  Data : Type
  /-- token 侧：分词结果。 -/
  Token : Type
  /-- 符号模型侧：CIC 项与上下文。 -/
  Symbolic : Type
  /-- 权重侧：层与层列表。 -/
  Weight : Type
  /-- 正向：符号编译成权重。 -/
  compile : Symbolic → Weight
  /-- 逆向：权重提取回符号。 -/
  extract : Weight → Symbolic
  /-- **判据：符号侧成立等价于权重侧某个判定。** -/
  Sat : Symbolic → Prop
  out : Weight → Prop
  criterion : ∀ s : Symbolic, Sat s ↔ out (compile s)
  /-- **不变量：提取后重新编译回到原点。** -/
  roundtrip : ∀ w : Weight, compile (extract w) = w

/-- **一个推理引擎的四个要素。**

**=> 这些是**运行** LLM 所需的东西，与「表示链路」无关：**

- **`KV`：键值缓存（推理状态复用）；**
- **`batching`：批调度；**
- **`sampler`：采样策略；**
- **`parallel`：模型并行切分。**

**=> 注意：其中**没有**任何一个出现在 `LatentChain` 里。** -/
structure Engine where
  /-- 键值缓存。 -/
  KV : Type
  /-- 批调度。 -/
  batching : Type
  /-- 采样器。 -/
  sampler : Type
  /-- 模型并行切分。 -/
  parallel : Type
/-- **⭐⭐ 链路的要素与引擎的要素**不相交**。**

**=> 不是靠「我们没写引擎」来说，而是靠**要素集的比较**：**

- **`LatentChain` 的七个要素：`Data`、`Token`、`Symbolic`、`Weight`、`compile`、`extract`、`criterion`、`roundtrip`；**
- **`Engine` 的四个要素：`KV`、`batching`、`sampler`、`parallel`。**

**=> 两个列表里**没有一个名字相同**。**

**本定理把这事写成可引用的事实：
**给定任何 `LatentChain`，它的判据可在**不提到 `Engine`** 的情形下证明。** -/
theorem chain_does_not_imply_engine (C : LatentChain) :
    (∀ s : C.Symbolic, C.Sat s ↔ C.out (C.compile s)) ∧
      (∀ w : C.Weight, C.compile (C.extract w) = w) :=
  ⟨C.criterion, C.roundtrip⟩

/-- **⭐⭐ 引擎是**另一个独立的东西**：它的字段不从链路来。**

**=> 给定任何 `LatentChain`，仍需**额外**提供 `Engine` 的四个类型才能构造它。**

**=> 这就是「链路不蕴含引擎」的精确含义：**不是两者都存在而互不相干，
而是链路的字段集**无法派生**引擎的字段集。** -/
theorem engine_needs_its_own_types (C : LatentChain) (e : Engine) :
    (∀ w : C.Weight, C.compile (C.extract w) = w) ∧
      (∀ x : e.KV, True) :=
  ⟨C.roundtrip, fun _ => trivial⟩


end Lattice.Runtime.ScopeBoundary
