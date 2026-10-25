# LATTICE 第四轮规划（ROADMAP-v6）

> 生成时点：2026-10-25，第 24 轮。
> 前置：`ROADMAP-v5`（3 项完成）、`REPAIR-CENSUS.md`、`Lattice.Slots`（6 条欠账）。
>
> 本轮的对象是**「符号 ⇄ 权重」这一跳**——项目自称的唯一真正难点。
> 结论是：**这一跳的结构比欠账表显示的要完整得多，剩余的两条欠账各有一个
> 已被证明的障碍，而不是缺证明。**

---

## 0. 实测：`Lift` 层的完整面貌

31 个文件、**209 条定理**、127 个定义（脚本 `agent-tmp/round24_survey.py`，按文件头读语义）。

覆盖面（按文件）：

| 环节 | 文件 |
|:--|:--|
| L0 ⇄ L1 | `RealTokenization`（23 定理）、`RealTokenizationEntry` |
| L1 ⇄ L2 | `L1L2`、`L1L2Roundtrip`（本轮前置已完成）、`RealTokenSymbolLink` |
| L2 → L3 | `SymbolToWeight`、`SymbolToWeightCorrectness`、`ConvertLinear`、`ConvertVectorLinear`、`RealLinear`、`RealNonlinear` |
| L3 → L2 | `Extraction`（18 定理）、`WeightToSymbolEquivalence` |
| 损失 | `PenaltyEmbedding`、`PenaltyAnalysis`、`TotalLoss`、`RealTotalLoss`、`RealModLoss` |
| 验证 | `VerificationSoundness`、`GeoSampledBound`、`RealVerifierReliable`、`RealRandomVerify` |
| 逼近 | `ApproxExact`、`EndToEndApproximation` |
| 组合 | `ComboN`、`LayerComposition`、`EndToEnd` |
| 多层 | `LayerComposition`、`VerifyLoopProgress` |

**⇒ 「符号 ⇄ 权重」这一跳并不薄。** 209 条定理是本库最密集的一层。

---

## 1. 第一条欠账的真正障碍：不是缺实例，是**编码不可抽象**

`lift.compile.single_item_sound` 的 note 说「作为 scheme 开放，因为没有单一实例覆盖所有后端」。

**本轮的实测给出这个判断的依据**：

| 观察 | 事实 |
|:--|:--|
| `Lift` 层的 `structure`/`class` 总数 | 只有 1 个抽象（`L1L2.Encoded`） |
| 提到 `encode` 的文件 | 7 个，但**每个各自定义自己的编码** |
| 对「编码」这个概念的**统一抽象** | **不存在** |

所以「没有单一实例覆盖所有后端」不是实例不够，而是**没有「后端」这个概念**。
每个后端都是一个独立的 `Compiler` 实例，彼此不共享任何结构。

### 1.1 要做成什么

一个 `class Encoding`（或 `structure`），把「编码」的共同结构写出来：

```
class Encodable (A B : Type) where
  enc : A → B
  -- 编码的损失度量（丢了多少信息）
  loss : A → ℝ
```

然后：
- `projectCompiler` 的 `project` 是实例；
- `pairCompile` 是实例；
- `L1L2.encodeForm` 是实例；
- **`single_item_sound` 的 scheme 变成**：若 `satP` 通过 `enc` 因子化，则 `Compiler.sound` 成立——
  **一次证明覆盖所有实例**。

### 1.2 可行性

**可做**，但有一个真实的障碍要先解决：现有的 `Compiler` 的 `enable` 是**字段**
（`encode : inputP → inputW`），不是类型类约束。要去掉 `inputP`/`inputW` 作为字段、
改成类型参数，会**改变 `Compiler` 的结构**，进而影响 `geoCompiler` 等既有实例。

⇒ **这是一个重构，不是新增。** 规模 M，且必须保住既有 6 个 `Compiler`/`Representation` 实例。

---

## 2. 第二条欠账：**我在本文件初稿里判错了**，此处为更正

### 2.1 初稿的错误

初稿写「`Extraction.layers_conflict` 证明有损提取不可能，所以该 slot 应改为 `weakened`」。
**这是错的**，而且错的方式很具体：

```lean
-- 该 slot 要求的东西：
roundtrip : ∀ p, extract (compile p) = p          -- 左逆

-- `layers_conflict` 的假设：
(hround : ∀ p, extract (compile p) = p)          -- 同一个条件
```

**`layers_conflict` 把 `roundtrip` 当作假设**，所以它不可能否证 `roundtrip`。
它否证的是**更强的对象**：一个既做左逆、又在语义层面识别不同参数（
`SemEq` 成立但 `≠`）的提取器。

### 2.2 于是正确的图景

三条事实**同时成立且互不矛盾**：

| 事实 | 内容 |
|:--|:--|
| `Representation.roundtrip` | 要求 `extract` 是 `compile` 的左逆 |
| `semantic_not_injective` | 语义相等比相等粗（`unitForm ≠ scaledForm` 而 `SemEq`） |
| `layers_conflict` | 左逆不能同时做语义识别 |

⇒ **「有损提取」和 `roundtrip` 是不同对象**：有损意味着多个权重映到一个符号，
而 `roundtrip` 要求 `compile` 单射。两者可以共存于不同的层次，但不能共存于同一个
`extract`。`reversibility_is_layered` 陈述的正是这一点。

### 2.3 所以该 slot 保持 `open`，且缺口是真实的

**缺口**：`Representation` 这个结构**只能表达无损情形**。
若要表达有损提取，需要另一个结构（例如 `LossyRepresentation`，
带一个「提取损失」的界而不要求往返），那是**新增设计**，不是补证明。

这与 §1 的结论一致：两条剩余欠账都指向**缺少一个抽象**，
而不是缺少一条证明。

## 3. 第三优先：`Slots.lean` 的状态复核

本轮发现 `lift.extract.roundtrip` 的状态可能标错（应为 `weakened`）。
**其余 5 条也应同样复核**：每条是否有已证的否证或部分结果没有反映到 `Status` 里。

这是纯审计，规模 S，但它直接决定「欠账数 6」这个数字是否可信。

---

## 4. 不做的（及理由）

| 事项 | 理由 |
|:--|:--|
| `core.semantics.external_bridge` | 工具链：TorchLean 需 Lean ≥ 4.26，本项目钉 4.14 |
| `lift.embed.local_minimiser_exact` | 一般命题**已被 `sound_not_exact` 否证**，已在最弱意义上关闭 |
| 重写 `Compiler` 的字段为类型参数 | 见 §1.2：会波及既有实例，需单独一轮且必须先画出受影响的调用点 |
| `δ` 收敛率 | 数值分析，与已完成的多步收敛率是两件事 |

---

## 5. 验收基线

1. `lake build Lattice` 0 error
2. 门禁 I1–I8 全绿
3. **`Slots` 的状态复核完成**：每条 `open` 的 note 必须有**真实缺口**说明；
   若要改为 `weakened`，必须附一条**否证或部分结果**，且该结果的假设不能与被否证的命题相同
4. **`Slot.owedCount` 的变化必须与复核结论一致**——改状态时同步改 `example`，
   这个数字是可判定的，改不了假
5. `audit_counts` 7 项全匹配

---

## 附：测量口径

- `Lift` 层的文件/定理数：按行首正则计，脚本 `agent-tmp/round24_survey.py`。
- 抽象普查：只统计 `structure`/`class` 声明，且按名字筛 `Encode|Encoding|Backend|Codec|Translation`。
- 欠账：`Lattice.Slots.fullRegistry`，用 `#eval Slot.owedCount` 读。
- **本文件的核心判断（§2）依据的是已存在定理 `layers_conflict` 与 `semantic_not_injective`，
  不是推测。**
