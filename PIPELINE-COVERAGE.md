# 端到端链路：实测贯通状态（阶段 C，P4）

## 一、五个环节都存在，但**不是一条链**

| 环节 | 位置 | 模块数 | 被谁导入（跨层） |
|:--|:--|--:|:--|
| **数据** | `Core/Data` | **7** | **`Core` 内部 + `Reference`** |
| **token** | `Core/IR` | **31** | **`Core`、`Runtime`、`Lib`、`Compose`、`Plugins`** |
| **符号模型** | `Core/CIC` | **91** | **仅 5 个模块，全在 `Core` 内部** |
| **权重编译** | `Lib/Compiler` | **49** | **`Lib` 内部为主** |
| **量化** | `Lib/Quantization` | **25** | **`Lib` 内部为主** |

**=> 前两个环节与后三个环节之间，**唯一的连接是 `Core/IR` 的 `VectorConstraint`**；
而 `Core/CIC`（91 个模块，符号模型的核心）**与 `Lib/Compiler` 之间没有任何导入关系**。**

## 二、`Core/CIC` 的实际消费情况

**实测：91 个 CIC 模块中，层外只有 5 个模块导入它们：**

| 导入者 | 层 |
|:--|:--|
| **`Lattice.Core`（聚合器）** | **root** |
| **`Core.Data.Basic`** | **Core** |
| **`Core.Data.Encode`** | **Core** |
| **`Core.IR.Parse`** | **Core** |
| **`Reference.Geometry.Geometry.Encode.CIC`** | **Reference（归档侧）** |

**=> 符号模型**自成一体**：它证明了很多东西（91 个模块），但**没有任何权重侧的东西消费它**。**

## 三、真正贯通的那条闭环，以及它的边界

**`Lib/Editing/RealCompileExtractClosed.lean` 是**唯一**给出双向闭环的文件：**

| 定理 | 内容 |
|:--|:--|
| `extractLayer_compileToLayer` | **`extractLayer ∘ compileToLayer = id`** |
| `compileToLayer_extractLayer` | **`compileToLayer ∘ extractLayer = id`** |
| `compileToLayer_bijective` | **`compileToLayer` 是双射** |
| `compile_extract_end_to_end` | **`AllSatisfied (extractLayer (compileToLayer cs)) x ↔ AllZeroOutputs (compileToLayer cs) x`** |

**语义桥梁是 `Runtime/ConvertVectorLinear.lean:179`：**

```lean
theorem convertVec_preserves_semantics (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0
```

**=> 这是**符号约束**与**权重层输出**之间的精确等价。它是全项目最核心的一条定理。**

### 但它的载体是 `VectorConstraint`，不是 CIC

**`compileToLayer : ConstraintSet → Layer`，而 `ConstraintSet = List VectorConstraint`。
`VectorConstraint` 定义在 `Core/IR`（token 层），**不是** `Core/CIC`。**

**=> 所以闭环覆盖的是「token ⇄ 权重」这一跳，而**不是**「符号模型 ⇄ 权重」。**

## 四、文件自己也承认这一点

**`RealCompileExtractClosed.lean:69-73` 写明：**

> **「主张：线性子类（`convertVec`/`extractVec` 这一对）上，端到端闭环**成立**，
> 真内容全在 `convertVec_preserves_semantics` 的**零化语义**里。」**

**=> 这是诚实的自我界定：闭环是真的，但它限定在**线性子类**、载体是**约束集**，
不是完整的 CIC 符号模型。**

## 五、因此 P4 的真实缺口是什么

**不是「闭环不存在」——它存在且被证明到双向。**
**而是「闭环的上游端点比声称的短」：**

| 声称 | 实际 |
|:--|:--|
| 数据 ⇄ token ⇄ **符号模型** ⇄ 权重 | 数据 ⇄ token ⇄ 权重 |
| **CIC 参与闭环** | **CIC 不参与；闭环载体是 `VectorConstraint`** |

**=> 要补的是**一段真实的桥**：把某个 CIC 可表达的符号知识编译成 `ConstraintSet`，
从而使闭环的上游延伸到符号模型。**

**这不是措辞问题：`Core/CIC` 有 91 个模块，若它们不参与闭环，
那 91 个模块证明的东西与权重侧无关。**

## 六、下一轮的可执行方向

**最小可行的桥：`Core/CIC` 已经能把数据编码成 term（`Core/Data/Encode.lean` 的
`encodeCorpus` / `encodedIndices`），而 `ConstraintSet` 是约束列表。**

**=> 若能定义并证明：**

```
cicToConstraintSet : Term → Option ConstraintSet
cicToConstraintSet_sound : Typable K Γ t → Covered K d →
  (∀ x, ConstraintAllSatisfied (cicToConstraintSet t) x ↔ …)
```

**那么闭环的上游就真正到达了 CIC。**

**本轮**不**做这一步：它需要先确认「一个 CIC term 该对应哪个 `ConstraintSet`」这个语义选择，
那是一个**设计判断**而不是一次实现。本文件把判断所需的事实全部测量并记录在此。**
