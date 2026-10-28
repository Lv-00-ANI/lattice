import Mathlib
import Lattice.Lib.LearningTheory.RealCausalDoCalculus
import Lattice.Lib.LearningTheory.RealCausalInference
import Lattice.Lib.Architectures.RealBatchNorm
import Lattice.Lib.Architectures.RealLayerNorm
import Lattice.Lib.Architectures.RealBatchNormConsistency
import Lattice.Lift.RealLV
import Lattice.Runtime.RealLinear
/-!
# LATTICE: RealSeamBridges -- 接缝桥模块

## 为什么这个文件存在

`EXEC-V2` 的机器普查发现: 全库存在若干对**定义体逐字相同、却从未被写成恒等式**的声明.
本模块据 **EXEC-X1** 的更正机理只做接线: `import` 两端, 把两端写成恒等式, 证明体 `rfl`.
**不修改任何既有模块.**

## ⚠ 机理更正 (EXEC-X1 实测, 推翻 EXEC-V2 的表述)

全库 11 个相关模块**共用同一个 `namespace Lattice`**, 因此「同名冲突」并**不是**
两条同名声明分处不同命名空间, 而是**同一条 `Lattice.X` 被两个文件各自定义**.

* **两端名字【相同】** (都是 `Lattice.bmean`), 不是 `RealBatchNorm.bmean` / `RealLayerNorm.mean`.
  本文件第 1 版误用 `@RealBatchNorm.bmean` 语法, `lake build` 报
  `unknown identifier 'RealBatchNorm.bmean'` —— **文件名不是命名空间**.
* ⟹ 桥的正确写法是: **在同一命名空间内用不同的【桥定理名】** 把两端接起来,
  而**不是**用模块前缀限定 (模块前缀在 Lean 里不存在).

## 可桥性判据 (EXEC-X1 实测 + 协调者对照实验)

| 声明种类 | 同名并存 | 后果 |
|---|---|---|
| `def` / `abbrev` / `structure` / `inductive` | ❌ 不可能 | import 直接失败 |
| `theorem` / `lemma` | ✅ 可能 | 静默遮蔽 |

实测: `import RealRecoverBehavior` 失败
(`environment already contains 'Lattice.Beh' from RealRecoverEndpoint`),
因为二者**都**定义 `Lattice.Beh` 且 `RealRecoverBehavior:4` 已 import `RealRecoverEndpoint`.
**`Beh` 是 `def` ⟹ 该对物理不可桥接** (见 §5), 本文件不含它.
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、指示函数桥: `doInd` / `binInd`

两端声明名 `Lattice.doInd`(定义于 `RealCausalDoCalculus.lean:85`) 与
`Lattice.binInd`(定义于 `RealCausalInference.lean:76`) 定义体逐字相同:
`def f (p : Prop) [Decidable p] : ℝ := if p then 1 else 0`.
此处文件名**只用于定位文件**, 不构成命名空间限定 (见文件头「机理更正」:
两端同在 `Lattice` 命名空间).
`RealCausalDoCalculus.lean:83-84` 源码自认: 「`binInd` 是二值专用版;
本文件另立以免命名冲突」. -/

/-- 两端指示函数**逐字同一定义**的桥 (两端同在 `Lattice` 命名空间). -/
theorem doInd_eq_binInd (p : Prop) [Decidable p] : doInd p = binInd p := rfl

/-- 桥的函数级形式: 两个指示函数作为函数**相等**. -/
theorem doInd_fn_eq_binInd_fn : doInd = (binInd : (p : Prop) → [Decidable p] → ℝ) := rfl

/-! ## 二、BN / LN / 一致性 三处批均值桥

`RealBatchNorm.lean:29` / `RealLayerNorm.lean:26` / `RealBatchNormConsistency.lean:75`
三处定义体逐字相同: `def f (X : ι → ℝ) : ℝ := (∑ i, X i) / (Fintype.card ι : ℝ)`
(三处声明名分别为 `Lattice.bmean` / `Lattice.mean` / `Lattice.batchMean`; 上列文件名
只用于定位文件, 不构成命名空间限定).
一次接上 BN / LN / RMS 四模块统计量层. -/

variable {ι : Type*} [Fintype ι]

/-- BN 的 `bmean` 与 LN 的 `mean` 是同一个函数. -/
theorem bmean_eq_mean (X : ι → ℝ) : bmean X = mean X := rfl

/-- BN 的 `bmean` 与一致性文件的 `batchMean` 是同一个函数. -/
theorem bmean_eq_batchMean (X : ι → ℝ) : bmean X = batchMean X := rfl

/-! ## 三、LV / Linear 三连桥

`RealLV.lean:31,36,49` 的三个 def (`Lattice.lv_compile` / `Lattice.lv_neuron_out` /
`Lattice.lv_loss`) **全部逐字委派**给
`RealLinear.lean` 中对应的 def (`Lattice.convertReal` / `Lattice.RealNeuronOut` /
`Lattice.realLoss`), 证明体 `rfl` (文件名只用于定位文件, 不构成命名空间限定). -/

/-- `lv_compile` 就是 `convertReal` (系数拷贝). -/
theorem lv_compile_eq_convertReal (c : RealConstraint) : lv_compile c = convertReal c := rfl

/-- `lv_neuron_out` 就是 `RealNeuronOut`. -/
theorem lv_neuron_out_eq_RealNeuronOut (n : RealNeuron) (x : ℝ) :
    lv_neuron_out n x = RealNeuronOut n x := rfl

/-- `lv_loss` 就是 `realLoss` (平方损失). -/
theorem lv_loss_eq_realLoss (c : RealConstraint) (x : ℝ) : lv_loss c x = realLoss c x := rfl

end Lattice
