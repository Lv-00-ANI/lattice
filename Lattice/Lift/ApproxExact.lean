/-
# 逼近精确：从「精确成立」降级为「带界成立」

## 0. 本文件要解决什么问题

`Lattice.Lift.PenaltyEmbedding` 把「符号约束 → 损失」的嵌入分成三层：

| 层 | 命题 | 状态 |
|:--|:--|:--|
| A | `loss p x = 0 → Sat p x`（`PenaltySound`） | 对任意实例可证 |
| B | `IsLocalMin (loss p) x → Sat p x`（`PenaltyExact`） | **一般情形为假** |
| C | 梯度范数界 + 强凸性 ⇒ 距离界 | 本文件给出第一步 |

B 层为假，由 `PenaltyEmbedding.sound_not_exact` 机器证否：常数正损失 + 恒假谓词
（`constEmbedding`）满足 A 层（空洞地，因为无点满足 `loss = 0`），却在每一点都是
局部极小、处处违反约束。

因此「精确嵌入」这条路线不可达。本文件记录替代方案：
**把等价降级为带界蕴含，并保证在 `ε = 0` 时严格退化回精确版。**

## 1. 证明思路

### 1.1 为什么 `loss ≤ ε² ⟹ 残差 ≤ ε` 不能对任意 `PenaltyEmbedding` 陈述

`PenaltyEmbedding` 只记录两个字段：

```
loss : P → X → ℝ
Sat  : P → X → Prop
```

它**不记录 `loss` 的形状**。而「`loss ≤ ε²` 蕴含某个量 `≤ ε`」只有在
`loss` 恰好是某个量的平方时才成立；对一般 `loss`，`loss ≤ ε²` 与 `ε` 之间
没有可用的关系（例如 `loss ≡ ε²/2` 与残差无关）。

⇒ 必须先补一个字段承载这个形状。`ResidualEmbedding` 用 `extends` 补上
`resid : P → X → ℝ` 与 `loss_eq_sq : ∀ p x, loss p x = resid p x ^ 2`。
它**精化**而非替换 `PenaltyEmbedding`，所以既有代码不受影响。

### 1.2 核心不等式

`r ^ 2 ≤ ε ^ 2` 且 `0 ≤ ε` 蕴含 `|r| ≤ ε`。这是 mathlib 的
`abs_le_of_sq_le_sq`；本文件另给一个只用 `nlinarith` 的版本
（`abs_le_of_sq_le`），使得该结论在没有 `LinearOrderedRing` 完整实例的场合也可用，
并让「平方开方」这一步的推理在文件内可见。

### 1.3 `ε = 0` 的退化必须带 A 层

`EpsSat E p 0 x` 按定义是 `|E.loss p x| ≤ 0`，等价于 `E.loss p x = 0`。
它**只谈损失，不谈 `Sat`**。所以「`ε = 0` 时得到 `PenaltyExact`」需要额外假设
`PenaltySound`。这不是技术困难，而是**命题确实缺一块**：不假设 A 层，
`EpsSat 0` 与 `Sat` 之间没有任何联系。

这一条正好从另一条路径复现了 A/B 层区分：B 不能由 A 推出（`sound_not_exact`），
而 A 是 B 的极限形式的必要条件（`penaltyExact_of_epsSat_zero`）。

### 1.4 总损失到逐分量

`RealTotalLoss ls x = Σᵢ (outᵢ)²`。若总和 `≤ ε²`，则每个非负单项 `≤ ε²`
（`Finset.single_le_sum`），再开方得 `|outᵢ| ≤ ε`。
`ε = 0` 时退化为 `realTotalLoss_zero_iff_all_outputs`，即界在端点处不收放。

### 1.5 几何载体

四类精确性定理（标量 / 对角 / 满射矩阵 / 垂直约束）都落到
`sq_eq_zero_of_localMin`（本层 `PenaltyAnalysis`）：在非零导数的局部极小点处，
被平方的函数必为零。于是「局部极小 ⟹ 残差 = 0」已经蕴含
「局部极小 ⟹ 残差 ≤ ε」，对任意 `ε ≥ 0`。`geo_eps_bridge` 记录这一步，
它使几何侧的精确结论成为逼近结论的特例。

## 2. 与既有结论的相容性（本文件的验收判据）

| 定理 | 在 `ε = 0` 处退化为 |
|:--|:--|
| `epsSat_zero_iff` | `EpsSat 0 ↔ loss = 0`（A 层的前提） |
| `penaltyExact_of_epsSat_zero` | `PenaltySound` + 上述 ⇒ `PenaltyExact` |
| `component_eq_zero_of_totalLoss_eq_zero` | `realTotalLoss_zero_iff_all_outputs` |

三条都**逐字复现**既有定理，不是新加一个更弱的陈述。

## 3. 本文件不声称的内容

- 不声称「ε 可任意压小」。`ε` 在此是自由参数，本文件未证明它趋于 0；
  收敛率是另一件事（`RealVerifierReliable` 的头部也记着同一条边界）。
- 不声称 C 层已完成。本文件只给出 C 层的第一步（损失 → 残差），
  「残差 → 距离」需要强凸性与一阶条件，尚未做。
- 不声称 `ResidualEmbedding` 已有实例。给出实例是后续工作；
  本文件只保证**若**有实例，桥就成立。
-/
import Mathlib
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Lift.RealTotalLoss
import Lattice.Runtime.PenaltyAnalysis
open scoped ContinuousLinearMap

namespace Lattice.Lift

/-! ## 一、ε-满足谓词 -/

/-- **`ε`-满足**：损失在 `x` 处的绝对值不超过 `ε`。

这一层取代 `Sat` 的位置：当 `ε > 0` 时它不要求约束成立，只要求违反量有界。
取 `ε = 0` 得 `EpsSat E p 0 x ↔ E.loss p x = 0`（`epsSat_zero_iff`）。 -/
def EpsSat {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X) (p : P)
    (ε : ℝ) (x : X) : Prop :=
  |E.loss p x| ≤ ε

/-! ## 二、记录残差的嵌入 -/

/-- **记录残差的惩罚嵌入**：在 `PenaltyEmbedding` 之上补 `resid` 与 `loss = resid ^ 2`。

`PenaltyEmbedding` 不记录损失的形状，因此「损失小 ⟹ 残差小」对它不可陈述
（见文件头的论证）。这个结构补上的正是缺失的那一个字段；由于用 `extends`，
它是精化而不是替换，既有 `PenaltyEmbedding` 的使用点无需改动。 -/
structure ResidualEmbedding (P X : Type) [TopologicalSpace X] extends PenaltyEmbedding P X where
  /-- 未平方的残差。 -/
  resid : P → X → ℝ
  /-- 损失是残差的平方。 -/
  loss_eq_sq : ∀ p x, loss p x = resid p x ^ 2

/-! ## 三、核心不等式：平方界给出绝对值界 -/

/-- **平方界开方。** `0 ≤ ε` 时 `r ^ 2 ≤ ε ^ 2` 蕴含 `|r| ≤ ε`。

这里给出一个只用 `nlinarith` 的证明，不用 `abs_le_of_sq_le_sq`，
原因有二：一是让「开方」这一步的推理在文件内可见而不是被引理名隐藏；
二是不依赖 `LinearOrderedRing` 的完整实例。

机制：`|r| ≤ ε` 等价于 `-ε ≤ r ≤ ε`，两个不等式都由
`(r ± ε) ^ 2 ≥ 0` 展开后与 `r ^ 2 ≤ ε ^ 2` 相减得到。 -/
theorem abs_le_of_sq_le {r ε : ℝ} (hε : 0 ≤ ε) (h : r ^ 2 ≤ ε ^ 2) : |r| ≤ ε := by
  rw [abs_le]
  refine ⟨by nlinarith [sq_nonneg (r + ε)], by nlinarith [sq_nonneg (r - ε)]⟩

/-- **（ii）损失界 ⟹ 残差界。**

对 `ResidualEmbedding`，`loss p x ≤ ε ^ 2` 蕴含 `|resid p x| ≤ ε`。
这是候选 (ii) 的全部内容：一旦结构记录了 `loss = resid ^ 2`，证明只有一行。

边界：`0 ≤ ε` 不可省。`ε < 0` 时结论 `|resid| ≤ ε` 本身为假（绝对值非负），
所以这不是可以弱化的前提，而是命题成立的必要条件。 -/
theorem abs_resid_le_of_loss_le_sq {P X : Type} [TopologicalSpace X]
    (E : ResidualEmbedding P X) {ε : ℝ} (hε : 0 ≤ ε) (p : P) {x : X}
    (h : E.loss p x ≤ ε ^ 2) : |E.resid p x| ≤ ε := by
  rw [E.loss_eq_sq] at h
  exact abs_le_of_sq_le hε h

/-- **`EpsSat` 与 `ResidualEmbedding` 的连接**：同一事实的谓词形式。 -/
theorem epsSat_of_loss_le_sq {P X : Type} [TopologicalSpace X]
    (E : ResidualEmbedding P X) {ε : ℝ} (hε : 0 ≤ ε) (p : P) {x : X}
    (h : E.loss p x ≤ ε ^ 2) : |E.resid p x| ≤ ε :=
  abs_resid_le_of_loss_le_sq E hε p h

/-! ## 四、`ε = 0` 的退化 -/

/-- **`ε = 0` 时 `EpsSat` 就是「零损失」。**

证明即 `|a| ≤ 0 ↔ a = 0`。这一步是相容性检验的第一环：逼近层在端点处必须
退化为既有层，否则界在 `ε → 0` 时会跳变。 -/
theorem epsSat_zero_iff {P X : Type} [TopologicalSpace X] (E : PenaltyEmbedding P X)
    (p : P) (x : X) : EpsSat E p 0 x ↔ E.loss p x = 0 := by
  unfold EpsSat
  rw [abs_nonpos_iff]

/-- **退化到 B 层（附带 A 层）。**

若每个局部极小点都 `0`-满足，且嵌入在 A 层是可靠的，则它精确
（`PenaltyExact`）。

`hsound` 不可省，理由见文件头 §1.3：`EpsSat · 0` 只谈损失，与 `Sat` 无关。
去掉它，命题不可证（不是难证，是缺一块）。 -/
theorem penaltyExact_of_epsSat_zero {P X : Type} [TopologicalSpace X]
    {E : PenaltyEmbedding P X} (hsound : PenaltySound E)
    (h : ∀ p (x : X), IsLocalMin (E.loss p) x → EpsSat E p 0 x) : PenaltyExact E :=
  fun p x hmin => hsound p x ((epsSat_zero_iff E p x).mp (h p x hmin))

/-! ## 五、几何载体：精确性蕴含逼近性

四类精确性定理（`Penalty.sq_penalty_exact`、`PenaltyPerturbN.sq_penalty_exact_finN`、
`PenaltyMatrix.sq_penalty_exact_matrix`、`Nondegenerate.perpResid_localMin_of_nondegenerate`）
的共同落点是 `sq_eq_zero_of_localMin`（本层 `PenaltyAnalysis`）：在导数非零的
局部极小点处，被平方的函数为零。 -/

/-- **几何侧的逼近桥。**

若 `f` 在 `x` 处可微、导数非零，且 `x` 是 `fun y => f y ^ 2` 的局部极小点，
则 `|f x| ≤ ε` 对**任意** `ε ≥ 0` 成立。

实际内容：`sq_eq_zero_of_localMin` 给出 `f x = 0`，于是 `|f x| = 0 ≤ ε`。
所以几何侧的结论比逼近要求更强——已经精确为零。这条定理的价值在于把
「精确」与「逼近」两种陈述放进同一个词汇表，使逼近层可以覆盖几何侧的既有结论，
而不是与它并列成两套说法。

载体：一般的实赋范空间 `E`，不止 `ℝ`。这是 `sq_eq_zero_of_localMin` 本身的支持范围，
这里不额外加限制。 -/
theorem geo_eps_bridge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
    (hderiv : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hmin : IsLocalMin (fun y => f y ^ 2) x) {ε : ℝ} (hε : 0 ≤ ε) : |f x| ≤ ε := by
  have hzero : f x = 0 := sq_eq_zero_of_localMin hderiv hne hmin
  rw [hzero, abs_zero]
  exact hε

/-! ## 六、总损失到逐分量

`RealTotalLoss ls x = Σᵢ (outᵢ)²`。总和有界则每个分量有界，因为单项非负。 -/

/-- **（i）总损失界 ⟹ 逐分量界。**

`RealTotalLoss ls x ≤ ε²` 蕴含每个分量 `|outᵢ| ≤ ε`。

机制：单项 `(outᵢ)²` 非负，故不超过总和（`Finset.single_le_sum`），
传递得 `(outᵢ)² ≤ ε²`，再开方。

边界：`0 ≤ ε` 不可省，理由同 `abs_resid_le_of_loss_le_sq`。 -/
theorem component_abs_le_of_totalLoss_le {n : Nat} (ls : Fin n → RealNeuron) {x ε : ℝ}
    (hε : 0 ≤ ε) (h : RealTotalLoss ls x ≤ ε ^ 2) (i : Fin n) :
    |RealNeuronOut (ls i) x| ≤ ε := by
  have hsingle : (RealNeuronOut (ls i) x) ^ 2 ≤ RealTotalLoss ls x :=
    Finset.single_le_sum (f := fun j => (RealNeuronOut (ls j) x) ^ 2)
      (fun j _ => sq_nonneg (RealNeuronOut (ls j) x)) (Finset.mem_univ i)
  exact abs_le_of_sq_le hε (le_trans hsingle h)

/-- **（i）在 `ε = 0` 处逐字退化为既有定理。**

`component_eq_zero_of_totalLoss_eq_zero` 不是本文件的新结论，而是
`realTotalLoss_zero_iff_all_outputs` 的直接引用；把它写在这里是为了让
「界在端点处不收放」这一判断在文件内可查，而不是靠读者推断。 -/
theorem component_eq_zero_of_totalLoss_eq_zero {n : Nat} (ls : Fin n → RealNeuron) {x : ℝ}
    (h : RealTotalLoss ls x = 0) (i : Fin n) : RealNeuronOut (ls i) x = 0 :=
  (realTotalLoss_zero_iff_all_outputs ls x).mp h i

end Lattice.Lift
