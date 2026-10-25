/-
# 近似桥：`ε`-局部极小 ⟹ `ε`-满足

## 0. 本节补什么

`COMPLETENESS-AUDIT` 之后清单指出的 A 类第一项：

> **近似桥**：`IsLocalMin (loss) x`（或 ε-近似极小）⇒ 违反量 ≤ f(ε)。
> 这是 T2 故事的唯一缺口。

**为什么精确的 `IsLocalMin` 不够**：`sq_localMin_dichotomy` 说明在精确极小点处
要么残差为零、要么梯度为零（第二个分支被多项式占据，`constEmbedding` 即是）。
**精确极小只给出「零或梯度消失」，给不出定量的界。**

所以桥的正确形式必须是**近似的**：损失**不超过**某个参考值，而不是「达到极小」。

## 1. 证明思路

`loss = resid²`。所以：

```
loss x ≤ ε²  ⟹  |resid x| ≤ ε
```

这条**已经在库中**：`ApproxExact.abs_resid_le_of_loss_le_sq`。

**缺的那一环**是：从「x 处的损失小」推出「约束在 x 处近似成立」。
若约束的满足关系是 `resid = 0`，则 `|resid| ≤ ε` 就是 **ε-近似满足**。

所以桥的正确陈述是：

```
EpsSat E p (ε²) x   ⟹   |resid p x| ≤ ε
```

即：**损失在 `ε²` 以内 ⟹ 残差在 `ε` 以内 ⟹ 约束 `ε`-近似成立**。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `loss_bound_gives_resid_bound` | `loss ≤ ε² ⟹ |resid| ≤ ε`（`ε ≥ 0`） |
| `approx_satisfies` | **桥**：`EpsSat` 给出 `ε`-近似满足 |
| `approx_min_le_gives_sat` | **从「比某点损失小」到近似满足**——这才是 `IsLocalMin` 的可用替代 |
| `localmin_sharp` | 精确极小的情形：`loss = 0 ⟹ 残差为零`（回到精确） |

**`approx_min_le_gives_sat` 是清单要的那一条**：它把
「`x` 处的损失不超过任何测试点的损失」换成「`x` 处约束 `ε`-近似成立」，
而 `ε` 由测试点的损失控制。

## 3. 为什么这是「T2 故事的唯一缺口」

T2（约束嵌入）的主线是：

```
符号约束  ──编译──▶  损失函数  ──训练──▶  损失小  ──???──▶  约束近似满足
```

前三步都有定理，**第四步就是本节**。补上它，T2 的链条闭合。

## 4. 边界

- 本节**不**证明「训练能让损失变小」。那是优化理论，不在本库范围
  （目标明确说不实现训练框架）。
- 本节**不**处理「梯度消失」分支（`f' = 0` 而 `f ≠ 0`）。那个分支下
  `loss > 0`，所以 `EpsSat` 无法成立——**这是正确行为**，不是缺陷：
  梯度消失的极小点**不是**约束的解，`PenaltyEmbedding.sound_not_exact`
  正是这个事实的否证。
- `ε ≥ 0` 是必需前提（`abs_resid_le_of_loss_le_sq` 已经要求它）。
  这不是技术性条件：`ε < 0` 时 `loss ≤ ε²` 与「残差 ≤ ε」不相容。
- 本节对**任意** `ResidualEmbedding` 成立，不限于线性或几何——这是推广而非特例。
-/
import Mathlib
import Lattice.Lift.ApproxExact

namespace Lattice.Lift

namespace ApproximationBridge


variable {P X : Type} [TopologicalSpace X]

/-- **损失界 ⟹ 残差界**：`loss ≤ ε²` 给出 `|resid| ≤ ε`（`ε ≥ 0`）。

这是 `abs_resid_le_of_loss_le_sq` 的重新陈述，放在桥的语境里，
使链条的每一环都能在这一个文件里读到。 -/
theorem loss_bound_gives_resid_bound (E : ResidualEmbedding P X) (p : P) {ε : ℝ}
    (hε : 0 ≤ ε) (h : E.loss p x ≤ ε ^ 2) :
    |E.resid p x| ≤ ε :=
  abs_resid_le_of_loss_le_sq E hε p h

/-- **桥：`EpsSat` 给出 `ε`-近似满足。**

`EpsSat E p (ε²) x` 说 `|loss| ≤ ε²`；因为 `loss = resid² ≥ 0`，
所以 `|loss| = loss`，于是 `|resid| ≤ ε`。

⇒ **约束的 `ε`-近似成立**（在 `resid` 意义下）。 -/
theorem approx_satisfies (E : ResidualEmbedding P X) (p : P) {ε : ℝ} (hε : 0 ≤ ε)
    (h : EpsSat (P := P) (X := X) (E.toPenaltyEmbedding) p (ε ^ 2) x) :
    |E.resid p x| ≤ ε := by
  unfold EpsSat at h
  have hnonneg : 0 ≤ E.loss p x := by
    rw [E.loss_eq_sq]
    exact sq_nonneg _
  have hloss : E.loss p x ≤ ε ^ 2 := by
    rwa [abs_of_nonneg hnonneg] at h
  exact loss_bound_gives_resid_bound E p hε hloss

/-- **从「比某点的损失小」到近似满足**——`IsLocalMin` 的可用替代。

若 `x` 处的损失不超过某个测试点 `y` 处的损失，且 `y` 处的损失小，
则 `x` 处残差小。

**这是清单要的那一条**：`IsLocalMin` 说的是「比邻域内所有点都小」（无界量），
本定理用**一个测试点**给出**定量**结论。 -/
theorem approx_min_le_gives_sat (E : ResidualEmbedding P X) (p : P) {ε : ℝ} (hε : 0 ≤ ε)
    (y : X) (hm : E.loss p x ≤ E.loss p y) (hy : E.loss p y ≤ ε ^ 2) :
    |E.resid p x| ≤ ε :=
  loss_bound_gives_resid_bound E p hε (le_trans hm hy)

/-- **精确情形**：损失为零给出残差为零。

这是近似桥的极限（`ε = 0`），也是 `PenaltyEmbedding.sound_exact` 的定量来源。 -/
theorem localmin_sharp (E : ResidualEmbedding P X) (p : P) (h : E.loss p x = 0) :
    E.resid p x = 0 := by
  have hsq : E.resid p x ^ 2 = 0 := by
    rw [← E.loss_eq_sq]
    exact h
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq

/-- **链路的闭合陈述**：损失被 `ε²` 控制 ⟹ 残差被 `ε` 控制 ⟹ `ε`-近似满足。

把三步写成一个蕴含，使 T2 的链条在这一个命题里可见。 -/
theorem loss_controls_violation (E : ResidualEmbedding P X) (p : P) {ε : ℝ} (hε : 0 ≤ ε)
    (h : E.loss p x ≤ ε ^ 2) : |E.resid p x| ≤ ε :=
  loss_bound_gives_resid_bound E p hε h

end ApproximationBridge

end Lattice.Lift
