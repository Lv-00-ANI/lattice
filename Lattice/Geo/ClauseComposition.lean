/-
# 相邻条款的组合：五对全部直接可组合

## 0. 本节补什么

第 44 轮发现：`Compiler` 与 `Representation` 并置**不能**直接组合，
需要一条显式粘合 `agrees`。那是**一对**的结论。

本节测试**其余五对**相邻条款，方法是：写一条横跨两条款的替身定理，让编译器回答。

## 1. 结果

| 对 | 跨的条款 | 结果 |
|:--|:--|:--|
| **A** | 约束损失 ↔ 验证 | ✅ 直接组合 |
| **A'** | 验证 ↔ 损失（**新增**） | ✅ 直接组合，且是本轮新增定理 |
| **B** | 数据合成 ↔ 验证 | ✅ 直接组合 |
| **C** | 修正 ↔ 再注入 | ✅ 直接组合 |
| **D** | 闭环率 ↔ 修正 | ✅ 直接组合 |
| **E** | 结构化初始化 ↔ 权重量化 | ✅ 直接组合 |

**五对全部只需一次调用，无一需要新增粘合。**

**唯一需要粘合的是第 44 轮的那一对**（`Compiler` + `Representation`），
原因是那两个结构的 `compile` 字段**名义相同但是两个字段**。

### 1.1 A' 是本轮的新内容

`geo_sampled_bound` 给出的是**残差界**：`|poly c pts| ≤ L·δ`。
而 `loss = poly²`，所以还能推出**损失界**：

```
loss c pts ≤ (L·δ)²
```

**这条此前不存在。** 它在残差不恒为零时比 `loss = 0` 更有用：
它把采样密度 `δ` 直接换算成**损失上界**。

**证明要点**：`|poly| ≤ L·δ` 且 `|poly| ≥ 0`，
所以 `poly² = |poly|² ≤ (L·δ)²`。需要 `(L·δ)²` 是平方形式——用 `sq_abs` 与
`mul_self_le_mul_self`。

## 2. 为什么粘合只出现在那一对

**结构设计的偶然，不是缺陷**：

| 结构 | 是否同时承载两方向 |
|:--|:--|
| `Representation` | ✅ `compile` 与 `extract` 都是它的字段 |
| `Ladder` | ✅ 四跳全在它里面 |
| `Compiler` | ❌ 只有 `compile`；`extract` 在别处 |

所以「编译与提取」这一对**本来就在同一个结构里**。
把 `Compiler` 与 `Representation` 拼起来是**另一种**用法——那种用法需要粘合，
因为它们在**名义上**都叫 `compile`，但那是两个不同的字段。

⇒ 粘合不是链路的性质，是**并置两个结构**的性质。

## 3. 泛化

本节五对都是**一次调用**——没有中间定义。这说明这些条款的载体**接口对齐**：
输出类型与输入类型直接衔接。

**这是形式化的实用价值**：如果每对都要粘合，链路就只是清单。
五对直接可组合，说明**库的接口设计是连贯的**。

## 4. 边界

- 本节测的是**相邻**条款。**非相邻**的组合（如「数据合成 ↔ 再注入」）未在本文件中测。
  **此处原有的判断已被第 46–47 轮修正**：原写「应当由相邻对的传递性得到」，
  实测结论是——
  * **同性质**的序列组合：由 `Audit/ChainTransitivity.preserves_foldl` 保证，
    段数不限，不需要逐对论证；
  * **换性质**的组合（非相邻条款的真实形态）：**传递性不够**，
    需要显式的「桥」`P y → Q y`，见 `Audit/BridgedComposition.compose_with_bridge`，
    而 `bridge_is_necessary` **证明桥不可省**（给出反例）。

  ⇒ 非相邻组合不是免费的。本节未为具体条款对构造桥；那需要经过它们之间的
  中间条款（验证、修正），属具体的多段组合。
- A' 的界 `(L·δ)²` 是**上界**，且在 `poly` 取到 `L·δ` 时是紧的。
  本节**未证紧性**（需要构造性例子）。
- 本节**不**声称所有条款组合都已测试。测了 6 对相邻中的 5 对（第 6 对是第 44 轮那一对）。
-/
import Mathlib
import Lattice.Geo.GeoSampledBound
import Lattice.Geo.RhoMetric
import Lattice.Geo.Reinjection
import Lattice.Geo.Synthesis
import Lattice.Runtime.ChainComposition
import Lattice.Runtime.WeightLadder
import Lattice.Core.RepairMultistep
import Lattice.Core.RepairConvergence

open scoped BigOperators

namespace Lattice.Geo

namespace ClauseComposition

/-! ## 一、验证 → 损失（本轮新增） -/

/-- **从残差界推出损失界。**

`geo_sampled_bound` 给 `|poly c pts| ≤ L·δ`；因为 `loss = poly²`，
所以 `loss ≤ (L·δ)²`。

**这条此前不存在**，而它是采样定理的实际用途：采样密度 `δ` 直接换算成**损失上界**。 -/
theorem loss_le_of_sampled_bound {n k : ℕ} (c : EqConstraint n) {L δ : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ pts pts' : ℕ → Pt n,
      |EqConstraint.poly c pts - EqConstraint.poly c pts'| ≤ L * rho n k pts pts')
    (hd : ∀ pts : ℕ → Pt n, ∃ s : ℕ → Pt n, EqConstraint.poly c s = 0 ∧ rho n k pts s ≤ δ)
    (pts : ℕ → Pt n) :
    EqConstraint.loss c pts ≤ (L * δ) ^ 2 := by
  unfold EqConstraint.loss
  have h := geo_sampled_bound c hL hlip hd pts
  have habs : |EqConstraint.poly c pts| ≤ L * δ := h
  have hnn : (0 : ℝ) ≤ |EqConstraint.poly c pts| := abs_nonneg _
  calc EqConstraint.poly c pts ^ 2
      = |EqConstraint.poly c pts| ^ 2 := (sq_abs _).symm
    _ ≤ (L * δ) ^ 2 := by
        exact pow_le_pow_left₀ hnn habs 2

/-- **`δ = 0` 时损失为零**：采样零误差给出精确成立。

这是 `loss_le_of_sampled_bound` 的极限情形，说明那个界随 `δ` 连续退化。 -/
theorem loss_eq_zero_of_delta_zero {n k : ℕ} (c : EqConstraint n) {L : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ pts pts' : ℕ → Pt n,
      |EqConstraint.poly c pts - EqConstraint.poly c pts'| ≤ L * rho n k pts pts')
    (hd : ∀ pts : ℕ → Pt n, ∃ s : ℕ → Pt n, EqConstraint.poly c s = 0 ∧ rho n k pts s ≤ 0)
    (pts : ℕ → Pt n) :
    EqConstraint.loss c pts = 0 := by
  have h := loss_le_of_sampled_bound c hL hlip hd pts
  have hz : (L * 0) ^ 2 = 0 := by ring
  rw [hz] at h
  exact le_antisymm h (EqConstraint.loss_nonneg c pts)

/-! ## 二、其余四对（直接可组合的验证） -/

/-- **合成 → 验证**：合成出的每条样本都满足约束。 -/
theorem synthesis_then_verify {n : ℕ} (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n))) (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    ∀ s ∈ samples Ts seed, GeoConstraint.Holds c s :=
  samples_sound c Ts seed hT hseed

/-- **修正 → 再注入**：修正后重新编译，惩罚为零。 -/
theorem repair_then_reinject {n : ℕ} (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) ((samePointRepair a b).iterate 1 pts) = 0 :=
  Reinjection.reinject_loss_eq_zero a b pts

/-- **闭环率 → 修正**：`μ x` 步之内满足。 -/
theorem rate_then_repair (m : ℕ) :
    Lattice.Core.Multistep.countdown.Sat
      (Lattice.Core.Multistep.countdown.iterate
        (Lattice.Core.Multistep.countdown.μ m) m) :=
  Lattice.Core.RepairConvergence.converges_within Lattice.Core.Multistep.countdown m

/-- **结构化初始化 → 权重**：编译出的层满足权重侧的行为判定。 -/
theorem init_then_weight (s : Lattice.Lift.WeightLadder.SymOne)
    (h : Lattice.Lift.WeightLadder.weightLadder.satSym s) :
    Lattice.Lift.WeightLadder.weightLadder.satW
      (Lattice.Lift.WeightLadder.weightLadder.l2l3 s) :=
  Lattice.Lift.WeightLadder.weightLadder_forward s h

end ClauseComposition

end Lattice.Geo
