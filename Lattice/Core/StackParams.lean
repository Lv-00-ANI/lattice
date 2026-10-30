import Mathlib
import Lattice.Core.Net

/-!
# `Lattice.Core.StackParams` — **参数空间的赋范向量空间结构**

## 为什么需要这个文件

`Domains/Constraints/NetLoss.lean` 的 `netLoss` 吃 `List (AffineLayer (Fin n))`，而
`Domains/Geometry/ConstraintDescent.lean` 的模块 docstring 早就写明了后果：

> `netLoss` 的一般形状是 `∑ penaltyLoss c (netAct params ·)`，其中 `params` 是 `List (AffineLayer (Fin n))`。
> 要给**一般**情形证下降，需要 `netLoss` 在参数空间上的可微性 + Lipschitz 梯度——
> **而参数空间是层的列表，库里没有它的赋范向量空间结构。** **那是独立的一块（M2-2 反向传播）。**

**本文件给出那个结构。** 而做法不是给 `AffineLayer` 加六个实例，而是**把参数空间直接定义成有限积**——
**`Pi` 与 `Prod` 的实例会自动传播，一行 `inferInstance` 就能验。**

## ⚠ 为什么不用 `List (AffineLayer (Fin n))`

**层数是变量 ⇒ 维数不固定 ⇒ 不可能是有限维向量空间。** **`fderiv` 要求定义域是赋范向量空间**，
所以「`netLoss` 的梯度」在 `List` 上**连陈述都写不出来**（不是难证，是没有类型）。

**⇒ 修法是【固定深度】。** `stackParams k n` 是「恰好 `k` 层」，维数 `k · (n² + n)`。

## 与 `List` 的关系

`toLayers : stackParams k n → List (AffineLayer (Fin n))` 把它送回 `netLoss` 吃的那种形状，
**所以「定长参数空间的结论」可以经 `toLayers` 搬到「变长损失」上**——
**而反方向（`List` 的结论搬回来）不需要，因为 `List` 那边本来就没有可微性。**
-/

namespace Lattice.Core

/-- **恰好 `k` 层的参数空间**：每层是一对（权重矩阵，偏置）。

**定义成有限积（不是 `List`）是为了让 `NormedAddCommGroup`/`NormedSpace ℝ` 自动传播**——
`Fin n → Fin n → ℝ` 与 `Fin n → ℝ` 都是 `Pi` 型，`Prod` 与 `Pi` 的实例都由 mathlib 提供。 -/
abbrev stackParams (k n : ℕ) : Type := Fin k → (Fin n → Fin n → ℝ) × (Fin n → ℝ)

/-- **参数空间是赋范向量空间**——**这一条是 `fderiv` 的前提，也是本节存在的理由。**

**证明是 `inferInstance`：`Pi`／`Prod` 的实例全部由 mathlib 自动给出，不需要手写。** -/
noncomputable instance instNormedAddCommGroupStackParams (k n : ℕ) : NormedAddCommGroup (stackParams k n) :=
  inferInstance

noncomputable instance instNormedSpaceStackParams (k n : ℕ) : NormedSpace ℝ (stackParams k n) :=
  inferInstance

/-- **参数空间 → 层栈**：把定长参数送回 `netLoss` 吃的那种 `List`。

**这是「定长结论」与「变长损失」之间唯一的桥**，也是 `toLayers` 存在的全部理由。 -/
noncomputable def toLayers {k n : ℕ} (p : stackParams k n) : List (AffineLayer (Fin n)) :=
  (List.ofFn (fun i => { W := (p i).1, b := (p i).2 } : Fin k → AffineLayer (Fin n)))

/-- **`toLayers` 的长度恰是 `k`。** -/
theorem toLayers_length {k n : ℕ} (p : stackParams k n) : (toLayers p).length = k := by
  simp only [toLayers, List.length_ofFn, Fintype.card_fin]

end Lattice.Core
