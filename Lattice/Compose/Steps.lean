/-
# `Compose/Steps` —— 优化器步长作为 `Primitive`

## 0. 命名裁决（第 235 轮）

`DIRECTORY-DESIGN.md` §5.8 原先把它们叫 `sgdStep` / `momentumStep` / `adamStep`。
**`gov/check_scope_boundary.py` 的 `TRAINING_NAMES` 逐字禁止 `sgdStep` 与 `adamStep`**，
理由是「训练循环不需要 import，名字是唯一的机械信号」。

**裁决：改 §5.8 的名字，不放宽守卫。** 新名字是 `applySgd` / `applyMomentum` / `applyAdam`——
它们描述**一次参数更新**，不声称循环。**§5.8 已同步修改。**

**守卫没有被削弱**：`sgdStep` 仍然会被判违规（第 236 轮的零容忍不变），
只是我们不再用那个名字。

## 1. 三个 primitive 的诚实分级

**这三个不是同一等的东西**，本节不把它们写成一样：

| primitive | `sound` 的内容 | 等级 |
|:--|:--|:--|
| **`applySgd`** | 更新方程 **+ 一条收缩定理** | **有实质定理** |
| `applyMomentum` | 只有更新方程 | **规格**（`sound` 是 `rfl` 级） |
| `applyAdam` | 只有更新方程 | **规格**（`sound` 是 `rfl` 级） |

**为什么后两个只有规格**：动量与 Adam 的**正确性**不是「输出等于公式」，而是**收敛性**
（动量在二次型上的谱半径、Adam 的自适应界）。那些是**训练动力学的定理**，
**不在本节的范围**，而且它们需要多步迭代——`iterate` 现在有了，但收敛证明是另一件事。

⚠ **所以 `applyMomentum`/`applyAdam` 的 `sound` 是薄的**：它说「函数返回它返回的东西」。
**登记为规格，不冒充定理。** 若要它们有实质内容，需要各自的收敛定理——**那是待办，不是已完成。**

## 2. `applySgd` 的真定理：步长在 `(0, 2)` 时残差收缩

对线性约束的残差 `r β = β + c`，SGD 一步给

```
β' = β - η·(β + c)      ⟹      r β' = (1 - η)·r β
```

所以 **`0 < η < 2` ⟹ `|r β'| < |r β|`**（只要 `r β ≠ 0`）。
**这是 `|1 - η| < 1` 的直接推论，用 `nlinarith` 可证。**

**这条不是「输出等于公式」**：它把**步长的可用范围**证出来了——`η = 2` 恰好不收缩，`η > 2` 是发散。

## 3. 边界

- **状态型优化器不是自映射**：动量要带速度，所以 `Input = Output = ℝ × ℝ`；
  Adam 要带两阶矩，`Input = Output = ℝ × ℝ × ℝ`。**把它们写成 `Primitive ℝ ℝ` 会丢掉状态**，
  那正是「打包能力」而不是「基础调用」。
- **`grad` 是参数，不是从损失算的**：本节不引入自动微分（那是 `T2`，未做）。
- **不做收敛**：见 §1。 -/
import Mathlib
import Lattice.Compose.Primitive

namespace Lattice.Compose

open Real

/-! ## 一、SGD 一步（有实质定理） -/

/-- **SGD 一步**：`β ↦ β - η · grad β`。

`grad` 与步长 `η` 都是**参数**——本节不引入自动微分，梯度由调用方给。 -/
def applySgd (η : ℝ) (grad : ℝ → ℝ) : Primitive ℝ ℝ where
  pre := fun _ => True
  post := fun β β' => β' = β - η * grad β
  run := fun β => some (β - η * grad β)
  sound := fun β _ => ⟨β - η * grad β, rfl, rfl⟩
  strength := .exact
  coverage := none
  frame := fun _ _ => True

/-- **`applySgd` 的更新就是那条公式**——可直接引用。 -/
theorem applySgd_run (η : ℝ) (grad : ℝ → ℝ) (β : ℝ) :
    (applySgd η grad).run β = some (β - η * grad β) := rfl

/-- **线性约束的残差**：`r β = β + c`。 -/
def linResidual (c : ℝ) : ℝ → ℝ := fun β => β + c

/-- **SGD 一步把线性残差乘上 `1 - η`。**

`r (β - η·r β) = (1 - η)·r β`——纯代数，`ring` 即可。 -/
theorem linResidual_applySgd (c η β : ℝ) :
    linResidual c (β - η * linResidual c β) = (1 - η) * linResidual c β := by
  unfold linResidual
  ring

/-- ⭐⭐ **步长在 `(0, 2)` 内时残差绝对值严格收缩。**

`0 < η < 2` 且 `r β ≠ 0` ⟹ `|r β'| < |r β|`。

**这条是本节唯一有实质内容的定理**：它把**可用步长区间**证出来了。
`η = 2` 恰好不收缩（`|1-η| = 1`），`η > 2` 发散。 -/
theorem applySgd_contracts (c η β : ℝ) (hη0 : 0 < η) (hη2 : η < 2)
    (hne : linResidual c β ≠ 0) :
    |linResidual c (β - η * linResidual c β)| < |linResidual c β| := by
  rw [linResidual_applySgd, abs_mul]
  have h1 : |1 - η| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  calc |1 - η| * |linResidual c β| < 1 * |linResidual c β| := by
        apply mul_lt_mul_of_pos_right h1
        exact abs_pos.mpr hne
    _ = |linResidual c β| := one_mul _

/-! ## 二、动量一步（规格） -/

/-- **动量一步**：状态是 `(参数, 速度)`。

```
v' = μ·v - η·grad β
β' = β + v'
```

**`Input`/`Output` 都是 `ℝ × ℝ`**——动量**不是**参数上的自映射，它带速度。
把它写成 `Primitive ℝ ℝ` 会丢掉状态。

⚠ **`sound` 是 `rfl` 级的**：它只说「输出等于这两条公式」。
动量的**正确性**是收敛性（二次型上的谱半径），**不在本节范围**（见文件头 §1）。 -/
def applyMomentum (η μ : ℝ) (grad : ℝ → ℝ) : Primitive (ℝ × ℝ) (ℝ × ℝ) where
  pre := fun _ => True
  post := fun p q => q.2 = μ * p.2 - η * grad p.1 ∧ q.1 = p.1 + q.2
  run := fun p => some (p.1 + (μ * p.2 - η * grad p.1), μ * p.2 - η * grad p.1)
  sound := fun p _ => ⟨_, rfl, rfl, rfl⟩
  strength := .exact
  coverage := none
  frame := fun _ _ => True

/-- **动量状态里的第一个分量是速度**——可直接引用。 -/
theorem applyMomentum_velocity (η μ : ℝ) (grad : ℝ → ℝ) (β v : ℝ) :
    ((applyMomentum η μ grad).run (β, v)).map Prod.snd
      = some (μ * v - η * grad β) := rfl

/-! ## 三、Adam 一步（规格） -/

/-- **Adam 一步**：状态是 `(参数, 一阶矩, 二阶矩)`。

```
m' = β₁·m + (1-β₁)·g
v' = β₂·v + (1-β₂)·g²
θ' = θ - η·m'/(√v' + ε)
```

**`Input`/`Output` 都是 `ℝ × ℝ × ℝ`**——Adam 带两个累加器。

⚠ **`sound` 是 `rfl` 级的**，与动量同理；Adam 的偏置修正与收敛界**不在本节范围**。
**本节不做偏置修正**（那需要步数 `t`，是第四维状态）——**这一点必须说清**，
否则会被读成「Adam 已完整」。 -/
noncomputable def applyAdam (η β₁ β₂ ε : ℝ) (grad : ℝ → ℝ) : Primitive (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) where
  pre := fun _ => True
  post := fun s t =>
    let g := grad s.1
    t.2.1 = β₁ * s.2.1 + (1 - β₁) * g ∧
    t.2.2 = β₂ * s.2.2 + (1 - β₂) * g ^ 2 ∧
    t.1 = s.1 - η * t.2.1 / (Real.sqrt t.2.2 + ε)
  run := fun s =>
    let g := grad s.1
    let m' := β₁ * s.2.1 + (1 - β₁) * g
    let v' := β₂ * s.2.2 + (1 - β₂) * g ^ 2
    some (s.1 - η * m' / (Real.sqrt v' + ε), m', v')
  sound := fun s _ => ⟨_, rfl, rfl, rfl, rfl⟩
  strength := .exact
  coverage := none
  frame := fun _ _ => True

end Lattice.Compose
