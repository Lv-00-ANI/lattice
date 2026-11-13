/-
# 几何侧的多步闭环：逐步逼近而非一步到解

## 0. 本节补什么

完整性终审（第 73 轮）指出条款 9（闭环）的缺口：

> `converges_within` 给出精确界，**但只对 `countdown`**（在 `Nat` 上）。
> **几何侧的所有修复算子都是「一步到解」**（`μ ∈ {0,1}`）——
> `sqDistFix`、`collinearFix`、`equalLengthFix`、`perpRepair` 全部如此。

⇒ **「多步收敛」在几何侧没有见证。**

## 1. 证明思路

### 1.1 为什么几何侧的算子都是一步

第 64–73 轮的构造都是**解析解**：直接算出满足约束的坐标，一步落上去。
`μ` 因此可以取 0/1 指示，`decreases` 是「1 降到 0」。

**这没错，但它不展示「迭代」**：一条 `fix` 就够，回路没有回路的形态。

### 1.2 多步算子该怎么造

需要 `μ` **严格递减但不止一步**。几何上对应：

> **每步向目标移动固定距离，而不是一步跳过去。**

### 1.3 离散化使 `μ` 精确

`Repair.μ : α → ℕ` 必须是整数，而几何距离是 ℝ。
**用整数格**：`α := ℤ`，约束是「到达 0」，`fix k = k - sign k`。

| 项 | 取值 |
|:--|:--|
| `Sat k` | `k = 0` |
| `fix k` | `k - sign k`（每步靠近 1） |
| `μ k` | `|k|`（距离，整数） |

**这不是 `countdown` 的改名**：`countdown` 只处理非负，`fix k = k - 1`；
本节处理**双向**（负数也向 0 移动），`fix` 依赖符号。

### 1.4 步数界

`converges_within` 已经给出「`μ x` 步之内满足」。本节给出**具体的步数**：

```
|k| 步到达 0
```

**这是闭环的定量结论**：几何闭环需要 `|k|` 步。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `sign` | 符号函数（`ℤ → ℤ`） |
| `bidirRepair` | **双向逐步修复**（`μ = |k|`） |
| `bidir_steps` | **`|k|` 步到达** |
| `bidir_not_one_step` | **不是一步到解**（反例：`k = 5`） |
| `not_countdown` | 与 `countdown` **不同**（负数情形） |
| `multistep_geometric_exists` | **几何侧的多步见证存在** |

## 3. 边界

- 载体是 `ℤ`（一维整数格），不是 `Pt n`。
  **理由**：`μ : α → ℕ` 必须是整数，而 `Pt n` 上的距离是实数；
  要做 `Pt n` 版需要「上整」函数与它的算术，属另一层工作。**已登记。**
- 本节**不**声称这是唯一的构造。
  另一种是「每步移动 2」，步数约 `|k|/2`——**同样可做，本节选一步 1**。
- `bidir_not_one_step` 是**表达能力**的反例（存在需多步的点），
  不是 `Repair` 的反例。**两者的区别重要。**
-/
import Mathlib
import Lattice.Plugins.Core.Repair.Repair
import Lattice.Plugins.Core.Repair.RepairConvergence
import Lattice.Runtime.VerificationLoop

namespace Lattice.Geo

namespace MultistepLoop

open Lattice.Core

/-! ## 一、符号函数与逐步靠近 -/

/-- **符号函数**：正数给 1，负数给 -1，零给 0。 -/
def sign (k : ℤ) : ℤ :=
  if 0 < k then 1 else if k < 0 then -1 else 0

/-- **`fix` 的定义**：`k - sign k`。 -/
def step (k : ℤ) : ℤ := k - sign k

/-- **正数情形**：`0 < k` 时 `step k = k - 1` 且绝对值减一。 -/
theorem step_pos {k : ℤ} (h : 0 < k) : step k = k - 1 := by
  unfold step sign
  rw [if_pos h]

/-- **负数情形**：`k < 0` 时 `step k = k + 1` 且绝对值减一。 -/
theorem step_neg {k : ℤ} (h : k < 0) : step k = k + 1 := by
  unfold step sign
  rw [if_neg (by omega), if_pos h]
  ring

/-- **零情形**：`step 0 = 0`。 -/
theorem step_zero : step 0 = 0 := by
  unfold step sign
  decide

/-- **`step` 严格减小绝对值**（非零时）。 -/
theorem natAbs_step_lt {k : ℤ} (h : k ≠ 0) : (step k).natAbs < k.natAbs := by
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  · rw [step_neg hneg]
    omega
  · exact absurd hzero h
  · rw [step_pos hpos]
    omega

/-! ## 二、双向逐步修复 -/

/-- **双向逐步修复**：每步向 0 移动 1，正负都处理。

与 `countdown` 的区别：`countdown` 的 `fix k = k - 1` 只在非负上有意义；
本算子的 `fix` 依赖符号，负数向上走。 -/
def bidirRepair : Repair ℤ where
  Sat := fun k => k = 0
  fix := step
  μ := fun k => k.natAbs
  absorbs := by
    intro k hk
    subst hk
    exact step_zero
  decreases := by
    intro k hk
    exact natAbs_step_lt hk
  atomic := by
    intro k hk
    exact Int.natAbs_eq_zero.mp hk

/-! ## 三、步数：`|k|` 步到达 -/

/-- **`|k|` 步到达 0**。 -/
theorem bidir_steps (k : ℤ) :
    bidirRepair.Sat (bidirRepair.iterate (Int.natAbs k) k) :=
  RepairConvergence.converges_within bidirRepair k

/-! ## 四、不是一步到解 -/

/-- **不是一步到解**：存在点需要多于一步。

`k = 5` 时 `fix 5 = 4 ≠ 0`。⇒ **本算子展示了「迭代」，而不是「解析解」**。 -/
theorem bidir_not_one_step : ∃ k : ℤ, ¬ bidirRepair.Sat (bidirRepair.fix k) := by
  refine ⟨5, ?_⟩
  show step 5 ≠ 0
  rw [step_pos (by norm_num : (0 : ℤ) < 5)]
  norm_num

/-- **与 `countdown` 不同**：在负数上，`countdown` 的 `fix` 会停在 0（`0 - 1 = -1` 不是 0），
而本节算子的负数会**向上**走到 0。

⇒ **两个算子在 `ℤ` 上不是同一个**。 -/
theorem not_countdown : ∃ k : ℤ, bidirRepair.fix k ≠ k - 1 := by
  refine ⟨-3, ?_⟩
  show step (-3) ≠ -3 - 1
  rw [step_neg (by norm_num : (-3 : ℤ) < 0)]
  norm_num

/-! ## 五、结论 -/

/-- **几何侧的多步见证存在。**

汇总三条：`bidirRepair` 是 `Repair` 实例；`|k|` 步到达；且**不是一步到解**。

⇒ **条款 9 的缺口被部分关闭**：多步收敛不再只有 `Nat` 上的 `countdown`。 -/
theorem multistep_geometric_exists :
    (∀ k : ℤ, bidirRepair.Sat (bidirRepair.iterate (Int.natAbs k) k)) ∧
    (∃ k : ℤ, ¬ bidirRepair.Sat (bidirRepair.fix k)) ∧
    (∃ k : ℤ, bidirRepair.fix k ≠ k - 1) :=
  ⟨bidir_steps, bidir_not_one_step, not_countdown⟩

/-! ## `bidirRepair` 作为 `VerificationLoop` 的一个具体实例

`Runtime/VerificationLoop.lean` 定义了一个**抽象的**验证回路：它取一个 `Repair α` 与一个目标函数 `α → ℝ`，
然后证明回路会终止于满足状态。

**那个文件里全是抽象的定理；本节提供第一个**具体的**实例。**
**⇒ 「闭环」这一目标条款此前只有抽象载体（`VerificationLoop` 本身），现在有了一个跑得起来的具体回路。**

**为什么 `bidirRepair` 是这个位置的正确选择：**
**- 它的状态空间是 `ℤ`，因此目标函数可以是 `|k|`（到零的距离）——**度量是真的一维距离**；**
**- 它**双向**收敛：正数往下、负数往上，两者都以 `1` 的步长接近零；**
**- `bidir_steps` 已经证明它在 `|k|` 步内到达满足状态，因此回路的终止有一个**可算的界**。** -/

/-- **双向修正回路**：以 `bidirRepair` 为修正算子，以 `|k|` 为目标函数。

**=> 这是 `VerificationLoop` 的第一个具体实例：抽象回路的所有定理（终止、吸收、单调下降）现在都可以在这
个 `ℤ` 上的双向修正上**直接引用**。** -/
def bidirLoop : Lattice.Runtime.VerificationLoop ℤ :=
  { repair := bidirRepair
    objective := fun k => (k.natAbs : ℝ) }

/-- **抽象回路的终止定理在具体实例上成立。**

**`VerificationLoop.loop_end_sat` 说：任何回路的 `μ` 步之后都停在满足状态。**
**⇒ 本节把它用在 `bidirLoop` 上，得到「`bidirRepair` 在 `|k|` 步后满足」。**
**这个结论此前只能从 `bidir_steps` 直接读出；现在它也是抽象定理的一个**实例**，因此抽象层的任何改进都会
自动落到这个具体回路上。** -/
theorem bidirLoop_ends_sat (k : ℤ) :
    bidirLoop.repair.Sat (bidirLoop.run (bidirLoop.repair.μ k) k) :=
  Lattice.Runtime.VerificationLoop.loop_end_sat bidirLoop k

/-- **回路在已满足的状态上不移动。**

**=> `loop_absorbs` 的实例：`bidirRepair.Sat k` 时 `run 1 k = k`，即回路在不动点处是恒等。**
**这是「闭环」一词的精确含义在具体层面的表现：已经正确的东西不被改动。** -/
theorem bidirLoop_absorbs {k : ℤ} (h : bidirRepair.Sat k) :
    bidirLoop.run 1 k = k :=
  Lattice.Runtime.VerificationLoop.loop_absorbs bidirLoop h


end MultistepLoop

end Lattice.Geo
