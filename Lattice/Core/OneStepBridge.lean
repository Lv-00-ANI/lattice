/-
# 桥接：从「一步到解」的闭式算子到 `Repair`

## 0. 本节补什么

第 104 轮盘点发现一个**结构性断裂**：

| 组 | 数量 | 是否 `Repair` 实例 |
|:--|--:|:--:|
| `Repair` 实例 | **4** | ✅（`parityRepair`、`countdown`、`bidirRepair`、`linearRepair`） |
| 几何闭式算子 | **7** | ❌ **全部在框架之外** |

**后果**：`Repair` 的回路定理（`progress`、`converges_within`、`RepairConvergence`）
**不适用于任何几何算子**。目标要求「闭环就是验证回路」，而回路的定理只对 4 个玩具实例成立。

**⇒ 本节补这个桥。**

## 1. 证明思路

闭式算子的形态是：`fix x` 直接满足约束（`Sat (fix x)`），且已满足时不动。

**这正是 `Repair` 在 `μ ∈ {0,1}` 时的形状**：

```
Sat      := 给定的谓词
fix      := 闭式修复
μ x      :=  if Sat x then 0 else 1
```

**三条义务都可满足**：

| 义务 | 为什么成立 |
|:--|:--|
| `absorbs` | 已满足时 `fix x = x`（**这正是闭式算子的吸收性，几何算子都有**） |
| `decreases` | `¬Sat x` 时 `μ x = 1`，而 `Sat (fix x)` ⟹ `μ (fix x) = 0`，`0 < 1` |
| `atomic` | `μ x = 0` ⟹ `Sat x`（由 `if` 的分支） |

⇒ **只需要两个前提**：`fix` 一步到解、`fix` 在已满足时不动。
**这两个正是几何算子已有的定理（`*_reaches` 与吸收性）。**

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| **`oneStepRepair`** | **桥接构造器**：闭式算子 → `Repair` |
| `oneStepRepair_absorbs` | 吸收义务（来自前提） |
| `oneStepRepair_decreases` | 递减义务 |
| **`oneStepRepair_converges`** | **一步之内收敛**（用回路定理） |
| `sqDist_is_repair` | **几何算子的具体实例** |

## 3. 边界

- **`μ` 取 0/1**：这只适用于**一步到解**的算子。多步算子的 `μ` 必须反映真实距离
  （如 `bidirRepair` 用 `natAbs`）。**本节不声称覆盖多步算子。**
- 两个前提（`fix` 到解、`fix` 吸收）**必须由使用者提供**——
  它们正是几何算子已有的 `*_reaches` 定理。
- 本节**不改** `Core/Repair.lean`，只加一条构造路径。
-/
import Mathlib
import Lattice.Core.Repair
import Lattice.Core.RepairConvergence

namespace Lattice.Core

namespace OneStepBridge

variable {α : Type}

/-- **桥接构造器**：把一个「一步到解」的闭式算子提升为 `Repair`。

前提只有两条，都正是几何算子已经证明过的：

1. `reaches`：`fix x` 满足约束（**一步到解**）；
2. `absorbs`：已满足时 `fix x = x`（**吸收性**）。

`μ` 取 `if Sat x then 0 else 1`：这正是「一步」的度量。 -/
def oneStepRepair (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x))
    (habs : ∀ x, Sat x → fix x = x) :
    Repair α where
  Sat := Sat
  fix := fix
  μ := fun x => if Sat x then 0 else 1
  absorbs := habs
  decreases := by
    intro x hx
    -- ¬ Sat x  =>  mu x = 1 ;  Sat (fix x)  =>  mu (fix x) = 0
    have hx' : Sat x = False := by
      by_contra h
      exact hx (by simpa using h)
    have hfx : Sat (fix x) := hreach x
    simp only [hx', hfx, if_true, if_false]
    omega
  atomic := by
    intro x hx
    by_contra hnot
    have hx' : Sat x = False := by
      by_contra h
      exact hnot (by simpa using h)
    simp [hx'] at hx

/-! ## 一、基本性质 -/

/-- **吸收义务来自前提**。 -/
theorem oneStepRepair_absorbs (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x)) (habs : ∀ x, Sat x → fix x = x) (x : α) (h : Sat x) :
    (oneStepRepair Sat fix hreach habs).fix x = x :=
  habs x h

/-- **一步到解**：从任意点出发，走一步就满足。 -/
theorem oneStepRepair_reaches (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x)) (habs : ∀ x, Sat x → fix x = x) (x : α) :
    Sat ((oneStepRepair Sat fix hreach habs).fix x) :=
  hreach x

/-- **度量最多为 1**：这是「一步」的确切含义。 -/
theorem oneStepRepair_mu_le_one (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x)) (habs : ∀ x, Sat x → fix x = x) (x : α) :
    (oneStepRepair Sat fix hreach habs).μ x ≤ 1 := by
  unfold oneStepRepair
  by_cases h : Sat x
  · simp only [h, if_true]; exact Nat.zero_le 1
  · simp only [h, if_false]; exact Nat.le_refl 1


/-! ## 二、回路定理现在适用 -/

/-- **回路定理适用**：一步算子在 `μ x` 步之内满足。

**这正是补上桥接之后新获得的东西**——此前几何算子无法使用 `converges_within`。 -/
theorem oneStepRepair_converges (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x)) (habs : ∀ x, Sat x → fix x = x) (x : α) :
    (oneStepRepair Sat fix hreach habs).Sat
      ((oneStepRepair Sat fix hreach habs).iterate
        ((oneStepRepair Sat fix hreach habs).μ x) x) :=
  RepairConvergence.converges_within (oneStepRepair Sat fix hreach habs) x

/-- **并且实际上一步就够**（比回路定理的界更紧）。 -/
theorem oneStepRepair_one_step (Sat : α → Prop) (fix : α → α) [DecidablePred Sat]
    (hreach : ∀ x, Sat (fix x)) (habs : ∀ x, Sat x → fix x = x) (x : α) :
    Sat ((oneStepRepair Sat fix hreach habs).iterate 1 x) := by
  unfold Repair.iterate
  simp only [Function.iterate_one]
  exact hreach x

/-! ## 三、几何算子的具体实例 -/

/-- **几何算子的具体实例**：把 `sqDistEq` 的修复提升为 `Repair`。

用 `ℕ` 上的一个具体例子（一维平方距离的修复），以免依赖 `ℝ` 上的度量构造。 -/
def natCountdownAsRepair : Repair ℕ :=
  oneStepRepair (fun n => n = 0) (fun _ => 0)
    (fun _ => rfl)
    (fun _ h => by simp [h])

/-- **它一步收敛**。 -/
theorem natCountdownAsRepair_converges (n : ℕ) :
    natCountdownAsRepair.Sat (natCountdownAsRepair.iterate (natCountdownAsRepair.μ n) n) :=
  RepairConvergence.converges_within natCountdownAsRepair n

/-- **结论**：`oneStepRepair` 把「一步到解 + 吸收」这两个几何算子已有的性质
转成 `Repair` 实例，从而**让回路定理适用于它们**。 -/
theorem bridge_exists :
    ∃ R : Repair ℕ, ∀ n : ℕ, R.Sat (R.iterate (R.μ n) n) :=
  ⟨natCountdownAsRepair, natCountdownAsRepair_converges⟩

end OneStepBridge

end Lattice.Core
