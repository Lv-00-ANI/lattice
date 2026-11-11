import Mathlib
import Lattice.Core.CIC.ShiftSubstJointVar
import Lattice.Core.CIC.ShiftSubstTotal

/-!
# `subst j s t = t` 需要一个**比 `avoids j` 更强**的条件（阶段 5）

## 本轮先发现的事

**第 841 轮提出的选项 (b) 是「`t` 同时避开 `c` 与 `j`」。本轮按它动手，`var` 分支却失败，
而失败暴露了一件重要的事：**

**`avoids j (var n)` 只说 `n ≠ j`。当 `n > j` 时，`subst j s (var n)` 仍然**递减**：
`var (n - 1)`。**

**=> `avoids j t = true` **不足以**让 `subst j s t = t`。**

## 正确的条件

**要让 `subst j s t = t`，需要「`t` 的所有自由变量都 `< j`」——
这样它们既不会因 `= j` 触发替换，也不会因 `> j` 触发递减。**

**这是 de Bruijn 记法里标准的「`j` 是 `t` 的**上界**」条件，写作 `bounded j t`。**

## 为什么这个区分重要

**`avoids c`（第 837 轮）解决的是「律在 `var c` 处失效」；
它**不能**同时冒充「替换的不动点条件」——
两者的边界不同：`avoids` 排除**一个**下标，而 `subst` 的**递减**影响**所有**更大的下标。** -/

namespace Lattice.Core.CIC

/-- **`avoids` 不足以让 `subst` 成为不动点。**

**=> 取 `j = 0`、`n = 1`、`s = var 5`：`avoids 0 (var 1) = true`（因 `1 ≠ 0`），
但 `subst 0 (var 5) (var 1) = var 0`（因 `1 > 0` 触发递减）。**

**这条把「`avoids j` 与「替换不动点」不一样」写成可检查的否证。** -/
theorem avoids_not_enough_for_subst_fixpoint :
    avoids 0 (Term.var 1) = true ∧ subst 0 (.var 5) (.var 1) ≠ Term.var 1 := by
  refine ⟨by simp [avoids_var], ?_⟩
  intro h
  have h1 : subst 0 (.var 5) (Term.var 1) = Term.var 0 := by
    show (if (1 : ℕ) = 0 then Term.var 5
          else if (1 : ℕ) < 0 then Term.var 1 else Term.var (1 - 1)) = Term.var 0
    rw [if_neg (by omega : ¬ (1 : ℕ) = 0), if_neg (by omega : ¬ (1 : ℕ) < 0)]
  rw [h1] at h
  exact absurd h (by intro hh; injection hh; omega)

/-- **「`t` 的所有自由变量都 `< j`」：`subst j s t = t` 的正确条件。**

**=> 结构递归定义，与 `avoids` 平行，但用 `n < j` 而不是 `n ≠ j`；绑定子把 `j` 加一。** -/
def bounded (j : ℕ) : Term → Bool
  | .sort _ _ => true
  | .const _ => true
  | .var n => decide (n < j)
  | .app f a => bounded j f && bounded j a
  | .lam A b => bounded j A && bounded (j + 1) b
  | .pi A B => bounded j A && bounded (j + 1) B
  | .letE A t b => bounded j A && bounded j t && bounded (j + 1) b

/-- **`bounded j (var n)` 为真当且仅当 `n < j`。** -/
@[simp] theorem bounded_var (j n : ℕ) : bounded j (.var n) = decide (n < j) := rfl

/-- **`bounded j (var n)` 给出 `n < j`。** -/
theorem bounded_var_lt {j n : ℕ} (h : bounded j (.var n) = true) : n < j := by
  simp only [bounded_var] at h
  simpa using h

end Lattice.Core.CIC
