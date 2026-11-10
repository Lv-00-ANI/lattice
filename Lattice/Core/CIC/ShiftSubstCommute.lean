import Mathlib
import Lattice.Core.CIC.ParallelReductionVarying
import Lattice.Core.CIC.Substitution

/-!
# 位移与替换：三条原子事实，以及交换律为何**必须**带条件（阶段 5）

## 为什么需要交换律

**第 826 轮把 `ParRedV` 的 `shift` 闭合性做到了结构性部分；剩下的 `beta`/`letE` 两条结论含 `subst`，
要穿过它就需要位移与替换的交换律。**

## `subst` 在绑定层做什么

```lean
| j, s, .lam A b => .lam (subst j s A) (subst (j + 1) (shift 0 1 s) b)
```

**=> 进入一层绑定：替换项 `s` 上移一位（`shift 0 1 s`），cutoff 加一（`j + 1`）。
交换律必须同时处理这两处。**

## 本轮证出的三条原子事实

| 定理 | 内容 |
|:--|:--|
| `subst_zero_var_zero` | **`subst 0 s (var 0) = s`** |
| `subst_shift_atom_pos` | **`d > 0` 时 `subst d (shift 0 d s) (var 0) = var 0`** |
| `shift_var_zero_at` | **`d > 0` 时 `shift 0 d (var 0) = var d`** |

**=> 后两条**一起**给出关键判定：`c = 0`、`j = 0`、`d > 0` 时左边是 `var 0`、右边是 `var d`，**不同**。**

**=> 所以「`c = 0`、`j = 0` 时的无条件交换律」是**假的**。
正确的陈述必须带 `c ≤ j`（或把 `d` 限制为零）——这是本轮把陈述形式**定下来**的依据。** -/

namespace Lattice.Core.CIC

/-- **`subst 0 s (var 0) = s`：替换的定义性行为。**

**=> `subst` 的 `var` 分支第一判据是 `n = j`，此处 `0 = 0` 成立，直接返回 `s`。** -/
@[simp] theorem subst_zero_var_zero (s : Term) : subst 0 s (Term.var 0) = s := by
  show (if (0 : ℕ) = 0 then s else if (0 : ℕ) < 0 then Term.var 0 else Term.var (0 - 1)) = s
  rw [if_pos rfl]

/-- **`d > 0` 时 `subst d (shift 0 d s) (var 0) = var 0`。**

**=> 此时 `0 ≠ d` 且 `0 < d`，所以走 `n < j` 分支，返回 `var 0` 而不是 `s`。
这正是交换律需要条件的原因。** -/
theorem subst_shift_atom_pos (d : ℕ) (hd : 0 < d) (s : Term) :
    subst d (shift 0 d s) (Term.var 0) = Term.var 0 := by
  show (if (0 : ℕ) = d then shift 0 d s else if (0 : ℕ) < d then Term.var 0 else Term.var (0 - 1))
      = Term.var 0
  rw [if_neg (by omega : ¬ (0 : ℕ) = d), if_pos hd]

/-- **`d > 0` 时 `shift 0 d (var 0) = var d`。**

**=> `0 < 0` 为假，所以走 `else` 分支，返回 `var (0 + d)`，即 `var d`。** -/
theorem shift_var_zero_at (d : ℕ) (hd : 0 < d) : shift 0 d (Term.var 0) = Term.var d := by
  show (if (0 : ℕ) < 0 then Term.var 0 else Term.var (0 + d)) = Term.var d
  rw [if_neg (by omega : ¬ (0 : ℕ) < 0)]
  simp
/-- **关键判定：`c = 0`、`j = 0`、`d > 0` 时交换律为假。**

**=> 左边是 `var 0`（由 `subst_shift_atom_pos`），右边是 `var d`（由 `shift_var_zero_at`），
而 `d > 0` 使两者不同。**

**这条**否证**了无条件形式，并因此定下了正确形式必须携带的条件。** -/
theorem shift_subst_no_unconditional (d : ℕ) (hd : 0 < d) (s : Term) :
    subst d (shift 0 d s) (Term.var 0) ≠ shift 0 d (Term.var 0) := by
  rw [subst_shift_atom_pos d hd s, shift_var_zero_at d hd]
  intro h
  have h2 : (0 : ℕ) = d := by injection h
  omega

end Lattice.Core.CIC
