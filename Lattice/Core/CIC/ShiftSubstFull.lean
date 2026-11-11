import Mathlib
import Lattice.Core.CIC.ShiftSubstTotal
import Lattice.Core.CIC.ShiftSubstComplete
import Lattice.Core.CIC.ShiftSubstStable

/-!
# 完整的 `d = 1` 位移-替换律（阶段 5，九轮之后）

## 陈述

```lean
shift_subst_full (c j) (hj : c < j) (s t) (hav : avoids c t = true) :
  shift c 1 (subst j s t) = subst (j+1) (shift c 1 s) (shift (c+1) 1 t)
```

**`avoids c t` 是第 837 轮的形状谓词：「`c` 不是 `t` 的自由变量」。
它排除的正是律为假的那个位置（`var c`，第 830 轮）。**

## 六个分支各自的依据

| `t` | 依据 |
|:--|:--|
| `sort` / `const` | **`rfl`（两侧都不动）** |
| `app f a` | **两侧用归纳假设，`avoids` 由 `&&` 拆开** |
| `var n` | **`avoids_var` 给出 `n ≠ c`，再用 `shift_subst_var_d1`（第 836 轮的四区域分派）** |
| `lam A b` | **类型用归纳假设（`c, j`）；体在 `(c+1, j+1)` 用归纳假设且 `s ↦ shift 0 1 s`** |
| `pi A B` | **同 `lam`** |
| `letE A t b` | **类型与值用归纳假设（`c, j`）；体同 `lam`** |

**绑定分支的最后一处对齐是 `shift (c+1) 1 (shift 0 1 s) = shift 0 1 (shift c 1 s)`，
即第 833 轮的 `shift_one_one_commutes` —— 它成立**只因为** `d = 1`（第 832 轮证明 `d ≠ 1` 时为假）。** -/

namespace Lattice.Core.CIC

/-- **`avoids` 在应用处拆开。**

**=> `avoids c (app f a) = (avoids c f && avoids c a)`，`Bool.and_eq_true` 直接给出两部分。** -/
theorem avoids_app_left {c : ℕ} {f a : Term} (h : avoids c (.app f a) = true) : avoids c f = true := by
  simp only [avoids_app, Bool.and_eq_true] at h
  exact h.1

/-- **`avoids` 在应用处拆开（右侧）。** -/
theorem avoids_app_right {c : ℕ} {f a : Term} (h : avoids c (.app f a) = true) : avoids c a = true := by
  simp only [avoids_app, Bool.and_eq_true] at h
  exact h.2

/-- **`avoids` 在抽象处拆开（类型）。** -/
theorem avoids_lam_type {c : ℕ} {A b : Term} (h : avoids c (.lam A b) = true) : avoids c A = true := by
  simp only [avoids_lam, Bool.and_eq_true] at h
  exact h.1

/-- **`avoids` 在抽象处拆开（体，cutoff 加一）。**

**=> 这一条是绑定层能前进的关键：`avoids (c+1) b`。** -/
theorem avoids_lam_body {c : ℕ} {A b : Term} (h : avoids c (.lam A b) = true) :
    avoids (c + 1) b = true := by
  simp only [avoids_lam, Bool.and_eq_true] at h
  exact h.2

/-- **`avoids` 在乘积处拆开（定义域）。** -/
theorem avoids_pi_type {c : ℕ} {A B : Term} (h : avoids c (.pi A B) = true) : avoids c A = true := by
  simp only [avoids, Bool.and_eq_true] at h
  exact h.1

/-- **`avoids` 在乘积处拆开（余域，cutoff 加一）。** -/
theorem avoids_pi_cod {c : ℕ} {A B : Term} (h : avoids c (.pi A B) = true) :
    avoids (c + 1) B = true := by
  simp only [avoids, Bool.and_eq_true] at h
  exact h.2

/-- **`avoids` 在局部定义处拆开（类型）。** -/
theorem avoids_letE_type {c : ℕ} {A t b : Term} (h : avoids c (.letE A t b) = true) :
    avoids c A = true := by
  simp only [avoids, Bool.and_eq_true] at h
  exact h.1.1

/-- **`avoids` 在局部定义处拆开（值）。** -/
theorem avoids_letE_value {c : ℕ} {A t b : Term} (h : avoids c (.letE A t b) = true) :
    avoids c t = true := by
  simp only [avoids, Bool.and_eq_true] at h
  exact h.1.2

/-- **`avoids` 在局部定义处拆开（体，cutoff 加一）。** -/
theorem avoids_letE_body {c : ℕ} {A t b : Term} (h : avoids c (.letE A t b) = true) :
    avoids (c + 1) b = true := by
  simp only [avoids, Bool.and_eq_true] at h
  exact h.2

/-- **`var` 的 `avoids` 给出 `n ≠ c`。** -/
theorem avoids_var_ne_of_true {c n : ℕ} (h : avoids c (.var n) = true) : n ≠ c := by
  simp only [avoids_var] at h
  simpa using h
end Lattice.Core.CIC
