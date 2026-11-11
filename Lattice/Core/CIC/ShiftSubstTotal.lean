import Mathlib
import Lattice.Core.CIC.ShiftSubstAbove
import Lattice.Core.CIC.ShiftSubstStable

/-!
# `d = 1` 位移-替换律：完成陈述所需的形状前提（阶段 5）

## 八轮之后，还差什么

**`var` 分支的四个区域（第 829/830/831/835 轮）已全部处理，绑定层的路径也已验证（第 834 轮）。
剩下的障碍是：律在 `n = c` 处**为假**（第 830 轮），而那是**项内部**的一个位置，
无法作为整条定理的全局假设。**

## 正确做法：限制 `t` 的形状

**排除「`t` 的某个自由变量恰好是 `c`」这一情形，律就能对 `t` 归纳。
在 de Bruijn 记法下这是：**`c` 不是 `t` 的自由变量**。**

**绑定层自动保持它：`c` 与项内下标同时加一，所以「不含 `c`」在 `lam` 下变成「不含 `c+1`」，
正是归纳假设所需的形式。**

## 本文件给出谓词与前两条性质

**`Avoids c t`：`t` 不含自由变量 `c`。定义对 `Term` 的结构递归给出，
`var n` 要求 `n ≠ c`；`lam`/`pi`/`letE` 的体在 `c+1` 处要求，其余在 `c` 处。** -/

namespace Lattice.Core.CIC

/-- **项 `t` 不含自由变量 `c`。**

**=> 结构递归定义（不是归纳族）：`var n` 要求 `n ≠ c`；绑定子把 `c` 加一。
用 `Bool` 值使定义总化，便于在条件里直接使用。** -/
def avoids (c : ℕ) : Term → Bool
  | .sort _ _ => true
  | .const _ => true
  | .var n => decide (n ≠ c)
  | .app f a => avoids c f && avoids c a
  | .lam A b => avoids c A && avoids (c + 1) b
  | .pi A B => avoids c A && avoids (c + 1) B
  | .letE A t b => avoids c A && avoids c t && avoids (c + 1) b

/-- **`avoids c (var n)` 为真当且仅当 `n ≠ c`。**

**=> 直接展开定义；`decide` 与 `Bool` 的 `true` 判定一致。** -/
@[simp] theorem avoids_var (c n : ℕ) : avoids c (.var n) = decide (n ≠ c) := rfl

/-- **任何宇宙都不含自由变量。** -/
@[simp] theorem avoids_sort (c : ℕ) (k : SortKind) (l : Level) : avoids c (.sort k l) = true := rfl

/-- **任何常量都不含自由变量。** -/
@[simp] theorem avoids_const (c : ℕ) (k : ℕ) : avoids c (.const k) = true := rfl

/-- **应用不含 `c` 当且仅当两侧都不含。** -/
@[simp] theorem avoids_app (c : ℕ) (f a : Term) :
    avoids c (.app f a) = (avoids c f && avoids c a) := rfl

/-- **抽象不含 `c` 当且仅当类型不含 `c` 且体不含 `c+1`。**

**=> 体那一处的 `c + 1` 正是绑定层的加一，也是第 832 轮那次否证所在的 cutoff 差。** -/
@[simp] theorem avoids_lam (c : ℕ) (A b : Term) :
    avoids c (.lam A b) = (avoids c A && avoids (c + 1) b) := rfl

end Lattice.Core.CIC
