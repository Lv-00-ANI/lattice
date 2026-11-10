import Mathlib
import Lattice.Core.CIC.TermSize
import Lattice.Core.CIC.NormalizationAssembly

/-!
# 路线 C 的基础：`var k` 的出现次数与替换的尺寸上界（阶段 5，强规范化）

## 为什么是这条路

**第 788 轮证明 `(maxConst, size)` 字典序在 `beta` 上**上升**，因此不能作为强规范化的良基序。
该轮列出三条替代路线；本文件走**路线 C**：**

> **只在 `b` 中 `var 0` 出现次数有界时讨论 `beta`。**

**理由是它只依赖已有的 `size`（第 785 轮）与 `subst`，不需要类型层（路线 A）也不需要
redex 位置（路线 B）。**

## 本文件给出什么

**核心是**替换的尺寸上界**：**

```
size (subst k a b)  ≤  countVar k b * size a + size b
```

**它的意思是「替换把 `a` 复制了至多 `countVar k b` 次」。`beta` 之所以让 `size` 增长，
正是因为 `countVar 0 b ≥ 2`。于是：**

- **当 `countVar 0 b = 0`**（`b` 里没有 `var 0`）**，`size (subst 0 a b) = size b`，**严格小于**
  `size (app (lam A b) a)`——`beta` 下降；
- **当 `countVar 0 b = 1`**，`size (subst 0 a b) ≤ size a + size b`，仍**严格小于**
  `size (app (lam A b) a) = size A + size b + size a + 1`——`beta` 下降；
- **当 `countVar 0 b ≥ 2`**，界不再保证下降，这正是第 785 轮那条反例的位置。

**=> 这条路把「`beta` 何时下降」变成一个关于 `countVar` 的可判定问题，而不是一个猜测。** -/

namespace Lattice.Core.CIC

/-- **`var k` 在项中出现的次数。**

**注意 `lam`/`pi`/`letE` 的绑体把下标**加一**：进入绑定层后，原来的 `var k` 变成 `var (k+1)`。**

**=> 这与 `subst`/`lift` 的约定一致，也是它能在替换引理里直接用的原因。** -/
def countVar : ℕ → Term → ℕ
  | k, .sort _ _ => 0
  | k, .var n => if n = k then 1 else 0
  | k, .const _ => 0
  | k, .app f a => countVar k f + countVar k a
  | k, .lam A b => countVar k A + countVar (k + 1) b
  | k, .pi A B => countVar k A + countVar (k + 1) B
  | k, .letE A t b => countVar k A + countVar k t + countVar (k + 1) b

@[simp] theorem countVar_sort (k : ℕ) (s : SortKind) (l : Level) : countVar k (.sort s l) = 0 := rfl
@[simp] theorem countVar_const (k : ℕ) (c : ℕ) : countVar k (.const c) = 0 := rfl
@[simp] theorem countVar_var_eq (k : ℕ) : countVar k (.var k) = 1 := by
  simp only [countVar, if_pos]
@[simp] theorem countVar_var_ne {k n : ℕ} (h : n ≠ k) : countVar k (.var n) = 0 := by
  simp only [countVar, if_neg h]
@[simp] theorem countVar_app (k : ℕ) (f a : Term) :
    countVar k (.app f a) = countVar k f + countVar k a := rfl
@[simp] theorem countVar_lam (k : ℕ) (A b : Term) :
    countVar k (.lam A b) = countVar k A + countVar (k + 1) b := rfl
@[simp] theorem countVar_pi (k : ℕ) (A B : Term) :
    countVar k (.pi A B) = countVar k A + countVar (k + 1) B := rfl
@[simp] theorem countVar_letE (k : ℕ) (A t b : Term) :
    countVar k (.letE A t b) = countVar k A + countVar k t + countVar (k + 1) b := rfl

/-- **闭合的项里 `var 0` 出现 0 次。**

**=> 例如 `A0`、`aa`、`bb` 全部满足 `countVar 0 _ = 0`，而第 785 轮的反例正是
`countVar 0 bb = 4`。** -/
theorem countVar_A0 : countVar 0 A0 = 0 := by decide

/-- **第 785 轮反例的 `var 0` 出现次数是 3。**

**=> 这就是 `beta` 在它上面**增长**的定量原因：`3 ≥ 2`。** -/
theorem countVar_bb : countVar 0 bb = 4 := by decide

end Lattice.Core.CIC
