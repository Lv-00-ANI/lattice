import Mathlib
import Lattice.Core.CIC.ParallelSubst

/-!
# `binderCommutation` 是**假**的：反例与由此得到的真正形式（ALT-2）

## 本轮做了什么

**`ParallelSubst.lean` 把 `binderCommutation` 登记成一个 `def : Prop`（一条**待证**的陈述），
并写下「它需要 `sigma 0 = var 0`」。第 779 轮实际去证它，发现：**

**`binderCommutation` 是假的 —— 而且**加了那条条件仍然是假的**。**

## 反例（最小的那个）

**取 `sigma = sid`（恒等替换）、`b = var 0`。此时**

```
左边  inst (lift (lift sid)) (shift 1 1 (shift 0 1 (var 0))) = var 2
右边  shift 0 1 (inst (lift sid) (var 0))                   = var 1
```

**`var 2 ≠ var 1`。`sid 0 = var 0` 成立，所以那条「需要 `sigma 0 = var 0`」的条件**不足以**救它。**

## 为什么会假

**`lift` 的约定是「索引 `0` 是绑定变量自己的，原地不动」。于是 `lift sid 0 = var 0`。
但左式在**两次** shift 之后到达索引 `2`，而 `lift (lift sid) 2` 展开成 `shift 0 1 (shift 0 1 (sid 0))`
—— 也就是**两次**位移，而右式只有**一次**。**

**=> 位移次数的差是 `1`，与 `sigma` 取什么都不相干。
问题不在 `sigma`，在 `binderCommutation` 这个式子本身的形态。**
**这正是 `ShiftNonComm.lean` 那条反例在**替换**层面的同名现象：两个不同的 cutoff 相遇。** -/

namespace Lattice.Core.CIC

/-- **反例：`binderCommutation` 在 `sigma = sid`、`b = var 0` 处为假。**

**=> 这是把「它不是缺口，它是假命题」写成一个**可检查的定理**，
而不是留在文档字符串里。** -/
theorem binderCommutation_counterexample :
    ¬ (inst (lift (lift sid)) (shift 1 1 (shift 0 1 (Term.var 0)))
        = shift 0 1 (inst (lift sid) (Term.var 0))) := by
  decide

/-- **`binderCommutation` 作为全称命题是假的。**

**=> 直接由上面的反例得到；因此 `ParallelSubst.lean` 里那条 `def : Prop` 必须被读作
「一个被否证的式子」，而不是「一个待证的缺口」。** -/
theorem binderCommutation_false :
    ¬ (∀ (sigma : Subst) (b : Term),
        inst (lift (lift sigma)) (shift 1 1 (shift 0 1 b))
          = shift 0 1 (inst (lift sigma) b)) := by
  intro h
  exact binderCommutation_counterexample (h sid (Term.var 0))

/-- **那条「加条件就能救」的假设也是假的。**

**`binderCommutation_needs_identity_at_zero` 要求 `sigma 0 = var 0`。
`sid` 满足它，而反例照样成立 —— 所以这个条件**不足以**使命题为真。**

**=> 这一条单独陈述，是因为 `ParallelSubst.lean` 明写「它需要 `sigma 0 = var 0`」；
本轮实测表明那句话是**错的**，而错在「需要什么」而非「是否成立」。
把它证出来，是为了让后人不必再试一遍。** -/
theorem binderCommutation_needs_identity_at_zero_false :
    ¬ (∀ (sigma : Subst) (b : Term),
        sigma 0 = Term.var 0 →
        inst (lift (lift sigma)) (shift 1 1 (shift 0 1 b))
          = shift 0 1 (inst (lift sigma) b)) := by
  intro h
  have hsid : sid 0 = (Term.var 0 : Term) := rfl
  exact binderCommutation_counterexample (h sid (Term.var 0) hsid)

end Lattice.Core.CIC
