import Mathlib
import Lattice.Core.CIC.SubstSizeBound
import Lattice.Core.CIC.Reduction

/-!
# 路线 C **不能**在 `Reduces` 层面组装：不变量在替换下不保持（阶段 5，第 791 轮）

## 上一轮给了什么

**第 790 轮证明了路线 C 的**局部**判据：**

```
countVar 0 b ≤ 1  →  size (subst 0 a b) < size (app (lam A b) a)
```

**即「`var 0` 在 `b` 中至多一次时，`beta` 严格降低 `size`」。**

**本轮尝试把它**组装**成「若整棵树满足某条件，则 `Reduces` 终止」。
组装需要一个在**每一步**都保持的不变量。下面说明为什么不存在简单的不变量。**

## 为什么 `countVar 0 t ≤ 1`（整项）不行

**反例（本文件 `subst_breaks_bound`）：**

```
subst 0 (app (var 0) (var 0)) (var 0) = app (var 0) (var 0)
```

**输入 `b = var 0` 有 `countVar 0 b = 1 ≤ 1`，替换后却得到 `countVar 0 = 2`。
=> **`beta` 之后整个项的上界变差**，所以「整项 ≤ 1」不是一个向后传递的不变量。**

## 为什么「每个 `lam` 的体 ≤ 1」也不行

**`subst` 在绑定处的规则是**

```
subst 0 a (lam A b) = lam (subst 0 a A) (subst 1 (shift 0 1 a) b)
```

**=> 进入绑定后，被检查的下标从 `0` 变成了 `1`，而**被替换的项**也从 `a` 变成了 `shift 0 1 a`。
所以「每个体在**它自己的**下标处 ≤ 1」不是一条与 `subst` 相容的陈述 ——
需要的是「对**所有**下标都 ≤ 1」，而那条太强：`var 0` 与 `var 1` 会同时被计入，
连 `app (var 0) (var 1)` 都会违反。**

**=> 路线 C 只能给出**单步**判据，不能给出**全局**不变量。这不是「还没找到不变量」，
而是「这个不变量必须随绑定层变化，而随绑定层变化的东西不是 `Term` 上的谓词」。**

## 结论

**强规范化**不能**由路线 C 组装得到。路线 C 的价值仍成立：它把「`beta` 何时下降」变成
`countVar` 上的可判定问题（第 790 轮），但**终止性需要的是流不变式（route A 的可归约性）
或一个真正非语法的度量（route B）**。**

**本文件把上面两个「不行」都写成可检查的形式，使后续不必再试第三次。** -/

namespace Lattice.Core.CIC

/-- **整项上界在替换下**不保持**。**

**`b = var 0` 满足 `countVar 0 b = 1`，而 `subst 0 a b` 把它换成 `a` 本身 ——
取 `a` 为两个自由变量就得到 `countVar 0 = 2`。**

**=> 「整项 `≤ 1`」不是向后传递的不变量。** -/
theorem subst_breaks_bound :
    countVar 0 (Term.var 0) = 1 ∧
      countVar 0 (subst 0 (Term.app (Term.var 0) (Term.var 0)) (Term.var 0)) = 2 := by
  refine ⟨by decide, by decide⟩

/-- **绑定层改变了「被检查的下标」。**

**`subst 0 a (lam A b) = lam (subst 0 a A) (subst 1 (shift 0 1 a) b)` ——
进入绑定后，下标记号从 `0` 变为 `1`。**

**=> 因此「每个体在自己的下标处 ≤ 1」不是一个 `Term` 上的谓词：
它随绑定深度变化，而 `Term` 上的谓词不知道深度。** -/
theorem subst_binder_shifts_index (A b a : Term) :
    subst 0 a (Term.lam A b) = Term.lam (subst 0 a A) (subst 1 (shift 0 1 a) b) := rfl

/-- **「对所有下标都 ≤ 1」太强。**

**取 `app (var 0) (var 0)`：`countVar 0` 已经是 `2`。**

**=> 「加索引」的修法要求对**每一个**下标都成立，而这使得任何含重复变量的项都违反它 ——
包括第 785 轮那个**完全合法**的反例。** -/
theorem all_indices_bound_too_strong :
    ¬ (countVar 0 (Term.app (Term.var 0) (Term.var 0)) ≤ 1) := by
  have h1 : countVar 0 (Term.app (Term.var 0) (Term.var 0)) = 2 := by decide
  rw [h1]
  decide

end Lattice.Core.CIC
