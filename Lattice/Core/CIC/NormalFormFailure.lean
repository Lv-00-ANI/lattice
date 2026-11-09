import Mathlib
import Lattice.Core.CIC.Reduction
import Lattice.Core.CIC.TermSize

/-!
# 强规范化对**任意** `DefEnv` 是假的：`delta` 给出无限归约（阶段 5，`normal_form`）

## 为什么这一节必须先写

**第 785 轮证明 `size` 对 `beta` 递增。那说明「语法大小」这条路走不通，
但**没有**说明「正规形存在」本身是否成立。**

**本轮先回答后者。答案是否定的，而且是最平凡的那种否定：**

**`Step` 的 `delta` 构造子是**

```lean
| delta (k : ℕ) (body : Term) (h : E k = some body) : Step E (.const k) body
```

**`E : DefEnv` 是一个**任意**函数（`ℕ → Option Term`），没有任何「定义必须良基」的约束。
于是取 `E := fun _ => some (.const 0)`：**

```
const 0  --delta-->  const 0  --delta-->  const 0  --delta-->  ...
```

**`=> `Reduces E` 在这个 `E` 下有无限链，因此 `normal_form` 对任意 `E` **不成立**。**

## 这不是缺陷，是关于适用范围的事实

**同一条 `Step` 系统在**良基** `E` 下才可能强规范化。`Reduction.lean` 的 `DefEnv`
没有把「良基」写进类型，因此**

- **任何「`∀ E, ∃ nf`」形式的陈述都是假的，不应去证；**
- **正确的陈述必须带一个 `E` 上的良基性前提**（例如 `E` 的 `const` 深度有界），
  **而那正是 T2 的 `Modulus` / `steps` 所预备的东西。**

**下面两条定理把上面的论证写成可检查的形式：一条给出具体的循环 `E`，
另一条给出它的无限归约链。** -/

namespace Lattice.Core.CIC

/-- **一个自我循环的 `DefEnv`：每个常量都定义为 `const 0`。**

**=> 这是「定义环境」这个类型所能表达的**最坏情况**，而 `DefEnv` 的类型没有排除它。** -/
def selfLoopEnv : DefEnv := fun _ => some (Term.const 0)

/-- **`selfLoopEnv` 在每个下标上返回 `const 0`。** -/
@[simp] theorem selfLoopEnv_apply (k : ℕ) : selfLoopEnv k = some (Term.const 0) := rfl

/-- **`selfLoopEnv` 下有一步归约：`const 0 → const 0`。**

**=> 由 `delta` 构造子直接给出。** -/
theorem selfLoop_step : Step selfLoopEnv (Term.const 0) (Term.const 0) :=
  Step.delta 0 (Term.const 0) rfl

/-- **`selfLoopEnv` 下从 `const 0` 出发的**唯一**步进目标是 `const 0`。**

**=> 做成独立引理，因为下面关于 `Reduces` 的归纳需要它作为**一步**的形式。** -/
theorem selfLoop_step_eq {t : Term} (h : Step selfLoopEnv (Term.const 0) t) :
    t = Term.const 0 := by
  cases h with
  | delta k body he =>
      simp only [selfLoopEnv, Option.some.injEq] at he
      exact he.symm

/-- **`selfLoopEnv` 下有任意多步归约：`const 0` 归约到自身。**

**=> 对任意 `n`，都存在一条长度 `n` 的归约链。** -/
theorem selfLoop_reduces_n (n : ℕ) : ReducesWithin selfLoopEnv n (Term.const 0) (Term.const 0) := by
  induction n with
  | zero => exact ReducesWithin.refl (Term.const 0)
  | succ k ih => exact ReducesWithin.step selfLoop_step ih

/-- **`selfLoopEnv` 下 `const 0` 没有正规形。**

**陈述：不存在一个 `t`，使 `const 0` 归约到 `t` 且 `t` 不能再走一步。**

**=> 因为 `const 0` 每一步都能再走一步（`selfLoop_step` 是自环），
所以任何到达的 `t` 都只能是 `const 0` 本身，而它不是正规形。**

**=> 这就是「强规范化对任意 `DefEnv` 为假」的核心反例。** -/
theorem selfLoop_no_normal_form :
    ¬ ∃ t, Reduces selfLoopEnv (Term.const 0) t ∧ (∀ u, ¬ Step selfLoopEnv t u) := by
  rintro ⟨t, hred, hnf⟩
  -- The crux, stated so the `Reduces` induction keeps its index variable: from `const 0`,
  -- every single step lands on `const 0`, hence every reachable term IS `const 0`.
  have key : ∀ {a c : Term}, Reduces selfLoopEnv a c → a = Term.const 0 → c = Term.const 0 := by
    intro a c hr
    induction hr with
    | refl => intro ha; exact ha
    | step h _ ih =>
        intro ha
        subst ha
        exact ih (selfLoop_step_eq h)
  have ht : t = Term.const 0 := key hred rfl
  subst ht
  exact hnf (Term.const 0) selfLoop_step

end Lattice.Core.CIC
