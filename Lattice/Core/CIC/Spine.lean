import Mathlib
import Lattice.Core.CIC.NeutralClosed
import Lattice.Core.CIC.ReductionOriented

/-!
# 中性项的脊分解：`Neutral t` 就是「`var n` 套一层应用脊」（阶段 5，进展定理）

## 本轮先否掉了一个诱人的猜想

**自然的想法是：中性项**能步进**（沿参数位置归约到底），于是进展定理可以走「中性 ⟹ 步进」。
本轮第一步就把它否掉了：**

```lean
Neutral (.app (Term.var n) a)        -- 成立，由 Neutral.app (Neutral.var n)
```

**而 `app (var n) a` **不能步进** —— `var` 永不步进（`no_step_var`），所以 `appL` 不触发；
`var` 不是 `lam`，`beta` 不触发。**

**=> 「中性 ⟹ 能步进」是**假**的。**

## 正确的刻画：脊分解

**中性项的真实形状是「一个变量套上一层应用脊」：**

```lean
def spine : Term -> Term × List Term
  | .app f a => ((spine f).1, (spine f).2 ++ [a])
  | t        => (t, [])
```

**并且**

```lean
neutral_spine_head {t} (h : Neutral t) : exists n args, spine t = (var n, args)
```

**=> 中性项 = `var n` 应用到一串参数。这是它**卡住**的确切形式，
也是进展定理里「中性项的头部是变量」这句的真正含义。** -/

namespace Lattice.Core.CIC

/-- **项的脊分解：`(头, 参数列表)`。**

**`app f a` 的脊是 `f` 的脊把 `a` 追加到参数末尾；其余构造子自成一节。
=> 因此 `spine (app (app (var n) a) b) = (var n, [a, b])`。** -/
def spine : Term → Term × List Term
  | .app f a => ((spine f).1, (spine f).2 ++ [a])
  | .sort k l => (.sort k l, [])
  | .var n => (.var n, [])
  | .const c => (.const c, [])
  | .lam A b => (.lam A b, [])
  | .pi A B => (.pi A B, [])
  | .letE A t b => (.letE A t b, [])

/-- **`var` 的脊是它自己，无参数。** -/
@[simp] theorem spine_var (n : ℕ) : spine (.var n) = (.var n, []) := rfl

/-- **`app` 的脊把参数追加到末尾。** -/
@[simp] theorem spine_app (f a : Term) : spine (.app f a) = ((spine f).1, (spine f).2 ++ [a]) := rfl

/-- **两层应用的脊正好是 `var n` 配 `[a, b]`。**

**=> 检验定义的行为，而不是只写下来。** -/
theorem spine_two_apps (n : ℕ) (a b : Term) :
    spine (.app (.app (.var n) a) b) = (.var n, [a, b]) := by
  simp only [spine_app, spine_var, List.nil_append, List.cons_append, List.singleton_append]

/-- **中性项的脊头必然是一个变量。**

**=> 对 `Neutral` 归纳：`var n` 情形取 `n` 与空参数；
`app` 情形把新参数追加到归纳假设给出的列表上。**
**这条就是「中性项不会卡在非变量头上」的形式化，也是第 798 轮 `neutral_head` 的加强版
（它给出**完整的参数列表**，而不只是头）。** -/
theorem neutral_spine_head {t : Term} (h : Neutral t) :
    ∃ n args, spine t = (Term.var n, args) := by
  induction h with
  | var n => exact ⟨n, [], rfl⟩
  | @app f a hf ih =>
      obtain ⟨n, args, hargs⟩ := ih
      exact ⟨n, args ++ [a], by simp only [spine_app, hargs]⟩


/-- **变量的头部不能步进。**

**=> 这正是 `no_step_var` 的内容。单独写出，是为了让下一条的推理读得出来。** -/
theorem neutral_head_cannot_step (n : ℕ) (t : Term) :
    ¬ Step (fun _ => none) (Term.var n) t :=
  no_step_var (fun _ => none) n t

/-- **中性项可以就是一个变量 —— 而变量是不动的。**

**=> 这就是为什么进展定理不能写成「中性 ⇒ 步进」。
它必须写成「中性 ⇒ 头部是变量，且在封闭下该变量被绑定」。** -/
theorem neutral_can_be_stuck_var (n : ℕ) :
    Neutral (.var n) ∧ ¬ ∃ t, Step (fun _ => none) (.var n) t := by
  refine ⟨Neutral.var n, ?_⟩
  rintro ⟨t, h⟩
  exact no_step_var (fun _ => none) n t h

end Lattice.Core.CIC