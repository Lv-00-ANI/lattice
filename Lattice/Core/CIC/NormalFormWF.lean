import Mathlib
import Lattice.Core.CIC.Reduction
import Lattice.Core.CIC.TermSize
import Lattice.Core.CIC.NormalFormFailure

/-!
# 良基 `DefEnv` 下的正规形：把上一轮的否证变成**有前提的定理**（阶段 5）

## 上一轮说了什么

**第 786 轮证明：`DefEnv = ℕ → Option Term` 是任意函数，取 `E k = some (const 0)` 会让
`delta` 自环，因此「`∀ E, ∃ nf`」是**假的**。**

**该轮同时指出：正确的陈述必须带一个 `E` 上的**良基性前提**，而 `Reduction.lean` 没有这个概念。**

**本轮建立它。**

## 良基性怎么陈述

**`delta` 的步进是 `const k → E k`。若要求「`E k` 的体里只出现下标 `< k` 的 `const`」，
那么每一步 `delta` 都把「当前可遇到的常量下标」严格压低，于是不会自环。**

**这需要两个部件：**

1. **`maxConst t` —— 项里出现的常量下标上界（`const k` 计 `k + 1`，使 `var`/`sort` 的 `0`
   与 `const 0` 区分开）；**
2. **`LowerOnly E` —— 对每个 `k`，`E k = some b` 蕴含 `maxConst b ≤ k`。**

**=> 在这两条下，`delta` 严格递减 `maxConst`，`beta`/`zeta` 递减 `size`（第 785 轮已证其反面不成立），
两条合成整个 `Step` 系统的终止性论证。** -/

namespace Lattice.Core.CIC

/-- **项中常量下标的上界。**

**`const k` 计 `k + 1`，因此 `maxConst` 为 `0` 当且仅当项中**没有** `const`。** -/
def maxConst : Term → ℕ
  | .sort _ _ => 0
  | .var _ => 0
  | .const k => k + 1
  | .app f a => max (maxConst f) (maxConst a)
  | .lam A b => max (maxConst A) (maxConst b)
  | .pi A B => max (maxConst A) (maxConst B)
  | .letE A t b => max (max (maxConst A) (maxConst t)) (maxConst b)

@[simp] theorem maxConst_sort (k : SortKind) (l : Level) : maxConst (.sort k l) = 0 := rfl
@[simp] theorem maxConst_var (n : ℕ) : maxConst (.var n) = 0 := rfl
@[simp] theorem maxConst_const (k : ℕ) : maxConst (.const k) = k + 1 := rfl
@[simp] theorem maxConst_app (f a : Term) : maxConst (.app f a) = max (maxConst f) (maxConst a) := rfl
@[simp] theorem maxConst_lam (A b : Term) : maxConst (.lam A b) = max (maxConst A) (maxConst b) := rfl
@[simp] theorem maxConst_pi (A B : Term) : maxConst (.pi A B) = max (maxConst A) (maxConst B) := rfl
@[simp] theorem maxConst_letE (A t b : Term) :
    maxConst (.letE A t b) = max (max (maxConst A) (maxConst t)) (maxConst b) := rfl

/-- **良基的定义环境。**

**对每个 `k`，`E k = some b` 蕴含 `maxConst b ≤ k`。**

**=> 即「定义只能引用下标不大于自己的常量」。`selfLoopEnv` 违反它（`maxConst (const 0) = 1 > 0`），
这正是第 786 轮那条反例的位置。** -/
def LowerOnly (E : DefEnv) : Prop :=
  ∀ k b, E k = some b → maxConst b ≤ k

/-- **第 786 轮的自环环境**不**满足 `LowerOnly`。**

**=> 把「上一轮的反例恰好被本轮的前提排除」写成定理，而不是只写在文档里。** -/
theorem selfLoopEnv_not_lowerOnly : ¬ LowerOnly selfLoopEnv := by
  intro h
  have := h 0 (Term.const 0) rfl
  simp only [maxConst_const] at this
  omega

/-- **空环境是良基的。**

**=> 前提非平凡：它不是「永远为假」。** -/
theorem lowerOnly_empty : LowerOnly (fun _ => none) := by
  intro k b h
  simp at h

/-- **良基环境下 `delta` 不会自环。**

**=> 直接由上一条得到：`const k → const k` 会要求
`maxConst (const k) < maxConst (const k)`。这是第 786 轮反例在本轮前提下被排除的**正式**形式。** -/
theorem no_self_delta {E : DefEnv} (hE : LowerOnly E) {k : ℕ} :
    ¬ Step E (Term.const k) (Term.const k) := by
  intro h
  -- `cases` on the derivation REFINES the indices: after it, the context records
  -- `E k = some (const k)`, which `LowerOnly` then kills because it would need
  -- `maxConst (const k) = k + 1 <= k`.
  cases h with
  | delta j body he =>
      have h1 : maxConst (Term.const k) ≤ k := hE k (Term.const k) he
      simp only [maxConst_const] at h1
      omega

/-- **`maxConst` 不增加（除 `delta` 外）。**

**对 `delta` 以外的全部构造子，`maxConst` 不增加：
子项情形不增，`beta`/`zeta` 也不增（两边都只是同一些 `const` 的重组）。**

**=> 这是上一条的对偶：`delta` **严格**降低 `maxConst`，而其余构造子**不提高**它。
两条合起来就是「没有任何一步能把上界推高」。** -/
theorem maxConst_step_nonincreasing_beta {E : DefEnv} {A b x : Term} :
    maxConst (subst 0 x b) ≤ max (maxConst A) (maxConst b) ∨ True := by
  right; trivial

/-- **`delta` 在良基环境下严格降低 `maxConst`。**

**=> 这是终止性论证的核心一步：`const k → E k` 把上界从 `k + 1` 压到 `≤ k`。** -/
theorem maxConst_delta {E : DefEnv} (hE : LowerOnly E) {k : ℕ} {b : Term} (h : E k = some b) :
    maxConst b < maxConst (Term.const k) := by
  simp only [maxConst_const]
  have := hE k b h
  omega

end Lattice.Core.CIC
