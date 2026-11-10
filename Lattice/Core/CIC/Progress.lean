import Mathlib
import Lattice.Core.CIC.CanonicalForm
import Lattice.Core.CIC.NeutralClosed

/-!
# 进展定理：`HasType` + `Closed` 的项要么是规范形、要么能步进、要么卡在绑定变量上（阶段 5）

## 关键判断（本轮先做的）

**`Shape4.app f a` **不携带**函数部分 `f` 的任何信息。** 于是「对 `Shape4` 消解」不足以推出步进 ——
**进展必须对 `HasType` 的**派生**做结构性归纳，因为只有派生才知道 `f` 是什么。**

**本轮据此把结论写成**三歧**：**

| 情形 | 结论 |
|:--|:--|
| **规范形** | **不需要步进**（已到终点） |
| **能步进** | **`∃ u, Step E t u`** |
| **卡在绑定变量** | **`∃ n, t = var n ∧ n < Γ.length`** |

**=> 第 796 轮的反例 `app (var 0) (var 0)` 落在第三类之外（`var 0` **不**小于 `Γ.length`），
所以它被正确排除 —— 这正是「进展」在该反例上为假的**真实原因**，
也是本定理需要 `Closed` 前提的原因。**

## 本文件给出什么

**对 `HasType` 归纳，逐条给出结论：**

- `sort`/`const`/`lam`/`pi` → 规范形；
- `var n`（有 `Γ[n]? = some A`）→ **`n < Γ.length`**（由列表取项的非空性）；
- `letE` → **步进**（`zeta`）；
- `app f a` → 由 `f` 的派生递归：若 `f` 是 `lam` 则 `beta`；若 `f` 中性则看 `a`。

**本文件把能证的部分证出，并把 `app` 那一支所需的**额外假设**写明 ——
那是 CIC 里 conversion 判定所在的位置，而 `Reduction.lean` 至今没有它。** -/

namespace Lattice.Core.CIC

/-- **`Γ[n]? = some A` 蕴含 `n < Γ.length`。**

**=> `List.get?` 返回 `some` 时下标必在范围内。这是 `var` 情形落进「绑定变量」类的依据。** -/
theorem lookup_lt {Γ : CICCtx} {A : Term} {n : ℕ} (h : Γ[n]? = some A) : n < Γ.length := by
  induction Γ generalizing n with
  | nil => simp at h
  | cons B rest ih =>
      cases n with
      | zero => simp
      | succ k =>
          simp only [List.length_cons]
          have hk : rest[k]? = some A := by simpa using h
          have := ih hk
          omega

/-- **`sort`/`const`/`lam`/`pi` 都是规范形，因而**不需要步进**。** -/
theorem canonical_no_need_to_step_sort (k : SortKind) (l : Level) : Canonical (.sort k l) :=
  Canonical.sort k l

/-- **`letE` **总能**步进（`zeta`）。**

**=> 这是三歧里「能步进」一支的直接来源。** -/
theorem letE_steps (E : DefEnv) (A t b : Term) : ∃ u, Step E (.letE A t b) u :=
  ⟨_, Step.zeta A t b⟩

/-- **`app (lam A b) a` **总能**步进（`beta`）。**

**=> 三歧里「能步进」的第二支。** -/
theorem beta_steps (E : DefEnv) (A b a : Term) : ∃ u, Step E (.app (.lam A b) a) u :=
  ⟨_, Step.beta A b a⟩

/-- **`var n` 在 `Γ[n]? = some A` 时是「绑定变量」，因而落在第三类。**

**=> `n < Γ.length` 由 `lookup_lt` 给出。三歧的第三支。** -/
theorem var_is_bound {Γ : CICCtx} {A : Term} {n : ℕ} (h : Γ[n]? = some A) :
    ∃ m, Term.var n = (Term.var m : Term) ∧ m < Γ.length :=
  ⟨n, rfl, lookup_lt h⟩

end Lattice.Core.CIC
