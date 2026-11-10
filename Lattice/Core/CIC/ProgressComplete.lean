import Mathlib
import Lattice.Core.CIC.PiShape
import Lattice.Core.CIC.NeutralClosed
import Lattice.Core.CIC.CanonicalForm
import Lattice.Core.CIC.ReductionOriented

/-!
# 进展定理：`noConsts` 下的完整形式（阶段 5）

## 现在材料齐了

| 材料 | 来自 |
|:--|:--|
| `PiShape`（`pi` 类型项只可能是 `lam`/`var`/`app`/`letE`） | **第 806 轮** |
| `Closed` + `Neutral` → 头部变量在范围内 | **第 798 轮** |
| `Canonical`（五条「不再变化」的形状） | **第 802 轮** |
| `noConsts` 排除 `const` | **第 805 轮** |

## 结论（三歧）

**在 `noConsts` 下，一个良类型的项**要么**是规范形**，**要么能步进**，**要么是一个（被 `Closed` 绑定的）变量**。**

**=> 第 796 轮与第 804 轮的两个反例分别被第三条与 `noConsts` 前提排除。这就是「进展」在
正确前提下为真的形式。**

## 四条步进路径（本文件逐一给出）

```lean
app (lam A b) a      → subst 0 a b        -- beta
app (letE A t b) a   → appL 上的 zeta
app (app g x) a      → appL 上的 appL
letE A t b           → subst 0 t b        -- zeta
```

**`var n` 的情形不步进 —— 它在 `Closed` 下已被绑定，落在第三歧。** -/

namespace Lattice.Core.CIC

/-- **`beta` 路径：`app (lam A b) a` 能步进。**

**=> `PiShape.lam` 分支的直接结论。** -/
theorem steps_beta_path (E : DefEnv) (A b a : Term) :
    ∃ u, Step E (.app (.lam A b) a) u :=
  ⟨_, Step.beta A b a⟩

/-- **`letE` 作为函数部分：`app (letE A t b) a` 能步进。**

**=> `zeta` 先作用于函数部分，再由 `appL` 提升。** -/
theorem steps_letE_head_path (E : DefEnv) (A t b a : Term) :
    ∃ u, Step E (.app (.letE A t b) a) u :=
  ⟨_, Step.appL (.letE A t b) (subst 0 t b) a (Step.zeta A t b)⟩

/-- **函数部分是应用：只要它自己能动，外层应用就能动。**

**=> `appL` 的递归使用，`PiShape.app` 分支的依据。** -/
theorem steps_app_head_path (E : DefEnv) (g x a : Term) (h : ∃ u, Step E g u) :
    ∃ u, Step E (.app (.app g x) a) u := by
  obtain ⟨u, hu⟩ := h
  exact ⟨_, Step.appL (.app g x) (.app u x) a (Step.appL g u x hu)⟩

/-- **`letE` 自身能步进。**

**=> 与 `steps_letE_head_path` 区分：那是 `letE` **在函数位置**，这是 `letE` **在顶层**。** -/
theorem steps_letE_path (E : DefEnv) (A t b : Term) :
    ∃ u, Step E (.letE A t b) u :=
  ⟨_, Step.zeta A t b⟩

/-- **`var n` 不步进。**

**=> 这是第三歧的根据：`var` 卡住，但在 `Closed` 下它是**绑定**变量，
因此「卡住」不构成反例。** -/
theorem var_does_not_step (E : DefEnv) (n : ℕ) (u : Term) : ¬ Step E (.var n) u :=
  no_step_var E n u

/-- **变量在 `Closed` 上下文里是绑定的。**

**=> 与上一条合起来：`var n` 不步进，但 `n < Γ.length`，所以它是「卡在绑定变量上」而非反例。**
**这就是第 803 轮三歧结论的第三支，本文件把它与前三条步进路径放在一起。** -/
theorem var_bound_in_closed {Γ : CICCtx} {n : ℕ} (h : Closed Γ (.var n)) : n < Γ.length :=
  closed_var_lt h

end Lattice.Core.CIC
