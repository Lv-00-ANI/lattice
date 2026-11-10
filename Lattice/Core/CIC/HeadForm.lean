import Mathlib
import Lattice.Core.CIC.Spine
import Lattice.Core.CIC.HasType
import Lattice.Core.CIC.ReductionOriented

/-!
# 头部形态三分：值 / 中性 / redex（阶段 5，进展定理的最后一块）

## 为什么需要「三分」而不是「中性/值二分」

**第 799 轮给出 `Neutral` 的确切形状（`var n` 套应用脊）。但本轮先确认了一件事：
`HasType` 与 `Neutral` **没有**直接关系 —— `lam A b` 是良类型的，却**不是**中性项。**

**=> 进展定理的划分不能是「中性 or 非中性」（那太粗），也不能是「中性 or 能步进」
（第 799 轮已否证）。真正需要的是**按头部形态三分**：**

| 形态 | 例子 | 它做什么 |
|:--|:--|:--|
| **值** | `sort`、`lam`、`pi` | **不需要步进** |
| **中性** | `var n` 套应用脊 | **卡在变量上；在 `Closed` 下该变量被绑定** |
| **redex** | `app (lam A b) a`、`letE A t b`、`const c` | **按 `beta`/`zeta`/`delta` 步进** |

**`const c` 被归入 redex，是因为它在 `E c = some body` 时按 `delta` 步进；
在空环境下它退化为「值状」的卡住项 —— 这一层差别由 `DefEnv` 提供，不由 `Term` 决定。**

## 本文件给出

**`HeadForm` 的归纳定义（七条），以及每条的两条基本事实：**

- **`sort`/`lam`/`pi` 不可能是中性项**（第 799 轮已由 `neutral_not_*` 给出，此处并置）；
- **redex 的形状可以被 `Step` 直接匹配**（`beta`/`zeta` 由构造子给出）。

**进展定理本身仍**未**证出。它需要的最后一步是：`HasType` 与 `Closed` 一起蕴含某个 `HeadForm`。
本文件把那一步所需的**分类表**摆出来。** -/

namespace Lattice.Core.CIC

/-- **头部形态三分。**

**=> 七条构造子：三条「值」（`sort`、`lam`、`pi`）、一条「中性」、三条「redex」
（`const` 展开、`letE` 求值、`beta` 应用）。**

**`app f a` 且 `f` 非 `lam` 的情形由 `neutral` 覆盖（当 `f` 中性时）；
若 `f` 是 `app (lam ..)` 以外的东西且非中性，本定义不覆盖 —— 那正是需要
「`HasType` 蕴含某个 `HeadForm`」来补的地方。** -/
inductive HeadForm : Term → Prop
  /-- **宇宙是值。** -/
  | sort (k : SortKind) (l : Level) : HeadForm (.sort k l)
  /-- **抽象是值。** -/
  | lam (A b : Term) : HeadForm (.lam A b)
  /-- **乘积是值。** -/
  | pi (A B : Term) : HeadForm (.pi A B)
  /-- **常量：在环境给出定义时按 `delta` 步进。** -/
  | const (c : ℕ) : HeadForm (.const c)
  /-- **中性项：`var n` 套应用脊。** -/
  | neutral {t : Term} : Neutral t → HeadForm t
  /-- **局部定义：按 `zeta` 步进。** -/
  | letE (A t b : Term) : HeadForm (.letE A t b)
  /-- **β-redex。** -/
  | beta (A b a : Term) : HeadForm (.app (.lam A b) a)

/-- **β-redex 能步进。**

**=> 直接由 `Step.beta` 给出：`app (lam A b) a → subst 0 a b`。** -/
theorem headForm_beta_steps (A b a : Term) :
    Step (fun _ => none) (.app (.lam A b) a) (subst 0 a b) :=
  Step.beta A b a

/-- **`zeta`-redex 能步进。**

**=> 直接由 `Step.zeta` 给出：`letE A t b → subst 0 t b`。** -/
theorem headForm_zeta_steps (A t b : Term) :
    Step (fun _ => none) (.letE A t b) (subst 0 t b) :=
  Step.zeta A t b

/-- **`delta` 在环境给出定义时步进。**

**=> 由 `Step.delta` 给出。`const c` 之所以归入 redex，全靠这一条。** -/
theorem headForm_delta_steps (E : DefEnv) (c : ℕ) (body : Term) (h : E c = some body) :
    Step E (.const c) body :=
  Step.delta c body h

/-- **值是值：`lam` 不是中性项。**

**=> 并置第 799 轮的 `neutral_not_lam`，说明「值」与「中性」是**互斥**的两类，
这正是三分里「值不需要步进」有意义的前提。** -/
theorem headForm_value_not_neutral {A b : Term} : ¬ Neutral (.lam A b) :=
  neutral_not_lam

end Lattice.Core.CIC
