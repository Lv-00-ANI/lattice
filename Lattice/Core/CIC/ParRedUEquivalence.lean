import Mathlib
import Lattice.Core.CIC.ParallelReductionComplete
import Lattice.Core.CIC.ReducesCongruence

/-!
# `ParRedU` 与 `Reduces` 的双向对应（阶段 5，Tait–Martin–Löf 第 3 步）

## 本轮完成什么

**第 3 步是 `Reduces E a b ↔ ParRedU∗ E a b` 的两向等价。本文件给出**两个方向**：**

| 方向 | 定理 | 情形数 |
|:--|:--|:--|
| **`Step → ParRedU`** | **`step_to_parRedU`** | **10（一步一条）** |
| **`ParRedU → Reduces`** | **`parRedU_imp_reduces`** | **9（一平行步由有限多单步模拟）** |

**第一条是「每个单步都是一次平行步」；第二条是「每次平行步都可由有限多单步复现」。**
**两者合起来说明 `ParRedU` 与 `Reduces` 是**同一个关系**的两种呈现。**

## 第二条为什么需要 `Reduces` 的合同性

**`ParRedU.app` 说 `f ⟹ f'` 与 `a ⟹ a'` 同时成立时 `app f a ⟹ app f' a'`。
要把它变成 `Reduces`，必须先证 `app f a →∗ app f' a`（左侧，`reduces_app_l`），
再证 `app f' a →∗ app f' a'`（右侧，`reduces_app_r`），最后 `reduces_trans`。**

**=> 第 818 轮补的七条合同性定理正是这一步的全部依赖。**
**`letL`/`letR` 用 `reduces_letE_value`/`reduces_letE_body`；`lam` 用 `reduces_lam_body`；
`pi` 用 `reduces_pi_domain`/`reduces_pi_codomain`。** -/

namespace Lattice.Core.CIC

/-- **每个单步都是一次平行步。**

**=> 对 `Step` 归纳，十个构造子各给一条 `ParRedU` 构造子：
`beta`/`zeta` 用 `zero` 填两处前提，`appL`/`appR`/`piDom`/`piCod` 用 `zero` 填另一侧，
`letVal`/`letBody` 用本轮新增的 `letL`/`letR`。** -/
theorem step_to_parRedU (E : DefEnv) {a b : Term} (h : Step E a b) : ParRedU E a b := by
  induction h with
  | beta A bd ar => exact ParRedU.beta (ParRedU.zero _) (ParRedU.zero _)
  | zeta A t bd => exact ParRedU.letE (ParRedU.zero _) (ParRedU.zero _)
  | delta c body he => exact ParRedU.delta c body he
  | appL f f' ar hs ih => exact ParRedU.app ih (ParRedU.zero _)
  | appR f ar ar' hs ih => exact ParRedU.app (ParRedU.zero _) ih
  | lamBody A bd bd' hs ih => exact ParRedU.lam ih
  | piDom A A' B hs ih => exact ParRedU.pi ih (ParRedU.zero _)
  | piCod A B B' hs ih => exact ParRedU.pi (ParRedU.zero _) ih
  | letVal A t t' bd hs ih => exact ParRedU.letL ih
  | letBody A t bd bd' hs ih => exact ParRedU.letR ih

/-- **每次平行步都可由有限多单步复现。**

**=> 对 `ParRedU` 归纳，九个构造子：**

- **`zero`**：`Reduces.refl`；
- **`delta`**：一步 `Step.delta` 再 `refl`；
- **`app`**：先 `reduces_app_l` 再 `reduces_app_r`，`reduces_trans` 相接；
- **`lam`/`letL`/`letR`**：一条合同性各够；
- **`pi`**：`reduces_pi_domain` 接 `reduces_pi_codomain`；
- **`beta`/`letE`**：需先归约子项再执行替换，用 `Reduces.step` 配 `Step.beta`/`Step.zeta`
  与合同性；本文件给出 `beta` 与 `letE` 的两种处理。**

**注意 `beta`/`letE` 的证明需要「替换在 `Reduces` 下合同」，
那是第 786 轮 `SubstSizeBound`/`SubstitutionShift` 一族所处理的领域，
本文件**不**依赖它，而是把 `beta`/`letE` 的结论直接由 `Step.beta`/`Step.zeta` 与
子项归约的合同性组合出来。** -/
theorem parRedU_imp_reduces (E : DefEnv) {a b : Term} (h : ParRedU E a b) : Reduces E a b := by
  induction h with
  | zero t => exact Reduces.refl t
  | delta c body he => exact Reduces.step (Step.delta c body he) (Reduces.refl body)
  | app hf ha ihf iha =>
      exact reduces_trans E (reduces_app_l E ihf) (reduces_app_r E iha)
  | @beta A bd bd' ar ar' hb ha ihb iha =>
      -- app (lam A bd) ar -> app (lam A bd') ar -> app (lam A bd') ar' -> subst 0 ar' bd'
      have s1 : Reduces E (.app (.lam A bd) ar) (.app (.lam A bd') ar) :=
        reduces_app_l E (reduces_lam_body E ihb)
      have s2 : Reduces E (.app (.lam A bd') ar) (.app (.lam A bd') ar') :=
        reduces_app_r E iha
      exact reduces_trans E s1 (reduces_trans E s2
        (Reduces.step (Step.beta A bd' ar') (Reduces.refl _)))
  | lam hb ihb => exact reduces_lam_body E ihb
  | pi hA hB ihA ihB =>
      exact reduces_trans E (reduces_pi_domain E ihA) (reduces_pi_codomain E ihB)
  | letL ht iht => exact reduces_letE_value E iht
  | letR hb ihb => exact reduces_letE_body E ihb
  | @letE A t t' bd bd' ht hb iht ihb =>
      have s1 : Reduces E (.letE A t bd) (.letE A t' bd) := reduces_letE_value E iht
      have s2 : Reduces E (.letE A t' bd) (.letE A t' bd') := reduces_letE_body E ihb
      exact reduces_trans E s1 (reduces_trans E s2
        (Reduces.step (Step.zeta A t' bd') (Reduces.refl _)))

end Lattice.Core.CIC
