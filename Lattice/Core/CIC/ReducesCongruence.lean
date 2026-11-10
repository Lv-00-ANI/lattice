import Mathlib
import Lattice.Core.CIC.ParallelReduction

/-!
# `Reduces` 的合同性：哪些成立、哪些**不**成立（阶段 5，Tait–Martin–Löf 第 3 步的准备）

## 本文件先做的核实，以及它的结果

**第 3 步需要 `Reduces` 在每个构造子上合同。我先把 `Step` 的十个构造子逐一查了签名，结果是：**

| `Step` 构造子 | 它归约的位置 |
|:--|:--|
| `beta` | **`app (lam A b) a` 的**头部** |
| `zeta` | **`letE A t b` 的**头部** |
| `delta` | **`const c` 的头部** |
| **`appL`** | **`app f a` 的 `f`** |
| **`appR`** | **`app f a` 的 `a`** |
| **`lamBody`** | **`lam A b` 的 `b` —— **不是** `A`** |
| **`piDom`** | **`pi A B` 的 `A`** |
| **`piCod`** | **`pi A B` 的 `B`** |
| **`letVal`** | **`letE A t b` 的 `t` —— **不是** `A`** |
| **`letBody`** | **`letE A t b` 的 `b`** |

**=> `Step` **没有**在 `lam` 的类型位置、也没有在 `letE` 的类型位置上归约的规则。**
**`lam A b` 与 `letE A t b` 的类型位置**是惰性的**。**

## 这决定了哪些合同性成立

**成立的（本文件全部证出）：**

- **`app` 的左/右位置；**
- **`lam` 的体；**
- **`pi` 的两个位置；**
- **`letE` 的值与体。**

**不成立的：**

- **`lam` 的类型位置**（`lam A b ~> lam A' b` 只有在 `A' = A` 时成立）；
- **`letE` 的类型位置**（同理）。

**=> 这不是缺陷。惰性的类型位置是**有意的设计**：`Term` 里 `lam` 与 `letE` 都带一个类型标注，
而 `Step` 把它当作不可归约的注解。** **`ParRed` 却**带**了 `lam A A'` 与 `letE A A'` 的归约 ——
那是第 817 轮从文献照搬时**没有**核实的部分，本轮把它作为**不一致**记下来。** -/

namespace Lattice.Core.CIC

/-- **`Reduces` 在应用左侧合同。** -/
theorem reduces_app_l (E : DefEnv) {f f' a : Term} (h : Reduces E f f') :
    Reduces E (.app f a) (.app f' a) := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.appL x y a hxy) ih

/-- **`Reduces` 在应用右侧合同。** -/
theorem reduces_app_r (E : DefEnv) {f a a' : Term} (h : Reduces E a a') :
    Reduces E (.app f a) (.app f a') := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.appR f x y hxy) ih

/-- **`Reduces` 在抽象的**体**上合同（类型位置不动）。** -/
theorem reduces_lam_body (E : DefEnv) {A b b' : Term} (h : Reduces E b b') :
    Reduces E (.lam A b) (.lam A b') := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.lamBody A x y hxy) ih

/-- **`Reduces` 在乘积的定义域上合同。** -/
theorem reduces_pi_domain (E : DefEnv) {A A' B : Term} (h : Reduces E A A') :
    Reduces E (.pi A B) (.pi A' B) := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.piDom x y B hxy) ih

/-- **`Reduces` 在乘积的余域上合同。** -/
theorem reduces_pi_codomain (E : DefEnv) {A B B' : Term} (h : Reduces E B B') :
    Reduces E (.pi A B) (.pi A B') := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.piCod A x y hxy) ih

/-- **`Reduces` 在局部定义的**值**上合同（类型位置不动）。** -/
theorem reduces_letE_value (E : DefEnv) {A t t' b : Term} (h : Reduces E t t') :
    Reduces E (.letE A t b) (.letE A t' b) := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.letVal A x y b hxy) ih

/-- **`Reduces` 在局部定义的**体**上合同。** -/
theorem reduces_letE_body (E : DefEnv) {A t b b' : Term} (h : Reduces E b b') :
    Reduces E (.letE A t b) (.letE A t b') := by
  induction h with
  | refl t => exact Reduces.refl _
  | @step x y z hxy _ ih => exact Reduces.step (Step.letBody A t x y hxy) ih
/-- **`lam` 的类型位置冻结：任何一步 `Step` 都不改变 `lam` 的类型标注。**

**=> `Step.lamBody` 是唯一能从 `lam` 出发的规则，而它的结论两边**同一个** `A`。
于是「类型位置惰性」不是猜测，而是 `Step` 构造子的直接结果。** -/
theorem lam_type_position_frozen (E : DefEnv) (A A' b b' : Term)
    (h : Step E (.lam A b) (.lam A' b')) : A = A' := by
  cases h
  rfl

end Lattice.Core.CIC
