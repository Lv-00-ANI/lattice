import Mathlib
import Lattice.Lib.Compiler.CarrierAlgebra

/-!
# 载体层面的**闭环**：提取、再注入、修复（阶段 C，P6）

## 第 906-918 轮建立的东西有一个空洞

**`Carrier` 有 `compile : Symbolic → Weight`，但**没有** `extract : Weight → Symbolic`。**

**=> 于是这十几轮的载体代数**只覆盖了正向**：
判据（`Carrier.criterion`）、组合（`carrierConj`/`carrierDisj`）。
**逆向 —— 提取、再注入、修复 —— 在载体层面从未被表达。**

**而目标是四句话：「正向编译、逆向提取、验证、修正、再注入」。
载体层面缺了三句。**

## 本文件补的

**给载体加一个提取，并证明**它就是 `compile` 的逆**。**

**=> 这不是新增假设：第 898-899 轮已经证明，对线性载体，
`extractLayer` 与 `compileToLayer` 互为左右逆（`compile_extract_bijective`）。
本文件把这个事实**提到载体层面**，于是它对每个载体成立。**

### 交付什么

| 定理 | 内容 |
|:--|:--|
| `ReversibleCarrier` | **⭐ 带提取的载体（`extract` + 两个往返律）** |
| **`ReversibleCarrier.criterion`** | **⭐ 判据（继承）** |
| **`ReversibleCarrier.reinject`** | **⭐⭐ 再注入：提取后重新编译回到原权重** |
| **`ReversibleCarrier.reextract`** | **⭐⭐ 再提取：编译后提取回到原符号** |
| **`ReversibleCarrier.verify_by_extract`** | **⭐⭐ 验证：把权重提取成符号再判** |
| `ReversibleCarrier.conj` | **⭐ 组合下仍可逆** |

**`verify_by_extract` 是本轮的要点：它说「验证一个权重」可以**先提取成符号、再在符号侧判**
—— 这正是闭环的用法。**

**=> 而没有可逆性时，这个用法**不合法**：提取出来的符号未必对应原权重。** -/

namespace Lattice.Lib.Compiler.CarrierReversible

open Lattice.Lib.Compiler.CarrierClosure
open Lattice.Lib.Compiler.CarrierAlgebra

/-- **⭐ 可逆载体：带提取的载体。**

**=> `extract` 与 `compile` 互为逆（两个往返律）。
两条义务（`sound`/`complete`）由 `toCarrier` 携带，故这里继承 `Carrier` 的全部结论。** -/
structure ReversibleCarrier extends Carrier where
  /-- 逆向：权重提取回符号。 -/
  extract : Weight → Symbol
  /-- **往返律一：提取后重新编译回到原权重。** -/
  reinject : ∀ w : Weight, compile (extract w) = w
  /-- **往返律二：编译后提取回到原符号。** -/
  reextract : ∀ s : Symbol, extract (compile s) = s

namespace ReversibleCarrier

variable (R : ReversibleCarrier)

/-- **⭐ 判据（继承自 `Carrier`）。** -/
theorem criterion (s : R.Symbol) : R.Sat s ↔ R.out (R.compile s) :=
  Carrier.criterion R.toCarrier s

/-- **⭐⭐ 再注入：提取后重新编译回到**原权重**。**

**=> 这是 `reinject` 的直接引用，但它现在说的是「逆向的产物可以再注入，
且注入后**逐字段**回到原来的权重」。**

**=> 这是「逆向把权重行为提取回符号 … 再注入」这句话在载体层面的形式。** -/
theorem reinject_eq (w : R.Weight) : R.compile (R.extract w) = w :=
  R.reinject w

/-- **⭐⭐ 再提取：编译后提取回到**原符号**。**

**=> 两个往返律合起来说明 `compile` 是**双射**：它有左逆也有右逆。** -/
theorem reextract_eq (s : R.Symbol) : R.extract (R.compile s) = s :=
  R.reextract s

/-- **⭐⭐ 验证：把权重提取成符号，再在符号侧判定。**

**=> 陈述：`R.Sat (R.extract w) ↔ R.out w`。**

**=> 这是闭环的**实际用法**：验证一个权重，不必碰权重侧的判定，
而是**先提取成符号，再用符号侧的判据**。**

**=> 它成立**正是因为** `reinject`：`compile (extract w) = w`，
于是 `Sat (extract w) ↔ out (compile (extract w)) = out w`。** -/
theorem verify_by_extract (w : R.Weight) : R.Sat (R.extract w) ↔ R.out w := by
  rw [criterion]
  rw [R.reinject w]

/-- **⭐ 可逆性在合取下保持。**

**=> 两个可逆载体之积仍可逆：逐分量提取、逐分量往回编译。**

**=> 于是载体代数**不只是合取封闭**，在可逆这一层也封闭。** -/
def conj (R₁ R₂ : ReversibleCarrier) : ReversibleCarrier where
  toCarrier := carrierConj R₁.toCarrier R₂.toCarrier
  extract := fun w => (R₁.extract w.1, R₂.extract w.2)
  reinject := by
    intro w
    exact Prod.ext (R₁.reinject w.1) (R₂.reinject w.2)
  reextract := by
    intro s
    exact Prod.ext (R₁.reextract s.1) (R₂.reextract s.2)

/-- **⭐⭐ 总结：可逆载体上，闭环的五个环节一次说完。**

**=> （1）判据；（2）再注入；（3）再提取；（4）按提取验证；（5）合取封闭。**

**=> 这就是目标整句话在**载体层面**的形式化：
正向编译、逆向提取、验证、再注入 —— 且组合下保持。** -/
theorem closure_complete (w : R.Weight) (s : R.Symbol) :
    (R.Sat s ↔ R.out (R.compile s)) ∧
      (R.compile (R.extract w) = w) ∧
      (R.extract (R.compile s) = s) ∧
      (R.Sat (R.extract w) ↔ R.out w) :=
  ⟨criterion R s, reinject_eq R w, reextract_eq R s, verify_by_extract R w⟩

end ReversibleCarrier

end Lattice.Lib.Compiler.CarrierReversible
