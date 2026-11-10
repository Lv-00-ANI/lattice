import Mathlib
import Lattice.Core.CIC.ShiftSubstAssembly
import Lattice.Core.CIC.ShiftCommGeneral

/-!
# 对绑定层稳定的表述：`d = 1` 时的位移-替换律（阶段 5）

## 上一轮排除了什么

**第 832 轮证明 `shift c d` 与 `shift 0 1` **在 `d ≠ 1` 时不可交换**（`shift_shift_mixed_d_false`）。
而绑定层恰恰需要它 —— 因为 `subst` 在 `lam` 下把 `s` 换成 `shift 0 1 s`。**

## 本轮的判定：把律限制到 `d = 1`

**若律只在 `d = 1` 时陈述，则绑定层需要的两处位移量**都是 1**：

- **律本身在 `c+1` 处作用：`shift (c+1) 1`；**
- **`s` 被换成 `shift 0 1 s`。**

**=> 于是两者由 `shift_commute_general` 联系，而它是**同 `d`** 的律（第 786 轮）。
本轮先验证这一点确实成立（`shift_one_one_commutes`）。**

## 代价与收益

**代价：律只对 `d = 1` 成立 —— 但 `ParRedV` 的 `shift` 合同性只需要 `d` 任意时的**结构性**部分，
而 `beta`/`letE` 需要的正是对 `s` 的位移，那一处 `d` 恰好是 1。**

**收益：绑定层不再需要一条假引理。**

**=> 这是「把一般性降到刚好够用的水平，换来可证性」的一次具体应用。** -/

namespace Lattice.Core.CIC

/-- **`d = 1` 时两个 `shift` 交换（`shift_commute_general` 的直接实例）。**

**=> `shift 0 1 (shift c' 1 s) = shift (c' + 1) 1 (shift 0 1 s)`：两处位移量都是 1，
所以第 786 轮的同 `d` 律适用。**

**这条就是绑定层需要的替代品 —— 第 832 轮否证的是 `d` **不同**时的版本。** -/
theorem shift_one_one_commutes (c' : ℕ) (s : Term) :
    shift 0 1 (shift c' 1 s) = shift (c' + 1) 1 (shift 0 1 s) :=
  shift_commute_general s 0 1 c' (Nat.zero_le c')

/-- **`d = 1` 时 `shift` 与 `shift 0 1` 在 `c = 0` 处一致。**

**=> `shift 0 1 (shift 0 1 s)` 两侧相同 —— 退化的自反情形，
说明 `d = 1` 的限定没有引入矛盾。** -/
theorem shift_one_one_self (s : Term) : shift 0 1 (shift 0 1 s) = shift (0 + 1) 1 (shift 0 1 s) :=
  shift_one_one_commutes 0 s

end Lattice.Core.CIC
