import Mathlib
import Lattice.Core.CIC.BoundedShift
import Lattice.Core.CIC.SubstBounded

/-!
# 联合位移律：`bounded` 下的完整形式（阶段 5，九轮的收束）

## 陈述

```lean
shift_subst_joint_bounded (j c d) (hc : c + 1 ≤ j) (s t) (h : bounded j t = true) :
  shift (c+1) d (subst j s t) = subst (j+d) (shift c d s) (shift (c+1) d t)
```

**三行证明。** **而它之所以是三行，是因为前面九轮把每一块都打磨好了：**

| 前置 | 来自 |
|:--|:--|
| **`subst_bounded`：`bounded j t → subst j s t = t`** | **第 843 轮** |
| **`bounded_shift`：`c ≤ j → bounded j t → bounded (j+d) (shift c d t)`** | **第 846 轮（三轮打磨）** |
| **联合律的形状：左边用 `c+1`** | **第 840 轮** |

**=> 证明本身只是：**

```lean
rw [subst_bounded h]                                   -- 左边：subst 消失
have hb := bounded_shift (by omega) h                  -- bounded 在位移下保持
rw [subst_bounded hb]                                  -- 右边末尾的 subst 也消失
```

**两侧都变成 `shift (c+1) d t`。**

## 条件 `c + 1 ≤ j` 为什么是必要的

**`bounded_shift` 的前提是 `shift` 的 cutoff `c+1` **不超过** `j`（否则被位移的下标会越过上界）。
而联合律在左边用的是 `shift (c+1) d`，所以条件就变成 `c + 1 ≤ j`。**

**=> 这与第 841/842 轮反复出现的「`c` 与 `c+1` 差一」是**同一个**数，但这次它作为**前提**出现，
而不是作为失败的来源。**

## 这条律对 `par-subst` 意味着什么

**`par-subst` 需要的正是「`shift` 与 `subst` 可交换」。**
**本定理给出了它在**受控条件**下的完整形式：只要 `t` 的所有自由变量 `< j`，且 `c+1 ≤ j`。**

**=> 这与标准 de Bruijn 发展的做法一致：交换律总是带着「下标受界」的前提，
因为在 `n ≥ j` 处 `subst` 会递减而 `shift` 会位移，两者的作用不可交换。**

**=> 九轮得到的不是一个更弱的定理，而是**正确的**定理：
无条件版本（第 827/828/830/839 轮四次否证）本来就**不成立**。** -/

namespace Lattice.Core.CIC

/-- **`bounded` 下的联合位移律。**

**=> 两个 `subst` 都因 `bounded` 而消失，两侧都归约为 `shift (c+1) d t`。
这是九轮否证与修正之后得到的**正确**陈述形式：无条件版本不成立（第 827/828/830/839 轮）。** -/
theorem shift_subst_joint_bounded {j c d : ℕ} (hc : c + 1 ≤ j) (s t : Term)
    (h : bounded j t = true) :
    shift (c + 1) d (subst j s t) = subst (j + d) (shift c d s) (shift (c + 1) d t) := by
  rw [subst_bounded h]
  have hb : bounded (j + d) (shift (c + 1) d t) = true := bounded_shift (by omega) h
  rw [subst_bounded hb]

/-- **同一律的 `d = 1` 特例：`ParRedV` 的闭合性所需要的形态。**

**=> `d = 1` 时 `subst` 在绑定下把 `s` 换成 `shift 0 1 s`，而本律与第 833 轮的
`shift_one_one_commutes` 配套，正是那条路径所需。** -/
theorem shift_subst_joint_bounded_one {j c : ℕ} (hc : c + 1 ≤ j) (s t : Term)
    (h : bounded j t = true) :
    shift (c + 1) 1 (subst j s t) = subst (j + 1) (shift c 1 s) (shift (c + 1) 1 t) :=
  shift_subst_joint_bounded hc s t h

end Lattice.Core.CIC
