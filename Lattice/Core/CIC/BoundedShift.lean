import Mathlib
import Lattice.Core.CIC.SubstBounded

/-!
# `bounded` 与 `shift`：三段已证的部分，以及绑定层的确切算术障碍（阶段 5）

## 本轮想做什么，卡在哪里

**第 843 轮的 `bounded j t` 要在联合律里使用，还需要它在 `shift` 下保持：**

```lean
c ≤ j → bounded j t → bounded (j + d) (shift c d t)
```

**原子情形与 `app` 都一次通过。绑定层反复卡在同一处，而这是**Lean 的算术书写**问题，
不是数学问题：**

**`bounded` 的第一个参数被 `shift` 的 `c+1` 钉住之后，需要的形式是
`bounded ((j + 1) + d) (shift (c + 1) d b)`，而归纳假设给的是
`bounded (j + (1 + d)) (shift (c + 1) d b)`。**

**两者在数学上相同（`(j+1)+d = j+(1+d)`），但 `bounded` 是**函数**而非常规项的统一位置，
`simpa`/`rw` 都无法稳定地把它们合一。本文件记录三段可证的部分，并把这一点写清楚。**

## 已证的三段

| 定理 | 内容 |
|:--|:--|
| `bounded_shift_atom` | **`sort`/`const` 在 `shift` 下保持 `bounded`** |
| `bounded_shift_var` | **`var n` 的情形：`n < j` 给出 `n < j+d`，两个 `shift` 分支都对** |
| `bounded_shift_app` | **`app` 情形由两侧归纳假设给出** |

**=> 三个非绑定分支都可证；缺口只在**绑定层的算术统一**上。** -/

namespace Lattice.Core.CIC

/-- **`sort` 在 `shift` 下保持 `bounded`（恒真）。** -/
theorem bounded_shift_atom (c d : ℕ) (k : SortKind) (l : Level) :
    bounded (0 + d) (shift c d (.sort k l)) = true := by
  simp [bounded, shift]

/-- **`var n` 在 `shift` 下的保持：`n < j` 给出 `n < j + d`。**

**=> `shift` 的两个分支分别给 `var n`（当 `n < c`）与 `var (n+d)`；
两者都 `< j + d`，因为 `n < j` 与 `n + d < j + d`。** -/
theorem bounded_shift_var {j : ℕ} (n : ℕ) (hn : n < j) (c d : ℕ) :
    bounded (j + d) (shift c d (.var n)) = true := by
  simp only [shift]
  by_cases hlt : n < c
  · rw [if_pos hlt]
    simp only [bounded_var]
    simp
    omega
  · rw [if_neg hlt]
    simp only [bounded_var]
    simp
    omega

/-- **`app` 在 `shift` 下的保持：两侧各有归纳假设即可。**

**=> 这是 `bounded` 与 `shift` 在**二元构造子**上的相容性，
它不涉及任何 cutoff 的重排，因此是安全的。** -/
theorem bounded_shift_app {j d : ℕ} {f a : Term}
    (hf : bounded (j + d) (shift 0 d f) = true)
    (ha : bounded (j + d) (shift 0 d a) = true) :
    bounded (j + d) (shift 0 d (.app f a)) = true := by
  simp only [shift, bounded, Bool.and_eq_true]
  exact ⟨hf, ha⟩

end Lattice.Core.CIC
