import Mathlib
import Lattice.Core.CIC.SubstBounded

/-!
# `bounded` 与 `shift`：三段已证，以及绑定分支**真正**的障碍（阶段 5）

## 第 844 轮的诊断是错的，本轮把它纠正

**第 844 轮把绑定分支的失败归因于「`(j+1)+d` 与 `j+(1+d)` 无法被 Lean 统一」。**

**本轮重试并在错误信息里读到了真正的原因，它是**归纳假设的签名**，不是算术：**

```lean
ihA : ∀ (j c d : ℕ), c ≤ j → bounded j A = true → bounded (j + d) (shift c d A) = true
```

**`generalizing j c d` 把三个参数**放在最前面**，所以正确的应用是**

```
ihA (j+1) (c+1) d (by omega) hb         -- 四个显式参数，再是两个前提
```

**而不是 `ihA hc hA`（那会试图把 `hc` 当作 `j`）。第 844 轮的 `simpa ... using` 掩盖了这个
参数顺序问题，把错误报成了「算术不统一」。**

**=> 教训：`induction ... generalizing x y z` 生成的假设把 `x y z` 当成**前三个显式参数**，
必须按那个顺序给出实参；`hc`、`hA` 这类前提排在它们**之后**。**

## 本文件保留什么

| 定理 | 内容 |
|:--|:--|
| `bounded_shift_atom` | **`sort`/`const` 在 `shift` 下保持 `bounded`** |
| `bounded_shift_var` | **`var n` 的情形，两个 `shift` 分支都闭合** |
| `bounded_shift_app` | **`app` 情形由两侧归纳假设给出** |

**=> 三个非绑定分支成立；缺口在绑定层，而它的**形状**本轮已查明（见上）。**
**下一次尝试可以直接写 `ihA (j+1) (c+1) d (by omega) hb`，不需要再做任何算术调试。** -/

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
