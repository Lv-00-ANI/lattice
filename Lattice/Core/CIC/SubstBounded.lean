import Mathlib
import Lattice.Core.CIC.SubstAvoids

/-!
# `bounded j t → subst j s t = t`：替换的不动点判据（阶段 5）

## 第 842 轮的结论，本轮把它证出来

**第 842 轮证明 `avoids j` **不足以**使 `subst` 成为不动点（`n > j` 仍会递减），
并引入 `bounded j t`（「`j` 是 `t` 自由变量的上界」）作为正确条件。**

**本文件证明那条判据：**

```lean
subst_bounded (j) (s t) (h : bounded j t = true) : subst j s t = t
```

## 六个分支

| `t` | 依据 |
|:--|:--|
| `sort` / `const` | **`rfl`** |
| `var n` | **`bounded_var_lt` 给出 `n < j`，于是 `subst` 走 `n < j` 分支返回 `var n`** |
| `app f a` | **两侧用归纳假设，`bounded` 由 `&&` 拆开** |
| `lam A b` | **类型在 `j` 处，体在 `j+1` 处（`bounded` 的绑定加一，与 `subst` 的 `j+1` 恰好对上）** |
| `pi A B` | **同 `lam`** |
| `letE A t b` | **类型与值在 `j` 处，体在 `j+1` 处** |

**=> 绑定层之所以闭合，是因为 `bounded` 与 `subst` 在绑定处**加的是同一个一**。
这与第 839 轮 `avoids`/`shift` 在 cutoff 上错开一的那次失败形成直接对照：
**当两个定义的加一位置一致时，归纳就闭合。** -/

namespace Lattice.Core.CIC

/-- **`bounded j t` 蕴含 `subst j s t = t`。**

**=> 对 `t` 结构归纳，`j` 与 `s` 一般化。六个分支全部闭合；
绑定层靠 `bounded (j+1) b` 与 `subst (j+1) (shift 0 1 s) b` 在同一个 `j+1` 上对齐。** -/
theorem subst_bounded {j : ℕ} {s t : Term} (h : bounded j t = true) : subst j s t = t := by
  induction t generalizing j s with
  | sort k l => rfl
  | const k => rfl
  | var n =>
      have hn : n < j := bounded_var_lt h
      show (if n = j then s else if n < j then Term.var n else Term.var (n - 1)) = Term.var n
      rw [if_neg (by omega : ¬ n = j), if_pos hn]
  | app f a ihf iha =>
      have hf : bounded j f = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have ha : bounded j a = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      simp only [subst, ihf hf, iha ha]
  | lam A b ihA ihb =>
      have hA : bounded j A = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have hb : bounded (j + 1) b = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      simp only [subst, ihA hA, ihb hb]
  | pi A B ihA ihB =>
      have hA : bounded j A = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have hB : bounded (j + 1) B = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      simp only [subst, ihA hA, ihB hB]
  | letE A t b ihA iht ihb =>
      have hA : bounded j A = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1.1
      have ht : bounded j t = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1.2
      have hb : bounded (j + 1) b = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      simp only [subst, ihA hA, iht ht, ihb hb]

/-- **`bounded` 把 `subst` 变成恒等：替换项 `s` 完全不出现在结果里。**

**=> 上一条的直接推论；单独命名以便在联合律的 `var` 分支里直接引用。** -/
theorem subst_bounded_ignores {j : ℕ} {s t : Term} (h : bounded j t = true) :
    subst j s t = t :=
  subst_bounded h

end Lattice.Core.CIC
