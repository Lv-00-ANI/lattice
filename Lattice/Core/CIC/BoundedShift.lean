import Mathlib
import Lattice.Core.CIC.SubstBounded

/-!
# `bounded` 在 `shift` 下保持：完整证明（阶段 5）

## 两轮才走通的原因，以及最终写法

**第 844 轮把障碍误报成「算术不统一」；第 845 轮读错误信息后查明真正原因是
`induction ... generalizing j c d` 生成的归纳假设把这三个参数放在**最前面**：**

```lean
ihA : ∀ (j c d : Nat), c ≤ j → bounded j A = true → bounded (j + d) (shift c d A) = true
```

**所以正确的应用是 `ihA j c d hc hA`（本体）与 `ihA (j+1) (c+1) d (by omega) hb`（绑定体内），
而不是 `ihA hc hA`。**

**本轮按这个顺序写，`app` 与 `lam` 一次通过 —— 两轮的全部差别就是一个参数顺序。**

## 六个分支

| `t` | 依据 |
|:--|:--|
| `sort` / `const` | **`simp [bounded, shift]`** |
| `var n` | **`bounded_shift_var`** |
| `app f a` | **`ihf j c d hc hf` 与 `iha j c d hc ha`** |
| `lam A b` | **`ihA j c d hc hA` 与 `ihb (j+1) (c+1) d (by omega) hb`** |
| `pi A B` | **同 `lam`** |
| `letE A t b` | **类型与值用 `(j, c)`；体用 `(j+1, c+1)`** |

**=> 关键是把每个归纳假设的**三个一般化参数**显式给出，并把前提排在它们之后。** -/

namespace Lattice.Core.CIC

/-- **`var n` 在 `shift` 下的保持：`n < j` 给出 `n < j + d`。** -/
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

/-- **`bounded` 在 `shift` 下保持：上界恰好抬高 `d`。**

**=> 对 `t` 结构归纳，`j`、`c`、`d` 一般化。每个归纳假设的应用都显式给出这三个参数
（第 845 轮查明的那条规则），绑定处用 `(j+1, c+1, d)`。** -/
theorem bounded_shift {j c d : ℕ} (hc : c ≤ j) {t : Term} (h : bounded j t = true) :
    bounded (j + d) (shift c d t) = true := by
  induction t generalizing j c d with
  | sort k l => simp [bounded, shift]
  | const k => simp [bounded, shift]
  | var n => exact bounded_shift_var n (bounded_var_lt h) c d
  | app f a ihf iha =>
      have hf : bounded j f = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have ha : bounded j a = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      have h1 := @ihf j c d hc hf
      have h2 := @iha j c d hc ha
      simp only [shift, bounded, Bool.and_eq_true]
      exact ⟨h1, h2⟩
  | lam A b ihA ihb =>
      have hA : bounded j A = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have hb : bounded (j + 1) b = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      have h1 := @ihA j c d hc hA
      have h2 := @ihb (j + 1) (c + 1) d (by omega) hb
      have he : j + d + 1 = j + 1 + d := by omega
      simp only [shift, bounded, Bool.and_eq_true, he]
      exact ⟨h1, h2⟩
  | pi A B ihA ihB =>
      have hA : bounded j A = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.1
      have hB : bounded (j + 1) B = true := by
        simp only [bounded, Bool.and_eq_true] at h
        exact h.2
      have h1 := @ihA j c d hc hA
      have h2 := @ihB (j + 1) (c + 1) d (by omega) hB
      have he : j + d + 1 = j + 1 + d := by omega
      simp only [shift, bounded, Bool.and_eq_true, he]
      exact ⟨h1, h2⟩
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
      have h1 := @ihA j c d hc hA
      have h2 := @iht j c d hc ht
      have h3 := @ihb (j + 1) (c + 1) d (by omega) hb
      have he : j + d + 1 = j + 1 + d := by omega
      simp only [shift, bounded, Bool.and_eq_true, he]
      exact ⟨⟨h1, h2⟩, h3⟩

/-- **`sort` 在 `shift` 下保持 `bounded`（恒真）。** -/
theorem bounded_shift_atom (c d : ℕ) (k : SortKind) (l : Level) :
    bounded (0 + d) (shift c d (.sort k l)) = true := by
  simp [bounded, shift]

end Lattice.Core.CIC
