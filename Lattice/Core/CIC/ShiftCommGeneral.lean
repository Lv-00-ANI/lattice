import Mathlib
import Lattice.Core.CIC.Syntax
import Lattice.Core.CIC.ShiftComm

/-!
# 一般 cutoff 下的 shift 复合律（ALT-1）

## 这个文件为什么存在

**`ShiftNonComm.lean` 已经证明：不同 cutoff 的两次 `shift` **不**可交换 —— 那是一条反例，
它排除了 `shift c d (shift c' d t) = shift c' d (shift c d t)` 这个朴素形式。**

**但那只是说「朴素形式是假的」，没有说「真相是什么」。**
**⇒ 本文件给出**在什么条件下、以什么形式**两次 shift 可以复合 —— 也就是反例的正面补充。**

## 规律

**`shift c d` 把 `≥ c` 的自由变量整体右移 `d`。所以先 `shift c'`（较外层）再 `shift c`（较内层）时，
第二次必须**把第一次带来的位移算进去**：它的 cutoff 应当是 `c' + d` 而不是 `c'`。**

```
shift c d (shift c' d t) = shift (c' + d) d (shift c d t)      (c ≤ c')
```

**⇒ 「交换」的正确含义是**参数也一起调整**，而不是两个调用原样对调。
这正是 `CARRIER-REPLACEMENT.md` 里 ALT-1 所要求的「`c ≤ c'` 显式复合」形式。**

## 与既有结果的关系

| 定理 | 内容 |
|:--|:--|
| `shift_different_cutoffs_dont_commute` | 朴素形式是**假的**（反例） |
| **`shift_commute_general`（本节）** | **正确形式，带 `c ≤ c'` 前提** |
| `shift_zero_succ_var` | `c = 0, d = 1` 的特例 |

**三者并存，一件不废止。**
-/

namespace Lattice.Core.CIC

/-- **变量情形的复合律。**

**=> 唯一有内容的原子情形；其余构造子由归纳假设直接给出。**
**证明的关键是**先把内层 `shift` 归约成 `if`**，否则外层 `shift` 的模式匹配无法前进。** -/
theorem shift_commute_var (n c d c' : ℕ) (h : c ≤ c') :
    shift c d (shift c' d (Term.var n)) = shift (c' + d) d (shift c d (Term.var n)) := by
  -- Reduce the INNER shift first: `shift c' d (Term.var n)` is an `if`, and only after rewriting it
  -- does the outer `shift`'s pattern match become reducible.
  have hinner : shift c' d (Term.var n) = Term.var (if n < c' then n else n + d) := by
    unfold shift
    split <;> rfl
  have hinner' : shift c d (Term.var n) = Term.var (if n < c then n else n + d) := by
    unfold shift
    split <;> rfl
  rw [hinner, hinner']
  unfold shift
  by_cases h1 : n < c
  · have h2 : n < c' := by omega
    have h4 : n < c' + d := by omega
    simp only [h1, h2, h4, if_true]
  · by_cases h2 : n < c'
    · have h3 : n + d < c' + d := by omega
      have h4 : ¬ (n + d < c) := by omega
      simp only [h1, h2, h3, h4, if_true, if_false]
    · have h3 : ¬ (n + d < c' + d) := by omega
      have h4 : ¬ (n + d < c) := by omega
      simp only [h1, h2, h3, h4, if_false]

/-- **一般 cutoff 下的 shift 复合律（ALT-1）。**

**`c ≤ c'` 时，`shift c d` 与 `shift c' d` 复合为 `shift (c' + d) d` 与 `shift c d` 的复合。**

**=> 这是 `ShiftNonComm.lean` 那条反例的**正面补充**：反例说朴素形式假，本定理说真形式是什么。
二者并存 —— 一件不废止，而「交换」一词被换成可证的严格陈述。**
**⇒ 证明对 term 归纳；绑体情形的 `c' + 1 + d = c' + d + 1` 由 `omega` 给出，再用 `simp` 重写。**
**这一步不加就不能通过 —— 它不是排版问题，是两个定义上不同的数需要被证明相等。** -/
theorem shift_commute_general (t : Term) (c d c' : ℕ) (h : c ≤ c') :
    shift c d (shift c' d t) = shift (c' + d) d (shift c d t) := by
  induction t generalizing c c' with
  | var n => exact shift_commute_var n c d c' h
  | sort k l => simp only [shift]
  | const k => simp only [shift]
  | app f a ihf iha => simp only [shift, ihf c c' h, iha c c' h]
  | lam A b ihA ihb =>
      have e : c' + 1 + d = c' + d + 1 := by omega
      simp only [shift, ihA c c' h, e, ihb (c + 1) (c' + 1) (by omega)]
  | pi A B ihA ihB =>
      have e : c' + 1 + d = c' + d + 1 := by omega
      simp only [shift, ihA c c' h, e, ihB (c + 1) (c' + 1) (by omega)]
  | letE A tt b ihA iht ihb =>
      have e : c' + 1 + d = c' + d + 1 := by omega
      simp only [shift, ihA c c' h, iht c c' h, e, ihb (c + 1) (c' + 1) (by omega)]

end Lattice.Core.CIC
