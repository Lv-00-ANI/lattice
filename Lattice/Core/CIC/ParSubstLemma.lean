import Mathlib
import Lattice.Core.CIC.ParallelReductionVarying

/-!
# `ParRedV` 在 `shift` 下合同：结构子部分已证（阶段 5）

## 本轮做了什么

**第 825 轮把缺口定位为「`shift` 作用于标注，而 `ParRedU` 固定标注」。
本轮建立 `ParRedV`（`lam`/`letE`/`beta` 的标注可以变），并检验它在 `shift` 下是否合同。**

**结果：**结构性的构造子一次通过** —— 差别只在于标注是否允许变化。**

| 构造子 | 位移规则 | 结果 |
|:--|:--|:--|
| `app` | 两侧同 `c, d` | **通过** |
| **`lam`** | 标注 `c, d`；体 `c+1, d` | **通过（本轮修正的要点）** |
| **`pi`** | 定义域 `c, d`；余域 `c+1, d` | **通过** |
| `letL` / `letR` | 值 `c, d`；体 `c+1, d` | **通过** |

## 两类**不能**纳入的原因（本轮查清）

**1. `delta`：`const c` 按 `E c = some body` 展开。**

**`shift` 不改变 `const c`，也不改变 `E`，但它会把 `body` 变成 `shift c d body`。
而 `delta` 的结论是 `body`，**不是** `shift c d body`。
=> `delta` 与位移**不交换**：环境 `DefEnv` 与 `shift` 之间没有任何关系，
唯一自然的情形是 `d = 0`（此时 `shift c 0` 是恒等，本轮顺带证出 `shift_zero_displacement`）。**

**2. `beta` / `letE`：结论含 `subst`。**

**要穿过 `subst`，需要位移-替换交换律，本层没有。**

## 结论

**`ParRedV` 的**结构性部分**在 `shift` 下合同；`delta` 与含 `subst` 的部分不行。
本文件把结构部分写成 `ParRedVStruct` 并证出。** -/

namespace Lattice.Core.CIC

/-- **位移量为零时 `shift` 是恒等。**

**=> 对 `Term` 归纳，`c` 一般化。七个构造子全部闭合：`var` 情形因 `n + 0 = n` 而恒等，
`lam`/`pi`/`letE` 的体在 `c+1` 处也恒等（归纳假设对任意 `c` 成立）。
=> 这条说明 `delta` 的位移问题在 `d = 0` 时确实消失。** -/
theorem shift_zero_displacement (c : ℕ) (t : Term) : shift c 0 t = t := by
  induction t generalizing c with
  | sort k l => rfl
  | var n => simp [shift, Nat.add_zero]
  | const k => rfl
  | app f a ihf iha => simp only [shift]; rw [ihf, iha]
  | lam A b ihA ihb => simp only [shift]; rw [ihA, ihb]
  | pi A B ihA ihB => simp only [shift]; rw [ihA, ihB]
  | letE A t b ihA iht ihb => simp only [shift]; rw [ihA, iht, ihb]

/-- **结构性的平行归约：只含不触及环境与替换的构造子。**

**=> `zero`、`app`、`lam`、`pi`、`letL`、`letR` 六条。
`delta` 被排除（与 `E` 绑定），`beta`/`letE` 被排除（含 `subst`）。** -/
inductive ParRedVStruct (E : DefEnv) : Term → Term → Prop
  /-- **零处。** -/
  | zero (t : Term) : ParRedVStruct E t t
  /-- **应用。** -/
  | app {f f' a a' : Term} :
      ParRedVStruct E f f' → ParRedVStruct E a a' →
      ParRedVStruct E (.app f a) (.app f' a')
  /-- **抽象：标注与体都变。** -/
  | lam {A A' b b' : Term} :
      ParRedVStruct E A A' → ParRedVStruct E b b' →
      ParRedVStruct E (.lam A b) (.lam A' b')
  /-- **乘积：两部分都变。** -/
  | pi {A A' B B' : Term} :
      ParRedVStruct E A A' → ParRedVStruct E B B' →
      ParRedVStruct E (.pi A B) (.pi A' B')
  /-- **局部定义：只归约值。** -/
  | letL {A t t' b : Term} :
      ParRedVStruct E t t' → ParRedVStruct E (.letE A t b) (.letE A t' b)
  /-- **局部定义：只归约体。** -/
  | letR {A t b b' : Term} :
      ParRedVStruct E b b' → ParRedVStruct E (.letE A t b) (.letE A t b')

/-- **`ParRedVStruct` 在 `shift` 下合同。**

**=> 六情形全部一次闭合。`lam`/`pi`/`letR` 的体在 `c+1` 处递归、标注在 `c` 处 ——
因为 `ParRedVStruct` **允许标注变化**，这一点可以同时满足，
而第 825 轮的 `ParRedU`（固定标注）做不到。** -/
theorem parRedVStruct_shift (E : DefEnv) {a b : Term} (h : ParRedVStruct E a b) :
    ∀ (c d : ℕ), ParRedVStruct E (shift c d a) (shift c d b) := by
  induction h with
  | zero t => intro c d; exact ParRedVStruct.zero _
  | app hf ha ihf iha => intro c d; exact ParRedVStruct.app (ihf c d) (iha c d)
  | lam hA hb ihA ihb => intro c d; exact ParRedVStruct.lam (ihA c d) (ihb (c + 1) d)
  | pi hA hB ihA ihB => intro c d; exact ParRedVStruct.pi (ihA c d) (ihB (c + 1) d)
  | letL ht iht => intro c d; exact ParRedVStruct.letL (iht c d)
  | letR hb ihb => intro c d; exact ParRedVStruct.letR (ihb (c + 1) d)

end Lattice.Core.CIC
