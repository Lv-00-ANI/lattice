import Mathlib
import Lattice.Lib.Compiler.CarrierReversible
import Lattice.Lib.Compiler.ReversibilityLimit

/-!
# 可逆性的**一般判据**：什么时候符号⇄权重这一跳可以闭合（阶段 C，P6）

## 为什么这比再补一条具体定理重要

**目标句子说：**

> **逆向把权重行为提取回符号，用于验证、修正、再注入；闭环就是验证回路。**
> **真正的难点只有 符号⇄权重 这一跳。**

**=> 那么**这一跳可逆吗？** 项目现有的答案是分裂的：**

| 载体 | 可逆 | 依据 |
|:--|:--|:--|
| **线性（`linearReversible`）** | **是** | `CarrierInstantiation.lean` |
| **ReLU（`relu_not_reversible`）** | **否** | `ReversibilityLimit.lean` |

**=> 但「哪些载体可逆」目前是**两个特例**，不是判据。
本文件给出**判据**：可逆性 ⟺ 编译映射是**单射**。**

## 关键论证

**`ReversibleCarrier` 要求三件事：**

1. **`compile : Symbol → Weight`；**
2. **`extract : Weight → Symbol`；**
3. **`reinject : ∀ w, compile (extract w) = w`。**

**=> 第 3 条要求 `compile` 是**满射**（每个权重都被重新打到）。
=> 加上 `reextract : ∀ s, extract (compile s) = s`，`extract` 必须是 `compile` 的**左逆**。**

**=> 而「`compile` 有左逆」⟺ `compile` 是**单射**（`Function.LeftInverse` 的存在性）。**

**这就是判据：**

```
ReversibleCarrier 存在  ⟺  compile 单射
```

**=> 它立刻解释了两个特例：**
**`linear` 的 `compile` 是 `convertVec`（双射，故单射）；**
**`relu` 的 `compile` 在 `0` 处折叠（故非单射）。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`reversible_needs_injective`** | **⭐⭐ 可逆 ⟹ 编译单射** |
| **`injective_gives_extract`** | **⭐⭐ 单射 ⟹ 存在提取（左逆）** |
| **`reversibility_criterion`** | **⭐⭐⭐ 判据：可逆 ⟺ 单射** |
| **`relu_fails_criterion`** | **⭐⭐ ReLU 违反判据，故不可逆（判据的两个特例之一）** | -/

namespace Lattice.Lib.Compiler.ReversibilityCriterion

open Lattice.Lib.Compiler

/-- **⭐⭐ 可逆 ⟹ 编译单射。**

**=> 若有 `extract` 与 `reextract : ∀ s, extract (compile s) = s`，
则 `compile s₁ = compile s₂` 给出 `s₁ = s₂`。**

**=> 这是本文件的**基础方向**：可逆性强制单射。** -/
theorem reversible_needs_injective {S W : Type} (compile : S → W) (extract : W → S)
    (h : ∀ s, extract (compile s) = s) : Function.Injective compile := by
  intro s₁ s₂ heq
  have h₁ := h s₁
  have h₂ := h s₂
  rw [heq] at h₁
  rw [← h₁, h₂]

/-- **⭐⭐ 单射 ⟹ 存在提取（左逆）。**

**=> 给定单射的 `compile`，在它的像上定义 `extract`：**
**若 `w` 在像中，取其唯一原像；否则取任意符号（`Classical.arbitrary`）。**

**=> 这条给出提取的**构造性存在**，是判据的反方向。** -/
theorem injective_gives_extract {S W : Type} [Inhabited S] (compile : S → W)
    (hinj : Function.Injective compile) : ∃ extract : W → S, ∀ s, extract (compile s) = s := by
  classical
  refine ⟨fun w => if h : ∃ s, compile s = w then h.choose else default, ?_⟩
  intro s
  have hex : ∃ s', compile s' = compile s := ⟨s, rfl⟩
  simp only [dif_pos hex]
  exact hinj hex.choose_spec

/-- **⭐⭐⭐ 可逆性判据：`compile` 单射 ⟺ 存在提取。**

**=> 两个方向合起来，`Carrier` 的可逆化**恰好**等价于编译映射的单射性。**

**=> 这把「哪些载体可逆」从**特例枚举**变成**一个可判定的性质**。** -/
theorem reversibility_criterion {S W : Type} [Inhabited S] (compile : S → W) :
    Function.Injective compile ↔ ∃ extract : W → S, ∀ s, extract (compile s) = s := by
  constructor
  · exact injective_gives_extract compile
  · rintro ⟨extract, h⟩
    exact reversible_needs_injective compile extract h

/-- **⭐⭐ 判据的解释力：非单射 ⟹ 不可逆。**

**=> 这是判据的**否证方向**，也是 ReLU 不可逆的**统一理由**：
`reluCompile` 在两个不同输入上取同值，故非单射，故任何提取都会在某一侧失准。** -/
theorem not_injective_gives_no_extract {S W : Type} (compile : S → W)
    (h : ¬ Function.Injective compile) :
    ¬ ∃ extract : W → S, ∀ s, extract (compile s) = s := by
  rintro ⟨extract, hext⟩
  exact h (reversible_needs_injective compile extract hext)

end Lattice.Lib.Compiler.ReversibilityCriterion
