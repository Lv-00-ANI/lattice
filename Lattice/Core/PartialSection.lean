import Mathlib

/-!
# **部分截面：符号嵌入权重，而提取可以失败**

## 为什么需要这个抽象

目标说真正的难点只有「符号 ⇄ 权重」这一跳。这一跳在树里有两个**方向**的定理：

- 正向（符号 → 权重）：`compileSkel : IRSkeleton → IRWeights`，**全函数**；
- 逆向（权重 → 符号）：`extract : IRWeights → Option IRSkeleton`，**部分函数**。

（`extract_compile : extract (compileSkel k) = some k` 在 `Core/IR/Extract.lean`；
`compile_extract_layer : compileToLayer (extractLayer ls) = ls` 在 `Runtime/LoopClosure.lean`。）

**两个方向不是同一种东西，而 `Option` 不是瑕疵。** 权重携带的信息比骨架多
（`compileSkel` 只在位置 0 写 `skeletonCode k`，其余位置写 `0`），所以提取在**像之外**可以失败。
把它说成「提取恰好定义在像上」是**陈述错了**——它在某些像外输入上也会返回值。
准确的说法是：**像 ⊆ 提取有定义的地方**，且**在像上提取给出的见证就是原像**。

## 本文件提供什么

`PartialSection Sym W` = 一个全映射 `compile` 加一个部分映射 `extract`，满足
`extract ∘ compile = some` 且 `compile` 单射。这正是「符号嵌入权重」的代数内容：
**`compile` 是一个分裂单态射**（在 `Option` 的 Kleisli 意义下），而不是同构。

**⇒ 它比单独引用那两条定理更强的地方在于：它把「这一跳是嵌入而非同构」变成**类型**，
于是「哪些结论只依赖嵌入性」有了答案——本文件的五条引理就是那个答案。**
-/

namespace Lattice.Core

/-- **部分截面**：符号嵌入权重，提取是它的部分右逆。

**字段含义：**
- `compile`：全映射（符号 → 权重）。**必须全——编译不会失败。**
- `extract`：部分映射（权重 → `Option` 符号）。**必须部分——权重比符号多携带信息。**
- `retract`：`extract (compile s) = some s`。**提取在像上恒成功。**
- `compile_injective`：`compile` 单射。**不同符号编译出不同权重，这一跳不丢信息。**

**⇒ 四条合起来就是「`compile` 是分裂单态射」。`Option` 出现在 `extract` 的返回类型里，
是「提取在像外可能失败」这一事实的**类型级**记录，不是补丁。** -/
structure PartialSection (Sym W : Type) where
  /-- The total map: symbols compile into weights. -/
  compile : Sym → W
  /-- The partial map: extraction may fail, which is why it returns `Option`. -/
  extract : W → Option Sym
  /-- **Extraction succeeds on the image.** -/
  retract : ∀ s : Sym, extract (compile s) = some s
  /-- **Compilation is injective**, so the embedding loses no information. -/
  compile_injective : Function.Injective compile

namespace PartialSection

variable {Sym W : Type}

/-- **提取在像上恒成功**（`retract` 的直读）。 -/
theorem retract_some (P : PartialSection Sym W) (s : Sym) : P.extract (P.compile s) = some s :=
  P.retract s

/-- **像上的提取有定义**：存在一个 `s` 使 `extract` 返回 `some s`。

**⇒ 这是「部分」与「全」的差别的可用形式：在像上，`Option` 从不落到 `none`。** -/
theorem isSome_retract (P : PartialSection Sym W) (s : Sym) :
    (P.extract (P.compile s)).isSome := by
  rw [P.retract s]
  rfl

/-- **反向的截面性**：若 `w = compile s`，则提取 `w` 恰好得到 `s`。

**⇒ 与 `retract` 互为反向陈述；它给出「已知原像时提取的结果可预测」。** -/
theorem extract_eq_some_of_compile_eq (P : PartialSection Sym W) {s : Sym} {w : W}
    (h : P.compile s = w) : P.extract w = some s := by
  rw [← h]
  exact P.retract s

/-- **在像上，提取给出的见证就是原像。**

**⇒ 这是本抽象最有用的推论，也是它强于「两条定理并列」的地方：
调用者拿到一个提取结果 `some s` 和一个「该权重是编译出来的」事实 `w ∈ range compile`，
就能断言 `compile s = w`——不必再比较权重向量。**

**⇒ 证明只用到 `retract`：把 `w ∈ range` 展开成 `w = compile s'`，则 `some s' = some s`，故 `s' = s`。** -/
theorem compile_eq_of_mem_range (P : PartialSection Sym W) {w : W} {s : Sym}
    (hext : P.extract w = some s) (hmem : w ∈ Set.range P.compile) : P.compile s = w := by
  obtain ⟨s', rfl⟩ := hmem
  rw [P.retract s'] at hext
  have hss : s' = s := Option.some.inj hext
  rw [hss]

end PartialSection

end Lattice.Core