import Lattice.Core.PartialSection
import Lattice.Core.IR.Extract

/-!
# **符号 ⇄ 权重那一跳是一个部分截面**

## 这个文件做什么

`Core/PartialSection.lean` 给出了抽象：`compile` 全、`extract` 部分、`extract ∘ compile = some`、
`compile` 单射——即「符号嵌入权重」。本文件把「符号 ⇄ 权重」这一跳**实例化**为那个抽象。

**⇒ 这一步不是包装。它把「这一跳是哪一类映射」这个问题从**两条并列定理**变成一个**类型**，
从而让抽象层的五条引理（尤其是 `compile_eq_of_mem_range`）可以直接用于这一跳。**
-/

namespace Lattice.Core.IR

/-- **符号 ⇄ 权重：`compileSkel` 是 `extract` 的部分截面。**

**⇒ 四个字段的来源：**
- `compile := compileSkel`（`Core/IR/Chain.lean`，全函数）
- `extract := extract`（`Core/IR/Extract.lean`，返回 `Option`）
- `retract := extract_compile`（提取在像上恒成功）
- **`compile_injective`**：由 `extract_injective_on_compiled` 得出——若 `compileSkel k = compileSkel l`，
  则两边 `extract` 相同，故 `k = l`。

**⇒ 这一条把「注入性」与「往返」联系起来：注入性不是另证的性质，而是**提取在像上成功**的直接推论。** -/
noncomputable def extractPartialSection : Lattice.Core.PartialSection IRSkeleton IRWeights where
  compile := compileSkel
  extract := extract
  retract := extract_compile
  compile_injective := fun k l h => extract_injective_on_compiled k l (by rw [h])

/-- **编译出的权重恒可提取。**（抽象层 `isSome_retract` 在这一跳上的兑现。） -/
theorem compiled_weights_extract (k : IRSkeleton) : (extract (compileSkel k)).isSome :=
  Lattice.Core.PartialSection.isSome_retract extractPartialSection k

/-- **在像上，提取给出的见证就是原像。**

**⇒ 这是抽象层 `compile_eq_of_mem_range` 在这一跳上的兑现，也是它最实用的形式：
调用者已知 `extract W = some k` 且 `W` 是某个骨架编译出来的，就能断言 `compileSkel k = W`——
不必比较函数（`IRWeights` 是 `ℕ → ℝ`，逐点比较并不便宜）。**

**⇒ 注意这条**不**声称 `extract` 在像外一定失败：它只说**在像内**成功且见证唯一。
`Option` 的 `none` 分支在这里没有出现，这正是「像 ⊆ 提取有定义的地方」的准确含义。** -/
theorem extract_witness_is_preimage {k : IRSkeleton} {W : IRWeights}
    (hext : extract W = some k) (hmem : W ∈ Set.range compileSkel) : compileSkel k = W :=
  Lattice.Core.PartialSection.compile_eq_of_mem_range extractPartialSection hext hmem

/-- **这一跳丢掉了什么：`extract` 不是单射。**

**⇒ 存在两个不同的权重提取到同一个骨架。这不是缺陷，而是「权重携带的信息比符号多」的
形式化后果：`compileSkel` 只在位置 `0` 写 `skeletonCode k`，其余位置恒为 `0`，
所以任何只在别处不同的权重都与它提取到同一个骨架。**

**⇒ 本条的内容就是**指出这一半不对称**：`compile` 单射（上一条），`extract` 不单射（本条），
于是这一跳是**嵌入**而非同构。** -/
theorem extract_not_injective :
    ¬ Function.Injective (extract : IRWeights → Option IRSkeleton) := by
  intro hinj
  -- **两个权重：全零，与「仅在位置 1 处不同」。**
  -- **两者在位置 0 上相等，而 `weightCodeIR` 只读位置 0，故提取结果相等。**
  let W₁ : IRWeights := fun _ => (0 : ℝ)
  let W₂ : IRWeights := fun n => if n = 1 then (1 : ℝ) else 0
  have h0 : W₂ 0 = W₁ 0 := by
    simp only [W₂, W₁]
    rw [if_neg (by norm_num : (0 : ℕ) ≠ 1)]
  have hneq : W₁ ≠ W₂ := by
    intro h
    have h1 := congrFun h 1
    simp only [W₁, W₂, if_pos rfl] at h1
    norm_num at h1
  have heq : extract W₁ = extract W₂ := by
    unfold extract weightCodeIR
    rw [h0]
  exact hneq (hinj heq)

end Lattice.Core.IR