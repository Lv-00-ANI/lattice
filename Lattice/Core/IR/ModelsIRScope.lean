import Mathlib
import Lattice.Core.IR.Obligations

/-!
# **`ModelsIR` 到底约束了什么：把「重言」拆成四条定理**（阶段 X）

## 这个文件要回答的问题

**`Core/IR/Obligations.lean` 的 `compile_sound` 是 `have _ := h; exact rfl`，审计把它记为 X 类（重言）。**

**⇒ 说它「重言」只描述症状。本文件回答**为什么**重言、以及它到底约束了多少东西。**

## 根因：`ModelsIR` 只约束**一个实数**

```lean
def ModelsIR (W : IRWeights) (k : IRSkeleton) : Prop := W = compileSkel k

noncomputable def compileSkel (k : IRSkeleton) : IRWeights :=
  fun n => if n = 0 then (skeletonCode k : ℝ) else 0
```

**=> `compileSkel k` 的**第 0 个坐标**是码，**其余全部为 0**。**
**=> 于是 `ModelsIR W k` 说的是「`W 0` 等于那个码，别的坐标都为 0」——
它**根本没有提到** `W` 除第 0 位以外的任何值。**

**⇒ 这就是它无法成为行为陈述的机制：行为要看的是权重**怎样被读取**，
而 `ModelsIR` 只看**一个被塞进槽 0 的整数码**。**

## 四条定理，逐条收紧

| 定理 | 内容 |
|:--|:--|
| **`modelsIR_iff`** | 展开式：`ModelsIR W k ↔ W = compileSkel k` |
| **`modelsIR_slot_zero`** | 成立时 `W 0` **必须**等于码 |
| **`modelsIR_off_zero`** | 成立时**所有其它坐标必须为 0** |
| **`modelsIR_factors_through_code`** | **码相同则 `ModelsIR` 不可区分**——它**只**依赖 `skeletonCode` |
| **`compile_sound_hypothesis_unused`** | `WellFormed k` 这个前提**在不需要它的情况下**已成立 |

**=> 前两条合起来给出**充要**刻画的味道（第 3 条 + 第 2 条），
第 4 条说明它对「哪些骨架」完全不敏感，第 5 条说明 `compile_sound` 的前提是装饰。**

## 这为什么是 M-5 的前置

**M-5 是「权重 ⇄ 符号」在 `Compose` 层的那一跳。**
**⇒ 要给正向写 `Primitive`，它的 `post` 必须是一个**关于行为**的命题。**

**⇒ 而 `ModelsIR` 只约束一个码，所以以它为基础的 `post` 只能存 `True` 级别的信息。**
**=> 本文件把那句话变成了可引用的四条定理，从而**指出**修法：
新的 `ModelsIR` 必须**读取**权重（例如经 `extractSkel`）并把它与骨架比对，
而不是把骨架的**编码**塞进一个坐标。** -/

namespace Lattice.Core.IR

/-- **展开式：`ModelsIR W k` 就是 `W = compileSkel k`。**

**=> 本条自身是 `Iff.rfl` 级，但它把「`ModelsIR` 是一个等式」变成可引用的前提。** -/
theorem modelsIR_iff (W : IRWeights) (k : IRSkeleton) :
    ModelsIR W k ↔ W = compileSkel k :=
  Iff.rfl

/-- **成立时第 0 个坐标必须是那个码。**

**=> `compileSkel` 在 `n = 0` 处给出 `(skeletonCode k : ℝ)`。** -/
theorem modelsIR_slot_zero {W : IRWeights} {k : IRSkeleton} (h : ModelsIR W k) :
    W 0 = (skeletonCode k : ℝ) := by
  rw [modelsIR_iff] at h
  subst h
  unfold compileSkel
  rw [if_pos rfl]

/-- **⭐⭐ 成立时**其余所有坐标必须为 0**。**

**=> 这是本文件最锋利的一条：`ModelsIR` 对权重向量的**无限多个坐标**中
除第 0 位以外的每一个都只说「你是 0」，**没有任何一个坐标承载行为信息**。** -/
theorem modelsIR_off_zero {W : IRWeights} {k : IRSkeleton} (h : ModelsIR W k)
    (n : ℕ) (hn : n ≠ 0) : W n = 0 := by
  rw [modelsIR_iff] at h
  subst h
  unfold compileSkel
  rw [if_neg hn]

/-- **⭐⭐ `ModelsIR` **只**依赖 `skeletonCode`：码相同的两个骨架不可区分。**

**=> 于是它对「骨架里有哪些张量、哪些关系」**完全不敏感**——
**这是它不能充当行为陈述的结构性理由。** -/
theorem modelsIR_factors_through_code (W : IRWeights) (k j : IRSkeleton)
    (hcode : skeletonCode k = skeletonCode j) :
    (ModelsIR W k ↔ ModelsIR W j) := by
  rw [modelsIR_iff, modelsIR_iff]
  unfold compileSkel
  rw [hcode]

/-- **⭐⭐⭐ `compile_sound` 的前提**在不需要它的情况下**已成立。**

**=> 即 `WellFormed k` 是装饰：对**任意**骨架，`ModelsIR (compileSkel k) (semantics k)` 都成立。**
**=> 这是「X 类（重言）」的精确形式，也是把 `compile_sound` 从重言改成实质陈述时
**必须**改变的那一侧：改结论（`ModelsIR`），不是改前提。** -/
theorem compile_sound_hypothesis_unused (k : IRSkeleton) :
    ModelsIR (compileSkel k) (semantics k) :=
  rfl

end Lattice.Core.IR
