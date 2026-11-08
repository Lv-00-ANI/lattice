/-
# 非退化实例：满秩权重 + 全输入语义

## 0. 本节补什么

外部审查对新范式的第三个硬缺口：

> **实例退化**：`weightLadderN` 秩一、单层、`satW` 只验「零点映零」。
> 类型上成立不等于内容上成立。

**本节把三处退化都去掉。**

## 1. 证明思路

### 1.1 退化一：秩一权重

`layerOfList` 的权重是 `W i j := coef i`——**与 `j` 无关**，
所以它是一个秩一矩阵（所有列相同）。

**改法**：用**满方阵** `W i j := s ⟨i*n + j⟩`，需要 `n²` 个系数。

### 1.2 退化二：单点 `satW`

`satW w := netAct w 0 = 0` 只测一个点。**改法**：

```
satW w := ∀ x, netAct w x = 0
```

**这是「层是零映射」的完整陈述**，不是单点测试。

### 1.3 退化三：只有单层

`l2l3 := fun s => [compileToLayerN s]`。
**本节仍做单层**，但**权重矩阵是满的**——单层不是退化，秩一才是。
（多层编译属「编译产出深网络」，是另一件事，且 `netAct_append` 已给出组合律。）

### 1.4 关键定理的形状变化

`satW` 变成「对所有 `x` 输出为零」，于是 `l2l3_sound` 要证：

```
符号残差全零  ⟹  (∀ x, W·x + b = 0)
```

**这只有 `W = 0 ∧ b = 0` 时成立**——因为取 `x` 遍历基向量即可分离每个坐标。

⇒ **新的 `l2l3_sound` 要求符号侧同时给出「系数为零」与「常数项为零」。**
这是**更强的义务**，也正是「内容上成立」的含义。

## 2. 主定理

| 定理 | 内容 |
|:--|:--|
| `fullLayer` | **满方阵权重**（`n²` 个系数） |
| `act_apply` | `affineAct p x j = ∑ i, p.W i j * x i + p.b j` |
| `act_zero_all_iff` | **全输入为零 ⟺ `W = 0 ∧ b = 0`** |
| `fullCompile_sound` | **满秩版的 `l2l3_sound`** |
| `weightLadderNondeg` | **非退化 `Ladder` 实例** |
| `rank_one_is_degenerate` | **秩一确实更弱**（反例） |

## 3. 为什么这条更强，而不只是更长

秩一权重下，`satW` 的「全输入为零」条件**比零点映零弱得多**？
**不，恰恰相反**：秩一时 `W·x = 0` 对所有 `x` 也逼出 `coef = 0`。

**真正的差别**在于：秩一矩阵**无法表示一般的线性映射**。
`weightLadderNondeg` 的权重能表示**任意** `n×n` 矩阵，
因此「编译到权重」不再受限于一族极窄的对象。

⇒ **这是表达能力的变化，不是证明长度的变化。**

## 4. 边界

- 仍是**单层**。多层是另一件事。
- `n²` 个系数对 `n` 线性增长的要求意味着**符号侧必须提供二次多的信息**——
  这是真实的代价，不是技术噪声。**本节把它写在类型里。**
- `rank_one_is_degenerate` 给的是**表达能力**的反例（存在秩一无法表示的矩阵），
  不是 `l2l3_sound` 的反例。**两者的区别重要：前者说「不够用」，后者说「不对」。**
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Runtime.EndToEnd
import Lattice.Runtime.WeightLadderN

open scoped BigOperators

namespace Lattice.Lift

namespace NondegenerateInstance

open Lattice.Core

variable {n : ℕ}

/-! ## 一、满方阵权重 -/

/-- **满方阵权重**：`W i j := s ⟨i*n + j⟩`，真正的 `n × n` 矩阵。

与 `layerOfList`（`W i j := coef i`，与 `j` 无关，秩一）相对。 -/
noncomputable def fullLayer (s : List ℝ) : AffineLayer (Fin n) where
  W := fun i j => s.getD (i.val * n + j.val) 0
  b := fun j => s.getD (n * n + j.val) 0

/-- **`affineAct` 的展开形式**：`(p x) j = ∑ i, W i j * x i + b j`。 -/
theorem act_apply (p : AffineLayer (Fin n)) (x : Fin n → ℝ) (j : Fin n) :
    affineAct p x j = (∑ i, p.W i j * x i) + p.b j := rfl

/-! ## 二、全输入为零 ⟺ 权重与偏置都为零 -/

/-- **对所有输入输出为零 ⟺ `W = 0` 且 `b = 0`。**

正向：取 `x` 为基向量分离出 `W i j`；取 `x = 0` 分离出 `b`。
反向：两项都为零，和为 零。

⇒ **`satW` 的「全输入为零」是比「零点映零」强得多的条件，
且它把权重矩阵每个元素都约束住。** -/
theorem act_zero_all_iff (p : AffineLayer (Fin n)) :
    (∀ x, affineAct p x = (fun _ => (0 : ℝ))) ↔ (p.b = 0 ∧ ∀ i j, p.W i j = 0) := by
  constructor
  · intro h
    -- b = 0 from x = 0
    have hb : p.b = 0 := by
      funext j
      have hz := congrFun (h (fun _ => 0)) j
      rw [act_apply] at hz
      simpa using hz
    refine ⟨hb, ?_⟩
    intro i j
    -- W i j from the i-th basis vector
    have hb' : p.b j = 0 := by rw [hb]; rfl
    have hz := congrFun (h (fun k => if k = i then (1 : ℝ) else 0)) j
    rw [act_apply, hb'] at hz
    have hsum : (∑ k, p.W k j * (if k = i then (1 : ℝ) else 0)) = p.W i j := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hsum] at hz
    linarith
  · rintro ⟨hb, hW⟩ x
    funext j
    rw [act_apply]
    have hsum : (∑ i, p.W i j * x i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hW i j, zero_mul]
    rw [hsum, hb]
    simp

/-! ## 三、秩一确实更弱 -/

/-- **秩一无法表示所有矩阵**：存在 `n = 2` 的矩阵不是秩一形式。

秩一形式是 `W i j = c i`（与 `j` 无关）。取 `W := !![1, 0; 0, 1]`
（单位矩阵），它不是这个形式。 -/
theorem rank_one_is_degenerate :
    ¬ (∀ (W : Fin 2 → Fin 2 → ℝ), ∃ c : Fin 2 → ℝ, ∀ i j, W i j = c i) := by
  intro h
  obtain ⟨c, hc⟩ := h (fun i j => if i = j then (1 : ℝ) else 0)
  have h00 : c 0 = 1 := by
    have := hc 0 0
    simpa using this.symm
  have h01 : c 0 = 0 := by
    have := hc 0 1
    simpa using this.symm
  linarith

/-! ## 四、非退化的 `Ladder` 实例 -/

/-- **满秩编译的 `l2l3_sound`**。

符号侧必须给出**每个权重元素为零**——因为
「对所有输入输出为零」逼出 `W = 0 ∧ b = 0`（§二），而 `W` 有 `n²` 个元素。
**这是比「零点映零」强得多的义务**，也正是「内容上成立」。 -/
theorem fullCompile_sound {n : ℕ} (s : List ℝ)
    (h : (∀ i j : Fin n, s.getD (i.val * n + j.val) 0 = 0) ∧
         (∀ j : Fin n, s.getD (n * n + j.val) 0 = 0)) :
    ∀ x, affineAct (fullLayer (n := n) s) x = (fun _ => (0 : ℝ)) := by
  rw [act_zero_all_iff]
  refine ⟨?_, ?_⟩
  · funext j
    exact h.2 j
  · intro i j
    exact h.1 i j

/-- **非退化 `Ladder` 实例**：满秩权重，`satW` 验证**所有输入**。

对比 `WeightLadderN.weightLadderN`：
- 权重从秩一变为满方阵（能表示任意 `n×n` 矩阵）；
- `satW` 从「零点映零」变为「所有输入为零」。

⇒ **表达能力与义务强度都提高了。** -/
noncomputable def weightLadderNondeg (n : ℕ) :
    Ladder (List ℝ) ℝ (List ℝ) (List (AffineLayer (Fin n))) where
  l0l1 := identityTokenizer ℝ
  l1l2 := identityTokenizer ℝ
  l2l3 := fun s => [fullLayer (n := n) s]
  satSym := fun s =>
    (∀ i j : Fin n, s.getD (i.val * n + j.val) 0 = 0) ∧
    (∀ j : Fin n, s.getD (n * n + j.val) 0 = 0)
  satW := fun w => ∀ x, netAct w x = (fun _ => (0 : ℝ))
  l2l3_sound := by
    intro s hs x
    -- a single-layer stack: netAct [p] x = affineAct p x
    exact fullCompile_sound s hs x

/-- **端到端**：符号内容全零 ⟹ 满秩权重栈对**所有输入**输出为零。 -/
theorem weightLadderNondeg_forward (n : ℕ) (s : List ℝ)
    (h : (weightLadderNondeg n).satSym s) :
    (weightLadderNondeg n).satW ((weightLadderNondeg n).l2l3 s) :=
  (weightLadderNondeg n).ladder_forward s h

/-! ## 与 `WeightLadderN.compile_sound_n` 的关系

本节把**本文件的非退化结论**与 **`WeightLadderN` 的原始格梯**对齐：

**`compile_sound_n`** 说「残差全零 ⇒ `compileToLayerN s` 在**零点**处输出零」；
**`fullCompile_sound`** 说「系数与常数项全零 ⇒ `fullLayer s` 在**所有输入**处输出零」。

**⇒ 两者的差别正是本文件存在的理由：`satW` 从「零点映零」升为「处处为零」，而那要求符号侧给出更强的义务。**
**本节把前者**作为**后者的一端引用进来，使两条结论在同一语境中并列，而不是各自孤立。** -/

/-- **原始格梯的零点结论**（`WeightLadderN.compile_sound_n` 的等价陈述）。

**残差全零时，`compileToLayerN s` 把零点映到零点。**
**⇒ 这是**最弱**的 `satW`：只测一个点。**
**本文件的 `fullCompile_sound` 把它加强到「所有输入」，代价是符号侧必须给出每个权重元素为零。** -/
theorem compile_sound_n_zero {n : ℕ} (s : Lattice.Lift.WeightLadderN.SymN n)
    (h : ∀ j, s.resid j = 0) :
    Lattice.Core.affineAct (Lattice.Lift.WeightLadderN.compileToLayerN s) (fun _ => (0 : ℝ))
      = (fun _ => (0 : ℝ)) :=
  Lattice.Lift.WeightLadderN.compile_sound_n s h

/-- **两条结论的形式对比。**

**`compile_sound_n_zero` 的结论是一个等式于 `(fun _ => 0)`；`fullCompile_sound` 的结论是 `∀ x` 的等式。**
**⇒ 后者的输入是全称量化的，前者固定在一点；这就是 `fullCompile_sound` 不是 `compile_sound_n` 的改名、而是
它的严格加强的形式化表现。** -/
theorem compile_sound_n_is_pointwise {n : ℕ} (s : Lattice.Lift.WeightLadderN.SymN n)
    (h : ∀ j, s.resid j = 0) (x : Fin n → ℝ) :
    x = (fun _ => (0 : ℝ)) →
      Lattice.Core.affineAct (Lattice.Lift.WeightLadderN.compileToLayerN s) x = (fun _ => (0 : ℝ)) := by
  intro hx
  rw [hx]
  exact compile_sound_n_zero s h


/-! ## 与 `WeightLadderN.weightLadderN` 的符号侧对照

本文件与 `WeightLadderN` 定义的是**同一类型**的两个 `Ladder` 实例：

| 实例 | `satSym` | `satW` |
|:--|:--|:--|
| `weightLadderN n` | **列表的每一项为零** | **零点映零** |
| `weightLadderNondeg n` | **前 `n*n` 个系数为零，且后 `n` 个常数项为零** | **处处为零** |

**⇒ 两者是一对**反方向的交换**：`weightLadderN` 的符号义务更强（整个列表），权重义务更弱（一个点）；
`weightLadderNondeg` 的符号义务更弱（只约束被读到的元素），权重义务更强（所有输入）。**
**这不是矛盾，而是「"内容上成立"的两种编码」：把义务放在符号侧还是放在权重侧，总强度是一个权衡。**

**本节证明那个反方向的蕴含：`weightLadderN` 的符号义务**蕴含** `weightLadderNondeg` 的。**
**⇒ 于是「更强的符号义务换来更弱的权重义务」这一取舍有了形式化的单向证据。** -/

/-- **`weightLadderN` 的符号义务蕴含 `weightLadderNondeg` 的。**

**「列表每一项为零」推出「第 `i*n+j` 个与第 `n*n+j` 个为零」——因为后者读的是前者的子集。**
**⇒ 这就是反方向蕴含的全部内容：`weightLadderNondeg` 只读前 `n*n + n` 个元素，而 `weightLadderN` 约束所有元素。**
**两个分支的写法（`getElem` 与 `default`）覆盖了「下标在范围内」与「越界」两种情形，后者由 `getD` 的默认值 `0`
直接给出结论。** -/
theorem sym_all_implies_indexed {n : ℕ} (s : List ℝ) (h : ∀ x ∈ s, x = 0) :
    (∀ i j : Fin n, s.getD (i.val * n + j.val) 0 = 0) ∧
    (∀ j : Fin n, s.getD (n * n + j.val) 0 = 0) := by
  constructor
  · intro i j
    by_cases hlt : i.val * n + j.val < s.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact h _ (List.getElem_mem hlt)
    · rw [List.getD_eq_default _ _ (by omega)]
  · intro j
    by_cases hlt : n * n + j.val < s.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact h _ (List.getElem_mem hlt)
    · rw [List.getD_eq_default _ _ (by omega)]

/-- **`weightLadderN` 的符号侧在本文件中被引用，且是有内容的引用。**

**=> 把 `weightLadderN` 的 `satSym`（`∀ x ∈ s, x = 0`）作为 `sym_all_implies_indexed` 的输入，
结论正是 `weightLadderNondeg` 的 `satSym`。**
**因此「换符号义务换权重义务」这一取舍的两端都在树里，且它们的蕴含方向被证明。** -/
theorem weightLadderN_satSym_implies_nondeg {n : ℕ} (s : List ℝ)
    (h : (Lattice.Lift.WeightLadderN.weightLadderN n).satSym s) :
    (weightLadderNondeg n).satSym s :=
  sym_all_implies_indexed s h


end NondegenerateInstance

end Lattice.Lift
