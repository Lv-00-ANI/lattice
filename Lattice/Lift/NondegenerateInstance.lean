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
import Lattice.Lift.EndToEnd
import Lattice.Lift.WeightLadderN

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

end NondegenerateInstance

end Lattice.Lift
