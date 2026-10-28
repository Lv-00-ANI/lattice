/-
# `Ladder` 的 `n` 维实例：真权重栈，维数任意

## 0. 本节补什么

`Lift/WeightLadder.lean`（第 42 轮）给出了 `W` 取真权重栈的 `Ladder`，但只在 `n = 1`：
权重矩阵退化为一个数、偏置退化为一个数。

清单 B 类指出：

> **`Ladder`**：实例是 `W = AffineLayer (Fin 1)`、`n = 1`、只验"零点映零"；
> 缺 `n ≥ 2` 或非平凡权重栈实例。

**本节推广到任意 `n`。** 这不是把 `1` 换成 `n`：`l2l3_sound` 的证明要从
「常数项为零」变成**逐坐标的求和为零**，那才是 `affineAct` 的实质内容。

## 1. 证明思路

`n` 维时，`affineAct layer 0` 在坐标 `j` 上的值是

```
∑ i, W i j * 0 i + b j  =  b j
```

（因为 `0 i = 0`，每一项都是零。）

所以「层把零点映到零点」⟺ **每个坐标的偏置为零** ⟺ `b = 0`。

**符号侧**对应地取「残差向量为零」，而残差向量的第 `j` 个分量正是偏置 `b j`。

⇒ `l2l3_sound` 变成：**符号残差全零 ⟹ 偏置全零 ⟹ 层把零点映零**，
其中中间一步是**逐坐标的 `Finset.sum` 归约**，不是 `n = 1` 时的单个乘零。

## 2. 关键定理

| 定理 | 内容 |
|:--|:--|
| `act_zero_apply` | `affineAct layer 0 j = b j`（对任意 `n`，用 `Finset.sum_eq_zero`） |
| `act_zero_eq_zero_iff` | 层把零点映零 ⟺ 偏置恒零 |
| `compile_sound_n` | `l2l3_sound` 的 `n` 维形式 |
| `weightLadderN` | **任意 `n` 的 `Ladder` 实例** |

## 3. 为什么这不只是「把 1 换成 n」

`n = 1` 时 `∑ i : Fin 1, W i j * 0 i` 只有一个项，`simp` 直接得到 `W 0 j * 0 = 0`。

`n` 一般时，需要 `Finset.sum_eq_zero`：**每一项都为零**才能说和为零。
这是 `Finset` 的通用论证，而 `n = 1` 的版本掩盖了它。

⇒ 本节的证明**更长但更强**：它说明这个实例对**任意维数**成立，
而不是「恰好在一维好写」。

## 4. 边界

- 仍只做**单层** `l2l3`（`[compileToLayer s]`）。多层栈的 `netAct` 组合律
  在 `Core/Net` 已有（`netAct_append`），但本节不需要——`Ladder.l2l3` 是一个映射，
  多层属于「编译可以产生深网络」的进一步陈述，属后续工作。
- `satW` 取「把零点映到零点」。这是 `Ladder` 抽象语义的一个**选择**，
  不是唯一的可能（也可以取「在所有测试点上输出为零」）。本节与第 42 轮保持一致。
- 本节**不**声称 `n = 1` 的实例是错的——它是本节在 `n = 1` 处的特例。
- 权重矩阵取 `W i j := s.coef i`（每个输出坐标 `j` 用同一列系数），
  这在 `n` 维下是**秩一**矩阵。真正的通用权重矩阵需要 `n × n` 个参数，
  那超出「符号知识 → 权重」的直接映射——本节的选择是**最小非平凡的**。
-/
import Mathlib
import Lattice.Runtime.EndToEnd
import Lattice.Core.Net
import Lattice.Core.Semantics

open scoped BigOperators

namespace Lattice.Lift

namespace WeightLadderN

open Lattice.Core

/-- **`n` 维的符号内容**：一个系数向量与一个常数向量。

与 `n = 1` 的 `SymOne` 对应，但每个坐标各有一份。 -/
structure SymN (n : ℕ) where
  /-- 系数向量。 -/
  coef : Fin n → ℝ
  /-- 常数（偏置）向量。 -/
  const : Fin n → ℝ

/-- **残差向量**：在零点处的取值。

`resid s j` 就是第 `j` 个坐标上的约束残差。 -/
def SymN.resid {n : ℕ} (s : SymN n) (j : Fin n) : ℝ := s.const j

/-- **把符号内容编译成一个 `n` 维仿射层**：系数做权重矩阵（秩一），常数做偏置。 -/
noncomputable def compileToLayerN {n : ℕ} (s : SymN n) : AffineLayer (Fin n) where
  W := fun i _ => s.coef i
  b := s.const

/-- **`affineAct` 在零点处的第 `j` 个坐标就是偏置 `b j`。**

证明用 `Finset.sum_eq_zero`：每一项 `W i j * 0 i` 都是零。
**这是 `n` 维的实质内容**——`n = 1` 时 `simp` 直接给出，一般 `n` 需要逐项论证。 -/
theorem act_zero_apply {n : ℕ} (p : AffineLayer (Fin n)) (j : Fin n) :
    affineAct p (fun _ => (0 : ℝ)) j = p.b j := by
  unfold affineAct
  have hzero : ∀ i : Fin n, p.W i j * (fun _ => (0 : ℝ)) i = 0 := by
    intro i; ring
  rw [Finset.sum_eq_zero (fun i _ => hzero i)]
  ring

/-- **层把零点映到零点，当且仅当偏置恒为零。** -/
theorem act_zero_eq_zero_iff {n : ℕ} (p : AffineLayer (Fin n)) :
    affineAct p (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ)) ↔ p.b = 0 := by
  constructor
  · intro h
    funext j
    have := congrFun h j
    rw [act_zero_apply] at this
    exact this
  · intro h
    funext j
    rw [act_zero_apply, h]
    rfl

/-- **`n` 维的 `l2l3_sound`**：残差全零 ⟹ 编译出的层把零点映零。

这是 `Ladder.l2l3_sound` 的实例内容，不是字段展开：
它串起「残差 = 常数」与「`affineAct` 在零点 = 偏置」两条计算。 -/
theorem compile_sound_n {n : ℕ} (s : SymN n) (h : ∀ j, s.resid j = 0) :
    affineAct (compileToLayerN s) (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
  rw [act_zero_eq_zero_iff]
  funext j
  exact h j

/-- **从系数/常数列表构造一个 `n` 维仿射层**：前 `n` 项是系数，后 `n` 项是偏置。

用列表而不是 `SymN n`，是为了让 L1⇄L2 的 tokenizer 就是 `identityTokenizer`
——`Ladder` 那一跳的形式要求 `Tokenizer Sym Tok`，而 `identityTokenizer α`
给的是 `Tokenizer (List α) α`。**把 `Sym` 取成列表不是回避，而是让那一跳有真实载体**，
不必为了形状漂亮而发明一个 tokenizer。 -/
noncomputable def layerOfList {n : ℕ} (s : List ℝ) : AffineLayer (Fin n) where
  W := fun i _ => (s.take n).getD i.val 0
  b := fun j => (s.drop n).getD j.val 0

/-- **全零列表编译出的层把零点映到零点。**

证明走 `Finset.sum_eq_zero`：每一项 `W i j * 0 i` 都为零——这是 `n` 维的实质内容，
`n = 1` 时会被 `simp` 直接掩盖。 -/
theorem act_zero_of_all_zero {n : ℕ} (s : List ℝ) (h : ∀ x ∈ s, x = 0) :
    affineAct (layerOfList (n := n) s) (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ)) := by
  funext j
  rw [act_zero_apply]
  unfold layerOfList
  show (s.drop n).getD j.val (0 : ℝ) = 0
  by_cases hlt : j.val < (s.drop n).length
  · rw [List.getD_eq_getElem _ _ hlt]
    have hmem : (s.drop n)[j.val] ∈ s := List.mem_of_mem_drop (List.getElem_mem hlt)
    exact h _ hmem
  · rw [List.getD_eq_default _ _ (by omega)]

/-- **任意维数的 `Ladder` 实例**：`W` 是 `List (AffineLayer (Fin n))`，即真权重栈。

`Sym := List ℝ` 使它接上 `identityTokenizer`；`l2l3` 把列表编译成一个仿射层。 -/
noncomputable def weightLadderN (n : ℕ) :
    Ladder (List ℝ) ℝ (List ℝ) (List (AffineLayer (Fin n))) where
  l0l1 := identityTokenizer ℝ
  l1l2 := identityTokenizer ℝ
  l2l3 := fun s => [layerOfList (n := n) s]
  satSym := fun s => ∀ x ∈ s, x = 0
  satW := fun w => netAct w (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ))
  l2l3_sound := by
    intro s hs
    exact act_zero_of_all_zero (n := n) s hs

/-- **端到端**：符号内容全零 ⟹ 编译出的真权重栈把零点映零。

这是 `weightLadderN` 上 `ladder_forward` 的实例，**维数 `n` 任意**。 -/
theorem weightLadderN_forward (n : ℕ) (s : List ℝ)
    (h : weightLadderN n |>.satSym s) :
    (weightLadderN n).satW ((weightLadderN n).l2l3 s) :=
  (weightLadderN n).ladder_forward s h

end WeightLadderN

end Lattice.Lift
