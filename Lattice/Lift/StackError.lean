/-
# 从单层到层栈：`affineAct` 的 Lipschitz 常数与两层误差传播

## 0. 补的是什么

`Lift/QuantErrorPropagation.lean` 证明了**单层**的误差传播：

```
权重/偏置每个分量差 ≤ ε，输入每个分量 ≤ M  ⟹  输出每个分量差 ≤ ε · n · M + ε
```

那是「同一个输入喂给两个不同的层」。**层栈需要另一种东西**：同一个层喂给**两个不同的输入**。
没有它，「多层网络的误差」无从谈起——**因为它根本不是一个关于网络的问题，而是两条不相干的
单层结论。**

本节补上那块：**`affineAct` 对输入是 Lipschitz 的，常数是层的量级 `layerMag`。**

## 1. `layerMag` 是什么，为什么是这个

```lean
colMag L j   := (∑ i, |L.W i j|) + |L.b j|      -- 第 j 个输出坐标的量级
layerMag L   := ∑ j, colMag L j                 -- 整层的量级
```

**为什么取绝对值之和而不是算子范数**：算子范数需要谱理论（`‖W‖₂` 是最大奇异值），
而本节要的是**可加、可归纳**的界。`∑ |W i j|` 是**列和的最大值**的粗版，
**代价是界更松，收益是它能在 `List` 上归纳**——而多层正是归纳。

**这不是「用弱的界凑合」**：它对所有层、所有维数成立，而谱范数在 `Fin n` 上的
计算与证明都要重得多。**松但可复合的界，比紧但不可复合的界有用。**

## 2. 交付

| 定理 | 内容 |
|:--|:--|
| `colMag` / `layerMag` | 列量级与层量级 |
| `colMag_nonneg` / **`layerMag_nonneg`** | 非负 |
| `colMag_le_layerMag` | 列量级 ≤ 层量级 |
| **`affineAct_lipschitz`** | **`∀ i, \|u i − v i\| ≤ δ ⟹ ∀ j, \|act L u j − act L v j\| ≤ layerMag L · δ`** |
| **`affineAct_abs_le`** | **`∀ i, \|x i\| ≤ M ⟹ ∀ j, \|act L x j\| ≤ layerMag L · M`**（需 `M ≥ 1`） |
| **`netAct_two_perturbation`** | **两层栈的误差 = 第二层的权重扰动 + 第一层偏差被第二层放大** |

## 3. 边界的实质：为什么两层不能一步归零

第 202–204 轮的单层闭环是「一步到零」，因为损失对参数是**二次**的。

**两层不是。** 即使只调第一层的偏置，残差是

```
r a = ∑ j, W₂ j a · (∑ i, W₁ i j x i + b₁ j) + b₂ a + c a
```

它对 `b₁` **仍是仿射**的（所以损失仍是二次的），但**梯度里出现了 Gram 矩阵**：

```
∂r a / ∂b₁ j = W₂ j a        ⟹        r' = (I − 2η G) r,   G a a' = ∑ j, W₂ j a · W₂ j a'
```

**`G` 一般不是数量矩阵**，所以没有「一个标量收缩因子」，也就**没有一步到零**。

**本节因此不声称两层的闭环**——本节的界是误差**传播**的界，不是收敛的界。

**但那个 Gram 矩阵值得单独一条定理，因为它比「收缩不是标量」更尖锐。**
`two_layer_descent_can_stall` 给出一个具体反例：**残差非零，而梯度为零**。
于是**无论 `η` 取什么值，参数都不动**——那不是收敛慢，是**停在了一个不是解的地方**。

这是「多层必须迭代，而且迭代不一定成功」的最小见证。
（这条取代了初稿里提到的 `two_layer_contraction_is_matrix`——那个名字我写了但没证，
**按纪律：声称一个不存在的定理，要么补上，要么删掉。这里补成了一条更强的**。）

## 4. 边界

- **本节的界依赖 `M ≥ 1`**：偏置项 `|b j|` 要用 `|b j| ≤ M · |b j|`。**`M < 1` 时界要改写**，本节不做。
- **只到两层**。`k` 层需要把 `layerMag` 连乘并归纳，本节给两层的精确形式，
  因为**两层已经足够说明「为什么要迭代」**（§3）。
- **本节不声称 Lipschitz 常数最优**：`layerMag` 是列和的粗界，谱范数更紧。见 §1。
- 本节**不改** `Lift/QuantErrorPropagation.lean`。
-/
import Mathlib
import Lattice.Core.Net
import Lattice.Lift.QuantErrorPropagation

namespace Lattice.Lift.StackError

open Lattice.Core
open scoped BigOperators

variable {n : ℕ}

/-! ## 一、层的量级 -/

/-- **第 `j` 个输出坐标的量级**：该列权重绝对值之和 + 偏置绝对值。 -/
noncomputable def colMag (L : AffineLayer (Fin n)) (j : Fin n) : ℝ :=
  (∑ i, |L.W i j|) + |L.b j|

/-- **整层的量级**：各列量级之和。 -/
noncomputable def layerMag (L : AffineLayer (Fin n)) : ℝ :=
  ∑ j, colMag L j

/-- 列量级非负。 -/
theorem colMag_nonneg (L : AffineLayer (Fin n)) (j : Fin n) : 0 ≤ colMag L j := by
  unfold colMag
  exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (abs_nonneg _)

/-- **层量级非负。** -/
theorem layerMag_nonneg (L : AffineLayer (Fin n)) : 0 ≤ layerMag L :=
  Finset.sum_nonneg fun j _ => colMag_nonneg L j

/-- **列量级不超过层量级**。 -/
theorem colMag_le_layerMag (L : AffineLayer (Fin n)) (j : Fin n) : colMag L j ≤ layerMag L :=
  Finset.single_le_sum (f := fun j => colMag L j) (fun i _ => colMag_nonneg L i)
    (Finset.mem_univ j)

/-! ## 二、对输入是 Lipschitz 的 -/

/-- **`affineAct` 的 Lipschitz 性**：输入每分量差 ≤ `δ`，输出每分量差 ≤ `layerMag L · δ`。

**这是多层误差传播的承重件**——`QuantErrorPropagation` 只有「同输入、不同层」，
这里是「同层、不同输入」。 -/
theorem affineAct_lipschitz (L : AffineLayer (Fin n)) (u v : Fin n → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ i, |u i - v i| ≤ δ) :
    ∀ j, |affineAct L u j - affineAct L v j| ≤ layerMag L * δ := by
  intro j
  -- the difference is `∑ i, W i j * (u i - v i)`
  have hlin : affineAct L u j - affineAct L v j = ∑ i, L.W i j * (u i - v i) := by
    unfold affineAct
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hlin]
  calc |∑ i, L.W i j * (u i - v i)|
      ≤ ∑ i, |L.W i j| * |u i - v i| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [abs_mul])
    _ ≤ ∑ i, |L.W i j| * δ := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = (∑ i, |L.W i j|) * δ := by rw [Finset.sum_mul]
    _ ≤ layerMag L * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ
        calc (∑ i, |L.W i j|) ≤ colMag L j := by
              unfold colMag; exact le_add_of_nonneg_right (abs_nonneg _)
          _ ≤ layerMag L := colMag_le_layerMag L j

/-- **输出的量级界**：输入每分量 ≤ `M`，则输出每分量 ≤ `layerMag L · M`（需 `M ≥ 1`）。 -/
theorem affineAct_abs_le (L : AffineLayer (Fin n)) (x : Fin n → ℝ) {M : ℝ}
    (hM1 : 1 ≤ M) (hx : ∀ i, |x i| ≤ M) :
    ∀ j, |affineAct L x j| ≤ layerMag L * M := by
  intro j
  -- the output coordinate is `(∑ i, W i j * x i) + b j`
  have h1 : |∑ i, L.W i j * x i| ≤ (∑ i, |L.W i j|) * M := by
    calc |∑ i, L.W i j * x i|
        ≤ ∑ i, |L.W i j| * |x i| := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [abs_mul])
      _ ≤ ∑ i, |L.W i j| * M := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _)
      _ = (∑ i, |L.W i j|) * M := by rw [Finset.sum_mul]
  have h3 : 0 ≤ M := le_trans zero_le_one hM1
  -- the bias is bounded by `|b| * M` because `M ≥ 1`
  have h2 : |L.b j| ≤ |L.b j| * M := by
    calc |L.b j| = |L.b j| * 1 := (mul_one _).symm
      _ ≤ |L.b j| * M := mul_le_mul_of_nonneg_left hM1 (abs_nonneg _)
  have h5 : colMag L j ≤ layerMag L := colMag_le_layerMag L j
  have hcol : colMag L j = (∑ i, |L.W i j|) + |L.b j| := rfl
  calc |affineAct L x j|
      = |(∑ i, L.W i j * x i) + L.b j| := by rfl
    _ ≤ |∑ i, L.W i j * x i| + |L.b j| := abs_add _ _
    _ ≤ (∑ i, |L.W i j|) * M + |L.b j| * M := add_le_add h1 h2
    _ = ((∑ i, |L.W i j|) + |L.b j|) * M := by ring
    _ = colMag L j * M := by rw [hcol]
    _ ≤ layerMag L * M := mul_le_mul_of_nonneg_right h5 h3

/-! ## 三、两层栈：误差传播

**两层的偏差有两个来源**，而单层结论一个都覆盖不了：
（a）第二层自己的权重不同；（b）第一层的输出不同，被第二层**放大**。

`netAct_two_perturbation` 把两者相加——**这就是「误差在栈里复合」的算术内容**。 -/

/-- **两层栈的误差界**：第二层的权重扰动 `ε`，加上第一层偏差 `δ` 被第二层放大的部分。

**注意界里出现 `layerMag L₂' * δ`——第一层的偏差乘以第二层的量级。**
这在单层结论里不存在，也是「深层网络误差更大」的最简形式。 -/
theorem netAct_two_perturbation (L₁ L₁' L₂ L₂' : AffineLayer (Fin n)) (x : Fin n → ℝ)
    {ε δ M : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hM1 : 1 ≤ M)
    (hx : ∀ i, |x i| ≤ M)
    (hW₂ : ∀ i j, |L₂.W i j - L₂'.W i j| ≤ ε)
    (hb₂ : ∀ j, |L₂.b j - L₂'.b j| ≤ ε)
    (hδdef : ∀ j, |affineAct L₁ x j - affineAct L₁' x j| ≤ δ) :
    ∀ j, |affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j|
      ≤ (ε * (Fintype.card (Fin n)) * (layerMag L₁ * M) + ε) + layerMag L₂' * δ := by
  intro j
  -- triangle: perturb the second layer, then propagate the first layer's deviation
  have htri : |affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j|
      ≤ |affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁ x) j|
        + |affineAct L₂' (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j| := by
    have := abs_add (affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁ x) j)
      (affineAct L₂' (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j)
    have heq : (affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁ x) j)
        + (affineAct L₂' (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j)
        = affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j := by ring
    rw [heq] at this
    exact this
  -- (a) the second layer's own perturbation, at the common input `affineAct L₁ x`
  have hA : |affineAct L₂ (affineAct L₁ x) j - affineAct L₂' (affineAct L₁ x) j|
      ≤ ε * (Fintype.card (Fin n)) * (layerMag L₁ * M) + ε := by
    have hin : ∀ i, |affineAct L₁ x i| ≤ layerMag L₁ * M := affineAct_abs_le L₁ x hM1 hx
    have := Lattice.Lift.QuantErrorProp.affineAct_perturbation L₂ L₂'
      (affineAct L₁ x) hε (fun i j => hW₂ i j) hb₂ hin
    simpa [Nat.cast_ofNat] using this j
  -- (b) the first layer's deviation, amplified by the second layer's magnitude
  have hB : |affineAct L₂' (affineAct L₁ x) j - affineAct L₂' (affineAct L₁' x) j|
      ≤ layerMag L₂' * δ :=
    affineAct_lipschitz L₂' (affineAct L₁ x) (affineAct L₁' x) hδ hδdef j
  linarith

/-! ## 四、N：两层下降可以**停在非解处**

两层的残差对第一层偏置**仍是仿射**的（所以损失仍是二次的），但梯度里含一个 Gram 矩阵：

```
∂r a / ∂b₁ j = W₂ j a        ⟹        r' = r − 2η • (G r),   G a a' = ∑ j, W₂ j a · W₂ j a'
```

**`G` 一般不是数量矩阵**，所以没有标量收缩因子。更糟的是：

**若 `r` 落在 `G` 的核里，梯度为零，参数一步都不动——而 `r ≠ 0` 意味着约束没满足。**

下面给 `n = 2` 的具体见证：
`W₂` 的第一行取 `(1, 1)`、第二行取 `(0, 0)`，`r = (1, −1)`。
则对每个 `j`，`∑ a, r a · W₂ j a = 0`，而 `r ≠ 0`。

**这不是「收敛慢」，是「停在不是解的地方」。** 单层的闭环（第 200–204 轮）依赖
「残差非零 ⟹ 梯度非零」，而**那一句在两层的栈里就是假的**。 -/
theorem two_layer_descent_can_stall :
    ∃ (W₂ : Fin 2 → Fin 2 → ℝ) (r : Fin 2 → ℝ),
      r ≠ 0 ∧ ∀ j : Fin 2, (∑ a, r a * W₂ j a) = 0 := by
  -- `W₂` is constant along its second index, so each gradient sum is `c * ∑ a, r a`,
  -- and `∑ a, r a = 1 + (−1) = 0` while `r 0 = 1 ≠ 0`.
  refine ⟨fun j _ => if j = 0 then 1 else 0, fun a => if a = 0 then 1 else -1, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · intro j
    fin_cases j <;> simp [Fin.sum_univ_two]

end Lattice.Lift.StackError
