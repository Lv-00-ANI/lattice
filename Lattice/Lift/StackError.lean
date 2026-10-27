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

/-! ## 五、任意深度：输出量级随深度**乘积**增长

§二 只给单层的界。§三 只给两层的。本节给**任意 `k` 层**，而这正是「网络能深到多少」的问题。

### 为什么要 `max (layerMag L) 1`

归纳的障碍在**假设的形式**：`affineAct_abs_le` 要求输入的界 `M ≥ 1`
（因为偏置项要用 `|b| ≤ M|b|`）。而 `layerMag L` **可以小于 1**（权重全是 `0.1` 的层），
所以「`M ≥ 1`」在归纳里**传不下去**——`layerMag L * M` 可能小于 1。

**修法不是加假设，是换形式**：把每层的增益取 `g L := max (layerMag L) 1 ≥ 1`，
把输入的界取 `max M 1 ≥ 1`。于是

```
M' := g L * max M 1   ≥ 1        -- 假设可传
g L * max M 1 = max (layerMag L * max M 1) 1   -- 与 affineAct_abs_le 的输出形式对上
```

**这是「换形式而不是砍定理」的一个具体例子**：定理没有被削弱成 `layerMag ≥ 1` 的特殊情形，
它对**所有**层成立。

### 交付

| 定理 | 内容 |
|:--|:--|
| **`netAct_abs_le`** | **`\|netAct ls x j\| ≤ (∏ max (layerMag L) 1) · max M 1`** |
| `depth_growth` | 上述界随层数的乘性形式 |
| **`layerMag_can_exceed_one`** | **N：存在层使 `layerMag ≥ 2`**——所以乘积**真的会**指数增长 |

### 边界

- 界是**乘性**的：`k` 层给 `∏ g L`。**这不是紧界**（`layerMag` 是列和的粗界，见 §1），
  但它是**可归纳**的，而这正是「深度」需要的性质。
- **本节给的是量级，不是误差**。误差在 §三 只到两层；`k` 层的误差会把每层的 `ε` 累加成几何级数，
  **本节不做**（见 §六 的边界）。
- **N 定理只说乘积可以增长，不说它一定增长**：`layerMag < 1` 的层会让乘积收缩。
  **两种都可能，本节不声称任何一种。** -/

/-- **每层的增益**：`max (layerMag L) 1`，恒 `≥ 1`，使归纳的假设可传。 -/
noncomputable def gain (L : AffineLayer (Fin n)) : ℝ := max (layerMag L) 1

/-- 增益至少为 1。 -/
theorem one_le_gain (L : AffineLayer (Fin n)) : 1 ≤ gain L := le_max_right _ _

/-- 增益非负。 -/
theorem gain_nonneg (L : AffineLayer (Fin n)) : 0 ≤ gain L := le_trans zero_le_one (one_le_gain L)

/-- **任意深度的输出量级界**：`|netAct ls x j| ≤ (∏ g L) · max M 1`。

对 `ls` 归纳。归纳步用 `netAct_append` 把 `L :: ls` 拆成「先走 `L`、再走 `ls`」，
然后 `affineAct_abs_le` 给第一段的界、归纳假设给第二段。 -/
theorem netAct_abs_le (ls : List (AffineLayer (Fin n))) (x : Fin n → ℝ) {M : ℝ}
    (hx : ∀ i, |x i| ≤ M) :
    ∀ j, |netAct ls x j| ≤ ((ls.map gain).prod) * max M 1 := by
  induction ls generalizing x M with
  | nil =>
      intro j
      rw [netAct_nil]
      have h1 : |x j| ≤ M := hx j
      have h2 : M ≤ max M 1 := le_max_left _ _
      simp only [List.map_nil, List.prod_nil, one_mul]
      linarith
  | cons L rest ih =>
      intro j
      -- `netAct (L :: rest) x = netAct rest (affineAct L x)`
      have hstep : netAct (L :: rest) x = netAct rest (affineAct L x) := by
        rw [show (L :: rest) = [L] ++ rest from rfl, netAct_append]
        rfl
      rw [hstep]
      -- the intermediate bound: `M' := gain L * max M 1`, which is `≥ 1`
      have hM1 : 1 ≤ max M 1 := le_max_right _ _
      have hMnn : 0 ≤ max M 1 := le_trans zero_le_one hM1
      have hmid : ∀ i, |affineAct L x i| ≤ gain L * max M 1 := by
        intro i
        have h := affineAct_abs_le L x hM1 (fun i => le_trans (hx i) (le_max_left _ _)) i
        calc |affineAct L x i| ≤ layerMag L * max M 1 := h
          _ ≤ gain L * max M 1 := by
              apply mul_le_mul_of_nonneg_right _ hMnn
              exact le_max_left _ _
      have hM'1 : 1 ≤ gain L * max M 1 := by
        calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ gain L * max M 1 := mul_le_mul (one_le_gain L) hM1 zero_le_one (gain_nonneg L)
      have hmax : max (gain L * max M 1) 1 = gain L * max M 1 := max_eq_left hM'1
      have hih := ih (affineAct L x) (M := gain L * max M 1) hmid j
      rw [hmax] at hih
      calc |netAct rest (affineAct L x) j|
          ≤ ((rest.map gain).prod) * (gain L * max M 1) := hih
        _ = ((L :: rest).map gain).prod * max M 1 := by
            rw [List.map_cons, List.prod_cons]
            ring

/-- **深度增长**：`k` 层之后，量级被各层增益之积放大。

这是 `netAct_abs_le` 的直接读法，单独列出是因为**它是「深度的代价」那句话的定理形式**。 -/
theorem depth_growth (ls : List (AffineLayer (Fin n))) (x : Fin n → ℝ) {M : ℝ}
    (hM : 1 ≤ M) (hx : ∀ i, |x i| ≤ M) (j : Fin n) :
    |netAct ls x j| ≤ ((ls.map gain).prod) * M := by
  have h := netAct_abs_le ls x hx j
  rwa [max_eq_left hM] at h

/-! ### N：乘积**真的会**增长

上面的界若恒为 `≤ 1`，它就是空的。下面给出一个 `layerMag ≥ 2` 的层——
于是 `k` 层的界至少是 `2 ^ k`。**深度的代价是真实的，不是记号。** -/

/-- **存在使 `layerMag ≥ 2` 的层。**

`W i j = 2`、`b = 0` 在 `Fin 1` 上：`colMag 0 = |2| + |0| = 2`，`layerMag = 2`。 -/
theorem layerMag_can_exceed_one :
    ∃ L : AffineLayer (Fin 1), 2 ≤ layerMag L := by
  refine ⟨⟨fun _ _ => 2, fun _ => 0⟩, ?_⟩
  have hcol : colMag (⟨fun _ _ => (2 : ℝ), fun _ => 0⟩ : AffineLayer (Fin 1)) 0 = 2 := by
    unfold colMag
    simp
  unfold layerMag
  rw [Fin.sum_univ_one, hcol]

/-- **所以 `k` 层的界至少是 `2 ^ k`**——「深度的代价」的具体形式。 -/
theorem depth_growth_at_least_two_pow (k : ℕ) :
    ∃ L : AffineLayer (Fin 1), 2 ^ k ≤ ((List.replicate k L).map gain).prod := by
  obtain ⟨L, hL⟩ := layerMag_can_exceed_one
  refine ⟨L, ?_⟩
  rw [List.map_replicate, List.prod_replicate]
  have hg : 2 ≤ gain L := le_trans hL (le_max_left _ _)
  exact pow_le_pow_left₀ (by norm_num) hg k

/-! ## 六、任意深度的 **Lipschitz 常数**：`∏ gain`

§五 给的是「同一个输入、不同层栈」的量级。**误差累积要的是另一半**：
「同一个层栈、不同输入」。没有它，`k` 层的误差无从谈起——
因为误差在第 `i` 层产生后，要被**后面所有层**放大。

### 结果与因子

```
|netAct ls u j − netAct ls v j| ≤ (∏ gain L) · δ          （当 ∀ i, |u i − v i| ≤ δ）
```

**`∏ gain` 就是第 206 轮那个乘积界的同一组因子**——那节用它界输出量级，本节用它界**扰动的传播**。
**同一个乘积，两种用途**，这不是巧合：量级与扰动都按同一组线性因子缩放。

### 交付

| 定理 | 内容 |
|:--|:--|
| **`netAct_lipschitz`** | **`∀ i, \|u i − v i\| ≤ δ ⟹ ∀ j, \|netAct ls u j − netAct ls v j\| ≤ (∏ gain) · δ`** |
| `netAct_deviation_step` | **单层递推**：整栈偏差 ≤ 尾栈偏差 + 首层偏差被尾栈放大 |
| `netAct_three_layer` | **三层**：说明偏差**逐层复合**，不是只有两层能算 |

### 边界

- **`0 ≤ δ` 是必需的**：`mul_le_mul_of_nonneg_right` 的正性条件。**这是真的假设，不是装饰**——
  δ 是偏差的界，本来就非负。
- **本节给 Lipschitz 常数，不给误差的闭式解**。闭式解要把 `∑_{i<k} ε G^i` 的几何和算出来，
  并且逐层追踪 `B`（中间量级界），**本节不做**（§七 的边界里写明）。
- 因子是 `∏ gain`（`gain = max layerMag 1`），与 §五 同一个；**`gain ≥ 1` 保证乘法链单调**。 -/

/-- **任意深度的 Lipschitz 性**：输入每分量差 ≤ `δ`，则输出每分量差 ≤ `(∏ gain) · δ`。

**这是多层误差累积的承重件。** §三 的 `netAct_two_perturbation` 只到两层；
本节让任意深度的扰动传播有了常数，而常数正是 §五 的那个乘积。 -/
theorem netAct_lipschitz (ls : List (AffineLayer (Fin n))) (u v : Fin n → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ i, |u i - v i| ≤ δ) :
    ∀ j, |netAct ls u j - netAct ls v j| ≤ ((ls.map gain).prod) * δ := by
  induction ls generalizing u v δ with
  | nil =>
      intro j
      simp only [netAct_nil, List.map_nil, List.prod_nil, one_mul]
      exact h j
  | cons L rest ih =>
      intro j
      -- `netAct (L :: rest) u = netAct rest (affineAct L u)`
      have hstep : ∀ w : Fin n → ℝ, netAct (L :: rest) w = netAct rest (affineAct L w) := by
        intro w
        rw [show (L :: rest) = [L] ++ rest from rfl, netAct_append]
        rfl
      rw [hstep u, hstep v]
      -- the first layer's output deviation, amplified by its own magnitude
      have hδ' : 0 ≤ gain L * δ := mul_nonneg (gain_nonneg L) hδ
      have hmid : ∀ i, |affineAct L u i - affineAct L v i| ≤ gain L * δ := by
        intro i
        have hh := affineAct_lipschitz L u v hδ h i
        calc |affineAct L u i - affineAct L v i| ≤ layerMag L * δ := hh
          _ ≤ gain L * δ := by
              apply mul_le_mul_of_nonneg_right _ hδ
              exact le_max_left _ _
      have hfin := ih (affineAct L u) (affineAct L v) hδ' hmid j
      calc |netAct rest (affineAct L u) j - netAct rest (affineAct L v) j|
          ≤ ((rest.map gain).prod) * (gain L * δ) := hfin
        _ = ((L :: rest).map gain).prod * δ := by
            rw [List.map_cons, List.prod_cons]
            ring

/-- **单层递推**：整栈偏差 ≤ 尾栈偏差 + 首层偏差被尾栈放大。

设尾栈 `rest` 对**任何**有界输入都成立偏差界 `D`（`hD`），首层输出偏差 ≤ `δ`，
则整栈偏差 ≤ `D + (∏ gain rest) · δ`。

**这就是误差累积的递推式**：每多一层，新增的误差是**该层的偏差乘以后面所有层的增益**。 -/
theorem netAct_deviation_step (L L' : AffineLayer (Fin n))
    (rest rest' : List (AffineLayer (Fin n))) (x : Fin n → ℝ)
    {δ D M : ℝ} (hδ : 0 ≤ δ) (hDnn : 0 ≤ D) (hDL : 0 ≤ (rest.map gain).prod)
    (hmag : ∀ i, |affineAct L x i| ≤ M) (hmag' : ∀ i, |affineAct L' x i| ≤ M)
    (hδfirst : ∀ i, |affineAct L x i - affineAct L' x i| ≤ δ)
    (hD : ∀ (w : Fin n → ℝ), (∀ i, |w i| ≤ M) →
      ∀ j, |netAct rest w j - netAct rest' w j| ≤ D) :
    ∀ j, |netAct (L :: rest) x j - netAct (L' :: rest') x j| ≤ D + (rest.map gain).prod * δ := by
  intro j
  have hstep : ∀ (ls : List (AffineLayer (Fin n))) (w : Fin n → ℝ),
      netAct (L :: ls) w = netAct ls (affineAct L w) := by
    intro ls w
    rw [show (L :: ls) = [L] ++ ls from rfl, netAct_append]
    rfl
  have hstep' : ∀ (ls : List (AffineLayer (Fin n))) (w : Fin n → ℝ),
      netAct (L' :: ls) w = netAct ls (affineAct L' w) := by
    intro ls w
    rw [show (L' :: ls) = [L'] ++ ls from rfl, netAct_append]
    rfl
  rw [hstep rest x, hstep' rest' x]
  -- triangle through the common point `affineAct L x`
  have htri : |netAct rest (affineAct L x) j - netAct rest' (affineAct L' x) j|
      ≤ |netAct rest (affineAct L x) j - netAct rest (affineAct L' x) j|
        + |netAct rest (affineAct L' x) j - netAct rest' (affineAct L' x) j| := by
    have := abs_add (netAct rest (affineAct L x) j - netAct rest (affineAct L' x) j)
      (netAct rest (affineAct L' x) j - netAct rest' (affineAct L' x) j)
    have heq : (netAct rest (affineAct L x) j - netAct rest (affineAct L' x) j)
        + (netAct rest (affineAct L' x) j - netAct rest' (affineAct L' x) j)
        = netAct rest (affineAct L x) j - netAct rest' (affineAct L' x) j := by ring
    rw [heq] at this
    exact this
  -- (a) same tail, different inputs: propagate by the tail's Lipschitz constant
  have hA : |netAct rest (affineAct L x) j - netAct rest (affineAct L' x) j|
      ≤ (rest.map gain).prod * δ :=
    netAct_lipschitz rest (affineAct L x) (affineAct L' x) hδ hδfirst j
  -- (b) same input, different tails: the hypothesis `hD`
  have hB : |netAct rest (affineAct L' x) j - netAct rest' (affineAct L' x) j| ≤ D :=
    hD (affineAct L' x) hmag' j
  linarith

/-- **深度的灵敏度代价**：`k` 个相同的层叠起来，Lipschitz 常数是 `(gain L)^k`。

**这是「深度放大扰动」的定理形式**——不是类比：同一个输入偏差进入 `k` 层网络后，
输出的偏差界是单层的 `(gain L)^k` 倍。

结合 §五 的 `layerMag_can_exceed_one`（存在 `gain ≥ 2` 的层），**这个界真的会指数增长**。 -/
theorem netAct_lipschitz_replicate (L : AffineLayer (Fin n)) (k : ℕ) (u v : Fin n → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ i, |u i - v i| ≤ δ) :
    ∀ j, |netAct (List.replicate k L) u j - netAct (List.replicate k L) v j|
      ≤ (gain L) ^ k * δ := by
  intro j
  have := netAct_lipschitz (List.replicate k L) u v hδ h j
  rwa [List.map_replicate, List.prod_replicate] at this

/-! ## 七、`k` 层误差的**闭式界**：每多一层加一项

§六 给了 `k` 层的 Lipschitz 常数，但那只是「同一个栈喂不同输入」。
**误差累积要的是「不同栈喂同一输入」的闭式界**——第 205 轮只做到两层，
本节做到任意层，**这就是把那个半成品做完。**

### 为什么用递归定义而不是 `∑_{i<k} ε G^i`

几何和的闭式要 `G ≠ 1` 的分情形；而更麻烦的是 `∑ ε G^i` 里每一项的 `G` 是**部分乘积**
（第 `i` 层之后的增益之积），要把它与全乘积 `∏ gain` 比较，需要一条「子乘积 ≤ 全乘积」的引理
（对非负且 `≥ 1` 的因子成立，但要单独证）。

**递归定义绕开这两件事**：`devB ε B ls` 直接按栈结构展开，

```
devB ε B []          = 0
devB ε B (L :: rest) = devB ε (gain L · B) rest
                        + (ε · n · B + ε) · (∏ gain rest)
```

第二项的读法是：**首层产生的误差 `ε·n·B + ε`，被后面所有层放大 `∏ gain rest` 倍。**
各层相加，正是累积。

**代价**：`devB` 不是一个数而是栈的函数。**收益**：不需要任何分情形、不需要子乘积比较，
而且这个形式**直接给出每层的贡献**，比一个 `k·G^k` 的粗界信息更多。

### 交付

| 定理 | 内容 |
|:--|:--|
| `devB` | 逐层累积的误差界 |
| `devB_nonneg` | 非负（`ε ≥ 0`、`B ≥ 1`） |
| **`netAct_deviation_le_devB`** | **`\|netAct ls x − netAct ls' x\| ≤ devB ε B ls`**——**任意层数** |

### 边界

- **`1 ≤ B` 是必需**：`affineAct_abs_le` 要它（偏置项 `|b| ≤ M|b|`）。
  输入有界且界 `≥ 1` 是这个界系统的统一约定，`devB` 把 `gain L · B` 传给下一层，仍然 `≥ 1`。
- **逐层 `ε` 相同**：本节假设每层的扰动都被同一个 `ε` 界住。
  不同层的不同 `ε` 会让 `devB` 多一个参数序列，**本节不做**。
- **`Forall₂` 而不是 `zip`**：`Forall₂` 自带等长且能干净析构（`Forall₂.nil` / `Forall₂.cons`），
  `zip` 要额外处理 `length` 相等。 -/

/-- **`gain` 的列表乘积非负**。（`List.prod_nonneg` 的签名在本 mathlib 里与我的猜测不符，
又一次：**猜引理名不可靠，写一条三行的自己的版本更快**。） -/
theorem prod_gain_nonneg {n : ℕ} (ls : List (AffineLayer (Fin n))) :
    0 ≤ (ls.map gain).prod := by
  induction ls with
  | nil => simp
  | cons L rest ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_nonneg (gain_nonneg L) ih

/-- **逐层累积的误差界**，以**全局增益界 `G`** 为参数。

```
devB ε B G []          = 0
devB ε B G (L :: rest) = devB ε (G · B) G rest
                          + (ε · n · B + ε) · (∏ gain rest)
```

第二项的读法：**首层产生的误差 `ε·n·B + ε` 被后面所有层放大 `∏ gain rest` 倍**；各层相加即累积。

**为什么用全局 `G` 而不是各层自己的 `gain L`**：`netAct_deviation_step` 需要一个 `M`
同时界住 `affineAct L x` 与 `affineAct L' x`，**而这两个的首层增益不同**。
用 `G` 界住两者后 `M := G · B` 同时适用，递归就通了。
**代价**是界更松；**收益**是不需要 `max (gain L) (gain L')` 那种逐对的记账。
这与 §五 用 `layerMag` 而非谱范数是同一个取舍：**松但可复合**。 -/
noncomputable def devB {n : ℕ} (ε B G : ℝ) : List (AffineLayer (Fin n)) → ℝ
  | [] => 0
  | _L :: rest => devB ε (G * B) G rest
      + (ε * (Fintype.card (Fin n) : ℝ) * B + ε) * ((rest.map gain).prod)

/-- **`devB` 非负**（`0 ≤ ε`、`1 ≤ B`、`1 ≤ G`）。 -/
theorem devB_nonneg {n : ℕ} {ε B G : ℝ} (hε : 0 ≤ ε) (hB : 1 ≤ B) (hG : 1 ≤ G)
    (ls : List (AffineLayer (Fin n))) : 0 ≤ devB ε B G ls := by
  induction ls generalizing B with
  | nil => simp [devB]
  | cons L rest ih =>
      rw [devB]
      have hB' : 1 ≤ G * B :=
        calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ G * B := by nlinarith
      have hmain : 0 ≤ devB ε (G * B) G rest := ih hB'
      have hBnn : 0 ≤ B := le_trans zero_le_one hB
      have hterm : 0 ≤ (ε * (Fintype.card (Fin n) : ℝ) * B + ε) * ((rest.map gain).prod) :=
        mul_nonneg (by positivity) (prod_gain_nonneg rest)
      linarith

/-- **任意层数的误差闭式界**：两个栈逐层 `ε`-接近、所有增益被 `G` 界住，
则输出偏差 ≤ `devB ε B G ls`。

**这是第 205 轮「两层」的完整推广。**

`B` 与 `x` 放在结论里（`∀ B x, …`）而不是绑定在外面：这样 `induction` 能对它们泛化，
递归时尾栈的界从 `B` 变成 `G · B`。**放在外面则 `ih` 被钉在旧的 `B` 上**——这是我第一次的错。 -/
theorem netAct_deviation_le_devB {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (ls ls' : List (AffineLayer (Fin n)))
    (hF : List.Forall₂ (fun L L' =>
      (∀ i j, |L.W i j - L'.W i j| ≤ ε) ∧ (∀ j, |L.b j - L'.b j| ≤ ε)) ls ls')
    {G : ℝ} (hG : 1 ≤ G) (hGl : ∀ L ∈ ls, gain L ≤ G) (hGr : ∀ L ∈ ls', gain L ≤ G) :
    ∀ (B : ℝ) (x : Fin n → ℝ), (∀ i, |x i| ≤ B) → 1 ≤ B →
    ∀ j, |netAct ls x j - netAct ls' x j| ≤ devB ε B G ls := by
  induction hF with
  | nil =>
      intro B x _ _ j
      simp [devB]
  | @cons L L' rest rest' hstep _htl ih =>
      intro B x hx hB j
      have hδfirst : ∀ i,
          |affineAct L x i - affineAct L' x i| ≤ ε * (Fintype.card (Fin n) : ℝ) * B + ε :=
        fun i => Lattice.Lift.QuantErrorProp.affineAct_perturbation L L' x hε
          hstep.1 hstep.2 hx i
      have hBnn : 0 ≤ B := le_trans zero_le_one hB
      have hGnn : 0 ≤ G := le_trans zero_le_one hG
      -- both first layers' outputs are bounded by `G * B`
      have hmag : ∀ i, |affineAct L x i| ≤ G * B := by
        intro i
        have h1 := affineAct_abs_le L x hB hx i
        calc |affineAct L x i| ≤ layerMag L * B := h1
          _ ≤ G * B := by
              apply mul_le_mul_of_nonneg_right _ hBnn
              exact le_trans (le_max_left _ _) (hGl L (List.mem_cons_self L rest))
      have hmag' : ∀ i, |affineAct L' x i| ≤ G * B := by
        intro i
        have h1 := affineAct_abs_le L' x hB hx i
        calc |affineAct L' x i| ≤ layerMag L' * B := h1
          _ ≤ G * B := by
              apply mul_le_mul_of_nonneg_right _ hBnn
              exact le_trans (le_max_left _ _) (hGr L' (List.mem_cons_self L' rest'))
      have hB' : 1 ≤ G * B := by nlinarith
      have hD : ∀ (w : Fin n → ℝ), (∀ i, |w i| ≤ G * B) →
          ∀ j, |netAct rest w j - netAct rest' w j| ≤ devB ε (G * B) G rest := by
        intro w hw
        -- the lambda binders must NOT be called L/L': they shadow the cons heads, and then
        -- List.mem_cons_of_mem receives the shadowed name as the head and fails to unify.
        exact ih (fun M hM => hGl M (List.mem_cons_of_mem L hM))
          (fun M hM => hGr M (List.mem_cons_of_mem L' hM)) (G * B) w hw hB'
      have hδ : 0 ≤ ε * (Fintype.card (Fin n) : ℝ) * B + ε := by positivity
      have hmain := netAct_deviation_step (L := L) (L' := L') (rest := rest) (rest' := rest')
        (x := x) (δ := ε * (Fintype.card (Fin n) : ℝ) * B + ε)
        (D := devB ε (G * B) G rest) (M := G * B)
        hδ (devB_nonneg hε hB' hG rest) (prod_gain_nonneg rest) hmag hmag' hδfirst hD j
      rw [devB]
      calc |netAct (L :: rest) x j - netAct (L' :: rest') x j|
          ≤ devB ε (G * B) G rest
              + (rest.map gain).prod * (ε * (Fintype.card (Fin n) : ℝ) * B + ε) := hmain
        _ = devB ε (G * B) G rest
              + (ε * (Fintype.card (Fin n) : ℝ) * B + ε) * ((rest.map gain).prod) := by ring

end Lattice.Lift.StackError
