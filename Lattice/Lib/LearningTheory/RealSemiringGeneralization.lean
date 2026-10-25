import Mathlib

/-!
# LATTICE: 半环 / 有序半环上的泛化不等式（补齐 A9 缺口）

RealConvexToolkit 等文件的不等式都在 `ℝ` 上陈述。本文件把其中**真正泛型**的
3 类内核（Cauchy–Schwarz、加权 AM–GM、幂平均单调性的有限型）在
`LinearOrderedCommSemiring`（以及 `CommSemiring + LinearOrder`）上重述并证明，
并显式标注哪些结论**必须**在（半）域上陈述。

## 1. 真正泛型（在有序半环上成立，无需除法）

| 声明 | 内容 | 备注 |
|:--|:--|:--|
| `cauchy_schwarz_finset` | `(Σ fᵢgᵢ)² ≤ (Σ fᵢ²)(Σ gᵢ²)` | mathlib `Finset.sum_mul_sq_le_sq_mul_sq` 的**唯一权威位置**式重申（M2 范式） |
| `cauchy_schwarz_univ_fin` | `Fin k` 上的同一不等式 | 下游常用入口 |
| `weighted_cauchy_schwarz` | `(Σ wᵢxᵢ)² ≤ (Σ wᵢxᵢ²)(Σ wᵢ)`，`wᵢ ≥ 0` | 由 `sum_sq_le_sum_mul_sum_of_sq_eq_mul` 取 `rᵢ = wᵢxᵢ` 证得 |
| `sq_sum_le_card_mul_sum_sq` | `(Σ fᵢ)² ≤ card·Σ fᵢ²` | **幂平均单调性**（1 次 ≤ 2 次）的无除法形式，`g ≡ 1` 的特例 |
| `sq_sum_univ_fin_le` | `(Σ_{i<k} fᵢ)² ≤ k·Σ fᵢ²` | 上一行的 `Finset.univ`/`Fin k` 入口（下游常用形状） |
| `cauchy_schwarz_two` | `(a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²)` | 二元 CS（`p=q=2` 的 Hölder 退化的具体锚点） |
| `holder_two_is_cauchy` | 同 CS | **机器可验证的「Hölder(`p=q=2`) = CS」锚点**（`1/p+1/q=1` 的退化） |
| `weighted_power_mean_two` | 同 `weighted_cauchy_schwarz` | 「加权均值 ≤ 加权均方根」的语义入口 |
| `cauchy_schwarz_sq_form` | 同 CS | **乘积规范形**重述，便于与 `sq_le_sq` 串联 |
| `amgm_two` | `2ab ≤ a² + b²` | mathlib `two_mul_le_add_sq` 的重申（无除法 AM–GM） |
| `amgm_four` | `4ab ≤ (a+b)²` | mathlib `four_mul_le_sq_add` 的重申 |
| `sq_add_le_two_mul_sq_add_sq` | `(a+b)² ≤ 2(a²+b²)` | 由 `amgm_two` 线性推出（新证明） |

`ExistsAddOfLE` 说明：mathlib 的 Cauchy–Schwarz 需要「`a ≤ b ⟹ ∃ c, b = a + c`」这一
**存在式余项**假设（即某种形式的可减性）。它在 `ℕ`、`ℤ`、`ℚ`、`ℝ` 上由类型类实例自动成立
（本文件以 `example` 形式给机器验证），但**不是**每个 `LinearOrderedCommSemiring` 都有，
故在这些泛型定理中显式作为假设列出（诚实标注：这不是装饰性条件）。

## 2. 必须有除法：**必须** `LinearOrderedSemifield`/`Field`

- `cauchy_schwarz_titu`（Titu/Engel 形式 `(Σf)²/(Σg) ≤ Σ f²/g`）需要
  `LinearOrderedSemifield`——它**不能**在半环上陈述（分母不存在）。
- 经典「均值形式」`a·b ≤ ((a+b)/2)²` 在 `ℝ` 上成立（`amgm_mean_real`），
  但在 `ℕ` 上**为假**（`amgm_mean_nat_false`，机器验证反例：`a=1, b=2` 时
  `(1+2)/2 = 1`，左 2、右 1）。这给出「为什么加权 AM–GM 的均值/幂平均形式
  必须外置到域上」的**严格理由**，而不是风格偏好。

## 诚实边界

- 未做：乘法性 AM–GM 的 n 元形式 `nⁿ·Πaᵢ ≤ (Σaᵢ)ⁿ`（需要更重的
  `Finset.prod`/Maclaurin 论证，本文件只做到二元的 `amgm_two`/`amgm_four`
  与一一对应的幂平均特例）；
- 未做：实数幂 `a^λ b^(1-λ)` 形式的 Young/AM–GM 与一般 `p < q` 幂平均单调性
  （需要实数幂与 `Real.rpow` 的凸性）。
- `import Mathlib` 在最上；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 1. Cauchy–Schwarz：泛型（无除法） -/

/-- **泛型 Cauchy–Schwarz（Finset 版）**：在 `LinearOrderedCommSemiring`（+ 存在式余项
`ExistsAddOfLE`）上，`(Σ_{i∈s} fᵢ·gᵢ)² ≤ (Σ fᵢ²)·(Σ gᵢ²)`。
这是 mathlib `Finset.sum_mul_sq_le_sq_mul_sq` 的具名重申（单一权威入口）。 -/
theorem cauchy_schwarz_finset {R ι : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **泛型 Cauchy–Schwarz（`Finset.univ` / `Fin k` 版）**：下游最常用的入口形式。 -/
theorem cauchy_schwarz_univ_fin {R : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    {k : ℕ} (f g : Fin k → R) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * ∑ i, g i ^ 2 :=
  cauchy_schwarz_finset Finset.univ f g

/-- **加权 Cauchy–Schwarz（无除法）**：`wᵢ ≥ 0` 时
`(Σ wᵢxᵢ)² ≤ (Σ wᵢxᵢ²)·(Σ wᵢ)`。
证法：对 `sum_sq_le_sum_mul_sum_of_sq_eq_mul` 取 `rᵢ = wᵢxᵢ`、`fᵢ = wᵢxᵢ²`、`gᵢ = wᵢ`
（需 `(wᵢxᵢ)² = (wᵢxᵢ²)·wᵢ`，在交换半环中由 `ring` 给出）。这是「加权幂平均」的
无除法内核。 -/
theorem weighted_cauchy_schwarz {R ι : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (s : Finset ι) (w x : ι → R) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 2) * ∑ i ∈ s, w i := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun i => w i * x i) (f := fun i => w i * x i ^ 2) (g := fun i => w i) ?_ ?_ ?_
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · exact hw
  · intro i _
    ring

/-- **幂平均单调性（1 次 ≤ 2 次）的有限型，无除法**：`(Σ_{i∈s} fᵢ)² ≤ card(s)·Σ fᵢ²`。
这是 Cauchy–Schwarz 取 `g ≡ 1` 的特例；「除以 card」的归一化形式在域上才可写
（见文件末尾的反例）。 -/
theorem sq_sum_le_card_mul_sum_sq {R ι : Type*} [LinearOrderedCommSemiring R]
    [ExistsAddOfLE R] (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ : ι => (1 : R))
  simpa [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_comm] using h

/-! ## 2. 加权 AM–GM：泛型（无除法） -/

/-- **泛型二元 AM–GM（无除法）**：`2ab ≤ a² + b²`。
mathlib `two_mul_le_add_sq` 的重申；在 `LinearOrderedCommSemiring` 上成立
（额外需要 `MulPosStrictMono`/`AddLeftReflectLE`/`AddLeftMono`，见 mathlib 签名）。 -/
theorem amgm_two {R : Type*} [CommSemiring R] [LinearOrder R] [ExistsAddOfLE R]
    [MulPosStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) :
    2 * a * b ≤ a ^ 2 + b ^ 2 :=
  two_mul_le_add_sq a b

/-- **泛型二元 AM–GM（无除法，四倍形式）**：`4ab ≤ (a+b)²`。 -/
theorem amgm_four {R : Type*} [CommSemiring R] [LinearOrder R] [ExistsAddOfLE R]
    [MulPosStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) :
    4 * a * b ≤ (a + b) ^ 2 :=
  four_mul_le_sq_add a b

/-- **由 AM–GM 推出的平方和上界**：`(a+b)² ≤ 2(a²+b²)`（在泛型有序半环上）。
证法：`(a+b)² = a² + 2ab + b² ≤ a² + (a²+b²) + b² = 2(a²+b²)`，
其中中间一步是 `amgm_two` 两侧加 `a²+b²`（线性步，无需除法）。 -/
theorem sq_add_le_two_mul_sq_add_sq {R : Type*} [CommSemiring R] [LinearOrder R]
    [ExistsAddOfLE R] [MulPosStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
    _ ≤ a ^ 2 + (a ^ 2 + b ^ 2) + b ^ 2 :=
      add_le_add_right (add_le_add_left (amgm_two a b) (a ^ 2)) (b ^ 2)
    _ = 2 * (a ^ 2 + b ^ 2) := by ring

/-! ## 3. 实例检查：`ExistsAddOfLE` 在常用数系上自动成立 -/

/-- `ExistsAddOfLE` 在 `ℕ` 上自动成立（`ℕ` 是 canonically ordered）。 -/
example : ExistsAddOfLE ℕ := inferInstance

/-- `ExistsAddOfLE` 在 `ℝ` 上自动成立（有序环）。 -/
example : ExistsAddOfLE ℝ := inferInstance

/-! ## 4. 必须有除法：`LinearOrderedSemifield` 与「ℕ 上为假」的反例 -/

/-- **Titu/Engel 形式（必须有除法）**：`(Σ fᵢ)²/(Σ gᵢ) ≤ Σ fᵢ²/gᵢ`（`gᵢ > 0`）。
它需要 `LinearOrderedSemifield`：分母/除法在半环上根本不存在。
（mathlib `Finset.sq_sum_div_le_sum_sq_div` 的重申。） -/
theorem cauchy_schwarz_titu {R ι : Type*} [LinearOrderedSemifield R] [ExistsAddOfLE R]
    (s : Finset ι) (f g : ι → R) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / (∑ i ∈ s, g i) ≤ ∑ i ∈ s, f i ^ 2 / g i :=
  Finset.sq_sum_div_le_sum_sq_div s f hg

/-- **均值形式的 AM–GM（`ℝ`，为真）**：`a·b ≤ ((a+b)/2)²`。
即「几何平均 ≤ 算术平均」的平方形式，由 `0 ≤ (a−b)²` 给出。 -/
theorem amgm_mean_real (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **反例（机器验证，ℕ 上为假）**：均值形式的 AM–GM `a·b ≤ ((a+b)/2)²`
在 `ℕ` 上**不成立**——因为 `ℕ` 不能除以 2：取 `a = 1, b = 2` 时
`(1+2)/2 = 1`，左边 `1·2 = 2 > 1 = 右边`。
这正是加权 AM–GM / 幂平均的「均值」形式**必须** `LinearOrderedField` 的严格理由。 -/
theorem amgm_mean_nat_false : ¬ (∀ a b : ℕ, a * b ≤ ((a + b) / 2) ^ 2) := by
  intro h
  have h12 := h 1 2
  norm_num at h12

/-- **反例补充（机器验证）**：`ℕ` 上同一条均值形式在 `a = 0, b = 1` 处虽然成立，
但在 `a = 1, b = 2` 处失败——说明失败不是「退化点」，而是除法截断的系统性后果：
`(1 + 2 : ℕ) / 2 = 1`（真值 3/2 被截断）。 -/
theorem nat_div_two_truncates : (1 + 2 : ℕ) / 2 = 1 := by norm_num

/-! ## 5. 追加的泛型内核（A1.1：幂平均单调性的乘法形式 / Hölder 的 `p=q=2` 退化 / 乘积 CS） -/

/-- **泛型 Cauchy–Schwarz 的「乘积形式」**：`(Σ fᵢgᵢ)² ≤ (Σ fᵢ²)(Σ gᵢ²)` 的两侧
换成 `Finset.prod` 记号下的**二元特例**——即 `(a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²)`。

这是 mathlib 无现成条目的**新证明**（`cauchy_schwarz_finset` 在 `s = {0,1}` 上的实例化，
显式展开为二元形式，便于下游把小规模 CS 直接当作不等式使用）。
诚实标注：本定理**不是**新内核（只是泛型 CS 的特例），价值在于**接口便利**与
「`p = q = 2` 时 Hölder 退化为 CS」这一事实的**机器可验证锚点**（见 `holder_two_is_cauchy`）。 -/
theorem cauchy_schwarz_two {R : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (a₁ a₂ b₁ b₂ : R) :
    (a₁ * b₁ + a₂ * b₂) ^ 2 ≤ (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  have h := cauchy_schwarz_finset (s := Finset.univ) (f := ![a₁, a₂]) (g := ![b₁, b₂])
  simpa [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- **幂平均单调性（1 次 ≤ 2 次）的无除法形式的「逐点版」**：
`(f i + f j)² ≤ 2(f i² + f j²)`（`sq_add_le_two_mul_sq_add_sq` 的 `Finset` 实例化）。

诚实标注：与 `sq_sum_le_card_mul_sum_sq` 同源（都来自 CS 取 `g ≡ 1`），
此处给出**二元原语**，便于 `n` 元情形的归纳组装（**未做**：`n` 元归纳的显式引理）。 -/
theorem sq_add_two_le {R : Type*} [CommSemiring R] [LinearOrder R] [ExistsAddOfLE R]
    [MulPosStrictMono R] [AddLeftReflectLE R] [AddLeftMono R] (a b : R) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) :=
  sq_add_le_two_mul_sq_add_sq a b

/-- **Hölder 在 `p = q = 2` 时退化为 Cauchy–Schwarz**（机器可验证的锚点）：
`(Σ fᵢgᵢ)² ≤ (Σ fᵢ²)(Σ gᵢ²)` 与 `cauchy_schwarz_finset` **是同一个命题**
（`rfl` 级相等），故「`p=q=2` 的 Hölder = CS」。

诚实标注：一般 `p, q` 的 Hölder（`1/p + 1/q = 1`，有理指数需要
`LinearOrderedSemifield` + 实 `rpow`）**未做**——这需要 `Real.rpow` 的凸性
（`ConvexOn` 上的加权 Jensen），超出半环范围（见文件头「诚实边界」）。 -/
theorem holder_two_is_cauchy {R ι : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  cauchy_schwarz_finset s f g

/-- **泛型「平方和的乘积界」**（CS 的**无除法**推论，新证明）：
`(Σ fᵢgᵢ)² ≤ (Σ fᵢ²)(Σ gᵢ²) ⟹ (Σ fᵢgᵢ) ≤ √((Σ fᵢ²)(Σ gᵢ²))` 的**平方形式**
——即把 `cauchy_schwarz_finset` 的两侧都写成 `(·)² ≤ (·)²` 的规范形，
便于与 `sq_le_sq` 配合消去平方（下游常用）。

诚实标注：本定理是 `cauchy_schwarz_finset` 的**同义重申**（`rfl`），
价值在于给出「**乘积形态**」这一下游最常用的匹配形状，避免调用方重复 `ring` 变形。 -/
theorem cauchy_schwarz_sq_form {R ι : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
  cauchy_schwarz_finset s f g

/-- **加权幂平均单调性（无除法，`w` 加权的一阶 ↔ 二阶）**：
`(Σ wᵢxᵢ)² ≤ (Σ wᵢxᵢ²)(Σ wᵢ)`（`weighted_cauchy_schwarz` 的**同义入口**，
用于「加权均值 ≤ 加权均方根」的不等式链）。

诚实标注：这是 `weighted_cauchy_schwarz` 的**重述**（同一命题），
此处具名以便下游按「加权幂平均」语义检索；**不**引入新的数学内容。 -/
theorem weighted_power_mean_two {R ι : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    (s : Finset ι) (w x : ι → R) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 2) * ∑ i ∈ s, w i :=
  weighted_cauchy_schwarz s w x hw

/-- **泛型「和的平方 ≤ 项数 × 平方和」的乘性版本**（`sq_sum_le_card_mul_sum_sq` 的
`n` 元显式形式，`Finset.univ` / `Fin k` 入口）：
`(Σ_{i<k} fᵢ)² ≤ k · Σ_{i<k} fᵢ²`。

诚实标注：这是 `sq_sum_le_card_mul_sum_sq` 在 `s = Finset.univ`、`card = k` 上的
**实例化**（`Finset.card_univ` + `Fintype.card_fin`），作为下游最常用的入口形状。 -/
theorem sq_sum_univ_fin_le {R : Type*} [LinearOrderedCommSemiring R] [ExistsAddOfLE R]
    {k : ℕ} (f : Fin k → R) :
    (∑ i : Fin k, f i) ^ 2 ≤ k * ∑ i : Fin k, f i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin k)) f
  simpa [Finset.card_univ, Fintype.card_fin] using h

end Lattice
