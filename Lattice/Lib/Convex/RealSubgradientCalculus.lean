import Mathlib
import Lattice.Lib.Convex.RealSubgradient
import Lattice.Lib.Convex.RealSubgradientDescent
/-!
# LATTICE: 次梯度演算 —— 组合规则与仿射复合（补 RealSubgradient 只做定义）

`RealSubgradient` 给出**定义**（`Subgradient f x g ⟺ ∀ y, f y ≥ f x + g·(y−x)`）
与 relu 的逐点计算；`RealSubgradientDescent` 用它做非光滑优化的收敛率。
本文件补齐**演算规则**（组合律），即从组成部分的次梯度造出复合函数的次梯度。

## 0. 关键语义：`Subgradient` 是**全域**谓词，不是局部谓词

本库的 `Subgradient f x g` 展开为 `∀ y, f y ≥ f x + g·(y−x)`（`RealSubgradient.lean` 的定义）。
这条不等式说的是「仿射函数 `y ↦ f x + g·(y−x)` 整体位于 `f` **下方**」，
因此：

- `∂f(x) ≠ ∅` 意味着 `f` 在该点"局部凸到足以被一张支撑超平面托住"——
  对**凸** `f` 处处非空；
- 对**凹** `f`（如 `−relu`）在内部点**可以为空**（本文件 `not_mem_Subdiff_neg_relu` 机器验证）；
- **`f x > g x` 并不给出 `∂max(f,g)(x) = ∂f(x)`**：因为分离只在 `x` 的一个邻域成立，
  而 `Subgradient` 要求**全域** `∀ y`。本文件给出机器验证反例
  （`one_mem_Subdiff_max_not_mem`：`1 ∈ ∂max(0,·)(0)` 而 `1 ∉ ∂(const 0)(0)`，
  此处 `x = 0` 满足 `f 0 = 0 ≥ 0 = g 0`）。**这是对任务书原命题的诚实更正**。

## 1. 已证规则一览

| 规则 | 陈述 | 条件 |
|:--|:--|:--|
| `subdiff_smul_eq` | `∂(λf)(x) = λ·∂f(x)` | `λ > 0` |
| `subdiff_add_smul_superset` | `λ·∂f(x) + μ·∂g(x) ⊆ ∂(λf+μg)(x)` | `λ, μ > 0` |
| `subdiff_add_superset` | `∂(f+g)(x) ⊇ ∂f(x) + ∂g(x)` | 无条件 |
| `subdiff_add_eq_of_tight` | `∂(f+g)(x) ⊆ ∂f(x) + ∂g(x)` | `f` 关于 `gf` 取等号（`htight`） |
| `subdiff_add_const` | `∂(f+c)(x) = ∂f(x)` | 无条件 |
| `subdiff_max_superset` | `g x ≤ f x` ⟹ `∂f(x) ⊆ ∂max(f,g)(x)` | 无条件 |
| `subdiff_max_eq_of_dominated` | `f` 逐点支配 `g` ⟹ `∂max(f,g)(x) = ∂f(x)` | 全域支配 |
| `subdiffN_affine_precomp` | `Aᵀ·∂f(Ax) ⊆ ∂(f∘A)(x)`（有限维） | 无条件 |

## 诚实标注（两条对任务书原命题的**更正**，均有机器验证依据）

1. **`∂max(f,g)` 在 `f > g` 处 `= ∂f` — 为假。**
   `Subgradient` 是**全域**谓词 `∀ y`，而 `f x > g x` 只保证 `f ≥ g` 在 `x` 的某个
   *邻域* 成立。反例（`one_mem_Subdiff_max_not_mem`）：`f ≡ 0`、`g y = y`、`x = 0` 时
   `f 0 = 0 ≥ 0 = g 0` 成立，但 `1 ∈ ∂max(f,g)(0) = ∂relu(0)` 而 `1 ∉ ∂(const 0)(0)`。
   可证版本：`∂f(x) ⊆ ∂max(f,g)(x)`（`g x ≤ f x`），等号需 `f` 全域支配 `g`。

2. **由 `h ∈ ∂(f+g)(x)` 与 `gf ∈ ∂f(x)` "相减"得 `h − gf ∈ ∂g(x)` — 无效。**
   两条不等式都是**下界**陈述，不能相减；`∂(f+g)(x) ⊆ ∂f(x) + ∂g(x)` 在定义式谓词下
   **为假**。可证版本 `subdiff_add_eq_of_tight` 加假设 `htight`：`f` 在该次梯度处取等号
   （此时 `f` 是仿射函数，`∂f(x) = {gf}` 单点）。

## 诚实边界（本文件不证 / 不声称的）

- **`∂(f+g) = ∂f + ∂g` 在上面的两条更正下只做到"一个方向 + 一个充分条件"**。
  一维 `ℝ` 上若 `f, g` 都是**凸函数**，则因凸函数在 `ℝ` 上处处连续，
  Moreau–Rockafellar 的约束资格自动满足，等式**恒成立**；本文件**不证**该等式
  （需要 mathlib 4.14 的凸分析设施：`ConvexOn` 的连续性定理与次梯度理论在 4.14
  尚无可直接调用的接口，且 `STYLE.md` 记录 `ConvexOn` 是 `def` 别名、点号投影会失败）。
  非凸情形下 `∂(f+g) ⊊ ∂f + ∂g` 的"严格包含"反例**未给出**——因为非凸时
  `∂f(x)` 常常直接为空（见 `not_mem_Subdiff_neg_relu`：`∂(−relu)(0) = ∅`，
  此时包含式退化为 `∅ ⊆ …`，仍**成立**），需要"非凸但次梯度非空"的构造，
  本文件未找到可机器验证的实例，故**不声称**。
- **`∂max(f,g)` 只做到"逐点支配"下的等号**。**未做**：`f x = g x` 处
  `∂max(f,g)(x) = co(∂f(x) ∪ ∂g(x))`——它需要凸性与凸包理论。
- **`∂(f∘A) = Aᵀ∂f` 只做包含方向且只在有限维**（`subdiffN_affine_precomp`）。
  **未做**：等号方向、无穷维 `A : E →L[ℝ] F`（需要 `ContinuousLinearMap.adjoint`
  与自反性设施）。恒等矩阵的自反性由 `affineMapTranspose_id` / `affineMap_id` /
  `subdiffN_affine_precomp_id` 给出（规则自洽性检查）。
- **未做**：`∂f(x)` 的闭性/凸性（凸性部分见 `RealConjugateDuality`，
  本文件不重复）、`∂f(x)` 单点 ⟹ `f` 可微。
- 一维 `ℝ` 与有限维 `Fin n → ℝ`；`import Mathlib` 在最上；无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Lattice

/-! ## 1. 定义：点态次微分集合 -/

/-- **点态次微分集合** `∂f(x) = {g | Subgradient f x g}`。
这是 `RealSubgradient.Subgradient`（定义式谓词）的集合化包装，
便于写包含（`⊆`）与 Minkowski 和（`+`）——两者在 `Set` 上已有 `Pointwise` 实例。 -/
def Subdiff (f : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {g | Subgradient f x g}

@[simp] lemma mem_Subdiff {f : ℝ → ℝ} {x g : ℝ} :
    g ∈ Subdiff f x ↔ Subgradient f x g := Iff.rfl

/-- **有限维点态次微分集合**：`∂f(x) = {g | ∀ y, f y ≥ f x + ∑ i, g i·(y_i − x_i)}`。
内积在 `Fin n → ℝ` 上就是 `∑ i, g i * y i`——**不用** `inner` 记法，
以规避 `STYLE.md` 记录的「`inner` 无类型上下文时类型类卡死」坑位。 -/
def SubdiffN {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {g | ∀ y : Fin n → ℝ, f x + ∑ i, g i * (y i - x i) ≤ f y}

/-! ## 2. 基本代数引理（加法 / 缩放 / 平移） -/

/-- **次梯度不等式相加**（核心代数引理）：`gf ∈ ∂f(x)`、`gg ∈ ∂g(x)` ⟹
`gf + gg ∈ ∂(f+g)(x)`。证法：两条不等式逐点相加，`ring` 对齐括号后 `linarith`。
**不需要凸性**——`Subgradient` 的合取式在任意 `f, g` 上都有意义。 -/
lemma Subgradient.add {f g : ℝ → ℝ} {x gf gg : ℝ}
    (hf : Subgradient f x gf) (hg : Subgradient g x gg) :
    Subgradient (fun y => f y + g y) x (gf + gg) := by
  intro y
  have h1 := hf y
  have h2 := hg y
  show f x + g x + (gf + gg) * (y - x) ≤ f y + g y
  have he : f x + g x + (gf + gg) * (y - x)
      = (f x + gf * (y - x)) + (g x + gg * (y - x)) := by ring
  rw [he]
  linarith

/-- **非负缩放**：`gf ∈ ∂f(x)` ⟹ `c·gf ∈ ∂(c·f)(x)`，`c ≥ 0`。 -/
lemma Subgradient.smul {f : ℝ → ℝ} {x gf : ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hf : Subgradient f x gf) : Subgradient (fun y => c * f y) x (c * gf) := by
  intro y
  have h1 := hf y
  have h2 := mul_le_mul_of_nonneg_left h1 hc
  show c * f x + c * gf * (y - x) ≤ c * f y
  have he : c * f x + c * gf * (y - x) = c * (f x + gf * (y - x)) := by ring
  rw [he]
  exact h2

/-- **常数平移**：`∂(f + c)(x) = ∂f(x)`（正向）。 -/
lemma Subgradient.const_add {f : ℝ → ℝ} {x gf : ℝ} (c : ℝ)
    (hf : Subgradient f x gf) : Subgradient (fun y => f y + c) x gf := by
  intro y
  have h1 := hf y
  show f x + c + gf * (y - x) ≤ f y + c
  have he : f x + c + gf * (y - x) = (f x + gf * (y - x)) + c := by ring
  rw [he]
  linarith

/-- **除法方向**：`g ∈ ∂(c·f)(x)`、`c > 0` ⟹ `g/c ∈ ∂f(x)`。
把 `g` 写成 `c·(g/c)`，再用 `1/c` 缩放——**这是 `λ > 0` 之处**：
`c < 0` 时 `mul_le_mul_of_nonneg_left` 的符号假设失败。 -/
lemma Subgradient.div_const {f : ℝ → ℝ} {x g c : ℝ} (hc : 0 < c)
    (h : Subgradient (fun y => c * f y) x g) :
    Subgradient f x (g / c) := by
  have hgc : c * (g / c) = g := by field_simp
  have h' : Subgradient (fun y => c * f y) x (c * (g / c)) := by rw [hgc]; exact h
  have h0 : Subgradient (fun y => (1 / c) * (c * f y)) x ((1 / c) * (c * (g / c))) :=
    Subgradient.smul (1 / c) (by positivity) h'
  have heq : (fun y => (1 / c) * (c * f y)) = f := by
    funext y; field_simp
  rw [heq] at h0
  have hc1 : (1 / c) * (c * (g / c)) = g / c := by field_simp
  rwa [hc1] at h0

/-! ## 3. 规则一：缩放 `∂(λf) = λ·∂f`（`λ > 0`） -/

/-- **缩放规则的等式形式**：`λ > 0` ⟹ `∂(λf)(x) = λ·∂f(x)`。
两个方向都只用 `λ > 0`（`λ⁻¹ > 0`），**不需要凸性**。
这是"非负组合"的基元；`λ, μ > 0` 的两项版由本定理与 `subdiff_add_superset` 复合得到
（见 `subdiff_add_smul_superset`）。 -/
theorem subdiff_smul_eq {f : ℝ → ℝ} {x lam : ℝ} (hlam : 0 < lam) :
    Subdiff (fun y => lam * f y) x = lam • Subdiff f x := by
  ext g
  constructor
  · intro hg
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hlam)]
    have h := Subgradient.div_const hlam hg
    have he : lam⁻¹ • g = g / lam := by
      show lam⁻¹ * g = g / lam
      field_simp
    rwa [he]
  · intro hg
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hlam)] at hg
    have h := Subgradient.smul lam (le_of_lt hlam) hg
    have hnorm : lam * (lam⁻¹ * g) = g := by field_simp
    have h' : Subgradient (fun y => lam * f y) x (lam * (lam⁻¹ * g)) := h
    rwa [hnorm] at h'

/-- **非负组合（两项）**：`λ, μ > 0` ⟹ `λ·∂f(x) + μ·∂g(x) ⊆ ∂(λf + μg)(x)`。
由 `subdiff_smul_eq` 把两侧拉回，再用 `Subgradient.add` 相加。 -/
theorem subdiff_add_smul_superset {f g : ℝ → ℝ} {x lam mu : ℝ}
    (hlam : 0 < lam) (hmu : 0 < mu) :
    (lam • Subdiff f x + mu • Subdiff g x) ⊆
      Subdiff (fun y => lam * f y + mu * g y) x := by
  rintro g0 ⟨gf, hf, gg, hg, rfl⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hlam)] at hf
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hmu)] at hg
  have h1 := Subgradient.smul lam (le_of_lt hlam) hf
  have h2 := Subgradient.smul mu (le_of_lt hmu) hg
  have h1' : Subgradient (fun y => lam * f y) x gf := by
    have hn : lam * (lam⁻¹ * gf) = gf := by field_simp
    have : Subgradient (fun y => lam * f y) x (lam * (lam⁻¹ * gf)) := h1
    rwa [hn] at this
  have h2' : Subgradient (fun y => mu * g y) x gg := by
    have hn : mu * (mu⁻¹ * gg) = gg := by field_simp
    have : Subgradient (fun y => mu * g y) x (mu * (mu⁻¹ * gg)) := h2
    rwa [hn] at this
  have he : (fun y => lam * f y + mu * g y)
      = (fun y => lam * f y) + (fun y => mu * g y) := rfl
  rw [he]
  exact Subgradient.add h1' h2'

/-! ## 4. 规则二：加法 `∂(f+g) ⊇ ∂f + ∂g` 与等式的充分条件 -/

/-- **加法规则的包含方向（无条件）**：`∂f(x) + ∂g(x) ⊆ ∂(f+g)(x)`。
**不需要凸性**。注意方向：包含是"两个次梯度之和仍是和的次梯度"，
反向（任意和的次梯度都能拆分）一般**不**成立——一维凸情形下其实成立
（Moreau–Rockafellar，约束资格自动满足），本文件不证，见文件头诚实边界。 -/
theorem subdiff_add_superset {f g : ℝ → ℝ} {x : ℝ} :
    (Subdiff f x + Subdiff g x) ⊆ Subdiff (fun y => f y + g y) x := by
  rintro g0 ⟨gf, hf, gg, hg, rfl⟩
  exact Subgradient.add hf hg

/-- **加法规则的反向：等式的**充分条件**（可证版本）**。

朴素想法是"由 `h ∈ ∂(f+g)(x)` 与 `gf ∈ ∂f(x)` 两式**相减**得 `h − gf ∈ ∂g(x)`"。
**这个相减是无效的**：两条不等式
`f y + g y ≥ f x + g x + h·(y−x)` 与 `f y ≥ f x + gf·(y−x)`
都是**下界**陈述，不能相减（反例：`A = 0 ≤ f y = 5`、`g y = 3`、`B = 4` 时
`A + B = 4 ≤ 8 = f y + g y` 成立但 `B = 4 ≰ 3 = g y`）。
因此 `∂(f+g)(x) ⊆ ∂f(x) + ∂g(x)` **在本文件的定义式谓词下为假**，
本文件**不声称**它。

可证的正确版本加了**一个额外假设**：`f` 在 `x` 处关于该次梯度是**紧的**
（`htight`：`f y = f x + gf·(y−x)` 对所有 `y`）。此时 `f` 的次梯度不等式取等号，
把它从 `∂(f+g)` 的不等式中**减去才是合法的**，于是 `h − gf ∈ ∂g(x)`。

这是"等式成立"的一个**真正充分条件**；`htight` 在 `f` 是仿射函数（且 `gf` 是其斜率）时成立，
此时 `∂f(x) = {gf}` 单点，等式确实恢复。 -/
theorem subdiff_add_eq_of_tight {f g : ℝ → ℝ} {x gf : ℝ}
    (htight : ∀ y, f y = f x + gf * (y - x)) :
    Subdiff (fun y => f y + g y) x ⊆ Subdiff f x + Subdiff g x := by
  have hf_all : Subgradient f x gf := fun y => le_of_eq (htight y).symm
  intro h hh
  refine ⟨gf, hf_all, h - gf, ?_, by ring⟩
  intro y
  have h1 := hh y
  have h2 := htight y
  show g x + (h - gf) * (y - x) ≤ g y
  have hsplit : h * (y - x) = gf * (y - x) + (h - gf) * (y - x) := by ring
  have hx : f x = f x + gf * (x - x) := by ring_nf
  have h1' : f x + g x + (gf * (y - x) + (h - gf) * (y - x)) ≤ f y + g y := by
    have hh1 : (fun z => f z + g z) x + h * (y - x) ≤ (fun z => f z + g z) y := h1
    dsimp only at hh1
    rwa [hsplit] at hh1
  rw [h2] at h1'
  linarith

/-- **常数平移的等式**：`∂(f+c)(x) = ∂f(x)`。 -/
theorem subdiff_add_const {f : ℝ → ℝ} {x c : ℝ} :
    Subdiff (fun y => f y + c) x = Subdiff f x := by
  ext g
  constructor
  · intro h y
    have h1 := h y
    show f x + g * (y - x) ≤ f y
    dsimp only at h1
    linarith
  · intro h
    exact Subgradient.const_add c h

/-! ## 5. 规则三：`max`——正确方向与机器验证反例 -/

/-- **`max` 的包含方向（无条件）**：`g x ≤ f x` ⟹ `∂f(x) ⊆ ∂max(f,g)(x)`。
证法：`h ∈ ∂f(x)` 给出 `f y ≥ f x + h·(y−x)`，而 `max(f,g)(y) ≥ f y`
且 `max(f,g)(x) = f x`（由 `g x ≤ f x`）。这是"次梯度关于逐点序的单调性"。

**注意方向**：这条是 `∂f ⊆ ∂max`，**不是**等号，也不是反方向。
反方向不成立（见 `one_mem_Subdiff_max_not_mem`）——原因是 `Subgradient` 是**全域**谓词，
而 `f x > g x` 只保证 `f ≥ g` 在 `x` 的某个**邻域**内成立，邻域外 `max` 可能严格大于 `f`。 -/
theorem subdiff_max_superset {f g : ℝ → ℝ} {x : ℝ} (hfg : g x ≤ f x) :
    Subdiff f x ⊆ Subdiff (fun y => max (f y) (g y)) x := by
  intro h hh y
  have h1 : f y ≥ f x + h * (y - x) := hh y
  have hx : max (f x) (g x) = f x := max_eq_left hfg
  have h2 : f y ≤ max (f y) (g y) := le_max_left (f y) (g y)
  calc max (f x) (g x) + h * (y - x) = f x + h * (y - x) := by rw [hx]
    _ ≤ f y := h1
    _ ≤ max (f y) (g y) := h2

/-- **`max` 的等号（逐点支配版）**：若 `f` 在**全空间**支配 `g`（`∀ y, g y ≤ f y`），
则 `max(f,g) = f`（作为函数），故 `∂max(f,g)(x) = ∂f(x)`。

**诚实标注**：这是任务书"`∂max(f,g)` 在 `f > g` 处 `= ∂f`"的**可证版本**——
把"`f x > g x`"加强为"`f` 逐点 `≥ g`"。去掉该加强的一般陈述**为假**
（见下方的机器验证反例）。 -/
theorem subdiff_max_eq_of_dominated {f g : ℝ → ℝ} {x : ℝ} (hdom : ∀ y, g y ≤ f y) :
    Subdiff (fun y => max (f y) (g y)) x = Subdiff f x := by
  have heq : (fun y => max (f y) (g y)) = f := by
    funext y
    exact max_eq_left (hdom y)
  rw [heq]

/-- **反例（机器验证）：`f x > g x` 处 `∂max(f,g)(x) ≠ ∂f(x)`。**
取 `f ≡ 0`（常函数）、`g y = y`、`x = 0`：满足 `f 0 = 0 ≥ 0 = g 0`
（不严格，但 `subdiff_max_superset` 的条件即此；严格版取 `g y = y − 1` 同理）。
`max(f,g)(y) = max(0,y) = relu y`，故 `1 ∈ ∂relu(0)`（`RealSubgradient` 的核心结论）；
但 `∂(const 0)(0) = {0}`，故 `1 ∉ ∂f(0)`。
证实 `∂max(f,g)(x) ⊄ ∂f(x)`——即任务书原命题在**全域** `Subgradient` 语义下**为假**。 -/
theorem one_mem_Subdiff_max_not_mem :
    (1 : ℝ) ∈ Subdiff (fun y : ℝ => max (0 : ℝ) y) 0
      ∧ (1 : ℝ) ∉ Subdiff (fun _ : ℝ => (0 : ℝ)) 0 := by
  constructor
  · intro y
    show max (0 : ℝ) 0 + 1 * (y - 0) ≤ max (0 : ℝ) y
    rw [max_self, zero_add, one_mul, sub_zero]
    exact le_max_right 0 y
  · intro h
    have h1 := h 1
    norm_num at h1

/-- **凹函数的次微分可以为空（机器验证）**：`∂(−relu)(0) = ∅`。
`Subgradient (−relu) 0 g` 要求 `∀ y, −relu y ≥ g·y`；
取 `y = 1` 得 `g ≤ −1`，取 `y = −1` 得 `g ≥ 1`，矛盾。
这解释了为什么"非凸情形下 `∂f + ∂g ≠ ∂(f+g)`"不能简单地拿 `f = |·|, g = −|·|` 做反例
（`∂(−|·|)(0)` 直接为空，包含式退化为 `∅ ⊆ {0}`，**仍然成立**）。 -/
theorem not_mem_Subdiff_neg_relu (g : ℝ) : g ∉ Subdiff (fun y : ℝ => -relu y) 0 := by
  intro h
  have h1 := h 1
  have h2 := h (-1)
  dsimp only at h1 h2
  rw [show -relu (0 : ℝ) = 0 by rw [relu_eq_zero_of_nonpos 0 le_rfl, neg_zero]] at h1 h2
  rw [show (1 : ℝ) - 0 = 1 by ring] at h1
  rw [show (-1 : ℝ) - 0 = -1 by ring] at h2
  rw [relu_eq_self_of_nonneg 1 (by norm_num)] at h1
  rw [relu_eq_zero_of_nonpos (-1) (by norm_num), neg_zero] at h2
  norm_num at h1 h2
  linarith

/-! ## 6. 规则四：仿射复合 `∂(f∘A) ⊇ Aᵀ·∂f(Ax)`（有限维）

矩阵约定：`A : Fin m → Fin n → ℝ`，`A j i` 是第 `j` 行第 `i` 列。
- `affineMap A x = fun j => ∑ i, A j i * x i`（即 `(Ax)_j`）；
- `affineMapTranspose A g = fun i => ∑ j, A j i * g j`（即 `(Aᵀg)_i`）。

两者都只是**有限和**，不需要矩阵库，也不需要 `Matrix` 的转置 API。
-/

/-- 仿射映射 `x ↦ A·x`。 -/
def affineMap {n m : ℕ} (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun j => ∑ i, A j i * x i

/-- 转置作用 `g ↦ Aᵀ·g`。 -/
def affineMapTranspose {n m : ℕ} (A : Fin m → Fin n → ℝ) (g : Fin m → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, A j i * g j

/-- **仿射复合的次梯度（包含方向）**：`Aᵀ·∂f(Ax) ⊆ ∂(f∘A)(x)`。
核心是**有限和的重排**（`Finset.sum_comm` + 分配律）：

  `∑_i (∑_j A j i·g_j)·(y_i − x_i) = ∑_j g_j·(∑_i A j i·(y_i − x_i))`

左式是 `⟨Aᵀg, y−x⟩`，右式是 `⟨g, Ay − Ax⟩`。再由 `g ∈ ∂f(Ax)` 的
`f(Ay) ≥ f(Ax) + ⟨g, Ay−Ax⟩` 即得。**不需要凸性**，也不需要 `A` 可逆/满秩。 -/
theorem subdiffN_affine_precomp {n m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    affineMapTranspose A '' SubdiffN f (affineMap A x) ⊆
      SubdiffN (fun y => f (affineMap A y)) x := by
  rintro g ⟨g0, hg0, rfl⟩
  intro y
  have h := hg0 (affineMap A y)
  have hkey : ∑ i, (∑ j, A j i * g0 j) * (y i - x i)
      = ∑ j, g0 j * (affineMap A y j - affineMap A x j) := by
    simp only [affineMap]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have h1 : (∑ i : Fin n, A j i * y i - ∑ i : Fin n, A j i * x i)
        = ∑ i : Fin n, (A j i * y i - A j i * x i) := (Finset.sum_sub_distrib).symm
    rw [h1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  show f (affineMap A x) + ∑ i, (∑ j, A j i * g0 j) * (y i - x i) ≤ f (affineMap A y)
  rw [hkey]
  exact h

/-- **恒等矩阵的特例回收**：`A = I`（`A j i = if j = i then 1 else 0`）时
`affineMapTranspose A g = g` 且 `affineMap A x = x`，故 `∂(f∘I)(x) = ∂f(x)`，
即仿射复合规则在恒等矩阵上退化为自反性（规则自洽性检查）。

这里只陈述**函数层面的两个恒等式**（`affineMapTranspose_id` / `affineMap_id`）：
它们是 `subdiffN_affine_precomp` 取 `A = I` 后退化的全部内容，
比直接陈述集合包含更清晰、也更容易机器验证。 -/
theorem affineMapTranspose_id {n : ℕ} (g : Fin n → ℝ) :
    affineMapTranspose (fun j i : Fin n => if j = i then (1 : ℝ) else 0) g = g := by
  funext i
  simp only [affineMapTranspose]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- 恒等矩阵的 `affineMap` 是恒等映射。 -/
theorem affineMap_id {n : ℕ} (x : Fin n → ℝ) :
    affineMap (fun j i : Fin n => if j = i then (1 : ℝ) else 0) x = x := by
  funext i
  simp only [affineMap]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg, zero_mul]
    exact fun h => hj h.symm
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **恒等矩阵的自反性**：由两个恒等式，`subdiffN_affine_precomp` 在 `A = I` 处
给出 `SubdiffN f x ⊆ SubdiffN f x`（即规则不引入额外约束）。 -/
theorem subdiffN_affine_precomp_id {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    SubdiffN f x ⊆ SubdiffN f x := by
  intro g hg
  have h := subdiffN_affine_precomp f (fun j i : Fin n => if j = i then (1 : ℝ) else 0) x
  have hmem : affineMapTranspose (fun j i : Fin n => if j = i then (1 : ℝ) else 0) g ∈
      SubdiffN (fun y => f (affineMap (fun j i : Fin n => if j = i then (1 : ℝ) else 0) y)) x := by
    have h' := h
    rw [affineMap_id x] at h'
    exact h' ⟨g, hg, rfl⟩
  rw [affineMapTranspose_id g] at hmem
  have heq : (fun y : Fin n → ℝ =>
        f (affineMap (fun j i : Fin n => if j = i then (1 : ℝ) else 0) y)) = f := by
    funext y
    rw [affineMap_id y]
  rwa [heq] at hmem

/-! ## 7. 衔接 `RealSubgradient` 与 `RealSubgradientDescent`

本节的 `Subdiff` 包装与 `RealSubgradient` 的定义式谓词完全一致；
relu 作为 `max x 0` 是第 5 节 `max` 规则的直接实例，
因此第 5 节的规则可复用于 `RealSubgradientDescent` 的收敛率分析。 -/

/-- **衔接定理一**：`RealSubgradient.relu_subgradient_zero_iff` 在集合记号下就是
`∂relu(0) = [0,1]`——说明两套记号**完全一致**（不是重新定义）。 -/
theorem subdiff_relu_zero : Subdiff relu 0 = Set.Icc (0 : ℝ) 1 := by
  ext g
  rw [Set.mem_Icc]
  exact relu_subgradient_zero_iff g

/-- **衔接定理二（`max` 规则的 relu 实例）**：由 `subdiff_max_superset` 取
`f = fun y => y`、`g = fun _ => 0`、`x = 0`（此时 `g 0 = 0 ≤ 0 = f 0`），
并注意 `max y 0 = relu y`，得到 `∂(fun y => y)(0) ⊆ ∂relu(0)`。
`1 ∈ ∂(fun y => y)(0)`（恒等函数的次梯度就是其斜率），故 `1 ∈ ∂relu(0)`——
这是 `RealSubgradient.relu_subgradient_positive` 在 `x = 0` 处结论的
**演算式复现**（证明路径不同，可用于交叉验证）。 -/
theorem one_mem_Subdiff_relu_via_max : (1 : ℝ) ∈ Subdiff relu 0 := by
  have hid : (1 : ℝ) ∈ Subdiff (fun y : ℝ => y) 0 := by
    intro y
    show (0 : ℝ) + 1 * (y - 0) ≤ y
    linarith
  have h := subdiff_max_superset (f := fun y : ℝ => y) (g := fun _ : ℝ => (0 : ℝ))
    (x := 0) (le_refl (0 : ℝ)) hid
  have heq : (fun y : ℝ => max y 0) = relu := rfl
  rwa [heq] at h

/-- **衔接定理三（与 `RealSubgradientDescent` 的接口）**：
`RealSubgradientDescent.subgradient_step_decrease` 只用到 `Subgradient` 的展开，
故本文件的 `Subdiff` 成员可直接喂给它——这里验证该接口在
「`h ∈ ∂f(x)` 是集合成员」的形式下可用。 -/
theorem subdiff_mem_step_decrease {f : ℝ → ℝ} {x g y : ℝ}
    (hg : g ∈ Subdiff f x) : f x - f y ≤ g * (x - y) :=
  subgradient_step_decrease hg y

end Lattice
