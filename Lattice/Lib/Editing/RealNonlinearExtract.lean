import Mathlib
import Lattice.Lib.FCA.RealFCA
import Lattice.Lift.RealNonlinear
/-!
# LATTICE: 非线性提取 —— FCA 结构解与激活的分段可逆性

`RealFCA` 给出形式概念分析（FCA）的提取算子（`extent`/`intent`）及其闭包幂等性；
`RealNonlinear` 给出 ReLU 的零化编码 `relu x = max x 0`。本文件把两者收拢为
「非线性提取」的结构性结果：

  1. `closureOperator`：对象端提取算子 `Ol ↦ extent R (intent R Ol)`（↑↓ 复合）；
  2. `extract_idempotent`：提取幂等（回收 `RealFCA.closure_idempotent`）；
  3. `closureOperator_extensive`：提取扩张 `Ol ⊆ closureOperator Ol`；
  4. `closureOperator_monotone`：提取单调；
  5. `extract_preserves_fixpoint`：形式概念（`IsFormalConcept`）是不动点，提取后不变；
  6. `relu_extract_on_positive`：ReLU 在正区域可逆（`x ≥ 0 ⟹ relu x = x`），
     `relu_extract_recovery`：正区域上「取逆再激活」恢复输入；
  7. `piecewiseLin`：分段线性函数；`piecewiseLin_left/right` 给出逐段取值，
     `piecewiseLin_left_invertible/right_invertible`：每段内可逆 ⟹ 逐段恢复输入。

诚实标注（无 sorry / axiom / admit）：
- **全局激活级可逆仍开放**：非线性激活（ReLU 等）在 ℝ 上不是单射，
  「任意网络的激活级精确反演」不在本文件范围内。本文件只给出**区域可逆**
  （正区域、分段区域）的严格陈述。
- `piecewiseLin` 的「可逆」是**给定每段逆函数后的复合恒等**，并不构造逆函数本身；
  逆函数的存在性由用户以假设 `hfi`/`hgi` 提供。
- 本文件不引入任何未证假设。
-/

noncomputable section

namespace Lattice

/-! ## 一、FCA 提取算子 -/

/-- 对象端提取算子：`closureOperator R Ol = extent R (intent R Ol)`（先反提取属性、
再提取对象，即 FCA 中的 ↑↓ 复合）。 -/
def closureOperator {O A : Type*} (R : O → A → Prop) (Ol : Set O) : Set O :=
  extent R (intent R Ol)

/-- **提取幂等**：对提取算子再作用一次不改变结果（回收 `RealFCA.closure_idempotent`）。 -/
theorem extract_idempotent {O A : Type*} (R : O → A → Prop) (Ol : Set O) :
    closureOperator R (closureOperator R Ol) = closureOperator R Ol := by
  unfold closureOperator
  exact closure_idempotent R Ol

/-- **提取扩张**：`Ol ⊆ closureOperator R Ol`（回收 `RealFCA.subset_extent_intent`）。 -/
theorem closureOperator_extensive {O A : Type*} (R : O → A → Prop) (Ol : Set O) :
    Ol ⊆ closureOperator R Ol :=
  subset_extent_intent R Ol

/-- **提取单调**：`O₁ ⊆ O₂ ⟹ closureOperator O₁ ⊆ closureOperator O₂`
（`intent` 反变 + `extent` 反变 = 提取单调）。 -/
theorem closureOperator_monotone {O A : Type*} (R : O → A → Prop) {O₁ O₂ : Set O}
    (h : O₁ ⊆ O₂) : closureOperator R O₁ ⊆ closureOperator R O₂ := by
  unfold closureOperator
  exact extent_antitone R (intent_antitone R h)

/-- **提取保持不动点**：形式概念 `(Ol, B)` 在提取下不变。 -/
theorem extract_preserves_fixpoint {O A : Type*} (R : O → A → Prop) (Ol : Set O)
    (B : Set A) (h : IsFormalConcept R Ol B) : closureOperator R Ol = Ol := by
  unfold IsFormalConcept at h
  obtain ⟨h1, h2⟩ := h
  unfold closureOperator
  rw [← h2, ← h1]

/-! ## 二、ReLU 在正区域的可逆性 -/

/-- ReLU 的（正区域）逆函数：恒等映射。 -/
def reluInv (x : ℝ) : ℝ := x

/-- **ReLU 在正区域可逆**：`x ≥ 0 ⟹ relu x = x`（`relu = max x 0`）。 -/
theorem relu_extract_on_positive (x : ℝ) (hx : 0 ≤ x) : relu (reluInv x) = x := by
  unfold reluInv relu
  exact max_eq_left hx

/-- **正区域恢复**：先激活再取逆恢复输入（`x ≥ 0`）。 -/
theorem relu_extract_recovery (x : ℝ) (hx : 0 ≤ x) : reluInv (relu x) = x := by
  unfold reluInv relu
  rw [max_eq_left hx]

/-! ## 三、分段线性提取 -/

/-- 分段线性函数：阈值 `c`，左段 `f`、右段 `g`。 -/
def piecewiseLin (c : ℝ) (f g : ℝ → ℝ) : ℝ → ℝ := fun x => if x ≤ c then f x else g x

/-- 左段取值：`x ≤ c ⟹ piecewiseLin c f g x = f x`。 -/
theorem piecewiseLin_left (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) (hx : x ≤ c) :
    piecewiseLin c f g x = f x := by
  unfold piecewiseLin
  exact if_pos hx

/-- 右段取值：`c < x ⟹ piecewiseLin c f g x = g x`。 -/
theorem piecewiseLin_right (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) (hx : c < x) :
    piecewiseLin c f g x = g x := by
  unfold piecewiseLin
  exact if_neg (not_le.mpr hx)

/-- **左段可逆**：给定左段逆 `fi`（`fi (f x) = x`），逐段提取恢复输入。 -/
theorem piecewiseLin_left_invertible (c : ℝ) (f g fi : ℝ → ℝ) (x : ℝ) (hx : x ≤ c)
    (hfi : fi (f x) = x) : fi (piecewiseLin c f g x) = x := by
  rw [piecewiseLin_left c f g x hx]
  exact hfi

/-- **右段可逆**：给定右段逆 `gi`（`gi (g x) = x`），逐段提取恢复输入。 -/
theorem piecewiseLin_right_invertible (c : ℝ) (f g gi : ℝ → ℝ) (x : ℝ) (hx : c < x)
    (hgi : gi (g x) = x) : gi (piecewiseLin c f g x) = x := by
  rw [piecewiseLin_right c f g x hx]
  exact hgi

end Lattice
