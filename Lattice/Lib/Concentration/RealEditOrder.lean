import Lattice.Lib.Editing.RealEditRollback
import Lattice.Lib.Architectures.RealCrosstalkGeneral
import Lattice.Lib.Editing.RealEditCrosstalk
import Mathlib

/-!
# LATTICE: 序列编辑的顺序性质 —— 交换性、顺序无关性与顺序相关的显式刻画

权重编辑线（ROME/MEMIT 的 rank-one 补丁）的**顺序维度**：把多个编辑
依次施加时，最终权重是否依赖于施加顺序？本文件给出三种语义下的精确回答。

## 一、自由增量补丁：顺序**严格无关**（无需任何假设）

RealEditRollback.rankOneEdit 的自由增量版本

    rankOneEdit F Δ k : x ↦ F x + ⟨k,x⟩·Δ

中 Δ 是**预先给定**的常数（不依赖当前 F）。此时：

  · `editSeqComm`（核心）：`rankOneEdit (rankOneEdit F Δ₁ k₁) Δ₂ k₂
      = rankOneEdit (rankOneEdit F Δ₂ k₂) Δ₁ k₁`
    —— 两次编辑**无条件**可交换（纯加法交换律，`ring`）；
  · `editSeq_closed_form`：任意有限编辑列表的闭式
    `editSeq l F x = F x + Σ_{(Δ,k) ∈ l} ⟨k,x⟩·Δ`（对列表结构归纳，
    自由增量下补丁不依赖当前 F，故归纳步无需任何正交性）；
  · `order_invariance_free`（核心）：`editSeq (l₁ ++ l₂) F = editSeq (l₂ ++ l₁) F`
    —— 任意顺序拼接给出同一函数（闭式对顺序明显对称，由 `freeSum_append` + 交换律）。
  **诚实标注**：正交键对自由增量补丁的交换性**并非必需**——加法本身可交换；
  正交性只在 ROME/MEMIT 的**派生增量**语义下才成为顺序无关的充分条件（见下）。

## 二、ROME 语义（Δ 依赖当前权重）：正交键下顺序无关

RealEditCrosstalk.ApplyEdit 的增量 Δ = (v − F·k)/‖k‖² **依赖当前权重**，
故顺序一般不可交换。本文件给出两个精确的"顺序无关"结果：

  · `edit2_orthogonal_commutes`（核心）：两编辑键正交（⟨k₁,k₂⟩=⟨k₂,k₁⟩=0）时
    `ApplyEdits2 F k₁ k₂ v₁ v₂ = ApplyEdits2 F k₂ k₁ v₂ v₁`（函数相等）；
  · `romeEditSeq_orthogonal_fixed`：与 k 正交的键的编辑不改变 k 处的值
    （`ApplyEdit G k' v' k = G k`，⟨k',k⟩=0）；
  · `order_invariance_orthogonal`（核心）：编辑 e 在列表中的位置不影响**它在
    自己键处的最终值**：只要 e 之后（后缀 l₂）的编辑键与 e 正交，就有
    `romeEditSeq (l₁ ++ e :: l₂) F e.1 = e.2`，**与前缀 l₁ 完全无关**
    （写入是精确的，后续正交键编辑不动它）。

## 三、一般键：顺序相关的显式刻画

  · `order_dependence_general`（核心精确公式）：一般键下两次顺序之差**恰好**
    是两个串扰项：
    `ApplyEdits2 F k₁ k₂ v₁ v₂ x − ApplyEdits2 F k₂ k₁ v₂ v₁ x
      = ⟨k₁,x⟩·(⟨k₂,k₁⟩·d₂)/‖k₁‖² − ⟨k₂,x⟩·(⟨k₁,k₂⟩·d₁)/‖k₂‖²`
    其中 dᵢ = (vᵢ − F·kᵢ)/‖kᵢ‖²。此式是 RealCrosstalkGeneral.batchClosed_exact_residual
    的**顺序对偶**：批量残差把 j ≠ i 的补丁响应写成显式串扰和，本式把两次顺序
    之差写成两项串扰；⟨k₂,k₁⟩ = 0 时两式同时退化为零（正交 ⟹ 顺序无关）。
  · `order_error_bound`（核心界）：顺序选择对输出的影响有界
    `|两种顺序之差| ≤ ‖x‖·(|v₁ − F·k₁|/‖k₁‖ + |v₂ − F·k₂|/‖k₂‖)`
    —— 经三角不等式 + 两次 Cauchy–Schwarz `|⟨k,x⟩| ≤ ‖k‖‖x‖`，右端为
    ‖x‖ 乘以两个编辑的位移尺度之和（因子 2 的"Σ|串扰|"形态，串扰尺度
    |vᵢ − F·kᵢ|/‖kᵢ‖ 随键相似性线性增长，与
    RealEditCrosstalk.edit2_cauchy_crosstalk_bound 一致）。

模型无关：任意 ℝ-内积空间 E；诚实假设：ROME 语义部分键非零（‖k‖² 可除），
自由增量部分无任何假设。注意 另有一条只作用于声明签名的结构假设：本文件
`namespace Lattice` 内的 variable 块（见 `editSeqComm` 之前的 variable 声明）
含有 `[CompleteSpace E]`，因此 ROME 语义一节（见 `romeEditSeq` 起）的若干定理
（`edit2_orthogonal_commutes` / `order_dependence_general` / `order_error_bound` 等）
在隐式参数中额外携带该假设（自由增量一节已用 `omit [CompleteSpace E] in` 显式免除）；
它只影响这些定理能对哪些空间实例化，不进入任何命题内容。
无 sorry/axiom/admit/native_decide。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 一、自由增量 rank-one 补丁：顺序严格无关 -/

omit [CompleteSpace E] in
/-- **编辑交换律（自由增量，无条件）**：两次 rank-one 补丁编辑可交换——
`rankOneEdit (rankOneEdit F Δ₁ k₁) Δ₂ k₂ = rankOneEdit (rankOneEdit F Δ₂ k₂) Δ₁ k₁`。
Δ₁、Δ₂ 为预设常数，被编辑函数只在 `F x + ⟨k,x⟩Δ` 的加法位置上出现，
故交换性 = 实数加法交换律（`ring`），**不需要键正交**。 -/
theorem editSeqComm (F : E → ℝ) (Δ₁ Δ₂ : ℝ) (k₁ k₂ : E) :
    rankOneEdit (rankOneEdit F Δ₁ k₁) Δ₂ k₂
      = rankOneEdit (rankOneEdit F Δ₂ k₂) Δ₁ k₁ := by
  funext x
  unfold rankOneEdit
  ring

/-- 自由增量编辑列表的补丁和：`l.foldr (fun p acc => ⟨p.2,x⟩·p.1 + acc) 0`。
（`p = (Δ, k)`，与 RealEditRollback.editSeq 的配对顺序一致。） -/
def freeSum (l : List (ℝ × E)) (x : E) : ℝ :=
  l.foldr (fun p acc => inner p.2 x * p.1 + acc) 0

omit [CompleteSpace E] in
lemma freeSum_nil (x : E) : freeSum [] x = 0 := rfl

omit [CompleteSpace E] in
lemma freeSum_cons (p : ℝ × E) (l : List (ℝ × E)) (x : E) :
    freeSum (p :: l) x = inner p.2 x * p.1 + freeSum l x := rfl

lemma freeSum_append (l₁ l₂ : List (ℝ × E)) (x : E) :
    freeSum (l₁ ++ l₂) x = freeSum l₁ x + freeSum l₂ x := by
  induction l₁ with
  | nil => simp [freeSum]
  | cons p l ih =>
      rw [List.cons_append, freeSum_cons, ih, freeSum_cons]
      ring

/-- **编辑列表闭式（自由增量）**：`editSeq l F x = F x + Σ_{(Δ,k)∈l} ⟨k,x⟩·Δ`。
自由增量补丁不依赖当前权重，故归纳步无需任何正交假设。 -/
theorem editSeq_closed_form (l : List (ℝ × E)) (F : E → ℝ) (x : E) :
    editSeq l F x = F x + freeSum l x := by
  induction l generalizing F with
  | nil => simp [editSeq, freeSum]
  | cons p l ih =>
      rw [show editSeq (p :: l) F = editSeq l (rankOneEdit F p.1 p.2) from rfl]
      rw [ih (rankOneEdit F p.1 p.2), freeSum_cons]
      unfold rankOneEdit
      ring

/-- **顺序无关（自由增量，核心）**：任意两个编辑列表的拼接交换顺序给出同一函数
——`editSeq (l₁ ++ l₂) F = editSeq (l₂ ++ l₁) F`。由闭式 + `freeSum_append` +
实数加法交换律，**无条件成立**（正交性在此语义下多余）。 -/
theorem order_invariance_free (l₁ l₂ : List (ℝ × E)) (F : E → ℝ) :
    editSeq (l₁ ++ l₂) F = editSeq (l₂ ++ l₁) F := by
  funext x
  rw [editSeq_closed_form (l₁ ++ l₂) F x, editSeq_closed_form (l₂ ++ l₁) F x,
    freeSum_append, freeSum_append]
  ring

/-! ## 二、ROME 语义（Δ = (v − F·k)/‖k‖² 依赖当前权重）：正交键下顺序无关 -/

/-- 顺序编辑列表（ROME 语义）：把 (k, v) 对依次作为
`ApplyEdit · k v : x ↦ · x + ⟨k,x⟩·(v − ·k)/‖k‖²` 施加。 -/
def romeEditSeq (l : List (E × ℝ)) (F : E → ℝ) : E → ℝ :=
  l.foldl (fun G p => ApplyEdit G p.1 p.2) F

omit [CompleteSpace E] in
lemma romeEditSeq_nil (F : E → ℝ) : romeEditSeq [] F = F := rfl

omit [CompleteSpace E] in
lemma romeEditSeq_cons (p : E × ℝ) (l : List (E × ℝ)) (F : E → ℝ) :
    romeEditSeq (p :: l) F = romeEditSeq l (ApplyEdit F p.1 p.2) := rfl

omit [CompleteSpace E] in
lemma romeEditSeq_append (l₁ l₂ : List (E × ℝ)) (F : E → ℝ) :
    romeEditSeq (l₁ ++ l₂) F = romeEditSeq l₂ (romeEditSeq l₁ F) := by
  unfold romeEditSeq
  rw [List.foldl_append]

omit [CompleteSpace E] in
/-- 键正交时编辑不改变 k 处的值：⟨k',k⟩ = 0 ⟹ `ApplyEdit G k' v' k = G k`。 -/
lemma applyEdit_at_orthogonal_key (G : E → ℝ) (k' k : E) (v' : ℝ)
    (h : inner k' k = (0 : ℝ)) : ApplyEdit G k' v' k = G k := by
  unfold ApplyEdit
  rw [h]
  ring

/-- **正交键编辑不扰动 k 处的值**：列表中所有编辑的键都与 k 正交 ⟹
`romeEditSeq l F k = F k`（对列表结构归纳，逐步用 `applyEdit_at_orthogonal_key`）。 -/
lemma romeEditSeq_orthogonal_fixed (l : List (E × ℝ)) (F : E → ℝ) (k : E)
    (h : ∀ p ∈ l, inner p.1 k = (0 : ℝ)) : romeEditSeq l F k = F k := by
  induction l generalizing F with
  | nil => rfl
  | cons p l ih =>
      have hp : inner p.1 k = (0 : ℝ) := h p (List.mem_cons_self p l)
      have htail : ∀ q ∈ l, inner q.1 k = (0 : ℝ) := fun q hq => h q (List.mem_cons_of_mem p hq)
      show romeEditSeq l (ApplyEdit F p.1 p.2) k = F k
      rw [ih (ApplyEdit F p.1 p.2) htail]
      exact applyEdit_at_orthogonal_key F p.1 k p.2 hp

omit [CompleteSpace E] in
/-- **两编辑正交可交换（核心）**：⟨k₁,k₂⟩ = ⟨k₂,k₁⟩ = 0 ⟹
`ApplyEdits2 F k₁ k₂ v₁ v₂ = ApplyEdits2 F k₂ k₁ v₂ v₁`（函数相等）。
正交性使第二编辑在 k₁ 处的增量基准 `ApplyEdit F k₁ v₁ k₂ = F k₂` 不含第一编辑，
两序都退化为 `F + (Δ₁⊗k₁) + (Δ₂⊗k₂)`。 -/
theorem edit2_orthogonal_commutes (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (h₁₂ : inner k₁ k₂ = (0 : ℝ)) (h₂₁ : inner k₂ k₁ = (0 : ℝ)) :
    ApplyEdits2 F k₁ k₂ v₁ v₂ = ApplyEdits2 F k₂ k₁ v₂ v₁ := by
  funext x
  simp only [ApplyEdits2, ApplyEdit]
  rw [h₁₂, h₂₁]
  ring

/-- 编辑 e 的**自写 + 正交后缀不动**：`romeEditSeq (e :: l) G e.1 = e.2`，
只要 e.1 ≠ 0 且 l 中编辑的键都与 e.1 正交（e 精确写入自身键，后继正交键编辑不动它）。 -/
lemma romeEditSeq_cons_at_own_key (l : List (E × ℝ)) (e : E × ℝ) (G : E → ℝ)
    (hk : e.1 ≠ 0) (h : ∀ p ∈ l, inner p.1 e.1 = (0 : ℝ)) :
    romeEditSeq (e :: l) G e.1 = e.2 := by
  show romeEditSeq l (ApplyEdit G e.1 e.2) e.1 = e.2
  rw [romeEditSeq_orthogonal_fixed l (ApplyEdit G e.1 e.2) e.1 h]
  exact applyEdit_writes_fact G e.1 e.2 hk

/-- **顺序无关（ROME 语义，核心）**：编辑 e 在列表中的位置不影响 e 自己键处的
最终值——`romeEditSeq (l₁ ++ e :: l₂) F e.1 = e.2`，只要 e.1 ≠ 0 且后缀 l₂
的编辑键与 e.1 正交（前缀 l₁ 任意）。这是"正交键下编辑顺序不影响最终权重"
在 ROME 派生增量语义下的精确形式：写入是精确的，正交键编辑不动它。 -/
theorem order_invariance_orthogonal (l₁ l₂ : List (E × ℝ)) (e : E × ℝ) (F : E → ℝ)
    (hk : e.1 ≠ 0) (h₂ : ∀ p ∈ l₂, inner p.1 e.1 = (0 : ℝ)) :
    romeEditSeq (l₁ ++ e :: l₂) F e.1 = e.2 := by
  rw [romeEditSeq_append]
  exact romeEditSeq_cons_at_own_key l₂ e (romeEditSeq l₁ F) hk h₂

/-! ## 三、一般键：顺序相关的显式刻画（衔接 RealCrosstalkGeneral.batchClosed_exact_residual） -/

/-- **顺序相关的精确刻画（核心公式）**：一般键下两次编辑的两种顺序之差**恰好**
是两个串扰项，
`ApplyEdits2 F k₁ k₂ v₁ v₂ x − ApplyEdits2 F k₂ k₁ v₂ v₁ x
  = ⟨k₁,x⟩·(⟨k₂,k₁⟩·d₂)/‖k₁‖² − ⟨k₂,x⟩·(⟨k₁,k₂⟩·d₁)/‖k₂‖²`，
dᵢ = (vᵢ − F·kᵢ)/‖kᵢ‖²。正交键（⟨k₂,k₁⟩=0）时两项同时消失，回到
`edit2_orthogonal_commutes`；批量语义的对偶见
`RealCrosstalkGeneral.batchClosed_exact_residual`（把 j ≠ i 的响应写成串扰和）。 -/
theorem order_dependence_general (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (x : E) :
    ApplyEdits2 F k₁ k₂ v₁ v₂ x - ApplyEdits2 F k₂ k₁ v₂ v₁ x
      = inner k₁ x * (inner k₂ k₁ * ((v₂ - F k₂) / ‖k₂‖ ^ 2)) / ‖k₁‖ ^ 2
        - inner k₂ x * (inner k₁ k₂ * ((v₁ - F k₁) / ‖k₁‖ ^ 2)) / ‖k₂‖ ^ 2 := by
  simp only [ApplyEdits2, ApplyEdit]
  have h₁ : ‖k₁‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₁ hk₁
  have h₂ : ‖k₂‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₂ hk₂
  field_simp [h₁, h₂]
  ring

omit [CompleteSpace E] in
/-- Cauchy–Schwarz 逐项界：单个串扰项
`|⟨k,x⟩·(⟨k',k⟩·C)/‖k‖²| ≤ ‖x‖·‖k'‖·|C|`（两次 Cauchy–Schwarz
`|⟨k,x⟩| ≤ ‖k‖‖x‖`、`|⟨k',k⟩| ≤ ‖k'‖‖k‖` 后约去 ‖k‖²，需 k ≠ 0）。 -/
lemma abs_crosstalk_term_le (k k' : E) (C : ℝ) (hk : k ≠ 0) (x : E) :
    |inner k x * (inner k' k * C) / ‖k‖ ^ 2| ≤ ‖x‖ * ‖k'‖ * |C| := by
  have hkpos : 0 < ‖k‖ ^ 2 := pow_pos (norm_pos_iff.mpr hk) 2
  have hkne : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  have h1 : |inner k x| ≤ ‖k‖ * ‖x‖ := abs_real_inner_le_norm k x
  have h2 : |inner k' k| ≤ ‖k'‖ * ‖k‖ := abs_real_inner_le_norm k' k
  rw [abs_div, abs_of_pos hkpos]
  -- 分子：|⟨k,x⟩·(⟨k',k⟩·C)| ≤ (‖k‖‖x‖)(‖k'‖‖k‖)|C|
  have hnum : |inner k x * (inner k' k * C)| ≤ (‖k‖ * ‖x‖) * (‖k'‖ * ‖k‖) * |C| := by
    rw [abs_mul, abs_mul]
    have hab : |inner k x| * |inner k' k| ≤ (‖k‖ * ‖x‖) * (‖k'‖ * ‖k‖) :=
      mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hfin : |inner k x| * |inner k' k| * |C| ≤ (‖k‖ * ‖x‖) * (‖k'‖ * ‖k‖) * |C| :=
      mul_le_mul hab le_rfl (abs_nonneg _)
        (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    calc
      |inner k x| * (|inner k' k| * |C|)
          = |inner k x| * |inner k' k| * |C| := by ring
      _ ≤ (‖k‖ * ‖x‖) * (‖k'‖ * ‖k‖) * |C| := hfin
  calc
    |inner k x * (inner k' k * C)| / ‖k‖ ^ 2
        ≤ (‖k‖ * ‖x‖) * (‖k'‖ * ‖k‖) * |C| / ‖k‖ ^ 2 :=
          div_le_div_of_nonneg_right hnum (le_of_lt hkpos)
    _ = ‖x‖ * ‖k'‖ * |C| := by
          field_simp [hkne]
          ring

/-- **顺序误差界（核心界）**：两次编辑的两种顺序对任意 x 的输出差有界，
`|差| ≤ ‖x‖·(|v₁ − F·k₁|/‖k₁‖ + |v₂ − F·k₂|/‖k₂‖)`
—— 右端是 ‖x‖ 乘以两个编辑的位移尺度（"串扰尺度"）之和，
即顺序选择的影响 ≤ (因子 2)·Σ|串扰|；精确差由 `order_dependence_general` 给出，
用三角不等式 + 两次 Cauchy–Schwarz 放大。 -/
theorem order_error_bound (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (x : E) :
    |ApplyEdits2 F k₁ k₂ v₁ v₂ x - ApplyEdits2 F k₂ k₁ v₂ v₁ x|
      ≤ ‖x‖ * (|v₁ - F k₁| / ‖k₁‖ + |v₂ - F k₂| / ‖k₂‖) := by
  rw [order_dependence_general F k₁ k₂ v₁ v₂ hk₁ hk₂ x]
  set d₁ := (v₁ - F k₁) / ‖k₁‖ ^ 2 with hd₁
  set d₂ := (v₂ - F k₂) / ‖k₂‖ ^ 2 with hd₂
  have hA : |inner k₁ x * (inner k₂ k₁ * d₂) / ‖k₁‖ ^ 2| ≤ ‖x‖ * ‖k₂‖ * |d₂| :=
    abs_crosstalk_term_le k₁ k₂ d₂ hk₁ x
  have hB : |inner k₂ x * (inner k₁ k₂ * d₁) / ‖k₂‖ ^ 2| ≤ ‖x‖ * ‖k₁‖ * |d₁| :=
    abs_crosstalk_term_le k₂ k₁ d₁ hk₂ x
  have hd₂' : ‖x‖ * ‖k₂‖ * |d₂| = ‖x‖ * (|v₂ - F k₂| / ‖k₂‖) := by
    rw [hd₂]
    have hk₂ne : ‖k₂‖ ≠ 0 := norm_ne_zero_iff.mpr hk₂
    rw [abs_div, abs_of_nonneg (sq_nonneg (‖k₂‖ : ℝ))]
    field_simp [hk₂ne]
    ring
  have hd₁' : ‖x‖ * ‖k₁‖ * |d₁| = ‖x‖ * (|v₁ - F k₁| / ‖k₁‖) := by
    rw [hd₁]
    have hk₁ne : ‖k₁‖ ≠ 0 := norm_ne_zero_iff.mpr hk₁
    rw [abs_div, abs_of_nonneg (sq_nonneg (‖k₁‖ : ℝ))]
    field_simp [hk₁ne]
    ring
  calc
    |inner k₁ x * (inner k₂ k₁ * d₂) / ‖k₁‖ ^ 2
        - inner k₂ x * (inner k₁ k₂ * d₁) / ‖k₂‖ ^ 2|
        ≤ |inner k₁ x * (inner k₂ k₁ * d₂) / ‖k₁‖ ^ 2|
            + |inner k₂ x * (inner k₁ k₂ * d₁) / ‖k₂‖ ^ 2| := by
          have h := abs_add (inner k₁ x * (inner k₂ k₁ * d₂) / ‖k₁‖ ^ 2)
            (-(inner k₂ x * (inner k₁ k₂ * d₁) / ‖k₂‖ ^ 2))
          simpa [sub_eq_add_neg, abs_neg] using h
    _ ≤ ‖x‖ * ‖k₂‖ * |d₂| + ‖x‖ * ‖k₁‖ * |d₁| := add_le_add hA hB
    _ = ‖x‖ * (|v₂ - F k₂| / ‖k₂‖) + ‖x‖ * (|v₁ - F k₁| / ‖k₁‖) := by
          rw [hd₂', hd₁']
    _ = ‖x‖ * (|v₁ - F k₁| / ‖k₁‖ + |v₂ - F k₂| / ‖k₂‖) := by ring

/-! ## 注：三种语义的顺序性质对照
  自由增量补丁（RealEditRollback.rankOneEdit，Δ 预设）：顺序**严格无关**
  （editSeqComm / order_invariance_free，无需正交）；
  ROME 派生增量（RealEditCrosstalk.ApplyEdit，Δ = (v − F·k)/‖k‖²）：
  正交键 ⟹ 顺序无关（edit2_orthogonal_commutes / order_invariance_orthogonal），
  一般键 ⟹ 顺序差 = 两项显式和（order_dependence_general），
  并有 ‖x‖·Σ 位移尺度的界（order_error_bound）。
  批量语义的串扰闭式见 RealCrosstalkGeneral.batchClosed_exact_residual。 -/

end Lattice
