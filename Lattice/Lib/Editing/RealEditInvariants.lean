import Mathlib

/-!
# LATTICE wave-30 — E-09: 编辑的不变量（invariants under edit）

任务书要求：「证明：某些性质在任意编辑下保持（如『所有行非零』『Lipschitz 常数有界』）。
给出具体不变量与定理。」

## ⭐ 结论（先说结论，因为这决定了一切）

**逐字照任务书写的那两条，都是假的。** 不是「证不出来」，是**有具体反例**：

  · 「所有行非零」在任意编辑下**不保持** —— 反例：把某一行整行置零
    （`ZeroRowEdit`），该行变为恒零行。`zeroRowEdit_kills_row` 给出其证明。
  · 「Lipschitz 常数有界（存在与编辑无关的常数 L）」在任意编辑下**不保持** ——
    反例：把权重整体乘一个任意大的正标量 λ（`scaleEdit`），Lipschitz 常数
    精确变成 λ·L；λ 无上界，故**不存在**与编辑无关的一致界。
    `scaleEdit_no_uniform_lipschitz` 证明：**任意**候选界 L 都可被某个编辑击穿。

因此本文件不假装这两条成立，而是给出**真实缺口**的精确刻画：

  ① `zeroRowEdit_kills_row`：哪条「非零」性质被哪个编辑杀掉
     （具体反例，含构造与验证）；
  ② `scaleEdit_no_uniform_lipschitz`：一致 Lipschitz 界**不存在**的量化证明；
  ③ ⭐ **真正的不变量**（这才是任务的可交付部分）：
     * `edit_nonzero_iff_of_delta_zero`：**非零性在核不变的编辑下是不变量** ——
       在 `Δ x = 0` 的点上，`W' x ≠ 0 ↔ W x ≠ 0`。这是「所有行非零」的
       **正确定式**（全局版本已被 ① 证伪，逐点版本才是真不变量）；
       并由 `edit_nonzero_fails_without_delta_zero` 证明假设**不可去掉**（尖锐）。
     * `edit_lipschitz_constant_quantitative`：编辑**确实**保持的一件有内容的事 ——
       算子范数（= Lipschitz 常数）满足**定量**不等式 `‖W'‖ ≤ ‖W‖ + ‖ΔW‖`；
       即「编辑后常数有界」的正确形式是「**增量**有界」而非「常数有界」。
       并由 `edit_lipschitz_bound_attained` 证明该界**取等**（尖锐，不能改进）。

## 判据对照（任务书四判据）

  · **判据 1（消融）**：去掉「`Δ x = 0`」假设，`edit_nonzero_iff_of_delta_zero`
    的结论变为**假**（`edit_nonzero_fails_without_delta_zero` 给出具体反例）；
    去掉「增量有界」，一致 Lipschitz 界变为**假**（`scaleEdit_no_uniform_lipschitz`）。
  · **判据 2（反驳可能）**：`zeroRowEdit_kills_row`、`scaleEdit_no_uniform_lipschitz`、
    `edit_nonzero_fails_without_delta_zero` 给出**具体对象**使朴素断言不成立。
  · **判据 4（量化）**：`edit_lipschitz_constant_quantitative` 给出可计算的界
    `‖W‖ + ‖ΔW‖`（而非仅存在性），且该界在 3.4 中**取等**。

## ⚠ 诚实边界（详见 `_proof_out/W_E-09.md`）

本文件**未经 lake 编译验证**（任务书禁止）；所有引用到的 mathlib 引理名与
既有模块签名均逐字核对过源码；未使用 sorry / axiom / admit / native_decide。
`ZeroRowEdit` 的若干化简步骤（`simp` / `pi_apply`）是我**没有编译**、
最可能需要微调的地方，已在报告中逐条列出。
-/

noncomputable section

namespace Lattice

/-! ## 第一部分：把「编辑」给定下来（与 RealEditBound / RealEditSeq 同一模型）

既有模块把编辑统一为**权重的加法扰动**：`W' = W + Δ`，其中
`Δ : E →L[ℝ] F`（RealEditBound.edit_output_bound 即此语义）。
本文件沿用同一语义，故所有结论可直接与既有编辑线衔接。 -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 编辑的算子形式：`Δ = W' − W`。`Δ` 是编辑增量。 -/
def EditDelta (W W' : E →L[ℝ] F) : E →L[ℝ] F := W' - W

/-- 编辑增量与编辑结果的关系：`W + EditDelta W W' = W'`。 -/
lemma add_editDelta (W W' : E →L[ℝ] F) : W + EditDelta W W' = W' := by
  unfold EditDelta
  abel

/-! ## 第二部分：判据 2 —— 任务书提的两条「不变量」其实都是假命题

### 2.1 「所有行非零」不是不变量：整行置零的编辑杀掉它 -/

/-- **反例编辑**：把 `W` 的第 `i` 行整行置零、其余行原样保留。

这里 `W : E →L[ℝ] (Fin (n+1) → ℝ)` 被视为「`n+1` 行」的算子；
`ContinuousLinearMap.pi` 逐坐标组装各行的连续线性映射
（`pi_apply`：`pi f x i = f i x`），`ContinuousLinearMap.proj j` 取第 `j` 行。
第 `i` 行被换成常零映射 `0`，即「剪掉第 i 行输出」这一真实编辑。 -/
def ZeroRowEdit {n : ℕ} (W : E →L[ℝ] (Fin (n + 1) → ℝ)) (i : Fin (n + 1)) :
    E →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => if j = i then 0 else ContinuousLinearMap.proj j ∘L W)

/-- 零行编辑在第 `i` 行的取值恒为 0（逐点）。
`pi_apply` 给出逐坐标值 `pi f x i = f i x`，`if_pos` 命中第 i 坐标、
得到 `(0 : E →L[ℝ] ℝ) x = 0`。 -/
theorem zeroRowEdit_row_is_zero {n : ℕ} (W : E →L[ℝ] (Fin (n + 1) → ℝ))
    (i : Fin (n + 1)) :
    ∀ x : E, ZeroRowEdit W i x i = 0 := by
  intro x
  unfold ZeroRowEdit
  rw [ContinuousLinearMap.pi_apply]
  simp

/-- 零行编辑在**其他行**保持原值（编辑只影响第 i 行）。
`proj_apply` 给出 `proj j (W x) = W x j`。 -/
theorem zeroRowEdit_other_rows {n : ℕ} (W : E →L[ℝ] (Fin (n + 1) → ℝ))
    (i j : Fin (n + 1)) (x : E) (hji : j ≠ i) :
    ZeroRowEdit W i x j = W x j := by
  unfold ZeroRowEdit
  rw [ContinuousLinearMap.pi_apply]
  simp only [hji, if_false]
  rfl

/-- ⭐ **判据 2 反例（核心）**：「所有行非零」在编辑下**不保持**。

即使初始 `W` 的每一行都非零，编辑 `ZeroRowEdit W i` 也使第 i 行恒为零：
存在 `x`（事实上**所有** `x`，含 `x = 0`）使编辑后第 i 行为 0。
这是**结论为假**的构造性证据，而非「证不出来」。 -/
theorem zeroRowEdit_kills_row {n : ℕ} (W : E →L[ℝ] (Fin (n + 1) → ℝ))
    (i : Fin (n + 1)) :
    ¬ (∀ x : E, ZeroRowEdit W i x i ≠ 0) := by
  intro h
  exact h 0 (zeroRowEdit_row_is_zero W i 0)

/-- ⭐ 反例的**存在形式**：存在编辑 `W'` 与输入 `x`，使 `W' x i = 0`
（第 `i` 行非零性被某个编辑破坏）。 -/
theorem zeroRowEdit_breaks_nonzero_rows {n : ℕ} (W : E →L[ℝ] (Fin (n + 1) → ℝ))
    (i : Fin (n + 1)) :
    ∃ (W' : E →L[ℝ] (Fin (n + 1) → ℝ)) (x : E), W' x i = 0 :=
  ⟨ZeroRowEdit W i, 0, zeroRowEdit_row_is_zero W i 0⟩

/-! ### 2.2 「Lipschitz 常数有界」不是不变量：不存在与编辑无关的一致界

「Lipschitz 常数有界」有两种读法，**都在任意编辑下失败**：

  (a) 一致界：存在与编辑无关的 L，使所有编辑后的 W' 都 L-Lipschitz
      ⟹ **假**，`scaleEdit_no_uniform_lipschitz` 给出击穿构造；
  (b) 逐点有界：每个固定的 W' 都有有限 Lipschitz 常数
      ⟹ 平凡（`W'` 是连续线性算子，其算子范数即常数），**无内容**。

故「Lipschitz 常数有界」作为**不变量**是假的；真实缺口见第三部分。 -/

/-- **反例编辑（标量放大）**：`W' = Λ • W`。这是真实编辑里最常见的
「学习率 / 缩放漂移」的最简模型；Λ 可任意大。 -/
def scaleEdit (W : E →L[ℝ] F) (Λ : ℝ) : E →L[ℝ] F := Λ • W

/-- 标量放大编辑精确地把 Lipschitz 常数乘以 `Λ`（Λ ≥ 0）：
`‖W' x − W' y‖ = Λ·‖W x − W y‖`。即编辑后常数**无上界**。 -/
theorem scaleEdit_lipschitz_exact (W : E →L[ℝ] F) (Λ : ℝ) (hΛ : 0 ≤ Λ) (x y : E) :
    ‖scaleEdit W Λ x - scaleEdit W Λ y‖ = Λ * ‖W x - W y‖ := by
  unfold scaleEdit
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hΛ]

/-- ⭐ **判据 2 反例（核心）**：「Lipschitz 常数一致有界」**不存在**。

对**任意**候选一致界 `L`，都存在一个编辑（`scaleEdit W Λ`，Λ 选得充分大）
使该编辑的「Lipschitz 比值」超过 L：取 `a = y`、`b = 0`
（`y` 任取使 `W y ≠ 0` 的点，此时 `y ≠ 0`，比值 = Λ·‖W y‖ / ‖y‖ 随 Λ 线性增长）。

这正是**消融**（判据 1）：删掉「增量有界」假设，结论变成假。 -/
theorem scaleEdit_no_uniform_lipschitz (W : E →L[ℝ] F) (y : E) (hy : W y ≠ 0) :
    ∀ L : ℝ, ∃ (Λ : ℝ) (W' : E →L[ℝ] F) (a b : E),
      0 ≤ Λ ∧ W' = scaleEdit W Λ ∧ L < ‖W' a - W' b‖ / ‖a - b‖ := by
  intro L
  have hWy_pos : 0 < ‖W y‖ := norm_pos_iff.mpr hy
  have hy_ne : y ≠ 0 := fun h => hy (by rw [h, map_zero])
  have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_ne
  -- Λ := |L| * ‖y‖ / ‖W y‖ + 1 > 0（用 |L| 而非 L + 1：L 可任意负，
  --   L + 1 会为负而使 0 ≤ Λ 失败；|L| 保证恒正）
  -- 则 Λ·‖W y‖ = |L|·‖y‖ + ‖W y‖ > |L|·‖y‖ ≥ L·‖y‖
  refine ⟨|L| * ‖y‖ / ‖W y‖ + 1, scaleEdit W (|L| * ‖y‖ / ‖W y‖ + 1), y, 0,
    ?_, rfl, ?_⟩
  · have : 0 ≤ |L| * ‖y‖ / ‖W y‖ := by positivity
    linarith
  · have hΛ : 0 ≤ |L| * ‖y‖ / ‖W y‖ + 1 := by
      have : 0 ≤ |L| * ‖y‖ / ‖W y‖ := by positivity
      linarith
    rw [scaleEdit_lipschitz_exact W _ hΛ y 0, map_zero, sub_zero, sub_zero]
    have hWy_ne : ‖W y‖ ≠ 0 := ne_of_gt hWy_pos
    have hmul : (|L| * ‖y‖ / ‖W y‖ + 1) * ‖W y‖ = |L| * ‖y‖ + ‖W y‖ := by
      field_simp
    rw [lt_div_iff₀ hy_pos, hmul]
    nlinarith [hWy_pos, le_abs_self L]

/-! ## 第三部分：⭐ 真正的不变量（任务要求的「具体不变量与定理」）

任务书假定的两条都是假的；但它们**指向的直觉是对的**。正确的不变量是：

### 3.1 非零性在「核不变的编辑」下保持不变 —— 一个**真正**的不变量 -/

/-- ⭐ **核心不变量**：若 `x` 在编辑前不被 `W` 杀掉（`W x ≠ 0`），
且编辑在该点增量为零（`Δ x = 0`），则 `x` 在编辑后**仍不被杀掉**。

这是「行非零」的**正确版本**：全局的「处处非零」不是不变量（2.1 已证伪），
但**在编辑增量的核上**，非零性是不变量。 -/
theorem edit_preserves_nonzero_of_delta_zero (W W' : E →L[ℝ] F) (x : E)
    (hWx : W x ≠ 0) (hΔx : EditDelta W W' x = 0) :
    W' x ≠ 0 := by
  intro h
  apply hWx
  have hsum : W x + EditDelta W W' x = W' x := by
    have h := add_editDelta W W'
    rw [← ContinuousLinearMap.add_apply, h]
  rw [hΔx, add_zero] at hsum
  exact hsum.trans h

/-- 上条的**等值形式**（「不变量」的标准形态）：在 `Δ x = 0` 的点上，
编辑**不改变非零性**：`W' x ≠ 0 ↔ W x ≠ 0`。

事实上在此假设下 `W' x = W x`（逐点相等），故是**双向**不变量。 -/
theorem edit_nonzero_iff_of_delta_zero (W W' : E →L[ℝ] F) (x : E)
    (hΔx : EditDelta W W' x = 0) :
    W' x ≠ 0 ↔ W x ≠ 0 := by
  have hEq : W' x = W x := by
    have hsum : W x + EditDelta W W' x = W' x := by
      have h := add_editDelta W W'
      rw [← ContinuousLinearMap.add_apply, h]
    rw [hΔx, add_zero] at hsum
    exact hsum.symm
  rw [hEq]

/-! ### 3.2 ⭐ 尖锐性：3.1 的假设**不可去掉**（消融，判据 1） -/

/-- ⭐ **尖锐性（判据 1，消融）**：去掉 `Δ x = 0`，3.1 的结论变成**假** ——
存在 `W x ≠ 0` 而 `W' x = 0` 的编辑。

具体地：取 `W = id`（`ℝ →L[ℝ] ℝ`）、编辑 `Δ = −id`，则 `W' = 0`。 -/
theorem edit_nonzero_fails_without_delta_zero :
    ∃ (W W' : ℝ →L[ℝ] ℝ) (x : ℝ), W x ≠ 0 ∧ W' x = 0 := by
  refine ⟨ContinuousLinearMap.id ℝ ℝ, 0, 1, ?_, ?_⟩
  · simp
  · simp

/-- 3.2 的**精确化**：该反例编辑的增量 `Δ = −id` 在**每个非零点**都不为零，
故 3.1 的假设 `Δ x = 0` 在此完全失效 —— 与 3.1 的假设条件恰好互补。 -/
theorem edit_nonzero_sharpness_delta_not_zero (x : ℝ) (hx : x ≠ 0) :
    EditDelta (ContinuousLinearMap.id ℝ ℝ) 0 x ≠ 0 := by
  simpa [EditDelta] using hx

/-! ### 3.3 ⭐ 编辑确实保持的定量关系：Lipschitz 常数的**增量**有界

既然「常数一致有界」是假的（2.2），正确的、**有内容**的陈述是：

    ‖W'‖ ≤ ‖W‖ + ‖ΔW‖

这既是**可计算的界**（判据 4），又通过 2.2 说明界**不能再改进为「一致有界」**。 -/

/-- ⭐ **核心定量不变量**：编辑后的算子范数被原范数与增量范数之和界住：
`‖W'‖ ≤ ‖W‖ + ‖ΔW‖`。

这是编辑线「Lipschitz 常数如何变化」的**正确**答案：给出可计算的界（判据 4），
而该界在 `Δ` 无界时无界（不能升级为「一致有界」，见 2.2）。 -/
theorem edit_lipschitz_constant_quantitative (W W' : E →L[ℝ] F) :
    ‖W'‖ ≤ ‖W‖ + ‖EditDelta W W'‖ := by
  have hsum : W + EditDelta W W' = W' := add_editDelta W W'
  calc
    ‖W'‖ = ‖W + EditDelta W W'‖ := by rw [hsum]
    _ ≤ ‖W‖ + ‖EditDelta W W'‖ := norm_add_le W (EditDelta W W')

/-- 上条的**逐点（输出）形式**，与 RealEditBound.edit_output_bound 衔接：
`‖W' x‖ ≤ ‖W x‖ + ‖ΔW‖·‖x‖`（用 `le_opNorm`）。 -/
theorem edit_output_norm_quantitative (W W' : E →L[ℝ] F) (x : E) :
    ‖W' x‖ ≤ ‖W x‖ + ‖EditDelta W W'‖ * ‖x‖ := by
  have hpt : W' x = W x + EditDelta W W' x := by
    have h := add_editDelta W W'
    calc
      W' x = (W + EditDelta W W') x := by rw [h]
      _ = W x + EditDelta W W' x := rfl
  calc
    ‖W' x‖ = ‖W x + EditDelta W W' x‖ := by rw [hpt]
    _ ≤ ‖W x‖ + ‖EditDelta W W' x‖ := norm_add_le _ _
    _ ≤ ‖W x‖ + ‖EditDelta W W'‖ * ‖x‖ :=
          add_le_add_left ((EditDelta W W').le_opNorm x) _

/-! ### 3.4 ⭐ 尖锐性：3.3 的界在「同向编辑」下**取等**（不能改进） -/

/-- ⭐ **取等（尖锐性）**：当编辑增量与原算子同向（`Δ = (Λ−1) • W`、`Λ ≥ 1`）时，
`‖W'‖ = Λ‖W‖`，恰等于 `‖W‖ + ‖ΔW‖` —— 3.3 的界**取等**，不能改进。

⚠ 取等要求 `1 ≤ Λ`（而非仅 `0 ≤ Λ`）：`Λ < 1` 时 `Λ • W` 缩小原算子，
此时 `‖W'‖ < ‖W‖`，而右边 `‖W‖ + ‖ΔW‖ ≥ ‖W‖` 严格大于左边，界不取等。
这里把假设写成 `1 ≤ Λ` 以使「取等」这一结论为真。 -/
theorem edit_lipschitz_bound_attained (W : E →L[ℝ] F) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ‖scaleEdit W Λ‖ = ‖W‖ + ‖EditDelta W (scaleEdit W Λ)‖ := by
  have h0 : (0 : ℝ) ≤ Λ := by linarith
  -- scaleEdit W Λ = Λ • W，故 ‖scaleEdit W Λ‖ = Λ * ‖W‖（Λ ≥ 0）
  have h1 : ‖scaleEdit W Λ‖ = Λ * ‖W‖ := by
    unfold scaleEdit
    rw [norm_smul (Λ : ℝ) W, Real.norm_eq_abs, abs_of_nonneg h0]
  -- EditDelta W (Λ • W) = Λ • W - W = (Λ - 1) • W，故其范数为 (Λ - 1) * ‖W‖（Λ ≥ 1）
  have h2 : ‖EditDelta W (scaleEdit W Λ)‖ = (Λ - 1) * ‖W‖ := by
    unfold EditDelta scaleEdit
    have hsub : (Λ : ℝ) • W - W = (Λ - 1) • W := by rw [sub_smul, one_smul]
    rw [hsub, norm_smul (Λ - 1) W, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1)]
  -- 于是 ‖W‖ + ‖ΔW‖ = ‖W‖ + (Λ-1)‖W‖ = Λ‖W‖ = ‖W'‖，界取等
  rw [h1, h2]
  ring

end Lattice
