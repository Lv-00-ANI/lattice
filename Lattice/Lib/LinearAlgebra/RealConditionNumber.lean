import Mathlib

/-!
# LATTICE: 条件数与解扰动 —— κ(A) = ‖A‖·‖A⁻¹‖ / 右端扰动 / 矩阵扰动 / Neumann 型界

数值线性代数线的基础文件：**条件数**与 **A x = b 的解在扰动下的误差**。

以连续线性等价 `A : E ≃L[ℝ] F` 为「可逆矩阵」的抽象模型（Fin 矩阵可经
RealMatrixNorm 的 `matCLME` 桥嵌入此模型；此处不引入任何矩阵实现细节）：

  1. `condNumber A = ‖A‖·‖A⁻¹‖`（`A⁻¹` 即 `A.symm` 的算子范数）；
  2. `condition_number_ge_one`：κ(A) ≥ 1（恒等 = A⁻¹∘A 的范数不超过乘积）；
  3. `solution_perturbation_bound`：A x = b、A x' = b' ⟹
     ‖x − x'‖ ≤ ‖A⁻¹‖·‖b − b'‖（解的扰动只被右端扰动放大 ‖A⁻¹‖ 倍）；
  4. `relative_perturbation_bound`（乘法形式）：
     ‖x − x'‖·‖b‖ ≤ κ(A)·‖b − b'‖·‖x‖，等价地
     ‖x − x'‖/‖x‖ ≤ κ(A)·(‖b − b'‖/‖b‖)（`relative_perturbation_bound_div`）；
  5. `matrix_perturbation_bound`：A x = b、B x' = b 时
     ‖x − x'‖ ≤ ‖A⁻¹‖·‖B − A‖·‖x'‖（**无需** Neumann 级数：由
     A(x − x') = (B − A)x' 直接得到）；
  6. `matrix_perturbation_bound_contraction`：在收缩假设
     ‖B − A‖·‖A⁻¹‖ < 1 下，Neumann 型定量界
     ‖x − x'‖·(1 − ‖A⁻¹‖‖B−A‖) ≤ ‖A⁻¹‖²·‖B − A‖·‖b‖
     （先证 ‖x'‖·(1 − ‖A⁻¹‖‖B−A‖) ≤ ‖A⁻¹‖·‖b‖，即 Neumann 级数的
     有限截断形式）；
  7. `condNumber_comp_le`：κ(A∘B) ≤ κ(A)·κ(B)（多步运算条件数的复合，
     RealMatrixStability 的 `condition_number_perturbation_product` 由此得出）。

诚实假设与降级：
  · A 必须是**连续线性等价**（即抽象意义下的可逆算子，`A.symm` 存在）；
    一般奇异矩阵的条件数需要伪逆（见 RealPseudoInverse）；
  · 未形式化「κ(A) ≥ 1 严格取等 ⟺ A 是相似变换」之类的精细刻画；
  · Neumann 级数**收敛性**（无穷级数的构造）未形式化：这里给出的是
    「解的先验收缩假设 + 有限截断估计」下的定量扰动界，而非级数收敛定理。

模型无关：任意 ℝ-赋范空间之间的连续线性等价。无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ## 条件数定义与基本性质 -/

/-- 条件数：κ(A) = ‖A‖·‖A⁻¹‖（A⁻¹ 取 `A.symm` 的算子范数）。 -/
def condNumber (A : E ≃L[ℝ] F) : ℝ := ‖(A : E →L[ℝ] F)‖ * ‖(A.symm : F →L[ℝ] E)‖

lemma condNumber_nonneg (A : E ≃L[ℝ] F) : 0 ≤ condNumber A :=
  mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- A⁻¹ ∘ A = id（作为连续线性映射）。 -/
lemma symm_comp_self_eq_id (A : E ≃L[ℝ] F) :
    (A.symm : F →L[ℝ] E).comp (A : E →L[ℝ] F) = ContinuousLinearMap.id ℝ E := by
  ext x
  simp

/-- 定理一：条件数至少为 1（κ(A) ≥ 1）。 -/
theorem condition_number_ge_one [Nontrivial E] (A : E ≃L[ℝ] F) : 1 ≤ condNumber A := by
  calc
    (1 : ℝ) = ‖ContinuousLinearMap.id ℝ E‖ := (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := E)).symm
    _ = ‖(A.symm : F →L[ℝ] E).comp (A : E →L[ℝ] F)‖ := by rw [symm_comp_self_eq_id]
    _ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖(A : E →L[ℝ] F)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ = condNumber A := by rw [condNumber]; ring

/-! ## 定理二：右端扰动下的解扰动界 -/

/-- 定理二：A x = b、A x' = b' ⟹ ‖x − x'‖ ≤ ‖A⁻¹‖·‖b − b'‖。 -/
theorem solution_perturbation_bound (A : E ≃L[ℝ] F) (b b' : F) (x x' : E)
    (hx : A x = b) (hx' : A x' = b') :
    ‖x - x'‖ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖b - b'‖ := by
  have hsub : b - b' = A (x - x') := by
    rw [← hx, ← hx', map_sub]
  have hxsub : x - x' = A.symm (b - b') := by
    rw [hsub, ContinuousLinearEquiv.symm_apply_apply]
  rw [hxsub]
  exact (A.symm : F →L[ℝ] E).le_opNorm (b - b')

/-- 定理三（乘法形式）：‖x − x'‖·‖b‖ ≤ κ(A)·‖b − b'‖·‖x‖。
（注意 `b = A x` 时 `‖b‖ ≤ ‖A‖‖x‖`，两式相乘即得。） -/
theorem relative_perturbation_bound (A : E ≃L[ℝ] F) (b b' : F) (x x' : E)
    (hx : A x = b) (hx' : A x' = b') :
    ‖x - x'‖ * ‖b‖ ≤ condNumber A * ‖b - b'‖ * ‖x‖ := by
  have h1 := solution_perturbation_bound A b b' x x' hx hx'
  have hb : ‖b‖ ≤ ‖(A : E →L[ℝ] F)‖ * ‖x‖ := by
    rw [← hx]
    exact (A : E →L[ℝ] F).le_opNorm x
  have h2 : ‖x - x'‖ * ‖b‖ ≤
      (‖(A.symm : F →L[ℝ] E)‖ * ‖b - b'‖) * (‖(A : E →L[ℝ] F)‖ * ‖x‖) :=
    mul_le_mul h1 hb (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    ‖x - x'‖ * ‖b‖ ≤ (‖(A.symm : F →L[ℝ] E)‖ * ‖b - b'‖) * (‖(A : E →L[ℝ] F)‖ * ‖x‖) := h2
    _ = condNumber A * ‖b - b'‖ * ‖x‖ := by rw [condNumber]; ring

/-- 定理三（商形式）：b ≠ 0 时 ‖x − x'‖/‖x‖ ≤ κ(A)·(‖b − b'‖/‖b‖)。 -/
theorem relative_perturbation_bound_div (A : E ≃L[ℝ] F) (b b' : F) (x x' : E)
    (hx : A x = b) (hx' : A x' = b') (hb : b ≠ 0) :
    ‖x - x'‖ / ‖x‖ ≤ condNumber A * (‖b - b'‖ / ‖b‖) := by
  have hmul := relative_perturbation_bound A b b' x x' hx hx'
  have hxn : 0 < ‖x‖ := by
    apply norm_pos_iff.mpr
    intro hx0
    exact hb (by rw [← hx, hx0, map_zero])
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hdiv : ‖x - x'‖ ≤ condNumber A * ‖b - b'‖ * ‖x‖ / ‖b‖ := by
    rw [le_div_iff₀ hbn]
    exact hmul
  have heq : condNumber A * (‖b - b'‖ / ‖b‖) * ‖x‖ = condNumber A * ‖b - b'‖ * ‖x‖ / ‖b‖ := by
    rw [div_eq_mul_inv]
    ring
  rw [div_le_iff₀ hxn, heq]
  exact hdiv

/-! ## 定理四：矩阵扰动下的解扰动界（无需 Neumann 级数） -/

/-- 定理四：A x = b、B x' = b ⟹ ‖x − x'‖ ≤ ‖A⁻¹‖·‖B − A‖·‖x'‖。
核心恒等式：A(x − x') = (B − A)x'。 -/
theorem matrix_perturbation_bound (A B : E ≃L[ℝ] F) (b : F) (x x' : E)
    (hx : A x = b) (hx' : B x' = b) :
    ‖x - x'‖ ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖ * ‖x'‖ := by
  have h1c : A (x - x') = B x' - A x' := by rw [map_sub, hx, hx']
  have h1 : A (x - x') = (B : E →L[ℝ] F) x' - (A : E →L[ℝ] F) x' := by simpa using h1c
  have h2 : x - x' = A.symm ((B : E →L[ℝ] F) x' - (A : E →L[ℝ] F) x') := by
    rw [← h1, ContinuousLinearEquiv.symm_apply_apply]
  rw [h2]
  calc
    ‖(A.symm : F →L[ℝ] E) ((B : E →L[ℝ] F) x' - (A : E →L[ℝ] F) x')‖
        ≤ ‖(A.symm : F →L[ℝ] E)‖ * ‖(B : E →L[ℝ] F) x' - (A : E →L[ℝ] F) x'‖ :=
          (A.symm : F →L[ℝ] E).le_opNorm _
    _ = ‖(A.symm : F →L[ℝ] E)‖ * ‖((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x'‖ := by
          rw [ContinuousLinearMap.sub_apply]
    _ ≤ ‖(A.symm : F →L[ℝ] E)‖ *
          (‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖ * ‖x'‖) := by
          exact mul_le_mul_of_nonneg_left
            (((B : E →L[ℝ] F) - (A : E →L[ℝ] F)).le_opNorm x') (norm_nonneg _)
    _ = ‖(A.symm : F →L[ℝ] E)‖ * ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖ * ‖x'‖ := by ring

/-- 定理五：Neumann 型收缩定量界。设收缩条件
‖B − A‖·‖A⁻¹‖ < 1，则
‖x − x'‖·(1 − ‖A⁻¹‖·‖B−A‖) ≤ ‖A⁻¹‖²·‖B − A‖·‖b‖。 -/
theorem matrix_perturbation_bound_contraction (A B : E ≃L[ℝ] F) (b : F) (x x' : E)
    (hx : A x = b) (hx' : B x' = b)
    (hc : ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖ * ‖(A.symm : F →L[ℝ] E)‖ < 1) :
    ‖x - x'‖ * (1 - ‖(A.symm : F →L[ℝ] E)‖ * ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖) ≤
      ‖(A.symm : F →L[ℝ] E)‖ ^ 2 * ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖ * ‖b‖ := by
  set s := ‖(A.symm : F →L[ℝ] E)‖
  set d := ‖(B : E →L[ℝ] F) - (A : E →L[ℝ] F)‖
  have hs : 0 ≤ s := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  -- 步一：x' = A⁻¹(b − (B − A)x')
  have hx'rep : x' = A.symm (b - ((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x') := by
    have hBB : (B : E →L[ℝ] F) x' = b := by simpa using hx'
    have h : A x' = b - ((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x' := by
      rw [ContinuousLinearMap.sub_apply, hBB]
      abel
    rw [← h, ContinuousLinearEquiv.symm_apply_apply]
  have hx'bound : ‖x'‖ ≤ s * (‖b‖ + d * ‖x'‖) := by
    calc
      ‖x'‖ = ‖(A.symm : F →L[ℝ] E) (b - ((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x')‖ := by
              conv_lhs => rw [hx'rep]
              rfl
      _ ≤ s * ‖b - ((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x'‖ := by
              exact (A.symm : F →L[ℝ] E).le_opNorm _
      _ ≤ s * (‖b‖ + d * ‖x'‖) := by
              refine mul_le_mul_of_nonneg_left ?_ hs
              calc
                ‖b - ((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x'‖
                    ≤ ‖b‖ + ‖((B : E →L[ℝ] F) - (A : E →L[ℝ] F)) x'‖ := norm_sub_le _ _
                _ ≤ ‖b‖ + d * ‖x'‖ :=
                      add_le_add_left (((B : E →L[ℝ] F) - (A : E →L[ℝ] F)).le_opNorm x') _
      _ = s * (‖b‖ + d * ‖x'‖) := rfl
  have h1 : ‖x'‖ * (1 - d * s) ≤ s * ‖b‖ := by
    nlinarith [hx'bound]
  -- 步二：与一阶界相乘
  have h2 : ‖x - x'‖ ≤ s * d * ‖x'‖ := by
    have := matrix_perturbation_bound A B b x x' hx hx'
    simpa [s, d] using this
  have hnonneg : 0 ≤ 1 - d * s := by linarith
  calc
    ‖x - x'‖ * (1 - s * d) = ‖x - x'‖ * (1 - d * s) := by ring
    _ ≤ (s * d * ‖x'‖) * (1 - d * s) := mul_le_mul_of_nonneg_right h2 hnonneg
    _ = (s * d) * (‖x'‖ * (1 - d * s)) := by ring
    _ ≤ (s * d) * (s * ‖b‖) := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs hd)
    _ = s ^ 2 * d * ‖b‖ := by ring

/-! ## 定理六：条件数的复合（多步运算） -/

/-- 定理六：κ(A∘B) ≤ κ(A)·κ(B)（此处复合写成 `B.trans A`，即先 B 后 A）。 -/
theorem condNumber_comp_le (A : F ≃L[ℝ] G) (B : E ≃L[ℝ] F) :
    condNumber (B.trans A) ≤ condNumber A * condNumber B := by
  have hcoe : ((B.trans A : E ≃L[ℝ] G) : E →L[ℝ] G) =
      (A : F →L[ℝ] G).comp (B : E →L[ℝ] F) := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact ContinuousLinearEquiv.trans_apply B A x
  have hsymm : (((B.trans A).symm : G ≃L[ℝ] E) : G →L[ℝ] E) =
      (B.symm : F →L[ℝ] E).comp (A.symm : G →L[ℝ] F) := by
    ext x
    rw [ContinuousLinearMap.comp_apply]
    exact ContinuousLinearEquiv.symm_trans_apply A B x
  have h1 : ‖((B.trans A : E ≃L[ℝ] G) : E →L[ℝ] G)‖ ≤
      ‖(A : F →L[ℝ] G)‖ * ‖(B : E →L[ℝ] F)‖ := by
    rw [hcoe]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖(((B.trans A).symm : G ≃L[ℝ] E) : G →L[ℝ] E)‖ ≤
      ‖(B.symm : F →L[ℝ] E)‖ * ‖(A.symm : G →L[ℝ] F)‖ := by
    rw [hsymm]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  calc
    condNumber (B.trans A) =
        ‖((B.trans A : E ≃L[ℝ] G) : E →L[ℝ] G)‖ *
          ‖(((B.trans A).symm : G ≃L[ℝ] E) : G →L[ℝ] E)‖ := by simp only [condNumber]
    _ ≤ (‖(A : F →L[ℝ] G)‖ * ‖(B : E →L[ℝ] F)‖) *
        (‖(B.symm : F →L[ℝ] E)‖ * ‖(A.symm : G →L[ℝ] F)‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = condNumber A * condNumber B := by simp only [condNumber]; ring

/-! ## 注：衔接
  · `relative_perturbation_bound_div` 是教科书 κ·(‖δb‖/‖b‖) 的精确形式；
  · `matrix_perturbation_bound` 对应「矩阵扰动 ⟹ 解扰动」的一阶项，
    `..._contraction` 是其 Neumann 型定量强化；
  · `condNumber_comp_le` 给出多步运算条件数的次乘法性
    （RealMatrixStability 的 `condition_number_perturbation_product` 由其导出）。-/

end Lattice
