import Lattice.Lib.Editing.RealROME
import Mathlib

/-!
# LATTICE: 编辑间交互 —— 并发/顺序编辑的串扰分析（编辑线新维度）

调研（research/real-world/model-edit-math.md 目标 2）的编辑交互数学：
多个 rank-one 编辑同时/顺序应用时的相互干扰。

  顺序编辑（ApplyEdits2，先 k₁→v₁ 再 k₂→v₂）：
    1. 第一事实在第二编辑后的精确值 = v₁ + 串扰项（⟨k₂,k₁⟩·(v₂−W₂k₂)/‖k₂‖²）；
    2. 串扰大小 |结果 − v₁| = |⟨k₂,k₁⟩|·|v₂−W₂k₂|/‖k₂‖²（精确）；
    3. 正交键（⟨k₂,k₁⟩=0）⟹ 串扰 = 0，第一事实精确保持；
    4. 同键（k₂=k₁）⟹ 最后写入胜出：结果 = v₂（覆盖语义）；
    5. Cauchy-Schwarz 界：串扰 ≤ ‖k₁‖·|v₂−W₂k₂|/‖k₂‖
       （串扰随键相似性 ‖⟨k₂,k₁⟩‖ 线性增长）。

  批量编辑（BatchEdit2，同时应用，基准均为原 W）：
    6. 逐点变化 ≤ 各编辑量之和（三角不等式，MEMIT 层内批量语义）。

模型无关：任意 ℝ-内积空间；只假设键非零（‖k₀‖² 可除）。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## rank-one 编辑（作用于任意函数，ROME 的泛化） -/

def ApplyEdit (F : E → ℝ) (k₀ : E) (v : ℝ) (x : E) : ℝ :=
  F x + inner k₀ x * ((v - F k₀) / ‖k₀‖ ^ 2)

/-! ## 引理：编辑精确写入事实（泛化 ROME_writes_fact） -/

lemma applyEdit_writes_fact (F : E → ℝ) (k₀ : E) (v : ℝ) (hk : k₀ ≠ 0) :
    ApplyEdit F k₀ v k₀ = v := by
  unfold ApplyEdit
  have hnorm : inner k₀ k₀ = ‖k₀‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₀
  calc
    F k₀ + inner k₀ k₀ * ((v - F k₀) / ‖k₀‖ ^ 2)
        = F k₀ + ‖k₀‖ ^ 2 * ((v - F k₀) / ‖k₀‖ ^ 2) := by rw [hnorm]
    _ = F k₀ + (v - F k₀) := by
          have hk : ‖k₀‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₀ hk
          field_simp [hk]
    _ = v := by ring

/-! ## 顺序编辑：先 k₁→v₁ 再 k₂→v₂
（参数顺序：F k₁ k₂ v₁ v₂ x；历史代码把 k₂/v₁ 写反导致类型错误，已按定义序修正） -/

def ApplyEdits2 (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E) : ℝ :=
  ApplyEdit (fun y => ApplyEdit F k₁ v₁ y) k₂ v₂ x

/-! ## 定理一：第一事实在第二编辑后的精确值
结果 = v₁ + ⟨k₂,k₁⟩·(v₂ − W₂k₂)/‖k₂‖²（串扰项显式）。-/

theorem edit2_writes_first (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E)
    (hk₁ : k₁ ≠ 0) :
    ApplyEdits2 F k₁ k₂ v₁ v₂ k₁
      = v₁ + inner k₂ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2) := by
  have hw1 : ApplyEdit F k₁ v₁ k₁ = v₁ := applyEdit_writes_fact F k₁ v₁ hk₁
  unfold ApplyEdits2
  calc
    ApplyEdit (fun y => ApplyEdit F k₁ v₁ y) k₂ v₂ k₁
        = ApplyEdit F k₁ v₁ k₁ + inner k₂ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2) := by
          unfold ApplyEdit
          simp
    _ = v₁ + inner k₂ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2) := by rw [hw1]

/-! ## 定理二：第一事实的串扰偏移（精确大小）
|结果 − v₁| = |⟨k₂,k₁⟩|·|v₂−W₂k₂|/‖k₂‖²。-/

theorem edit2_first_fact_offset (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E)
    (hk₁ : k₁ ≠ 0) :
    |ApplyEdits2 F k₁ k₂ v₁ v₂ k₁ - v₁|
      = |inner k₂ k₁| * |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ ^ 2 := by
  rw [edit2_writes_first F k₁ k₂ v₁ v₂ k₁ hk₁]
  have hdiff : v₁ + inner k₂ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2) - v₁
      = inner k₂ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2) := by ring
  rw [hdiff]
  rw [abs_mul]
  have hpos : 0 ≤ ‖k₂‖ ^ 2 := sq_nonneg _
  have hdiv : |(v₂ - ApplyEdit F k₁ v₁ k₂) / ‖k₂‖ ^ 2|
      = |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ ^ 2 := by
    rw [abs_div, abs_of_nonneg hpos]
  rw [hdiv]
  ring

/-! ## 定理三：正交键无串扰
⟨k₂,k₁⟩ = 0 ⟹ 第一事实精确保持（第二编辑不干扰）。-/

theorem edit2_orthogonal_preserves_first (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E)
    (hk₁ : k₁ ≠ 0) (horth : inner k₂ k₁ = (0 : ℝ)) :
    ApplyEdits2 F k₁ k₂ v₁ v₂ k₁ = v₁ := by
  rw [edit2_writes_first F k₁ k₂ v₁ v₂ k₁ hk₁, horth]
  simp

/-! ## 定理四：同键覆盖（最后写入胜出）
k₂ = k₁ ⟹ 结果 = v₂（后编辑覆盖前编辑）。-/

theorem edit2_same_key_overwrites (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E)
    (hk₂ : k₂ ≠ 0) (h : k₂ = k₁) :
    ApplyEdits2 F k₁ k₂ v₁ v₂ k₁ = v₂ := by
  subst k₂
  have hk₁ : k₁ ≠ 0 := hk₂
  rw [edit2_writes_first F k₁ k₁ v₁ v₂ k₁ hk₁]
  have hw1 : ApplyEdit F k₁ v₁ k₁ = v₁ := applyEdit_writes_fact F k₁ v₁ hk₁
  have hnorm : inner k₁ k₁ = ‖k₁‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₁
  calc
    v₁ + inner k₁ k₁ * ((v₂ - ApplyEdit F k₁ v₁ k₁) / ‖k₁‖ ^ 2)
        = v₁ + ‖k₁‖ ^ 2 * ((v₂ - v₁) / ‖k₁‖ ^ 2) := by rw [hw1, hnorm]
    _ = v₁ + (v₂ - v₁) := by
          have hk : ‖k₁‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₁ hk₁
          field_simp [hk]
    _ = v₂ := by ring

/-! ## 定理五：Cauchy-Schwarz 串扰界
|串扰| ≤ ‖k₁‖·|v₂−W₂k₂|/‖k₂‖（键相似性 ⟹ 串扰线性增长）。-/

theorem edit2_cauchy_crosstalk_bound (F : E → ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) :
    |ApplyEdits2 F k₁ k₂ v₁ v₂ k₁ - v₁| ≤ ‖k₁‖ * |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ := by
  rw [edit2_first_fact_offset F k₁ k₂ v₁ v₂ k₁ hk₁]
  -- |⟨k₂,k₁⟩|·|d|/‖k₂‖² ≤ (‖k₂‖‖k₁‖)·|d|/‖k₂‖² = ‖k₁‖·|d|/‖k₂‖
  have hcs := abs_real_inner_le_norm k₂ k₁
  have hk2pos : 0 < ‖k₂‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hk₂) 2
  calc
    |inner k₂ k₁| * |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ ^ 2
        ≤ (‖k₂‖ * ‖k₁‖) * |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcs (abs_nonneg _)) (le_of_lt hk2pos)
    _ = ‖k₁‖ * |v₂ - ApplyEdit F k₁ v₁ k₂| / ‖k₂‖ := by
          have hk2n : ‖k₂‖ ≠ 0 := by
            intro hz
            exact hk₂ (norm_eq_zero.mp hz)
          have hk2sq : ‖k₂‖ ^ 2 ≠ 0 := pow_ne_zero 2 hk2n
          field_simp [hk2n, hk2sq]
          ring

/-! ## 批量编辑：同时应用（基准均为原 W，MEMIT 层内批量语义） -/

def BatchEdit2 (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E) : ℝ :=
  W x + inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2) + inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2)

/-! ## 定理六：批量编辑逐点总界
|Batch2(x) − W(x)| ≤ 各编辑量之和（三角不等式）。-/

omit [CompleteSpace E] in
theorem batch2_pointwise_bound (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ) (x : E) :
    |BatchEdit2 W k₁ k₂ v₁ v₂ x - W x|
      ≤ |inner k₁ x| * |v₁ - W k₁| / ‖k₁‖ ^ 2 + |inner k₂ x| * |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
  unfold BatchEdit2
  have hdiff : W x + inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2) + inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2) - W x
      = inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2) + inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2) := by ring
  calc
    |W x + inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2) + inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2) - W x|
        = |inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2) + inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2)| := by
          rw [hdiff]
    _ ≤ |inner k₁ x * ((v₁ - W k₁) / ‖k₁‖ ^ 2)| + |inner k₂ x * ((v₂ - W k₂) / ‖k₂‖ ^ 2)| :=
          abs_add _ _
    _ = |inner k₁ x| * |v₁ - W k₁| / ‖k₁‖ ^ 2 + |inner k₂ x| * |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
          have hpos₁ : 0 ≤ ‖k₁‖ ^ 2 := sq_nonneg _
          have hpos₂ : 0 ≤ ‖k₂‖ ^ 2 := sq_nonneg _
          have h₁ : |(v₁ - W k₁) / ‖k₁‖ ^ 2| = |v₁ - W k₁| / ‖k₁‖ ^ 2 := by
            rw [abs_div, abs_of_nonneg hpos₁]
          have h₂ : |(v₂ - W k₂) / ‖k₂‖ ^ 2| = |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
            rw [abs_div, abs_of_nonneg hpos₂]
          rw [abs_mul, h₁, abs_mul, h₂]
          ring

/-! ## 注：编辑策略语义
  顺序编辑（ApplyEdits2）：第二编辑基准含第一编辑（W₂ = W + Δ₁），
  串扰项来自 Δ₁ 对 k₂ 的响应——同键覆盖、正交无扰是它的两个极端；
  批量编辑（BatchEdit2）：所有补丁基准为原 W，无串扰但需总界
  （本文件定理六）——MEMIT 层内批量写入即此语义。
  Cauchy 界（定理五）量化「键越相似串扰越大」：‖⟨k₂,k₁⟩‖ 是
  编辑间干扰的度量，正交键 = 零干扰，同键 = 完全覆盖。-/

end Lattice
