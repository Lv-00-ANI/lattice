import Lattice.Lib.Editing.RealEditCrosstalk
import Mathlib

/-!
# LATTICE: m 元批量编辑（泛化）—— 任意数量并发编辑的总界

RealEditCrosstalk（双编辑批量）的 **m 元泛化**：任意有限个 rank-one
补丁同时应用（基准均为原 W，MEMIT 层内批量语义）：

    BatchEditN(x) = W·x + Σᵢ ⟨kᵢ, x⟩·(vᵢ − W·kᵢ)/‖kᵢ‖²

总界（三角不等式 + 逐项绝对值）：

    |BatchEditN(x) − W·x| ≤ Σᵢ |⟨kᵢ,x⟩|·|vᵢ−W·kᵢ|/‖kᵢ‖²

双编辑（RealEditCrosstalk.batch2_pointwise_bound）与本文件的 m 元定理在 m=2 时
命题一致；但后者是**独立证明**的（其文件不 import 本文件），并非由本定理实例化得到。

模型无关：任意 ℝ-内积空间、任意编辑数 m。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## m 元批量编辑（同时应用） -/

def BatchEditN {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ) (x : E) : ℝ :=
  W x + ∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)

/-! ## 定理：m 元批量编辑逐点总界（泛化）
|BatchEditN(x) − W·x| ≤ Σᵢ |⟨kᵢ,x⟩|·|vᵢ−W·kᵢ|/‖kᵢ‖²。-/

omit [CompleteSpace E] in
theorem batchN_pointwise_bound {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ) (x : E) :
    |BatchEditN W k v x - W x|
      ≤ ∑ i : Fin m, |inner (k i) x| * |v i - W (k i)| / ‖k i‖ ^ 2 := by
  unfold BatchEditN
  -- 差 = Σᵢ tᵢ（tᵢ = ⟨kᵢ,x⟩·(vᵢ−Wkᵢ)/‖kᵢ‖²）
  have hdiff : W x + (∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)) - W x
      = ∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2) := by ring
  rw [hdiff]
  -- |Σᵢ tᵢ| ≤ Σᵢ |tᵢ|（三角不等式）
  have hsum : |∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)|
      ≤ ∑ i : Fin m, |inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)| := by
    -- 注：mathlib 4.14 中 abs_sum_le_sum_abs 位于 Finset 命名空间
    exact Finset.abs_sum_le_sum_abs (fun i : Fin m => inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)) Finset.univ
  -- 逐项：|tᵢ| = |⟨kᵢ,x⟩|·|vᵢ−Wkᵢ|/‖kᵢ‖²
  calc
    |∑ i : Fin m, inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)|
        ≤ ∑ i : Fin m, |inner (k i) x * ((v i - W (k i)) / ‖k i‖ ^ 2)| := hsum
    _ = ∑ i : Fin m, |inner (k i) x| * |v i - W (k i)| / ‖k i‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul]
          have hpos : 0 ≤ ‖k i‖ ^ 2 := sq_nonneg _
          have hdiv : |(v i - W (k i)) / ‖k i‖ ^ 2| = |v i - W (k i)| / ‖k i‖ ^ 2 := by
            rw [abs_div, abs_of_nonneg hpos]
          rw [hdiv]
          ring

/-! ## 注：泛化闭环
  双编辑（RealEditCrosstalk.batch2_pointwise_bound，m=2）⟹ m 元
  （本文件，任意 m）；批量编辑无串扰（基准恒为原 W），总界 =
  各编辑量之和——MEMIT 层内批量写入的完整泛化。
  顺序编辑（ApplyEdits2）的 m 元版（逐次应用）串扰随编辑次数累积，
  留给 Cauchy 界（edit2_cauchy_crosstalk_bound）逐对组合。-/

end Lattice
