import Lattice.Lib.Editing.RealBatchEditClosed
import Lattice.Lib.Editing.RealEditCrosstalk
import Lattice.Lib.Editing.RealROME
import Mathlib

/-!
# LATTICE: 一般（非正交）键下批量编辑的精确闭式与串扰误差界

VERIFICATION.md §5 展望「一般键批量闭式」：RealBatchEditClosed 的
`batchClosed_orthogonal_writes` 在**键两两正交**（i ≠ j ⟹ ⟨kᵢ,kⱼ⟩ = 0）的
假设下给出批量编辑

    W' = W + Σᵢ Δᵢ⊗kᵢ,   Δᵢ = (vᵢ − W·kᵢ)/‖kᵢ‖²

的精确闭式 W'·kᵢ = vᵢ。本文件**去掉正交假设**：对一般（可能非正交）键，
j ≠ i 的项不再消失，而是作为**显式串扰残差**保留：

    ① 精确残差（batchClosed_exact_residual，无正交假设，核心等式）：
       ∀i, W'·kᵢ = vᵢ + Σ_{j≠i} ⟨kⱼ,kᵢ⟩·(vⱼ − W·kⱼ)/‖kⱼ‖²。
       展开 BatchEditClosed 后把求和拆成对角项 + 非对角项
       （Finset.sum_erase_add 拆分引理 sum_split_diag），对角项 = vᵢ − W·kᵢ
       （‖kᵢ‖² 消去，需键非零 hk），补上 W·kᵢ 即得。正交假设下该残差
       为 0，退化为 batchClosed_orthogonal_writes。

    ② 串扰界（batchClosed_crosstalk_bound，核心界）：
       |W'·kᵢ − vᵢ| ≤ Σ_{j≠i} |⟨kⱼ,kᵢ⟩|·|vⱼ − W·kⱼ|/‖kⱼ‖²
       （三角不等式 abs_add + abs_mul + 分母 ‖kⱼ‖² ≥ 0 拆绝对值）。
       此界同样需要键非零：对角项 ‖kᵢ‖²·(vᵢ−W·kᵢ)/‖kᵢ‖² 必须精确消成
       vᵢ−W·kᵢ 才能只留非对角残差——若 kᵢ = 0，补丁在 kᵢ 处贡献 0，
       W'·kᵢ = W·kᵢ ≠ vᵢ 一般成立，界不再成立（诚实假设，无正交假设）。
       正交键（∀j≠i, ⟨kⱼ,kᵢ⟩=0）⟹ 残差为 0，精确回写
       （batchClosed_crosstalk_bound_orthogonal_special 由本界推出，
       衔接 batchClosed_orthogonal_writes 作为正交特例）。

    ③ 小串扰定量版（batchClosed_small_crosstalk）：
       若键"近似正交"（∀j≠i, |⟨kⱼ,kᵢ⟩| ≤ ε·‖kⱼ‖²）且残差有界
       （∀j≠i, |vⱼ−W·kⱼ| ≤ R），则
       |W'·kᵢ − vᵢ| ≤ (m−1)·ε·R
       ——近似正交 ⟹ 近似写入，ε → 0 时回到精确（非对角和共 m−1 项）。

    ④ m=2 特例与顺序编辑对照：批量语义双键精确公式
       Batch2(k₁) = v₁ + ⟨k₂,k₁⟩·(v₂−W·k₂)/‖k₂‖²（batch2_exact_residual_first，
       结构同 RealEditCrosstalk.edit2_writes_first，仅基准 W 不同），
       及其 Cauchy 界（batch2_cauchy_crosstalk_bound_first，对照
       edit2_cauchy_crosstalk_bound）——「键相似性 ⟹ 串扰线性增长」对
       批量/顺序两种语义一致。

    模型无关：任意 ℝ-内积空间、任意编辑数 m。诚实假设：键非零
    （∀i, kᵢ ≠ 0，保证 ‖kᵢ‖² 可除）；域为 ℝ 欧氏内积；无正交假设。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 辅助引理：求和按对角/非对角拆分
（sum_orthogonal_kill 的"不 kill"版本：全和 = 对角项 + j ≠ i 项之和） -/

lemma sum_split_diag {m : ℕ} (t : Fin m → ℝ) (i : Fin m) :
    (∑ j : Fin m, t j) = t i + ∑ j in (Finset.univ.erase i), t j := by
  rw [← Finset.sum_erase_add Finset.univ t (Finset.mem_univ i)]
  ac_rfl

/-! ## 定理一：精确残差（核心精确公式，无正交假设）
∀i, W'·kᵢ = vᵢ + Σ_{j≠i} ⟨kⱼ,kᵢ⟩·(vⱼ − W·kⱼ)/‖kⱼ‖²。
正交键（⟨kⱼ,kᵢ⟩=0, j≠i）⟹ 残差为 0 ⟹ 回到 batchClosed_orthogonal_writes。-/

theorem batchClosed_exact_residual {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (hk : ∀ i : Fin m, k i ≠ 0) (i : Fin m) :
    BatchEditClosed W k v (k i)
      = v i + ∑ j in (Finset.univ.erase i),
          inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2) := by
  unfold BatchEditClosed RankOnePatch
  have hsplit := sum_split_diag
    (fun j => inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)) i
  rw [hsplit]
  have hnorm : inner (k i) (k i) = ‖k i‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) (k i)
  rw [hnorm]
  have hk' : ‖k i‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero (k i) (hk i)
  have hdiag : W (k i) + ‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2) = v i := by
    calc
      W (k i) + ‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2)
          = W (k i) + (v i - W (k i)) := by field_simp [hk']
      _ = v i := by ring
  rw [← add_assoc]
  rw [hdiag]

/-! ## 辅助引理：逐项绝对值 |a·(b/c)| = |a|·|b|/c（c = ‖kⱼ‖² ≥ 0） -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma abs_mul_div_sq {m : ℕ} (k : Fin m → E) (j : Fin m) (a b : ℝ) :
    |a * (b / ‖k j‖ ^ 2)| = |a| * |b| / ‖k j‖ ^ 2 := by
  rw [abs_mul]
  have hpos : 0 ≤ ‖k j‖ ^ 2 := sq_nonneg _
  have hdiv : |b / ‖k j‖ ^ 2| = |b| / ‖k j‖ ^ 2 := by
    rw [abs_div, abs_of_nonneg hpos]
  rw [hdiv]
  ring

/-! ## 定理二：串扰界（核心界，无正交假设；需键非零以消去对角项）
|W'·kᵢ − vᵢ| ≤ Σ_{j≠i} |⟨kⱼ,kᵢ⟩|·|vⱼ − W·kⱼ|/‖kⱼ‖²。
证明：对角项 ‖kᵢ‖²·(vᵢ−W·kᵢ)/‖kᵢ‖² = vᵢ−W·kᵢ 与 W·kᵢ − vᵢ 相消，
只剩非对角和；三角不等式 + 逐项绝对值。-/

theorem batchClosed_crosstalk_bound {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (hk : ∀ i : Fin m, k i ≠ 0) (i : Fin m) :
    |BatchEditClosed W k v (k i) - v i|
      ≤ ∑ j in (Finset.univ.erase i),
          |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2 := by
  unfold BatchEditClosed RankOnePatch
  have hsplit := sum_split_diag
    (fun j => inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)) i
  rw [hsplit]
  have hnorm : inner (k i) (k i) = ‖k i‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) (k i)
  rw [hnorm]
  have hk' : ‖k i‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero (k i) (hk i)
  have hdiff : W (k i) + (‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2)
      + ∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)) - v i
      = (‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2) - (v i - W (k i)))
          + ∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2) := by
    ring
  rw [hdiff]
  calc
    |(‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2) - (v i - W (k i)))
          + ∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)|
        ≤ |‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2) - (v i - W (k i))|
            + |∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)| :=
          abs_add _ _
    _ = 0 + |∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)| := by
          have hcancel : ‖k i‖ ^ 2 * ((v i - W (k i)) / ‖k i‖ ^ 2) - (v i - W (k i)) = 0 := by
            field_simp [hk']
          rw [hcancel]
          simp
    _ ≤ |∑ j in (Finset.univ.erase i), inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)| := by
          simp
    _ ≤ ∑ j in (Finset.univ.erase i), |inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)| := by
          exact Finset.abs_sum_le_sum_abs
            (fun j : Fin m => inner (k j) (k i) * ((v j - W (k j)) / ‖k j‖ ^ 2)) (Finset.univ.erase i)
    _ = ∑ j in (Finset.univ.erase i), |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact abs_mul_div_sq k j (inner (k j) (k i)) (v j - W (k j))

/-! ## 定理二推论：正交键（∀j≠i, ⟨kⱼ,kᵢ⟩=0）⟹ 串扰残差为 0，精确回写
由串扰界直接推出（界右端为 0 ⟹ |W'·kᵢ − vᵢ| = 0 ⟹ 等式），
衔接 batchClosed_orthogonal_writes 作为正交特例（两条路径结论一致）。 -/

theorem batchClosed_crosstalk_bound_orthogonal_special {m : ℕ} (W : E →L[ℝ] ℝ)
    (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    ∀ i : Fin m, BatchEditClosed W k v (k i) = v i := by
  intro i
  have hb := batchClosed_crosstalk_bound W k v hk i
  have hsum : (∑ j in (Finset.univ.erase i),
      |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hz : inner (k j) (k i) = (0 : ℝ) := horth j i hjne
    rw [hz]
    simp
  rw [hsum] at hb
  have habs : |BatchEditClosed W k v (k i) - v i| = 0 := le_antisymm hb (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habs)

/-! ## 定理三：小串扰定量版
若键"近似正交"（∀j≠i, |⟨kⱼ,kᵢ⟩| ≤ ε·‖kⱼ‖²）且残差有界（∀j≠i, |vⱼ−W·kⱼ| ≤ R），
则 |W'·kᵢ − vᵢ| ≤ (m−1)·ε·R（近似正交 ⟹ 近似写入，ε → 0 时回到精确；
Lean 中 (m−1) 写作 ↑(m − 1)，即 ℕ 截断减法后 cast 到 ℝ——非对角项共
m−1 个，m = 0 时 i : Fin 0 不存在，定理空洞成立）。-/

theorem batchClosed_small_crosstalk {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (i : Fin m) (ε R : ℝ)
    (hεnonneg : 0 ≤ ε)
    (hk : ∀ i : Fin m, k i ≠ 0)
    (hε : ∀ j : Fin m, j ≠ i → |inner (k j) (k i)| ≤ ε * ‖k j‖ ^ 2)
    (hR : ∀ j : Fin m, j ≠ i → |v j - W (k j)| ≤ R) :
    |BatchEditClosed W k v (k i) - v i| ≤ ↑(m - 1) * ε * R := by
  -- 先用串扰界（定理二），再逐项用 hε、hR 放大
  have hb := batchClosed_crosstalk_bound W k v hk i
  -- 逐项：|⟨kⱼ,kᵢ⟩|·|dⱼ|/‖kⱼ‖² ≤ ε·R
  have hterm : ∀ j : Fin m, j ∈ Finset.univ.erase i →
      |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2 ≤ ε * R := by
    intro j hj
    have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hk' : ‖k j‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero (k j) (hk j)
    calc
      |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2
          ≤ (ε * ‖k j‖ ^ 2) * |v j - W (k j)| / ‖k j‖ ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hε j hjne) (abs_nonneg _)) (sq_nonneg _)
      _ = ε * |v j - W (k j)| := by
            field_simp [hk']
            ring
      _ ≤ ε * R := by
            exact mul_le_mul_of_nonneg_left (hR j hjne) hεnonneg
  -- 逐项求和
  have hsum : (∑ j in (Finset.univ.erase i),
      |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2) ≤ ↑(m - 1) * ε * R := by
    calc
      (∑ j in (Finset.univ.erase i),
          |inner (k j) (k i)| * |v j - W (k j)| / ‖k j‖ ^ 2)
          ≤ ∑ j in (Finset.univ.erase i), ε * R := by
            exact Finset.sum_le_sum hterm
      _ = (Finset.univ.erase i).card * (ε * R) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = ↑(m - 1) * ε * R := by
            have hcard : (Finset.univ.erase i).card = m - 1 := by
              calc
                (Finset.univ.erase i).card = (Finset.univ : Finset (Fin m)).card - 1 := by
                      exact Finset.card_erase_of_mem (Finset.mem_univ i)
                _ = m - 1 := by
                      rw [Finset.card_univ, Fintype.card_fin]
            rw [hcard]
            ring
  exact le_trans hb hsum

/-! ## m=2 特例：双键批量编辑的精确残差（与 RealEditCrosstalk 对照）
批量语义（基准均为原 W）下双键精确公式：
Batch2(k₁) = v₁ + ⟨k₂,k₁⟩·(v₂−W·k₂)/‖k₂‖²（BatchEdit2 直接展开）。
-/

theorem batch2_exact_residual_first (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₁ : k₁ ≠ 0) :
    BatchEdit2 W k₁ k₂ v₁ v₂ k₁
      = v₁ + inner k₂ k₁ * ((v₂ - W k₂) / ‖k₂‖ ^ 2) := by
  unfold BatchEdit2
  have hnorm : inner k₁ k₁ = ‖k₁‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₁
  rw [hnorm]
  have hk' : ‖k₁‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₁ hk₁
  have hdiag : W k₁ + ‖k₁‖ ^ 2 * ((v₁ - W k₁) / ‖k₁‖ ^ 2) = v₁ := by
    calc
      W k₁ + ‖k₁‖ ^ 2 * ((v₁ - W k₁) / ‖k₁‖ ^ 2)
          = W k₁ + (v₁ - W k₁) := by field_simp [hk']
      _ = v₁ := by ring
  rw [hdiag]

theorem batch2_exact_residual_second (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₂ : k₂ ≠ 0) :
    BatchEdit2 W k₁ k₂ v₁ v₂ k₂
      = v₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) := by
  unfold BatchEdit2
  have hnorm : inner k₂ k₂ = ‖k₂‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₂
  rw [hnorm]
  have hk' : ‖k₂‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₂ hk₂
  have hdiag : W k₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2)
      + ‖k₂‖ ^ 2 * ((v₂ - W k₂) / ‖k₂‖ ^ 2)
      = v₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) := by
    calc
      W k₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2)
          + ‖k₂‖ ^ 2 * ((v₂ - W k₂) / ‖k₂‖ ^ 2)
          = (W k₂ + ‖k₂‖ ^ 2 * ((v₂ - W k₂) / ‖k₂‖ ^ 2))
              + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) := by ring
      _ = v₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) := by
            have hd : W k₂ + ‖k₂‖ ^ 2 * ((v₂ - W k₂) / ‖k₂‖ ^ 2) = v₂ := by
              calc
                W k₂ + ‖k₂‖ ^ 2 * ((v₂ - W k₂) / ‖k₂‖ ^ 2)
                    = W k₂ + (v₂ - W k₂) := by field_simp [hk']
                _ = v₂ := by ring
            rw [hd]
  rw [hdiag]

/-! ## m=2 串扰界（批量语义）
|Batch2(k₁) − v₁| ≤ |⟨k₂,k₁⟩|·|v₂−W·k₂|/‖k₂‖²（由精确残差直接取绝对值）。-/

theorem batch2_crosstalk_bound_first (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₁ : k₁ ≠ 0) :
    |BatchEdit2 W k₁ k₂ v₁ v₂ k₁ - v₁|
      ≤ |inner k₂ k₁| * |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
  rw [batch2_exact_residual_first W k₁ k₂ v₁ v₂ hk₁]
  have hdiff : v₁ + inner k₂ k₁ * ((v₂ - W k₂) / ‖k₂‖ ^ 2) - v₁
      = inner k₂ k₁ * ((v₂ - W k₂) / ‖k₂‖ ^ 2) := by ring
  rw [hdiff]
  rw [abs_mul]
  have hpos : 0 ≤ ‖k₂‖ ^ 2 := sq_nonneg _
  have hdiv : |(v₂ - W k₂) / ‖k₂‖ ^ 2| = |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
    rw [abs_div, abs_of_nonneg hpos]
  rw [hdiv]
  exact le_of_eq (by ring)

theorem batch2_crosstalk_bound_second (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₂ : k₂ ≠ 0) :
    |BatchEdit2 W k₁ k₂ v₁ v₂ k₂ - v₂|
      ≤ |inner k₁ k₂| * |v₁ - W k₁| / ‖k₁‖ ^ 2 := by
  rw [batch2_exact_residual_second W k₁ k₂ v₁ v₂ hk₂]
  have hdiff : v₂ + inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) - v₂
      = inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) := by ring
  rw [hdiff]
  rw [abs_mul]
  have hpos : 0 ≤ ‖k₁‖ ^ 2 := sq_nonneg _
  have hdiv : |(v₁ - W k₁) / ‖k₁‖ ^ 2| = |v₁ - W k₁| / ‖k₁‖ ^ 2 := by
    rw [abs_div, abs_of_nonneg hpos]
  rw [hdiv]
  exact le_of_eq (by ring)

/-! ## m=2 Cauchy 串扰界（对照 RealEditCrosstalk.edit2_cauchy_crosstalk_bound）
|Batch2(k₁) − v₁| ≤ ‖k₁‖·|v₂−W·k₂|/‖k₂‖：由 batch2_crosstalk_bound_first 进一步
用 Cauchy-Schwarz |⟨k₂,k₁⟩| ≤ ‖k₂‖·‖k₁‖ 放大——与顺序编辑的
edit2_cauchy_crosstalk_bound 结构完全一致，「键相似性 ⟹ 串扰线性增长」
对批量/顺序两种语义成立（仅基准 W 不同：批量用原 W，顺序用 W₂ = W + Δ₁）。-/

theorem batch2_cauchy_crosstalk_bound_first (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) :
    |BatchEdit2 W k₁ k₂ v₁ v₂ k₁ - v₁| ≤ ‖k₁‖ * |v₂ - W k₂| / ‖k₂‖ := by
  have hb := batch2_crosstalk_bound_first W k₁ k₂ v₁ v₂ hk₁
  have hcs := abs_real_inner_le_norm k₂ k₁
  have hk2pos : 0 < ‖k₂‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hk₂) 2
  calc
    |BatchEdit2 W k₁ k₂ v₁ v₂ k₁ - v₁|
        ≤ |inner k₂ k₁| * |v₂ - W k₂| / ‖k₂‖ ^ 2 := hb
    _ ≤ (‖k₂‖ * ‖k₁‖) * |v₂ - W k₂| / ‖k₂‖ ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcs (abs_nonneg _)) (le_of_lt hk2pos)
    _ = ‖k₁‖ * |v₂ - W k₂| / ‖k₂‖ := by
          have hk2n : ‖k₂‖ ≠ 0 := by
            intro hz
            exact hk₂ (norm_eq_zero.mp hz)
          have hk2sq : ‖k₂‖ ^ 2 ≠ 0 := pow_ne_zero 2 hk2n
          field_simp [hk2n, hk2sq]
          ring

/-! ## 注：与顺序编辑（ApplyEdits2）的对照
批量编辑（本文件）：所有补丁基准为原 W，串扰残差来自 j ≠ i 的补丁对 kᵢ 的
响应，精确公式 = 目标值 + 非对角和（batchClosed_exact_residual），
界 = 非对角绝对值和（batchClosed_crosstalk_bound），近似正交定量版
（batchClosed_small_crosstalk）；顺序编辑（RealEditCrosstalk.ApplyEdits2）：
第二编辑基准含第一编辑，m=2 时第一事实偏移
= ⟨k₂,k₁⟩·(v₂−W₂·k₂)/‖k₂‖²（edit2_writes_first），与批量语义 m=2 公式
batch2_exact_residual_first 结构一致（仅基准 W 不同：W₂ = W + Δ₁）。
Cauchy 界（edit2_cauchy_crosstalk_bound vs batch2_cauchy_crosstalk_bound_first）
两种语义一致：|⟨k₂,k₁⟩|·|d|/‖k₂‖² ≤ ‖k₁‖·|d|/‖k₂‖。
正交键（⟨kⱼ,kᵢ⟩=0, j≠i）⟹ 残差为 0：批量语义回到
batchClosed_orthogonal_writes（本文件 batchClosed_crosstalk_bound_orthogonal_special
由串扰界推出），顺序语义回到 edit2_orthogonal_preserves_first。 -/

end Lattice
