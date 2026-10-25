import Mathlib
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.Attention.RealSoftmaxTemp
/-!
# LATTICE: 对比损失 / InfoNCE —— 正性、log 基数界、CE 实例化与梯度

信息论线的又一块基石（衔接 RealCrossEntropy 的交叉熵/one-hot、RealSoftmaxTemp 的温度缩放）：

给定相似度 `s : Fin n → ℝ`、温度 `τ > 0`、正样本索引 `i`，定义

    infoNCE(s, τ, i) = −log softmax(s/τ)_i
                     = −log( exp(s_i/τ) / Σ_j exp(s_j/τ) )

即标准的 InfoNCE 对比损失（对齐 InfoNCE = 正样本 softmax 概率的负对数）。

本文件建立：

  1. `infoNCE`（定义）；`infonce_eq_neg_log_softmaxTemp`：与 `softmaxTemp` 的桥接；
  2. `infonce_eq_ce`（**InfoNCE 是交叉熵的实例**）：
     infoNCE(s,τ,i) = CE(onehot_i, softmax(s/τ))（回收 `ce_onehot_eq_neg_log`）；
  3. `infonce_nonneg`：InfoNCE ≥ 0（softmax 概率 ≤ 1 ⟹ 负对数 ≥ 0）；
  4. `infonce_le_log_card_of_max`：τ > 0 且正样本相似度最大时 InfoNCE ≤ log n
     （softmax_i ≥ 1/n）；
  5. `infonce_le_log_one_add_of_gap`（**核心上界 / 温度效应**）：
     若正样本以间隔 Δ > 0 严格领先（∀ j ≠ i, s_j ≤ s_i − Δ），则
     InfoNCE ≤ log(1 + (n−1)·e^{−Δ/τ})；
     τ → 0 时右端 → log 1 = 0（低温趋近 hard 对齐），τ → ∞ 时右端 → log n（高温趋近均匀）。
     这是「温度越低越接近 hard 目标」的定量刻画；
  6. `infonce_directional_deriv`（**梯度 = (1/τ)(softmax − one-hot)**）：
     沿方向 v 的方向导数
     = (1/τ)·(Σ_j softmax(s/τ)_j·v_j − v_i)（衔接 `softmax_ce_directional_deriv`）。

**诚实边界**（本文件不证 / 不声称的）：

- InfoNCE 的点式下界 **≥ log n 在单点上不成立**（当正样本不是最大相似度时
  softmax_i 可以远小于 1/n）。真实的「InfoNCE ≥ log n」是对**均匀随机正样本的期望**
  成立的下界（NCE 估计量的互信息下界），需要期望/平均的语境；本文件改为给出
  条件性上界（第 4、5 条），这是诚实且可证的版本。
- 第 5 条的间隔假设 `∀ j ≠ i, s_j ≤ s_i − Δ` 是「正样本严格领先」的强假设；
  无间隔时只有第 4 条（需要 `i` 是最大点）。
- 第 6 条给出的是**方向导数 / 梯度作用形式**（对偶配对计为 (1/τ)(softmax − one-hot)），
  未展开 fderiv 的显式线性映射；与 RealCrossEntropy 的 softmax-CE 梯度同型。
- 未做：τ → 0 的极限 `Tendsto`（由第 5 条右端的连续性即可得，但需要 0⁺ 邻域的
  滤子计算，标注为后续）；NCE 估计量与互信息的一致/下界关系。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

/-! ## 定义：InfoNCE -/

/-- InfoNCE 对比损失：−log softmax(s/τ)_i（正样本的负对数 softmax 概率）。 -/
noncomputable def infoNCE {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n) : ℝ :=
  -Real.log (softmax (fun j => s j / τ) i)

/-! ## 桥接与实例化 -/

theorem infonce_eq_neg_log_softmaxTemp {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n) :
    infoNCE s τ i = -Real.log (softmaxTemp s τ i) := by
  rw [infoNCE, softmax_temp_scale]

/-- InfoNCE 是交叉熵的实例：−log softmax_i = CE(onehot_i, softmax s/τ)（`ce_onehot_eq_neg_log`）。 -/
theorem infonce_eq_ce {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n) :
    infoNCE s τ i = crossEntropy (onehot i) (softmax (fun j => s j / τ)) := by
  rw [infoNCE, ce_onehot_eq_neg_log i (softmax (fun j => s j / τ)) (softmax_pos _ i)]

/-! ## 定理一：InfoNCE 非负 -/

theorem infonce_nonneg {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n) :
    0 ≤ infoNCE s τ i := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hpos : 0 < softmax (fun j => s j / τ) i := softmax_pos _ i
  have hle1 : softmax (fun j => s j / τ) i ≤ 1 := by
    have hsum := softmax_sum_one (fun j => s j / τ)
    have hsingle : softmax (fun j => s j / τ) i
        ≤ ∑ j, softmax (fun j => s j / τ) j :=
      Finset.single_le_sum
        (fun j _ => le_of_lt (softmax_pos (fun j => s j / τ) j)) (Finset.mem_univ i)
    linarith
  have hlog : Real.log (softmax (fun j => s j / τ) i) ≤ 0 := by
    have := Real.log_le_log hpos hle1
    rwa [Real.log_one] at this
  rw [infoNCE]
  linarith

/-! ## 定理二：正样本最大 ⟹ InfoNCE ≤ log n -/

theorem infonce_le_log_card_of_max {n : ℕ} (s : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (hτ : 0 < τ) (hmax : ∀ j, s j ≤ s i) :
    infoNCE s τ i ≤ Real.log n := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hden : ∑ j, Real.exp (s j / τ) ≤ (n : ℝ) * Real.exp (s i / τ) := by
    calc ∑ j, Real.exp (s j / τ) ≤ ∑ _j : Fin n, Real.exp (s i / τ) := by
          apply Finset.sum_le_sum
          intro j _
          exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hmax j) (le_of_lt hτ))
      _ = (n : ℝ) * Real.exp (s i / τ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hnumpos : 0 < Real.exp (s i / τ) := Real.exp_pos _
  have hdenpos : 0 < ∑ j, Real.exp (s j / τ) := softmax_denom_pos _
  have hfrac : 1 / (n : ℝ) ≤ softmax (fun j => s j / τ) i := by
    show 1 / (n : ℝ) ≤ Real.exp (s i / τ) / ∑ j, Real.exp (s j / τ)
    rw [div_le_div_iff₀ hnpos hdenpos]
    simpa [mul_comm] using hden
  have hlog := Real.log_le_log (div_pos one_pos hnpos) hfrac
  have h1n : Real.log (1 / (n : ℝ)) = -Real.log n := by
    rw [one_div, Real.log_inv]
  rw [infoNCE]
  linarith

/-! ## 定理三（核心）：间隔单调 —— InfoNCE ≤ log(1 + (n−1)e^{−Δ/τ})

正样本以间隔 Δ > 0 严格领先时，softmax_i ≥ 1/(1 + (n−1)e^{−Δ/τ})，
取负对数给出上界 log(1 + (n−1)e^{−Δ/τ})。
τ → 0 时 → 0（低温 hard 对齐），τ → ∞ 时 → log n（高温均匀）。 -/

theorem infonce_le_log_one_add_of_gap {n : ℕ} (s : Fin n → ℝ) (τ Δ : ℝ) (i : Fin n)
    (hτ : 0 < τ) (_hΔ : 0 < Δ) (hgap : ∀ j, j ≠ i → s j ≤ s i - Δ) :
    infoNCE s τ i ≤ Real.log (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ))) := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hn1 : 1 ≤ n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- 擦除 i 后的和的上界
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have herase : ∑ j in Finset.univ.erase i, Real.exp (s j / τ)
      ≤ ((n : ℝ) - 1) * (Real.exp (s i / τ) * Real.exp (-(Δ / τ))) := by
    calc ∑ j in Finset.univ.erase i, Real.exp (s j / τ)
        ≤ ∑ _j in Finset.univ.erase i,
            (Real.exp (s i / τ) * Real.exp (-(Δ / τ))) := by
          apply Finset.sum_le_sum
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          have hle : s j ≤ s i - Δ := hgap j hji
          have h1 : s j / τ ≤ (s i - Δ) / τ := div_le_div_of_nonneg_right hle (le_of_lt hτ)
          have h2 : (s i - Δ) / τ = s i / τ + (-(Δ / τ)) := by ring
          calc Real.exp (s j / τ) ≤ Real.exp (s i / τ + (-(Δ / τ))) :=
                Real.exp_le_exp.mpr (by rw [← h2]; exact h1)
            _ = Real.exp (s i / τ) * Real.exp (-(Δ / τ)) := Real.exp_add _ _
      _ = ((n : ℝ) - 1) * (Real.exp (s i / τ) * Real.exp (-(Δ / τ))) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul, hcast]
  -- 分母 Z 的上界
  have hZeq : ∑ j, Real.exp (s j / τ)
      = Real.exp (s i / τ) + ∑ j in Finset.univ.erase i, Real.exp (s j / τ) := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => Real.exp (s j / τ)) (Finset.mem_univ i),
      add_comm]
  have hZle : ∑ j, Real.exp (s j / τ)
      ≤ Real.exp (s i / τ) * (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ))) := by
    rw [hZeq]
    calc Real.exp (s i / τ) + ∑ j in Finset.univ.erase i, Real.exp (s j / τ)
        ≤ Real.exp (s i / τ)
          + ((n : ℝ) - 1) * (Real.exp (s i / τ) * Real.exp (-(Δ / τ))) :=
          add_le_add_left herase _
      _ = Real.exp (s i / τ) * (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ))) := by ring
  -- 倒数下界
  have hDpos : 0 < 1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ)) := by
    have h0 : 0 ≤ ((n : ℝ) - 1) * Real.exp (-(Δ / τ)) :=
      mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
    linarith
  have hnumpos : 0 < Real.exp (s i / τ) := Real.exp_pos _
  have hdenpos : 0 < ∑ j, Real.exp (s j / τ) := softmax_denom_pos _
  have hfrac : 1 / (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ)))
      ≤ softmax (fun j => s j / τ) i := by
    show 1 / (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ)))
      ≤ Real.exp (s i / τ) / ∑ j, Real.exp (s j / τ)
    rw [div_le_div_iff₀ hDpos hdenpos]
    simpa using hZle
  have hlog := Real.log_le_log (div_pos one_pos hDpos) hfrac
  have h1D : Real.log (1 / (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ))))
      = -Real.log (1 + ((n : ℝ) - 1) * Real.exp (-(Δ / τ))) := by
    rw [one_div, Real.log_inv]
  rw [infoNCE]
  linarith

/-! ## 定理四（核心）：梯度 = (1/τ)(softmax − one-hot)

沿方向 v 的方向导数。路线：把 `(s_j + t·v_j)/τ` 写成 `s_j/τ + t·(v_j/τ)`，
套 RealCrossEntropy.softmax_ce_directional_deriv（logits u = s/τ、方向 w = v/τ），
最后把系数 1/τ 提出。 -/

theorem infonce_directional_deriv {n : ℕ} (s v : Fin n → ℝ) (τ : ℝ) (i : Fin n)
    (_hτ : τ ≠ 0) :
    deriv (fun t : ℝ => -Real.log (softmax (fun j => (s j + t * v j) / τ) i)) 0
      = (1 / τ) * ((∑ j, softmax (fun j => s j / τ) j * v j) - v i) := by
  have hfun : (fun t : ℝ => -Real.log (softmax (fun j => (s j + t * v j) / τ) i))
      = (fun t : ℝ => -Real.log (softmax (fun j => s j / τ + t * (v j / τ)) i)) := by
    funext t
    have h : (fun j : Fin n => (s j + t * v j) / τ)
        = (fun j : Fin n => s j / τ + t * (v j / τ)) := by
      funext j
      ring
    rw [h]
  have hkey : (fun t : ℝ => -Real.log (softmax (fun j => s j / τ + t * (v j / τ)) i))
      = (fun t : ℝ => -Real.log
          (softmax ((fun j : Fin n => s j / τ) + t • (fun j : Fin n => v j / τ)) i)) := by
    funext t
    have h : (fun j : Fin n => s j / τ + t * (v j / τ))
        = ((fun j : Fin n => s j / τ) + t • (fun j : Fin n => v j / τ)) := by
      funext j
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
  rw [hfun, hkey, softmax_ce_directional_deriv (fun j => s j / τ) (fun j => v j / τ) i]
  have hsum : (∑ j, softmax (fun j => s j / τ) j * (v j / τ))
      = (∑ j, softmax (fun j => s j / τ) j * v j) / τ := by
    have hcong : (∑ j, softmax (fun j => s j / τ) j * (v j / τ))
        = ∑ j, (softmax (fun j => s j / τ) j * v j) / τ :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [hcong, ← Finset.sum_div]
  rw [hsum, ← sub_div, div_eq_mul_inv]
  ring

end Lattice
