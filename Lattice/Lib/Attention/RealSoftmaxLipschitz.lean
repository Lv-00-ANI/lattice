import Mathlib
import Lattice.Lib.Optim.RealValueIteration
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: softmax Lipschitz —— attention 组件常数收官（块界闭式）

RealBlockLipschitz（块界 Lf·(1+La+Lg)）最后的 open 假设：
**softmax 的输入-Lipschitz**（连续可微的推论，此处直接证明）。

  1. exp 有界域 Lipschitz：exp 在 (-∞, M] 上是 exp(M)-Lipschitz
     （一维 MVT：norm_image_sub_le_of_norm_deriv_le，deriv exp = exp ≤ exp M）；
  2. 分数差分解：|a/c − b/d| ≤ |a−b|/c + |b|·|c−d|/(c·d)（c,d > 0，
     把 softmax 差分解为「分子差 + 分母差」两项）；
  3. softmax 坐标 Lipschitz：|softmax(x)ᵢ − softmax(y)ᵢ| ≤ (n+1)·e^{4M}·‖x−y‖∞
     （有界输入 [-M,M]；exp Lipschitz + 分母下界 Z ≥ e^{−M} +
     和差界 |Z(x)−Z(y)| ≤ n·e^{M}·‖x−y‖∞）。

实例化（块界）：完整 attention（softmax 权重 + 凸组合）的 Lipschitz
= softmax 输入-Lipschitz（本文件）组合 convComb_lipschitz_prob
（权重固定版）——attention 层常数 La 完全闭式，块界 Lf·(1+La+Lg)
全组件常数齐备。

模型无关：任意指标数 n、有界输入（[-M,M]，数据范围假设）。
-/

noncomputable section

namespace Lattice

/-! ## 定理一：exp 有界域 Lipschitz
exp 在 (-∞, M] 上是 exp(M)-Lipschitz：|e^a − e^b| ≤ e^M·|a−b|（a,b ≤ M）。-/

theorem exp_lipschitz_on (M a b : ℝ) (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  -- 一维 MVT：exp 在 Iic M 上可导，导数 |exp x| = exp x ≤ exp M
  have hf : ∀ x : ℝ, x ∈ Set.Iic M → DifferentiableAt ℝ Real.exp x := by
    intro x hx
    exact (Real.differentiableAt_exp : DifferentiableAt ℝ Real.exp x)
  have hbound : ∀ x : ℝ, x ∈ Set.Iic M → ‖deriv Real.exp x‖ ≤ Real.exp M := by
    intro x hx
    rw [Real.deriv_exp]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt (Real.exp_pos x))]
    exact Real.exp_le_exp.mpr hx
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Iic M) hf hbound (convex_Iic M) ha hb
  -- |exp b − exp a| ≤ exp M·|b−a| ⟹ 目标
  simpa [abs_sub_comm] using hmvt

/-! ## 引理：分数差分解
|a/c − b/d| ≤ |a−b|/c + |b|·|c−d|/(c·d)（c,d > 0）。-/

lemma abs_div_sub (a b c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    |a / c - b / d| ≤ |a - b| / c + |b| * |c - d| / (c * d) := by
  -- a/c − b/d = (a−b)/c + b·(d−c)/(c·d)
  have hcalc : a / c - b / d = (a - b) / c + b * (d - c) / (c * d) := by
    field_simp [ne_of_gt hc, ne_of_gt hd]
    ring
  have hpos : 0 < c * d := mul_pos hc hd
  calc
    |a / c - b / d| = |(a - b) / c + b * (d - c) / (c * d)| := by rw [hcalc]
    _ ≤ |(a - b) / c| + |b * (d - c) / (c * d)| := abs_add _ _
    _ = |a - b| / c + |b| * |c - d| / (c * d) := by
          rw [abs_div, abs_div, abs_mul]
          rw [abs_of_pos hc, abs_of_pos hpos]
          -- |b·(d−c)| 已在前一步 abs_mul 展开；只需 |d−c| = |c−d|（rw 后目标即 rfl）
          rw [abs_sub_comm d c]

/-! ## 注：softmax 完整 Lipschitz 的组件基础
  exp_lipschitz_on（exp 有界域 Lipschitz）+ abs_div_sub（分数差分解）
  + Z 的上下界（Z ≥ e^{−M}、|Z(x)−Z(y)| ≤ n·e^M·‖x−y‖∞）⟹
  softmax 坐标 Lipschitz（下一步，本文件继续）。-/

/-! ## 引理：softmax 分母上界
Z(x) = Σe^{x_j} ≤ n·e^M（x_j ≤ M）。-/

lemma z_bound_upper {n : ℕ} (M : ℝ) (x : Fin n → ℝ) (hx : ∀ j : Fin n, x j ≤ M) :
    (∑ j : Fin n, Real.exp (x j)) ≤ n * Real.exp M := by
  calc
    (∑ j : Fin n, Real.exp (x j)) ≤ ∑ j : Fin n, Real.exp M := by
          apply Finset.sum_le_sum
          intro j hj
          exact Real.exp_le_exp.mpr (hx j)
    _ = n * Real.exp M := by simp [Finset.sum_const]

/-! ## 引理：softmax 分母下界
Z(x) ≥ e^{−M}（x_j ≥ −M，需非空指标）。-/

lemma z_bound_lower {n : ℕ} [NeZero n] (M : ℝ) (x : Fin n → ℝ) (hx : ∀ j : Fin n, -M ≤ x j) :
    Real.exp (-M) ≤ ∑ j : Fin n, Real.exp (x j) := by
  rcases (Fin.pos_iff_nonempty.mp (NeZero.pos n)) with ⟨j₀⟩
  calc
    Real.exp (-M) ≤ Real.exp (x j₀) := Real.exp_le_exp.mpr (hx j₀)
    _ ≤ ∑ j : Fin n, Real.exp (x j) := by
          exact Finset.single_le_sum (by intro j hj; exact le_of_lt (Real.exp_pos (x j))) (Finset.mem_univ j₀)

/-! ## 引理：softmax 分母差界
|Z(x) − Z(y)| ≤ n·e^M·‖x−y‖∞（x_j, y_j ≤ M）。-/

lemma z_diff_bound {n : ℕ} (M : ℝ) (x y : Fin n → ℝ)
    (hx : ∀ j : Fin n, x j ≤ M) (hy : ∀ j : Fin n, y j ≤ M) :
    |(∑ j : Fin n, Real.exp (x j)) - (∑ j : Fin n, Real.exp (y j))|
      ≤ n * Real.exp M * LinfNorm (x - y) := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin n, (Real.exp (x j) - Real.exp (y j))|
        ≤ ∑ j : Fin n, |Real.exp (x j) - Real.exp (y j)| :=
          Finset.abs_sum_le_sum_abs (fun j : Fin n => Real.exp (x j) - Real.exp (y j)) Finset.univ
    _ ≤ ∑ j : Fin n, Real.exp M * |x j - y j| := by
          apply Finset.sum_le_sum
          intro j hj
          exact exp_lipschitz_on M (x j) (y j) (hx j) (hy j)
    _ ≤ ∑ j : Fin n, Real.exp M * LinfNorm (x - y) := by
          apply Finset.sum_le_sum
          intro j hj
          have hz : |x j - y j| = |(x - y) j| := by rfl
          rw [hz]
          exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_abs (x - y)) (by exact ⟨j, rfl⟩)) (le_of_lt (Real.exp_pos M))
    _ = n * (Real.exp M * LinfNorm (x - y)) := by simp [Finset.sum_const]
    _ = n * Real.exp M * LinfNorm (x - y) := by ring

/-! ## 定理二：softmax 坐标 Lipschitz
|softmax(x)ᵢ − softmax(y)ᵢ| ≤ (n+1)·e^{4M}·‖x−y‖∞（有界输入 [-M,M]，M ≥ 0）。-/

theorem softmax_lipschitz_coord {n : ℕ} [NeZero n] (M : ℝ) (x y : Fin n → ℝ)
    (hM : 0 ≤ M) (hx : ∀ i : Fin n, -M ≤ x i ∧ x i ≤ M)
    (hy : ∀ i : Fin n, -M ≤ y i ∧ y i ≤ M) (i : Fin n) :
    |softmax x i - softmax y i| ≤ (n + 1) * Real.exp (4 * M) * LinfNorm (x - y) := by
  -- softmax_denom_pos 需要 [Nonempty (Fin n)]（由元素 i 提供）
  haveI : Nonempty (Fin n) := ⟨i⟩
  -- 分母
  have hZx : 0 < (∑ j : Fin n, Real.exp (x j)) := softmax_denom_pos x
  have hZy : 0 < (∑ j : Fin n, Real.exp (y j)) := softmax_denom_pos y
  -- 分解：|a/Zx − b/Zy| ≤ |a−b|/Zx + |b|·|Zx−Zy|/(Zx·Zy)（abs_div_sub 首项分母是 Zx）
  have hdec := abs_div_sub (Real.exp (x i)) (Real.exp (y i))
    (∑ j : Fin n, Real.exp (x j)) (∑ j : Fin n, Real.exp (y j)) hZx hZy
  -- 分母下界：1/Z ≤ e^M（Z ≥ e^{−M}）
  have hZx_low : Real.exp (-M) ≤ ∑ j : Fin n, Real.exp (x j) :=
    z_bound_lower M x (fun j => (hx j).1)
  have hZy_low : Real.exp (-M) ≤ ∑ j : Fin n, Real.exp (y j) :=
    z_bound_lower M y (fun j => (hy j).1)
  -- 通用：对任意有下界 z（−M ≤ z_j），1/Z(z) ≤ e^M
  have h1gen : ∀ z : Fin n → ℝ, (∀ j, -M ≤ z j) → 1 / (∑ j : Fin n, Real.exp (z j)) ≤ Real.exp M := by
    intro z hz
    -- 1/Z ≤ e^M ⟺ 1 ≤ e^M·Z ⟺ Z ≥ e^{−M}（交叉乘正，分母为 Z）
    have hzpos : 0 < ∑ j : Fin n, Real.exp (z j) := softmax_denom_pos z
    have hzlow : Real.exp (-M) ≤ ∑ j : Fin n, Real.exp (z j) := z_bound_lower M z hz
    have hpos : 0 < Real.exp M := Real.exp_pos M
    rw [div_le_iff₀ hzpos]  -- 1/Z ≤ e^M ⟺ 1 ≤ e^M·Z
    have hle : Real.exp M * Real.exp (-M) ≤ Real.exp M * (∑ j : Fin n, Real.exp (z j)) :=
      mul_le_mul_of_nonneg_left hzlow (le_of_lt hpos)
    -- e^M·e^{−M} = 1
    have hone : Real.exp M * Real.exp (-M) = 1 := by
      rw [← Real.exp_add]
      simp
    rwa [hone] at hle
  have h1x : 1 / (∑ j : Fin n, Real.exp (x j)) ≤ Real.exp M :=
    h1gen x (fun j => (hx j).1)
  -- 组合
  calc
    |softmax x i - softmax y i|
        = |Real.exp (x i) / (∑ j : Fin n, Real.exp (x j))
            - Real.exp (y i) / (∑ j : Fin n, Real.exp (y j))| := by
          rfl
    _ ≤ |Real.exp (x i) - Real.exp (y i)| / (∑ j : Fin n, Real.exp (x j))
        + |Real.exp (y i)| * |(∑ j : Fin n, Real.exp (x j)) - (∑ j : Fin n, Real.exp (y j))|
          / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j))) := hdec
    _ ≤ (Real.exp M * |x i - y i|) / (∑ j : Fin n, Real.exp (x j))
        + (Real.exp M) * (n * Real.exp M * LinfNorm (x - y))
          / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j))) := by
          -- exp Lipschitz；|Zx−Zy| ≤ n·e^M·Linf（z_diff_bound 直接给出）
          have hzdiff : |(∑ j : Fin n, Real.exp (x j)) - (∑ j : Fin n, Real.exp (y j))|
              ≤ n * Real.exp M * LinfNorm (x - y) :=
            z_diff_bound M x y (fun j => (hx j).2) (fun j => (hy j).2)
          have hb1 : |Real.exp (y i)| ≤ Real.exp M := by
            rw [abs_of_nonneg (le_of_lt (Real.exp_pos (y i)))]
            exact Real.exp_le_exp.mpr (hy i).2
          exact add_le_add
            (div_le_div_of_nonneg_right (exp_lipschitz_on M (x i) (y i) (hx i).2 (hy i).2) (le_of_lt hZx))
            (by
              have hprod : 0 < (∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)) :=
                mul_pos hZx hZy
              have hmul : |Real.exp (y i)| * |(∑ j : Fin n, Real.exp (x j)) - (∑ j : Fin n, Real.exp (y j))|
                  ≤ Real.exp M * (n * Real.exp M * LinfNorm (x - y)) := by
                exact mul_le_mul hb1 hzdiff (abs_nonneg _) (by positivity)
              exact div_le_div_of_nonneg_right hmul (le_of_lt hprod))
    _ ≤ (Real.exp M * LinfNorm (x - y)) / (∑ j : Fin n, Real.exp (x j))
        + (Real.exp M) * (n * Real.exp M * LinfNorm (x - y))
          / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j))) := by
          -- |x_i − y_i| ≤ LinfNorm
          have hz : |x i - y i| ≤ LinfNorm (x - y) := by
            have hz' : |x i - y i| = |(x - y) i| := by rfl
            rw [hz']
            exact le_csSup (bddAbove_abs (x - y)) (by exact ⟨i, rfl⟩)
          exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (le_of_lt (Real.exp_pos M))) (le_of_lt hZx)) le_rfl
    _ ≤ (n + 1) * Real.exp (4 * M) * LinfNorm (x - y) := by
          -- 两项上界：第一项 ≤ e^{2M}·Linf；第二项 ≤ n·e^{4M}·Linf
          have hterm1 : (Real.exp M * LinfNorm (x - y)) / (∑ j : Fin n, Real.exp (x j))
              ≤ Real.exp M * Real.exp M * LinfNorm (x - y) := by
            -- (e^M·L)/Z ≤ e^M·L·(1/Z) ≤ e^M·L·e^M
            calc
              (Real.exp M * LinfNorm (x - y)) / (∑ j : Fin n, Real.exp (x j))
                  = Real.exp M * LinfNorm (x - y) * (1 / (∑ j : Fin n, Real.exp (x j))) := by ring
              _ ≤ Real.exp M * LinfNorm (x - y) * Real.exp M := by
                    exact mul_le_mul_of_nonneg_left h1x (mul_nonneg (le_of_lt (Real.exp_pos M)) (linfNorm_nonneg _))
              _ = Real.exp M * Real.exp M * LinfNorm (x - y) := by ring
          -- 第二项：e^M·(n e^M L)/(Zx Zy) ≤ n·e^{4M}·L（1/(Zx Zy) ≤ e^{2M}）
          have hZxy_low : Real.exp (-2 * M) ≤
              (∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)) := by
            -- Zx·Zy ≥ e^{−M}·e^{−M} = e^{−2M}（mul_le_mul：0 ≤ c、0 ≤ b 分别用两因子）
            have hprod_le : Real.exp (-M) * Real.exp (-M) ≤
                (∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)) :=
              mul_le_mul hZx_low hZy_low (le_of_lt (Real.exp_pos (-M))) (le_of_lt hZx)
            -- e^{−M}·e^{−M} = e^{−2M}
            have hone : Real.exp (-M) * Real.exp (-M) = Real.exp (-2 * M) := by
              rw [← Real.exp_add]
              ring
            rwa [hone] at hprod_le
          have h2 : 1 / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j))) ≤ Real.exp (2 * M) := by
            have hpos : 0 < Real.exp (2 * M) := Real.exp_pos (2 * M)
            have hdenpos : 0 < (∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)) := mul_pos hZx hZy
            rw [div_le_iff₀ hdenpos]
            have hle : Real.exp (2 * M) * Real.exp (-2 * M)
                ≤ Real.exp (2 * M) * ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j))) :=
              mul_le_mul_of_nonneg_left hZxy_low (le_of_lt hpos)
            have hone : Real.exp (2 * M) * Real.exp (-2 * M) = 1 := by
              rw [← Real.exp_add]
              simp
            rwa [hone] at hle
          have hterm2 : (Real.exp M) * (n * Real.exp M * LinfNorm (x - y))
              / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)))
              ≤ n * Real.exp (4 * M) * LinfNorm (x - y) := by
            -- = e^M·n·e^M·L·(1/(ZxZy)) ≤ n·e^{2M}·L·e^{2M} = n·e^{4M}·L
            calc
              (Real.exp M) * (n * Real.exp M * LinfNorm (x - y))
                  / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)))
                  = n * (Real.exp M * Real.exp M * LinfNorm (x - y))
                      * (1 / ((∑ j : Fin n, Real.exp (x j)) * (∑ j : Fin n, Real.exp (y j)))) := by ring
              _ ≤ n * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M) := by
                    exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg n)
                      (mul_nonneg (mul_nonneg (le_of_lt (Real.exp_pos M)) (le_of_lt (Real.exp_pos M))) (linfNorm_nonneg _)))
              _ ≤ n * Real.exp (4 * M) * LinfNorm (x - y) := by
                    -- e^M·e^M·e^{2M} = e^{4M}（M ≥ 0 不需要——指数相加）
                    have hone : Real.exp M * Real.exp M * Real.exp (2 * M) = Real.exp (4 * M) := by
                      rw [← Real.exp_add, ← Real.exp_add]
                      ring
                    have hA : n * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M)
                        = n * Real.exp (4 * M) * LinfNorm (x - y) := by
                      calc
                        n * (Real.exp M * Real.exp M * LinfNorm (x - y)) * Real.exp (2 * M)
                            = n * (Real.exp M * Real.exp M * Real.exp (2 * M)) * LinfNorm (x - y) := by ring
                        _ = n * Real.exp (4 * M) * LinfNorm (x - y) := by rw [hone]
                    exact le_of_eq hA
          -- 第一项 ≤ e^{2M}·L ≤ e^{4M}·L（M ≥ 0 ⟹ 2M ≤ 4M）
          have hterm1' : Real.exp M * Real.exp M * LinfNorm (x - y) ≤ Real.exp (4 * M) * LinfNorm (x - y) := by
            have hle : Real.exp M * Real.exp M ≤ Real.exp (4 * M) := by
              -- e^{2M} ≤ e^{4M}（2M ≤ 4M，M ≥ 0）
              have h2M : 2 * M ≤ 4 * M := by nlinarith [hM]
              have hpow : Real.exp M * Real.exp M = Real.exp (2 * M) := by
                rw [← Real.exp_add]
                ring
              rw [hpow]
              exact Real.exp_le_exp.mpr h2M
            exact mul_le_mul_of_nonneg_right hle (linfNorm_nonneg _)
          nlinarith [hterm1, hterm1', hterm2]
