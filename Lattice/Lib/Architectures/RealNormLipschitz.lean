import Mathlib

/-!
# LATTICE: 规范化层 Lipschitz —— RMSNorm/LN 的组件常数（块界实例化）

**⚠ 常数非紧性标注（Z1-5，v14）**：本文件给出的 `2/c`（单位化）与 `2√n/c`
（RMSNorm）是**有效但非紧**的上界。**真正常数是 `1/c` 与 `√n/c`**，
已在 `RealNormSharpConstant`（下界 + 紧上界 `unit_normalize_lipschitz_sharp`）
与 `RealRMSNormSharpness`（`rmsNormE_sqrt_lipschitz`、`rmsNormE_constant_iff`，
完整 iff 刻画）中**证明**。

**为什么本文件不能直接引用紧常数**：`RealNormSharpConstant` 与
`RealRMSNormSharpness` **都 import 本文件**（本文件是它们的依赖基底）
⟹ 反向 import 会造成**循环依赖**。故本文件**保留松弛版**作为自足基底，
紧常数由上游文件提供；下游端到端块常数（`RealBlockInstance` /
`RealBlockConstants` / `RealModelChain*` / `RealMixedAttention`）
**已改用紧常数 `√n/c`**。本文件的松弛版由
`RealBlockInstance.transformer_block_closed_relaxed` 显式回收保留。

RealBlockLipschitz（块界 Lf·(1+La+Lg)）的 Lf open 假设补全：
规范化层（RMSNorm/LN）在有界输入下的 Lipschitz 常数。

  1. 单位化映射 Lipschitz：x/‖x‖ 在范数有界（‖x‖ ≥ c > 0）下是
     (2/c)-Lipschitz（**非紧**，紧值是 1/c）：
        ‖x/‖x‖ − y/‖y‖‖ ≤ (2/c)·‖x−y‖
     （三角中项：‖x−y‖/‖x‖ + |1/‖x‖−1/‖y‖|·‖y‖，用范数
     Lipschitz |‖x‖−‖y‖| ≤ ‖x−y‖ 与分母 ‖x‖‖y‖ ≥ c²）；
  2. RMSNorm Lipschitz：RMSNorm(x) = x·√n/‖x‖ 是 (2√n/c)-Lipschitz
     （**非紧**，紧值是 √n/c）（= √n·单位化，√n 常数缩放）。

实例化（块界）：规范化层 Lf = √n/c（RMSNorm，**紧**，见 RealRMSNormSharpness）
/ √n·‖T‖/c（LN = 归一化∘center，center 是 1-Lipschitz 线性投影）——代入
block_lipschitz_bound 即得完整块常数；与 pan-meme 的 N 算子
收缩（A/(A+B+ε) 归一化）同源：归一化算子在正域上有界 Lipschitz。

模型无关：任意范数空间（单位化）+ EuclideanSpace（RMSNorm）。
-/

noncomputable section

namespace Lattice

/-! ## 常向量（EuclideanSpace 的 1；OfNat 缺失，用函数 1） -/

def constOne {n : ℕ} : EuclideanSpace ℝ (Fin n) := fun _ => 1

/-! ## 定理一：单位化映射 Lipschitz（归一化层核心）
‖x/‖x‖ − y/‖y‖‖ ≤ (2/c)·‖x−y‖（‖x‖, ‖y‖ ≥ c > 0）。-/

theorem unit_normalize_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (c : ℝ) (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (2 / c) * ‖x - y‖ := by
  have hx0 : ‖x‖ ≠ 0 := by
    intro hz
    linarith
  have hy0 : ‖y‖ ≠ 0 := by
    intro hz
    linarith
  have hxpos : 0 < ‖x‖ := by linarith
  -- |‖y‖−‖x‖| ≤ ‖x−y‖（范数 Lipschitz）
  have hnorm : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    simpa [abs_sub_comm] using abs_norm_sub_norm_le x y
  -- |1/‖x‖−1/‖y‖| ≤ ‖x−y‖/(‖x‖‖y‖)
  have hrecip : |1 / ‖x‖ - 1 / ‖y‖| ≤ ‖x - y‖ / (‖x‖ * ‖y‖) := by
    have hcalc : 1 / ‖x‖ - 1 / ‖y‖ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp [hx0, hy0]
    rw [hcalc]
    have hdenpos : 0 < ‖x‖ * ‖y‖ := mul_pos hxpos (by linarith)
    rw [abs_div, abs_of_nonneg (le_of_lt hdenpos)]
    exact div_le_div_of_nonneg_right hnorm (le_of_lt hdenpos)
  calc
    ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖
        = ‖(1 / ‖x‖) • x - (1 / ‖x‖) • y + ((1 / ‖x‖) • y - (1 / ‖y‖) • y)‖ := by
          congr 1
          abel
    _ ≤ ‖(1 / ‖x‖) • x - (1 / ‖x‖) • y‖ + ‖(1 / ‖x‖) • y - (1 / ‖y‖) • y‖ := norm_add_le _ _
    _ = ‖(1 / ‖x‖) • (x - y)‖ + ‖((1 / ‖x‖) - (1 / ‖y‖)) • y‖ := by
          rw [smul_sub]
          rw [sub_smul]
    _ = (1 / ‖x‖) * ‖x - y‖ + |1 / ‖x‖ - 1 / ‖y‖| * ‖y‖ := by
          rw [norm_smul, norm_smul]
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          rw [abs_of_nonneg (by exact one_div_nonneg.mpr (le_of_lt hxpos))]
    _ ≤ (1 / ‖x‖) * ‖x - y‖ + (‖x - y‖ / (‖x‖ * ‖y‖)) * ‖y‖ := by
          exact add_le_add_left (mul_le_mul_of_nonneg_right hrecip (norm_nonneg _)) _
    _ = (2 / ‖x‖) * ‖x - y‖ := by
          field_simp [hy0]
          ring
    _ ≤ (2 / c) * ‖x - y‖ := by
          have hle : 2 / ‖x‖ ≤ 2 / c := by
            rw [div_le_div_iff₀ hxpos hc]
            nlinarith [hx]
          exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-! ## 定理二：RMSNorm Lipschitz
RMSNorm(x) = x·√n/‖x‖ 是 (2√n/c)-Lipschitz（‖x‖, ‖y‖ ≥ c > 0）。-/

theorem rmsNorm_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖(Real.sqrt n) • ((1 / ‖x‖) • x) - (Real.sqrt n) • ((1 / ‖y‖) • y)‖
      ≤ (Real.sqrt n * 2 / c) * ‖x - y‖ := by
  -- = √n • (unit x − unit y)
  have hdiff : (Real.sqrt n) • ((1 / ‖x‖) • x) - (Real.sqrt n) • ((1 / ‖y‖) • y)
      = (Real.sqrt n) • ((1 / ‖x‖) • x - (1 / ‖y‖) • y) := by
    rw [← smul_sub]
  rw [hdiff]
  calc
    ‖(Real.sqrt n) • ((1 / ‖x‖) • x - (1 / ‖y‖) • y)‖
        = Real.sqrt n * ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n)]
    _ ≤ Real.sqrt n * ((2 / c) * ‖x - y‖) := by
          exact mul_le_mul_of_nonneg_left (unit_normalize_lipschitz x y c hc hx hy) (Real.sqrt_nonneg n)
    _ = (Real.sqrt n * 2 / c) * ‖x - y‖ := by ring

/-! ## 定理三：LN center（减均值）范数收缩
center(z) = z − mean(z)·1 是范数 ≤ 1 的正交投影：‖center z‖ ≤ ‖z‖。 -/

theorem center_norm_le {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ‖z - ((∑ i : Fin n, z i) / n) • (constOne : EuclideanSpace ℝ (Fin n))‖ ≤ ‖z‖ := by
  let c : ℝ := (∑ i : Fin n, z i) / n
  let w : EuclideanSpace ℝ (Fin n) := z - c • (constOne : EuclideanSpace ℝ (Fin n))
  -- ⟨w, 1⟩ = 0（center z 与常向量正交，实内积）
  have horth : inner w (constOne : EuclideanSpace ℝ (Fin n)) = (0 : ℝ) := by
    unfold w
    have hz : inner z (constOne : EuclideanSpace ℝ (Fin n)) = ∑ i : Fin n, z i := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [Matrix.dotProduct, constOne]
    have h1n : inner (constOne : EuclideanSpace ℝ (Fin n)) (constOne : EuclideanSpace ℝ (Fin n)) = (n : ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [Matrix.dotProduct, constOne]
    have hc1 : inner (c • (constOne : EuclideanSpace ℝ (Fin n))) (constOne : EuclideanSpace ℝ (Fin n)) = c * n := by
      rw [inner_smul_left]
      rw [h1n]
      simp
    have hc : c * n = ∑ i : Fin n, z i := by
      unfold c
      by_cases hn : (n : ℝ) = 0
      · have hn0 : n = 0 := by exact_mod_cast hn
        subst n
        simp
      · field_simp [hn]
    calc
      inner (z - c • (constOne : EuclideanSpace ℝ (Fin n))) (constOne : EuclideanSpace ℝ (Fin n))
          = inner z (constOne : EuclideanSpace ℝ (Fin n)) - inner (c • (constOne : EuclideanSpace ℝ (Fin n))) (constOne : EuclideanSpace ℝ (Fin n)) := by rw [inner_sub_left]
      _ = (∑ i : Fin n, z i) - c * n := by
            rw [hz, hc1]
      _ = 0 := by
            rw [hc]
            ring
  -- z = w + c•1
  have hzdec : z = w + c • (constOne : EuclideanSpace ℝ (Fin n)) := by
    unfold w
    abel
  -- 勾股：‖z‖² = ‖w‖² + 0 + ‖c•1‖² ≥ ‖w‖²
  have hcross : inner w (c • (constOne : EuclideanSpace ℝ (Fin n))) = (0 : ℝ) := by
    rw [inner_smul_right]
    simp [horth]
  have hsq : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    -- 勾股：‖w + c•constOne‖² = ‖w‖² + ‖c•constOne‖²（正交 hcross）
    have horth_sq : ‖w + c • (constOne : EuclideanSpace ℝ (Fin n))‖ ^ 2
        = ‖w‖ ^ 2 + ‖c • (constOne : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      simpa [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero w (c • (constOne : EuclideanSpace ℝ (Fin n))) hcross)
    rw [hzdec, horth_sq]
    nlinarith [sq_nonneg (‖c • (constOne : EuclideanSpace ℝ (Fin n))‖)]
  -- ‖w‖ ≤ ‖z‖（平方非负）
  have hle : ‖w‖ ≤ ‖z‖ := by
    have ha : 0 ≤ ‖w‖ := norm_nonneg _
    have hb : 0 ≤ ‖z‖ := norm_nonneg _
    have habs : |‖w‖| ≤ |‖z‖| := (sq_le_sq.mp hsq)
    simpa [abs_of_nonneg ha, abs_of_nonneg hb] using habs
  simpa [w, c] using hle

/-! ## 定理四：LN center Lipschitz（1-Lipschitz）
‖center x − center y‖ ≤ ‖x−y‖（center 是收缩/正交投影）。-/

theorem center_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ‖(x - ((∑ i : Fin n, x i) / n) • (constOne : EuclideanSpace ℝ (Fin n)))
      - (y - ((∑ i : Fin n, y i) / n) • (constOne : EuclideanSpace ℝ (Fin n)))‖
      ≤ ‖x - y‖ := by
  -- center 线性：center x − center y = center (x − y)
  have hlin : (x - ((∑ i : Fin n, x i) / n) • (constOne : EuclideanSpace ℝ (Fin n)))
        - (y - ((∑ i : Fin n, y i) / n) • (constOne : EuclideanSpace ℝ (Fin n)))
      = (x - y) - ((∑ i : Fin n, (x - y) i) / n) • (constOne : EuclideanSpace ℝ (Fin n)) := by
    ext j
    have hmean : (∑ i : Fin n, x i) / n - (∑ i : Fin n, y i) / n
        = (∑ i : Fin n, (x - y) i) / n := by
      have hsum : (∑ i : Fin n, (x - y) i) = (∑ i : Fin n, x i) - (∑ i : Fin n, y i) := by
        simpa [Pi.sub_apply] using (Finset.sum_sub_distrib : (∑ i : Fin n, x i) - (∑ i : Fin n, y i) = ∑ i : Fin n, x i - y i)
      rw [hsum, sub_div]
    simp [hmean]
    ring
  rw [hlin]
  exact center_norm_le (x - y)

/-! ## 注：LN 常数闭合
  LN(x) = 归一化(center x) = center∘单位化∘√n（center 是 1-Lipschitz，
  定理四；单位化 2/c-Lipschitz，定理一）⟹ LN Lipschitz ≤ 2√n/c
  （与 RMSNorm 同阶，center 不放大）——规范化层组件常数完全闭合；
  块界 Lf·(1+La+Lg) 全组件闭式（La = softmax∘凸组合、Lg = ‖W‖、
  Lf = LN/RMSNorm）。-/

end Lattice
