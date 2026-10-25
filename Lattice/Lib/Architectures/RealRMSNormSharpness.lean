import Mathlib
import Lattice.Lib.Architectures.RealNormSharpConstant
import Lattice.Lib.Architectures.RealNormLipschitz
import Lattice.Lib.Architectures.RealRMSNorm
/-!
# LATTICE: RMSNorm 的**紧** Lipschitz 常数 √n/c（补 RealNormSharpConstant 缺的上半）

`RealNormLipschitz` 给出保守上界 (2√n/c)；`RealNormSharpConstant` 只给出
**下界** K ≥ √n/c（由对径取等点）与「2√n/c 不取等」。本文件补上缺失的另一半：
**上界恰为 √n/c**，从而把 RMSNorm 的 Lipschitz 常数**完全定死**。

## 主结果

1. `rmsNormE_sqrt_lipschitz`（**核心**）：RMSNorm（`RealNormSharpConstant.rmsNormE`，
   与 `RealRMSNorm.rmsNorm` 同构 = √n·单位化）满足
   `‖RMSNorm x − RMSNorm y‖ ≤ (√n/c)·‖x − y‖`（‖x‖, ‖y‖ ≥ c > 0）。
   证明：`rmsNormE = √n • 单位化`，直接调用 `unit_normalize_lipschitz_sharp`（1/c 紧界）。
   这比既有的 (2√n/c) 界**严格改进**（差因子 2）。
2. `rmsNormE_sharp_attained`：对径点对 (x, −x)（‖x‖ = c）**取等**：
   `‖RMSNorm x − RMSNorm(−x)‖ = (√n/c)·‖x − (−x)‖`。
3. `exists_norm_eq` / `rmsNormE_sharp_pair_exists`：取等点对的**显式构造**
   （n > 0 时），由 `Function.update 0 i c` 缩放得到，故常数 √n/c 确实可达。
4. `rmsNormE_constant_iff`（**紧常数刻画**）：n > 0 时
   「K 是有效 Lipschitz 常数」⟺ `√n/c ≤ K`。结合 1、2 即得真正常数 = √n/c。
5. `lnE` / `lnE_lipschitz_sqrt`：LayerNorm（= RMSNorm ∘ 中心化）在同口径
   （`c ≤ ‖ctr x‖`）下也满足 **√n/c** 上界——与 RMSNorm 同常数（中心化是 1-Lipschitz
   正交投影，不放大）。
6. `lnE_constant_iff` / `lnE_sharp_attained` / `lnE_sharp_pair_exists`：
   LayerNorm 的紧常数**同为 √n/c**（n ≥ 2 时有非零零均值取等点对）。
7. `rmsNorm_lnE_sharp_constant_compare`（**比较定理**）：RMSNorm 与 LayerNorm 的紧常数
   **相等**（都是 √n/c），且都**严格小于**既有的 2√n/c；即 RealNormLipschitz 的
   2√n/c 界对两者都不是紧界。

## 诚实边界

- 全部为**内积空间 / EuclideanSpace ℝ (Fin n)** 上的叙述；标量 c 是范数下界。
- `rmsNormE_constant_iff` 与 `lnE_constant_iff` 分别要求 `0 < n` 与 `2 ≤ n`：
  这是**本质的**（n = 0 时空间平凡、假设全空，n = 1 时不存在非零零均值向量，
  LayerNorm 退化），已在各定理中显式标注，不是被掩盖的 gap。
- `lnE` 是无 γ/β、无 ε 的核心 LayerNorm（与 `RealLayerNorm`/`RealRMSNorm` 同口径）；
  本文件**未**处理带仿射项 γ/β 与 ε 变体的常数（诚实标注：未做）。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 辅助引理：坐标单项向量的和、非零性与范数 -/

/-- `Function.update 0 i a` 的坐标和等于 a。 -/
lemma sum_update_zero {n : ℕ} (i : Fin n) (a : ℝ) :
    (∑ k : Fin n, (Function.update (0 : Fin n → ℝ) i a) k) = a := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Function.update_noteq hj a (0 : Fin n → ℝ)]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `a ≠ 0` 时 `Function.update 0 i a ≠ 0`（坐标 i 处非零）。 -/
lemma update_zero_ne_zero {n : ℕ} (i : Fin n) {a : ℝ} (ha : a ≠ 0) :
    (Function.update (0 : Fin n → ℝ) i a) ≠ 0 := by
  intro h
  have hc := congrFun h i
  simp [ha] at hc

/-- `Function.update 0 i a - Function.update 0 j a`（i ≠ j）的和为零，即中心化不动点。 -/
lemma sum_update_sub_zero {n : ℕ} (i j : Fin n) (a : ℝ) :
    (∑ k : Fin n,
      (Function.update (0 : Fin n → ℝ) i a - Function.update (0 : Fin n → ℝ) j a) k) = 0 := by
  rw [show (∑ k : Fin n,
      (Function.update (0 : Fin n → ℝ) i a - Function.update (0 : Fin n → ℝ) j a) k)
      = (∑ k : Fin n, (Function.update (0 : Fin n → ℝ) i a) k)
        - (∑ k : Fin n, (Function.update (0 : Fin n → ℝ) j a) k) from
    Finset.sum_sub_distrib]
  rw [sum_update_zero, sum_update_zero]
  ring

/-- `Function.update 0 i 1 - Function.update 0 j 1 ≠ 0`（i ≠ j）：
    在坐标 i 处其值为 1。 -/
lemma update_sub_ne_zero {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (Function.update (0 : Fin n → ℝ) i 1 - Function.update (0 : Fin n → ℝ) j 1) ≠ 0 := by
  intro h
  have hc := congrFun h i
  simp [hij] at hc

/-! ## 一、RMSNorm 的紧上界 √n/c -/

/-- **`rmsNormE_sqrt_lipschitz`（核心）**：RMSNorm 在范数下界 ‖x‖, ‖y‖ ≥ c > 0 上是
    **(√n/c)-Lipschitz**（真正常数，严格优于既有的 2√n/c）。 -/
theorem rmsNormE_sqrt_lipschitz {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    ‖rmsNormE x - rmsNormE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖ := by
  have hdiff : rmsNormE x - rmsNormE y
      = (Real.sqrt n) • ((1 / ‖x‖) • x - (1 / ‖y‖) • y) := by
    unfold rmsNormE
    rw [← smul_sub]
  rw [hdiff]
  calc
    ‖(Real.sqrt n) • ((1 / ‖x‖) • x - (1 / ‖y‖) • y)‖
        = Real.sqrt n * ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg n)]
    _ ≤ Real.sqrt n * ((1 / c) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (unit_normalize_lipschitz_sharp x y c hc hx hy)
            (Real.sqrt_nonneg n)
    _ = (Real.sqrt n / c) * ‖x - y‖ := by ring

/-! ## 二、取等点对与常数可达性 -/

/-- `‖x‖ = c` 时 `‖x − (−x)‖ = 2c`（对径点对的距离）。 -/
lemma norm_sub_neg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hx : ‖x‖ = c) :
    ‖x - (-x)‖ = 2 * c := by
  have hsub : x - (-x) = (2 : ℝ) • x := by rw [sub_neg_eq_add, two_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, hx]
  norm_num

/-- **`rmsNormE_sharp_attained`**：对径点对 (x, −x)（‖x‖ = c）取等，
    `‖RMSNorm x − RMSNorm(−x)‖ = (√n/c)·‖x − (−x)‖`。 -/
theorem rmsNormE_sharp_attained {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : ‖x‖ = c) :
    ‖rmsNormE x - rmsNormE (-x)‖ = (Real.sqrt n / c) * ‖x - (-x)‖ := by
  rw [rmsNormE_antipodal_norm x c hc hx, norm_sub_neg x c hx]
  have hval : (Real.sqrt n / c) * (2 * c) = 2 * Real.sqrt n := by
    field_simp [ne_of_gt hc]
    ring
  rw [hval]

/-- **范数可达性**：n > 0 时对任意 c > 0 存在范数恰为 c 的向量
    （由 `Function.update 0 i 1` 缩放得到）。 -/
lemma exists_norm_eq {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 < c) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = c := by
  set u : EuclideanSpace ℝ (Fin n) :=
    (Function.update (0 : Fin n → ℝ) ⟨0, hn⟩ 1 : EuclideanSpace ℝ (Fin n)) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def]
    exact update_zero_ne_zero ⟨0, hn⟩ one_ne_zero
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine ⟨(c / ‖u‖) • u, ?_⟩
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (le_of_lt hc) (norm_nonneg _))]
  exact div_mul_cancel₀ c (ne_of_gt hupos)

/-- **RMSNorm 取等点对存在**：n > 0 时，对任意 c > 0 存在范数为 c 的 x，
    使对径点对 (x, −x) 达到 √n/c 常数。 -/
theorem rmsNormE_sharp_pair_exists {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 < c) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = c ∧
      ‖rmsNormE x - rmsNormE (-x)‖ = (Real.sqrt n / c) * ‖x - (-x)‖ := by
  rcases exists_norm_eq hn c hc with ⟨x, hx⟩
  exact ⟨x, hx, rmsNormE_sharp_attained x c hc hx⟩

/-! ## 三、紧常数的完整刻画（iff） -/

/-- **`rmsNormE_constant_iff`（紧常数刻画）**：n > 0 时，
    K 是 RMSNorm 在 {‖·‖ ≥ c} 上的有效 Lipschitz 常数**当且仅当** √n/c ≤ K。
    结合 `rmsNormE_sqrt_lipschitz`（充分）与对径取等点（必要），真正常数 = √n/c。 -/
theorem rmsNormE_constant_iff {n : ℕ} (hn : 0 < n) (c K : ℝ) (hc : 0 < c) :
    (∀ x y : EuclideanSpace ℝ (Fin n), c ≤ ‖x‖ → c ≤ ‖y‖ →
        ‖rmsNormE x - rmsNormE y‖ ≤ K * ‖x - y‖) ↔ Real.sqrt n / c ≤ K := by
  constructor
  · intro hK
    rcases exists_norm_eq hn c hc with ⟨x, hx⟩
    have hy : c ≤ ‖-x‖ := by rw [norm_neg, hx]
    have h1 : ‖rmsNormE x - rmsNormE (-x)‖ ≤ K * ‖x - (-x)‖ :=
      hK x (-x) (le_of_eq hx.symm) hy
    have h2 : (Real.sqrt n / c) * ‖x - (-x)‖ ≤ K * ‖x - (-x)‖ := by
      rwa [rmsNormE_sharp_attained x c hc hx] at h1
    have hd : 0 < ‖x - (-x)‖ := by
      rw [norm_sub_neg x c hx]
      linarith
    rcases (mul_le_mul_right hd).mp h2 with hle
    exact hle
  · intro hK x y hx hy
    calc
      ‖rmsNormE x - rmsNormE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖ :=
        rmsNormE_sqrt_lipschitz x y c hc hx hy
      _ ≤ K * ‖x - y‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-! ## 四、LayerNorm：中心化 + RMSNorm，常数同为 √n/c -/

/-- LayerNorm 的核心映射：RMSNorm ∘ 中心化（`ctr` 来自 RealNormSharpConstant，
    与 `RealLayerNorm.center` 同义）。 -/
def lnE {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  rmsNormE (ctr x)

/-- 中心化对缩放线性：`ctr (a • z) = a • ctr z`。
    数值核对（n=2, a=2, z=(3,5)）：两侧同为 (−2,2)。 -/
lemma ctr_smul {n : ℕ} (a : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ctr (a • z) = a • ctr z := by
  funext i
  have hsum : (∑ x : Fin n, (a • z) x) = a * ∑ x : Fin n, z x := by
    rw [show (∑ x : Fin n, (a • z) x) = ∑ x : Fin n, a * z x from
      Finset.sum_congr rfl (fun x _ => rfl)]
    exact (Finset.mul_sum Finset.univ z a).symm
  have hL : ctr (a • z) i = (a • z) i - (a * ∑ x : Fin n, z x) * (n : ℝ)⁻¹ := by
    simp only [ctr, hsum, div_eq_mul_inv]
  have hR : (a • ctr z) i = a * (z i - (∑ x : Fin n, z x) * (n : ℝ)⁻¹) := by
    show a * (ctr z) i = a * (z i - (∑ x : Fin n, z x) * (n : ℝ)⁻¹)
    simp only [ctr, div_eq_mul_inv]
  have hz : (a • z) i = a * z i := rfl
  rw [hL, hR, hz]
  ring

/-- 中心化对取负线性：`ctr (−z) = −ctr z`。 -/
lemma ctr_neg {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) : ctr (-z) = -ctr z := by
  have h1 : -z = (-1 : ℝ) • z := by simp
  rw [h1, ctr_smul]
  simp

/-- **`lnE_lipschitz_sqrt`**：LayerNorm 在同口径 `c ≤ ‖ctr x‖`、`c ≤ ‖ctr y‖` 下
    也是 **(√n/c)-Lipschitz**（与 RMSNorm 同常数；中心化是 1-Lipschitz 正交投影）。 -/
theorem lnE_lipschitz_sqrt {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖ctr x‖) (hy : c ≤ ‖ctr y‖) :
    ‖lnE x - lnE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖ := by
  have h1 : ‖lnE x - lnE y‖ ≤ (Real.sqrt n / c) * ‖ctr x - ctr y‖ := by
    simpa [lnE] using rmsNormE_sqrt_lipschitz (ctr x) (ctr y) c hc hx hy
  have h2 : ‖ctr x - ctr y‖ ≤ ‖x - y‖ := ctr_lipschitz x y
  calc
    ‖lnE x - lnE y‖ ≤ (Real.sqrt n / c) * ‖ctr x - ctr y‖ := h1
    _ ≤ (Real.sqrt n / c) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg (Real.sqrt_nonneg n) (le_of_lt hc))

/-- **LayerNorm 取等点对**：若 x 是中心化不动点（ctr x = x）且 ‖x‖ = c，
    则对径点对 (x, −x) 达到 √n/c 常数。 -/
theorem lnE_sharp_attained {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : ctr x = x) (hxnorm : ‖x‖ = c) :
    ‖lnE x - lnE (-x)‖ = (Real.sqrt n / c) * ‖x - (-x)‖ := by
  have hneg : ctr (-x) = -x := by rw [ctr_neg, hx]
  have e1 : lnE x = rmsNormE x := by rw [lnE, hx]
  have e2 : lnE (-x) = rmsNormE (-x) := by rw [lnE, hneg]
  rw [e1, e2]
  exact rmsNormE_sharp_attained x c hc hxnorm

/-- **LayerNorm 取等点对存在**：n ≥ 2 时，对任意 c > 0 存在中心化不动点 x
    （`ctr x = x`）且 ‖x‖ = c，故 √n/c 在 LayerNorm 上也可达。
    构造：零均值的差向量 `update 0 i 1 − update 0 j 1`（i ≠ j）缩放至范数 c。 -/
theorem lnE_sharp_pair_exists {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) :
    ∃ x : EuclideanSpace ℝ (Fin n), ctr x = x ∧ ‖x‖ = c := by
  have hn0 : 0 < n := by omega
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hv : (i : ℕ) = (j : ℕ) := congrArg Fin.val h
    simp [i, j] at hv
  let u : EuclideanSpace ℝ (Fin n) :=
    (Function.update (0 : Fin n → ℝ) i 1 : EuclideanSpace ℝ (Fin n))
      - (Function.update (0 : Fin n → ℝ) j 1 : EuclideanSpace ℝ (Fin n))
  have hu : u ≠ 0 := by
    dsimp [u]
    exact update_sub_ne_zero i j hij
  have hsum : (∑ k : Fin n, u k) = 0 := by
    dsimp [u]
    rw [Finset.sum_sub_distrib, sum_update_zero, sum_update_zero]
    ring
  have hctr : ctr u = u := ctr_fixes u (by rw [hsum]; simp)
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  refine ⟨(c / ‖u‖) • u, ?_, ?_⟩
  · rw [ctr_smul, hctr]
  · rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (le_of_lt hc) (norm_nonneg _))]
    exact div_mul_cancel₀ c (ne_of_gt hupos)

/-- **`lnE_constant_iff`（LayerNorm 紧常数刻画）**：n ≥ 2 时，
    K 是 LayerNorm 在中心化集合上的有效 Lipschitz 常数**当且仅当** √n/c ≤ K。
    即 LayerNorm 的真正常数**同为 √n/c**（与 RMSNorm 相同）。 -/
theorem lnE_constant_iff {n : ℕ} (hn : 2 ≤ n) (c K : ℝ) (hc : 0 < c) :
    (∀ x y : EuclideanSpace ℝ (Fin n), c ≤ ‖ctr x‖ → c ≤ ‖ctr y‖ →
        ‖lnE x - lnE y‖ ≤ K * ‖x - y‖) ↔ Real.sqrt n / c ≤ K := by
  constructor
  · intro hK
    rcases lnE_sharp_pair_exists hn c hc with ⟨x, hxctr, hxnorm⟩
    have hneg : ctr (-x) = -x := by rw [ctr_neg, hxctr]
    have hcx : c ≤ ‖ctr x‖ := by rw [hxctr, hxnorm]
    have hcnx : c ≤ ‖ctr (-x)‖ := by rw [hneg, norm_neg, hxnorm]
    have h1 : ‖lnE x - lnE (-x)‖ ≤ K * ‖x - (-x)‖ := hK x (-x) hcx hcnx
    have h2 : (Real.sqrt n / c) * ‖x - (-x)‖ ≤ K * ‖x - (-x)‖ := by
      rwa [lnE_sharp_attained x c hc hxctr hxnorm] at h1
    have hd : 0 < ‖x - (-x)‖ := by
      rw [norm_sub_neg x c hxnorm]
      linarith
    exact (mul_le_mul_right hd).mp h2
  · intro hK x y hx hy
    calc
      ‖lnE x - lnE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖ := lnE_lipschitz_sqrt x y c hc hx hy
      _ ≤ K * ‖x - y‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- LayerNorm 的 (2√n/c) 界在取等点对上是**严格**的（n > 0），
    故 2√n/c 同样不是 LayerNorm 的紧界。 -/
theorem lnE_two_sqrt_not_attained {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (hc : 0 < c) (hx : ctr x = x)
    (hxnorm : ‖x‖ = c) :
    ‖lnE x - lnE (-x)‖ < (2 * Real.sqrt n / c) * ‖x - (-x)‖ := by
  have heq := lnE_sharp_attained x c hc hx hxnorm
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hlt : Real.sqrt n / c < 2 * Real.sqrt n / c := by
    have h1 : 0 < Real.sqrt n / c := div_pos hspos hc
    have h2 : 2 * Real.sqrt n / c - Real.sqrt n / c = Real.sqrt n / c := by ring
    linarith
  have hd : 0 < ‖x - (-x)‖ := by
    rw [norm_sub_neg x c hxnorm]
    linarith
  calc
    ‖lnE x - lnE (-x)‖ = (Real.sqrt n / c) * ‖x - (-x)‖ := heq
    _ < (2 * Real.sqrt n / c) * ‖x - (-x)‖ := mul_lt_mul_of_pos_right hlt hd

/-! ## 五、RMSNorm vs LayerNorm：紧常数比较定理 -/

/-- **`rmsNorm_lnE_sharp_constant_compare`（比较定理）**：n ≥ 2 时
    · RMSNorm 的紧常数是 √n/c（上界 + 可达）；
    · LayerNorm 的紧常数**同为** √n/c（上界 + 可达）；
    · 两者都严格小于既有的 2√n/c —— 即 RealNormLipschitz 的 2√n/c 界
      对 RMSNorm 与 LayerNorm **都不是紧界**。 -/
theorem rmsNorm_lnE_sharp_constant_compare {n : ℕ} (hn : 2 ≤ n) (c : ℝ) (hc : 0 < c) :
    (∀ x y : EuclideanSpace ℝ (Fin n), c ≤ ‖x‖ → c ≤ ‖y‖ →
        ‖rmsNormE x - rmsNormE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖) ∧
    (∀ x y : EuclideanSpace ℝ (Fin n), c ≤ ‖ctr x‖ → c ≤ ‖ctr y‖ →
        ‖lnE x - lnE y‖ ≤ (Real.sqrt n / c) * ‖x - y‖) ∧
    (Real.sqrt n / c < 2 * Real.sqrt n / c) := by
  have hn0 : 0 < n := by omega
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
  refine ⟨fun x y hx hy => rmsNormE_sqrt_lipschitz x y c hc hx hy,
    fun x y hx hy => lnE_lipschitz_sqrt x y c hc hx hy, ?_⟩
  have h1 : 0 < Real.sqrt n / c := div_pos hspos hc
  have h2 : 2 * Real.sqrt n / c - Real.sqrt n / c = Real.sqrt n / c := by ring
  linarith

/-! ## 注：闭环语义
  单位化紧界 1/c（RealNormSharpConstant）→ RMSNorm = √n·单位化 ⟹ 紧上界 √n/c
  （rmsNormE_sqrt_lipschitz）→ 对径取等（rmsNormE_sharp_attained）与可达性
  （rmsNormE_sharp_pair_exists）→ 紧常数刻画（rmsNormE_constant_iff）→
  LayerNorm = RMSNorm∘中心化 同常数（lnE_lipschitz_sqrt / lnE_constant_iff /
  lnE_sharp_pair_exists）→ 比较定理（rmsNorm_lnE_sharp_constant_compare）。
  诚实标注：n = 0 / n = 1 的退化已在各定理前提中显式排除；γ/β 与 ε 变体未做。 -/

end Lattice
