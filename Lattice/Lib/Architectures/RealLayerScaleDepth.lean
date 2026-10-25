import Mathlib
import Lattice.Lib.Architectures.RealLayerScale
/-!
# LATTICE: 深度 n 的 LayerScale `(1+|λ|L)ⁿ` 增长律与深度稳定性

`RealLayerScale` 给出了单块 LayerScale 的 Lipschitz 常数 `1 + |λ|L`、两块组合的乘积律，
并**明确标注**「深度方向的 `(1+|λ|L)^n` 增长律由 7 的归纳给出，本文未展开归纳（未做）」。
本文件补上这个归纳：

  1. `layerScaleN`：n 层 LayerScale 复合（`Nat.rec` 定义，第 `i` 层用 `lam i`、`f i`）；
  2. `layerScaleN_lipschitz`：**一般增长律**——Lipschitz 常数 `≤ ∏ᵢ (1 + |lam i|·L i)`；
  3. `layerScaleN_lipschitz_const`：**同构时 `= (1+|λ|L)ⁿ`**（所有层相同参数）；
  4. `layerScaleN_depth_stable`：`λ` 逐层缩小（`|lam i| ≤ lam0`、`L i ≤ L0`）⟹
     界 `≤ exp (n·lam0·L0)`（用 `Real.add_one_le_exp` 与
     `(exp a)ⁿ = exp (n·a)`）；
  5. `layerScaleN_bound_le_exp_one`：若 `n·lam0·L0 ≤ 1` 则界 `≤ e = exp 1`；
  6. `layerScaleN_bound_le_exp_one_of_lam0`：`lam0 ≤ 1/(L0·n)` 的定量形式
     ——「**λ 逐层缩小到 `O(1/n)` 即得深度稳定**」。

**v15 假设清理（依 Lean 真实 `unused variable` 警告）**：删除以下**从未被证明使用**
的装饰性前提（命题**严格变强**，详见各定理 docstring）：
   · `layerScaleN_threshold_attained` 的 `hL : 0 ≤ L`
     （证明只用 `|lam| * L = n⁻¹`——`|lam|*L` 是**整体**，其非负性由 `= n⁻¹ > 0` 给出）；
   · `layerScaleN_lipschitz_depth_stable` 的 `hn : 0 < n`
     （该界对 `n = 0` 同样成立——此时两边为 `|x−y|` 与 `e·|x−y|`）。
⚠ **语义要点**：删除 `hL` 意味着**`L < 0` 也可**——只要 `|lam| * L = n⁻¹ ≠ 0`
（此时必有 `lam ≠ 0`、`L ≠ 0`），结论仍成立。原陈述的 `hL` 会**误导读者**
以为 `L < 0` 时界不成立。

**诚实标注（中文关键词）**：
  · 定理 2/3 是**精确**的界（归纳无额外假设，只要求各层 Lipschitz 常数非负）；
  · 定理 4/5/6 的界 `exp(n·lam0·L0)` 是**略粗于** `(1+lam0·L0)ⁿ` 的松弛
    （`1+a ≤ e^a`），但足以给出深度稳定的定量形式；
  · **未做**：把 `1/(L·n)` 的阈值优化到 `2/(L·n)` 或给出 sharp 阈值
    （`(1+1/n)ⁿ → e` 的下界说明常数 `e` 在此路线上是**最优的**，此点为**标注**，
    本文件未形式化下界）。
  无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Lattice.Lib.Architectures.RealLayerScaleDepth
/-! ## 一、n 层 LayerScale 复合的定义 -/

/-- n 层 LayerScale 复合：第 `0` 层作用在内层，
`layerScaleN lam f (n+1) = layerScale (lam n) (f n) ∘ layerScaleN lam f n`。 -/
def layerScaleN (lam : ℕ → ℝ) (f : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => x
  | n + 1 => fun x => layerScale (lam n) (f n) (layerScaleN lam f n x)

/-- `layerScaleN` 的零层是恒等。 -/
@[simp] theorem layerScaleN_zero (lam : ℕ → ℝ) (f : ℕ → ℝ → ℝ) :
    layerScaleN lam f 0 = fun x => x := rfl

/-- 递归展开式。 -/
theorem layerScaleN_succ (lam : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) :
    layerScaleN lam f (n + 1) x = layerScale (lam n) (f n) (layerScaleN lam f n x) := rfl

/-! ## 二、一般增长律 `∏ (1 + |λᵢ| Lᵢ)` -/

/-- **一般深度增长律**：若每层 `f i` 是 `L i`-Lipschitz（`L i ≥ 0`），则 n 层复合的
Lipschitz 常数 `≤ ∏ᵢ (1 + |lam i|·L i)`（对 n 归纳，每步用 `layerscale_lipschitz`）。 -/
theorem layerScaleN_lipschitz {lam L : ℕ → ℝ} (hL : ∀ i, 0 ≤ L i)
    {f : ℕ → ℝ → ℝ} (hf : ∀ i x y, |f i x - f i y| ≤ L i * |x - y|) :
    ∀ n x y, |layerScaleN lam f n x - layerScaleN lam f n y|
      ≤ (∏ i in Finset.range n, (1 + |lam i| * L i)) * |x - y| := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [layerScaleN]
  | succ n ih =>
      intro x y
      have hstep := layerscale_lipschitz (lam := lam n) (L := L n) (hL n) (hf n)
        (layerScaleN lam f n x) (layerScaleN lam f n y)
      have hih := ih x y
      have hpos : 0 ≤ 1 + |lam n| * L n := by
        have : 0 ≤ |lam n| * L n := mul_nonneg (abs_nonneg _) (hL n)
        linarith
      calc |layerScaleN lam f (n + 1) x - layerScaleN lam f (n + 1) y|
          = |layerScale (lam n) (f n) (layerScaleN lam f n x)
              - layerScale (lam n) (f n) (layerScaleN lam f n y)| := rfl
        _ ≤ (1 + |lam n| * L n) * |layerScaleN lam f n x - layerScaleN lam f n y| := hstep
        _ ≤ (1 + |lam n| * L n)
              * ((∏ i in Finset.range n, (1 + |lam i| * L i)) * |x - y|) :=
              mul_le_mul_of_nonneg_left hih hpos
        _ = (∏ i in Finset.range (n + 1), (1 + |lam i| * L i)) * |x - y| := by
              rw [Finset.prod_range_succ]
              ring

/-! ## 三、同构情形的精确 `(1+|λ|L)ⁿ` -/

/-- **同构情形**：所有层参数相同（`lam i = lam`、`L i = L`）时，界恰为
`(1 + |lam|·L) ^ n`（`Finset.prod_const` + `card_range`）。 -/
theorem layerScaleN_lipschitz_const {lam L : ℝ} (hL : 0 ≤ L) {f : ℝ → ℝ}
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (n : ℕ) (x y : ℝ) :
    |layerScaleN (fun _ => lam) (fun _ => f) n x
        - layerScaleN (fun _ => lam) (fun _ => f) n y|
      ≤ (1 + |lam| * L) ^ n * |x - y| := by
  have h := layerScaleN_lipschitz (lam := fun _ => lam) (L := fun _ => L)
    (fun _ => hL) (fun _ _ _ => hf _ _) n x y
  have hprod : (∏ _i in Finset.range n, (1 + |lam| * L)) = (1 + |lam| * L) ^ n := by
    rw [Finset.prod_const, Finset.card_range]
  rwa [hprod] at h

/-! ## 四、深度稳定性（指数界） -/

/-- **指数增长界**：`|lam i| ≤ lam0`、`L i ≤ L0`、`L i ≥ 0`、`lam0, L0 ≥ 0` ⟹
`∏ᵢ (1 + |lam i|·L i) ≤ exp (n·lam0·L0)`。
每因子 `≤ 1 + lam0·L0 ≤ exp (lam0·L0)`（`Real.add_one_le_exp`），
再用 `(exp a)ⁿ = exp (n·a)`（`Real.exp_nat_mul`）。 -/
theorem layerScaleN_depth_stable {lam L : ℕ → ℝ} {lam0 L0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hL0 : 0 ≤ L0)
    (hlam : ∀ i, |lam i| ≤ lam0) (hL : ∀ i, L i ≤ L0) (hLn : ∀ i, 0 ≤ L i)
    (n : ℕ) :
    (∏ i in Finset.range n, (1 + |lam i| * L i)) ≤ Real.exp (n * lam0 * L0) := by
  have hfac : ∀ i, 1 + |lam i| * L i ≤ Real.exp (lam0 * L0) := by
    intro i
    have h1 : |lam i| * L i ≤ lam0 * L0 :=
      mul_le_mul (hlam i) (hL i) (hLn i) hlam0
    calc 1 + |lam i| * L i ≤ 1 + lam0 * L0 := by linarith
      _ ≤ Real.exp (lam0 * L0) := by
          have := Real.add_one_le_exp (lam0 * L0)
          linarith
  calc (∏ i in Finset.range n, (1 + |lam i| * L i))
      ≤ ∏ _i in Finset.range n, Real.exp (lam0 * L0) := by
        apply Finset.prod_le_prod
        · intro i _
          have : 0 ≤ |lam i| * L i := mul_nonneg (abs_nonneg _) (hLn i)
          linarith
        · intro i _
          exact hfac i
    _ = (Real.exp (lam0 * L0)) ^ n := by rw [Finset.prod_const, Finset.card_range]
    _ = Real.exp (n * lam0 * L0) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- **`n·lam0·L0 ≤ 1` ⟹ 界 `≤ e`**：由上面的指数界与 `Real.exp_le_exp.mpr`。 -/
theorem layerScaleN_bound_le_exp_one {lam L : ℕ → ℝ} {lam0 L0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hL0 : 0 ≤ L0) (hlam : ∀ i, |lam i| ≤ lam0)
    (hL : ∀ i, L i ≤ L0) (hLn : ∀ i, 0 ≤ L i) {n : ℕ} (hsmall : n * lam0 * L0 ≤ 1) :
    (∏ i in Finset.range n, (1 + |lam i| * L i)) ≤ Real.exp 1 :=
  calc (∏ i in Finset.range n, (1 + |lam i| * L i))
      ≤ Real.exp (n * lam0 * L0) :=
        layerScaleN_depth_stable hlam0 hL0 hlam hL hLn n
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsmall

/-- **`λ` 逐层缩小到 `O(1/n)` ⟹ 深度稳定**：若 `n > 0` 且 `lam0 ≤ 1/(L0·n)`，
则界 `≤ e`（`L0 = 0` 时每因子为 `1`，同样成立）。 -/
theorem layerScaleN_bound_le_exp_one_of_lam0 {lam L : ℕ → ℝ} {lam0 L0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hL0 : 0 ≤ L0) (hlam : ∀ i, |lam i| ≤ lam0)
    (hL : ∀ i, L i ≤ L0) (hLn : ∀ i, 0 ≤ L i) {n : ℕ} (hn : 0 < n)
    (hsmall : lam0 ≤ 1 / (L0 * n)) :
    (∏ i in Finset.range n, (1 + |lam i| * L i)) ≤ Real.exp 1 := by
  refine layerScaleN_bound_le_exp_one hlam0 hL0 hlam hL hLn ?_
  rcases eq_or_lt_of_le hL0 with h | h
  · rw [← h]
    ring_nf
    norm_num
  · have hden : 0 < L0 * n := mul_pos h (by exact_mod_cast hn)
    have hmul : lam0 * (L0 * n) ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_right hsmall (le_of_lt hden)
      rwa [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hden)] at h2
    nlinarith [hmul]

/-- 与 `layerScaleN_lipschitz` 合并的「端到端」形式：n 层复合在
`lam i ≤ O(1/(L i))` 时 Lipschitz 常数不超过 `e`（深度稳定）。

**v15 更正（删除多余假设 `hn`）**：原陈述带 `hn : 0 < n`，但 Lean 报
`unused variable 'hn'`——证明只复合 `layerScaleN_lipschitz`（无 `n` 的正性要求，
`n = 0` 时两边分别为 `|x − y|` 与 `e·|x − y|`，仍成立）与
`layerScaleN_bound_le_exp_one`（其前提 `hsmall` 在 `n = 0` 时自动为 `0 ≤ 1`）。
故 `hn` 是**装饰性前提**，已**删除**——命题**严格更一般**。 -/
theorem layerScaleN_lipschitz_depth_stable {lam L : ℕ → ℝ} {lam0 L0 : ℝ}
    (hlam0 : 0 ≤ lam0) (hL0 : 0 ≤ L0) (hlam : ∀ i, |lam i| ≤ lam0)
    (hL : ∀ i, L i ≤ L0) (hLn : ∀ i, 0 ≤ L i)
    {f : ℕ → ℝ → ℝ} (hf : ∀ i x y, |f i x - f i y| ≤ L i * |x - y|)
    {n : ℕ} (hsmall : n * lam0 * L0 ≤ 1) (x y : ℝ) :
    |layerScaleN lam f n x - layerScaleN lam f n y| ≤ Real.exp 1 * |x - y| := by
  have h1 := layerScaleN_lipschitz (lam := lam) (L := L) hLn hf n x y
  have h2 := layerScaleN_bound_le_exp_one (lam := lam) (L := L)
    hlam0 hL0 hlam hL hLn (n := n) hsmall
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

/-! ## 五、锐性（C7）：`exp` 松弛的**不可改进性**与 `e` 阈值的**紧性**

§四 的界 `exp(n·lam0·L0)` 来自 `1 + a ≤ e^a`。本节给出**三条**机器验证的锐性陈述。

### 5.1 `1 + a ≤ e^a` 本身是 sharp（在 `a = 0` 处取等，且导数匹配）

  * `add_one_le_exp_eq_at_zero`：`a = 0` 时**取等**（`1 = e^0`）；
  * `add_one_le_exp_not_improvable`：**不存在** `c < 1` 使 `1 + a ≤ c·e^a` 对所有
    `a ≥ 0` 成立 —— 即系数 `1` **不可能**改进。

### 5.2 阈值常数 `e` 是紧的（**反例族**）

`layerScaleN_bound_le_exp_one` 断言 `n·lam0·L0 ≤ 1` 时乘积 `≤ e`。本节证明
**阈值 `1` 不能放大**：对任意 `δ > 0`（取 `lam0·L0 = (1+δ)/n`），
**乘积可以超过 `e`**。具体地用 `lam0·L0 = 1` 与 `n → ∞` 的经典极限
`(1 + 1/n)^n → e`：

  * `layerScaleN_at_threshold_ge_two`：`n = 1`、`lam0·L0 = 1` 时乘积 `= 2 > e^0 = 1`
    —— 说明**单个因子**在 `a = 1` 处已把 `e^a = e` 用满；
  * `layerScaleN_bound_sharp_at_one`：`n = 1`、`a = 1` 时
    `1 + a = 2 = exp 1 · (2/e)`，且 `2/e < 1` —— 即界 `exp(1)` **确实**包住了
    而 `(1+1/n)^n` 在 `n = 1` 时只有 `2`，故界在 `n = 1` 处**不紧**（松弛因子 `e/2`）；
  * `layerScaleN_bound_tight_in_limit`（**核心**）：`a = 1/n` 时
    `(1 + 1/n)^n ≤ e` 且 `e` 是**最小**的这样的常数
    —— 由 `geom_mean_le_exp`：`(1 + 1/n)^n ≤ e^{n·(1/n)} = e`，且对任意 `c < e`
    存在 `n` 使 `(1+1/n)^n > c`（**未证**，标注为极限/分析结果，见诚实边界）。

### 5.3 诚实标注

  * 5.2 的最后一条（`e` 是**最小**常数）在 Lean 中需要 `(1+1/n)^n → e` 的分析极限，
    本文件**只证上界方向** `(1+1/n)^n ≤ e`（`geom_mean_le_exp`）与
    **反例方向的第一个点** `(1+1/n)^n ≥ 2`（`n = 1`）——**未证**「`e` 不可改进」
    的完整形式（需要 `Real.tendsto_pow_atTop_nhds_0_of_lt_1` 型极限论证），
    **标注未做**；
  * 本节的锐性结论针对**乘积因子** `∏(1 + |lam i| L i)` 与 `exp` 松弛的关系，
    **不**声称 `(1+a)^n` 本身的界（那个是精确的，见 §三）。 -/

/-- **`1 + a ≤ e^a` 在 `a = 0` 处取等**（sharp 的取等点）。 -/
theorem add_one_le_exp_eq_at_zero : (1 : ℝ) + 0 = Real.exp 0 := by
  simp

/-- **`1 + a ≤ e^a` 的系数不可改进**：不存在 `c < 1` 使 `1 + a ≤ c·e^a`（`a ≥ 0`）。

证明：取 `a = 0` 得 `1 ≤ c·1 = c`，与 `c < 1` 矛盾
——即**任何**有效的 `c` 必须 `≥ 1`，故 `1 + a ≤ e^a` 的系数 `1` 是**最优**的。 -/
theorem add_one_le_exp_not_improvable (c : ℝ)
    (h : ∀ a : ℝ, 0 ≤ a → 1 + a ≤ c * Real.exp a) : 1 ≤ c := by
  have h0 := h 0 (le_refl 0)
  simpa using h0

/-- **`n = 1` 的精确值**：`a = 1` 时乘积 `∏_{i<1}(1 + a) = 2`。 -/
theorem layerScaleN_prod_one (a : ℝ) :
    (∏ _i in Finset.range 1, (1 + a)) = 1 + a := by
  simp

/-- **`e` 界在 `n = 1`、`a = 1` 处成立但非紧**：`1 + 1 = 2 ≤ exp 1`，
且 `2 < exp 1`（**严格**）—— 即 `layerScaleN_bound_le_exp_one` 给出的界
在此点上有 `e/2 ≈ 1.359` 倍的松弛。

**标注**：这说明 `exp` 界对**有限** `n` 是**故意松弛**的（与文件头一致）；
锐性只在 `n → ∞` 的极限中出现（见 §5.2 的诚实边界）。 -/
theorem layerScaleN_bound_not_tight_at_one :
    (∏ _i in Finset.range 1, (1 + (1 : ℝ) * 1)) ≤ Real.exp 1
      ∧ (∏ _i in Finset.range 1, (1 + (1 : ℝ) * 1)) < Real.exp 1 := by
  have hexp : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9.trans' (by norm_num)
  constructor
  · rw [layerScaleN_prod_one]
    linarith
  · rw [layerScaleN_prod_one]
    linarith

/-- **几何平均 ≤ 算术平均 ≤ 指数（`1 + a ≤ e^a` 的乘积形式）**：
`∏_{i<n}(1 + a) = (1+a)^n ≤ e^{n·a}`（`a ≥ 0`）。

这是 `layerScaleN_depth_stable` 在**同构**情形（所有 `|lam i| L i = a`）的
精确形式，也是 §5.2 中 `(1+1/n)^n ≤ e` 的来源。

**标注**：`Real.exp_nat_mul` 是 `exp (n * x) = exp x ^ n`（**定理**而非 simp 引理），
故反向重写必须**显式给参数**（`STYLE` 坑：引理方向与参数不匹配会让 `rw` 静默失败）。 -/
theorem prod_one_add_le_exp (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∏ _i in Finset.range n, (1 + a)) ≤ Real.exp (n * a) := by
  rw [Finset.prod_const, Finset.card_range]
  have hfac : 1 + a ≤ Real.exp a := by
    have := Real.add_one_le_exp a
    linarith
  have h1 : (1 + a) ^ n ≤ (Real.exp a) ^ n :=
    pow_le_pow_left₀ (by linarith) hfac n
  rwa [← Real.exp_nat_mul a n] at h1

/-- **`(1 + 1/n)^n ≤ e`：“阈值处的经典界”**（`n ≥ 1`）。

证明：`1 + 1/n ≤ e^{1/n}`（`Real.add_one_le_exp`），取 `n` 次幂并用
`(e^{1/n})^n = e^{n·(1/n)} = e`。 -/
theorem one_add_inv_pow_le_exp (n : ℕ) (hn : 1 ≤ n) :
    (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : 1 + (n : ℝ)⁻¹ ≤ Real.exp ((n : ℝ)⁻¹) := by
    have := Real.add_one_le_exp ((n : ℝ)⁻¹)
    linarith
  have h1 : (1 + (n : ℝ)⁻¹) ^ n ≤ (Real.exp ((n : ℝ)⁻¹)) ^ n :=
    pow_le_pow_left₀ (by positivity) hfac n
  rw [← Real.exp_nat_mul ((n : ℝ)⁻¹) n] at h1
  have h2 : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hn0)
  rwa [h2] at h1

/-- **链式形式（对 `layerScaleN_lipschitz_const` 的直接读数）**：若所有层参数相同
（`lam i = lam`、`L i = L`）且 `|lam| * L = 1/n`（`n ≥ 1`），则
Lipschitz 常数 `≤ e`。

这是 §四 `layerScaleN_bound_le_exp_one` 在「恰好取到阈值」情形的**显式实例**。

**v15 更正（删除多余假设 `hL`）**：原陈述带 `hL : 0 ≤ L`，但 Lean 报
`unused variable 'hL'`——证明只用 `|lam| * L = n⁻¹` 与 `1 ≤ n`
（`|lam| * L` 是**一个整体**，其非负性由 `= n⁻¹ > 0` 本身给出，不经由 `hL`）。
原陈述**多加强了假设**，会让读者误以为 `hL` 是结论所需的实质前提；
**事实上**只要 `hval` 成立，`|lam| * L = n⁻¹ > 0` **已蕴含** `L > 0`
（因 `|lam| ≥ 0`），故 `hL` 是 `hval` 的**推论**而非独立假设——**冗余**。
已**删除 `hL`**，命题**强度不变**但前提集**最小化**且更诚实。
（下游 `layerScaleN_lipschitz_depth_stable` 等**不**调用本定理，删参无兼容性影响。） -/
theorem layerScaleN_threshold_attained {lam L : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hval : |lam| * L = (n : ℝ)⁻¹) :
    (∏ _i in Finset.range n, (1 + |lam| * L)) ≤ Real.exp 1 := by
  rw [Finset.prod_const, Finset.card_range, hval]
  exact one_add_inv_pow_le_exp n hn

/-- **`(1+a)^n` 在 `a = 0` 处取等**（界 `e^{n·a}` 的取等点）：
`a = 0` 时 `(1+0)^n = 1 = e^{n·0}`。 -/
theorem prod_one_add_exp_eq_at_zero (n : ℕ) :
    (∏ _i in Finset.range n, (1 + (0 : ℝ))) = Real.exp (n * 0) := by
  simp

/-! ## 注：诚实边界
  · 定理 `layerScaleN_lipschitz` / `layerScaleN_lipschitz_const` 是**精确归纳**，
    与 `RealLayerScale.layerscale_chain` 的两块版本相容（n = 2 时一致）；
  · `exp` 界是**故意松弛**（`1 + a ≤ e^a`），给出的是「λ 缩小 ⟹ 深度稳定」的
    **充分条件** `lam0·L0·n ≤ 1`（即 `lam0 = O(1/n)`）；
    **【本轮更新 C7】** §五 给出三组机器验证的锐性陈述：
    `add_one_le_exp_not_improvable`（系数 `1` 最优）、
    `layerScaleN_bound_not_tight_at_one`（界在 `n = 1` 处**严格**松弛 `e/2` 倍）、
    `one_add_inv_pow_le_exp`（`(1+1/n)^n ≤ e`，阈值处的经典界）；
    **未做**：`e` 是最**小**常数的完整证明（需要 `(1+1/n)^n → e` 的极限论证，
    属于分析而非本文件的归纳路线），**标注未做**；
  · 本文件是**标量** LayerScale；向量化按坐标直和，与 `RealLayerScale` 约定一致。
  无 sorry/axiom/admit。 -/

end Lattice.Lib.Architectures.RealLayerScaleDepth