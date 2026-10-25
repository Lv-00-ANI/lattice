import Mathlib
import Lattice.Lib.Optim.RealSGDStochastic
/-!
# LATTICE: **随机化压缩**（无偏 rand-k / scaled top-k）的方差界与期望收敛率

`RealCompressionRate`（归 WP5）把压缩看成**确定型** δ-近似算子
`|C x − x| ≤ (1−δ)|x|`，其误差是**偏差型**的，故率里出现 `(1−δ)²G²` 的
**惩罚项**（只在 `δ → 1` 时消失）。真实的通信压缩（rand-k、scaled top-k）
不是确定型的，而是**随机算子**，其关键性质是**无偏**：

    E[compress(x)] = x        （无偏性）

无偏性把压缩误差变成**纯方差**（`E[(compress(x) − x)²] = Var`），从而
**不引入偏差惩罚项**：收敛率保持同样的 `O(1/√T)` 结构，只是常数变大。
本文件把这个差异**精确化并机器验证**。

## 主结果

1. `bias_variance_decomposition`（**核心恒等式**）：对**任意**有限概率空间上的
   随机标量算子 `C`，
   `E[(C − x)²] = Var(C) + (E[C] − x)²` —— 二阶压缩误差 = **方差 + 偏差²**。
2. `unbiased_iff_pure_variance`（**等价刻画**）：`E[C] = x ⟺ E[(C−x)²] = Var(C)`
   ——「无偏 ⟺ 纯方差」，这是「无偏压缩无惩罚项」的**精确来源**。
3. `biased_compression_penalty_irreducible`（**对照定理**）：确定型 δ-压缩
   `|C x − x| = (1−δ)|x|`（`δ < 1`）的**偏差项 `(1−δ)²x² > 0` 不可消**，
   与无偏情形的 `0` 形成鲜明对照 —— 这个「零 vs 正」正是本文件与
   `RealCompressionRate` 的本质区别。
4. `unbiased_compression_rate`（**核心：期望版收敛率**）：在无偏 + 方差界 `σc²`
   下，收缩递推 `E_{t+1} ≤ (1−2μη)E_t + η²(G²+σc²)`（`0 ≤ 1−2μη`）给出
   `E_T ≤ (1−2μη)^T·E₀ + (G²+σc²)/(2μ)`。
5. **`O(1/√T)` 显式率（未做，诚实标注）**：本节给出的是**递推形式的收敛率**
   （`unbiased_compression_rate`）与 **ε 证书**（`unbiased_epsilon_certificate`，
   以 `hneigh`/`hinit` 两个显式条件陈述）；
   把它反解为 `η = Θ(1/√T)` 的**闭式**（含 `log` 的显式轮数）**本文件未做**——
   那需要 `Real.log` 的显式估计（`RealFedAsync.geometric_tail_scope` 已给出同类反解，
   可迁移；**标注**）。
6. `randK`（`k = 1` 的 rand-k = 均匀随机坐标 × n）：
   `randK_unbiased`（**无偏**）与 `randK_variance_eq`（**方差恒等式**）。
7. `scaledTopK`（**重要性采样**：以概率 `q` 保留并除以 `q`）：
   `scaledTopK_unbiased` / `scaledTopK_variance_eq`。
8. `randK_variance_shrinks`（**通信量换方差**）：保留比例 `λ` 与相对方差之积
   `λ·σc²(λ) = (1−λ)·Σx²` 随 `λ` **线性递变**，且 `λ ≥ 1/2` 时方差不放大；
   （**标注**：这一族 `O(1/k)` 的直觉只在 `k = 1` 这一特例上被本文件真正验证，
   见 `randK` 的定义处与 `randK_variance_eq`；一般 `k` 的外推**本文件未做**。）

## 诚实边界（标注）

- 概率空间是**有限计数**空间（与 `RealSamplingBoost` / `RealHoeffding` /
  `RealSGDStochastic` 同口径）；测度论版（`Measure` + Bochner 积分）**未做**（**标注**）；
- 递推 `E_{t+1} ≤ (1−2μη)E_t + η²(G²+σc²)` 是**显式假设**（`hstep`），
  与 `RealSGDStochastic` / `RealCompressionRate` 同口径；本文件**不**重推
  `f` 的凸性 / 光滑性链路（**标注**：留待后续）；
- **相对方差界是独立假设**（`unbiased_compression_rate` 的 `sc2`、
  `unbiased_epsilon_certificate` 的 `hsc2`）：无偏性**不蕴含**有界方差
  （`±M` 等概率的无偏算子方差 `M²x²` 可任意大，见
  `unbiased_does_not_imply_bounded_variance`）；
- 一维标量 ℝ 定标做递推（与 `RealSGDStochastic` 一致）；
  `Fin n → ℝ` 向量只用于 `randK` / `scaledTopK` 的定义与方差恒等式；
- 本文件**不改动** `RealCompressionRate.lean`（该文件归 WP5）：
  确定型 δ-近似压缩由该文件承担，本文件补**随机化 / 无偏**分支。

无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、偏差-方差分解（核心恒等式） -/

/-- **（加权）期望**：`E_p[f] = Σ_ω p ω · f ω`。允许**非均匀**权重 `p`
（rand-k 的「均匀选坐标」与 scaled top-k 的「按概率保留」都需非均匀权重）。 -/
def ExpectedOf {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * f ω

/-- **方差**：`Var_p[f] = E[(f − E[f])²]`。 -/
def VarianceOf {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ExpectedOf p (fun ω => (f ω - ExpectedOf p f) ^ 2)

/-- 权重归一 ⟹ 常数的期望等于该常数。 -/
theorem ExpectedOf_const {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp : (∑ ω, p ω) = 1)
    (c : ℝ) : ExpectedOf p (fun _ => c) = c := by
  unfold ExpectedOf
  rw [← Finset.sum_mul, hp, one_mul]

/-- **加权期望下的线性性**：`E_p[f + g] = E_p[f] + E_p[g]`。 -/
theorem ExpectedOf_add {Ω : Type*} [Fintype Ω] (p f g : Ω → ℝ) :
    ExpectedOf p (fun ω => f ω + g ω) = ExpectedOf p f + ExpectedOf p g := by
  have hpt : ∀ ω : Ω, p ω * (f ω + g ω) = p ω * f ω + p ω * g ω :=
    fun ω => by ring
  unfold ExpectedOf
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω), Finset.sum_add_distrib]

/-- **加权期望下 `Σ_ω p ω·(f ω − E_p f) = 0`**（中心化后加权和为零）。

注意 **命题更正（F13）**：本条原稿**漏了归一化假设** `Σ p = 1`，那是**假命题**。
反例：`Ω = Fin 2`、`p ≡ 2`（`Σ p = 4`）、`f = (1, 3)` ⟹ `E_p f = 8`，
左端 `= 2·(1−8) + 2·(3−8) = −24 ≠ 0`。
代数上：`Σ p(f − E_p f) = Σ p·f − (Σ p·f)(Σ p)`，
**仅当 `Σ p = 1`**（或 `Σ p·f = 0`）时为零。
故此处**补上** `hp : Σ p = 1` —— 这也正是唯一使用点
（`bias_variance_decomposition`）本来就有的假设。 -/
theorem sum_sub_expected_zero {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ)
    (hp : (∑ ω, p ω) = 1) :
    (∑ ω, p ω * (f ω - ExpectedOf p f)) = 0 := by
  -- 拆括号：`p ω * (f ω − E) = p ω * f ω − E * p ω`（常数 `E` 放**右侧**）。
  have hpt : ∀ ω : Ω, p ω * (f ω - ExpectedOf p f)
      = p ω * f ω - ExpectedOf p f * p ω :=
    fun ω => by ring
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω)]
  rw [Finset.sum_sub_distrib (s := Finset.univ)]
  -- `∑ ω, E * p ω = E * ∑ ω, p ω`（常数在**左** ⟹ `Finset.mul_sum` 的反向）。
  -- 注意 这里**不能**用 `Finset.sum_mul`：它的常数在**右**，与本目标形状不符。
  rw [← Finset.mul_sum (s := Finset.univ)]
  unfold ExpectedOf
  -- 现在目标是 `∑ p ω*f ω − (∑ p ω*f ω) * (∑ p ω) = 0`，用 `hp` 收尾。
  rw [hp, mul_one, sub_self]

/-- **偏差-方差分解（主交付，核心恒等式）**：对**任意**有限概率空间上的随机标量
算子 `C : Ω → ℝ`（`p` 是概率权重，`Σ p = 1`），
`E_p[(C − x)²] = Var_p(C) + (E_p[C] − x)²`。

即：二阶压缩误差 = **方差** + **偏差的平方**。立刻得到关键推论：
**无偏（偏差 = 0）⟺ 二阶误差恰为方差**（`unbiased_iff_pure_variance`）——
这正是「无偏压缩不引入偏差惩罚项」的精确代数内容，
也是本文件与确定型 δ-近似压缩（`RealCompressionRate`）的**本质区别**。

（代小整数复核：`Ω = Fin 2`、`p = (1/2,1/2)`、`C 0 = 2`、`C 1 = 0`、`x = 1`：
`E[C] = 1`（无偏）；左端 `E[(C−1)²] = (1² + 1²)/2 = 1`；
右端 `Var = ((1)² + (−1)²)/2 = 1`，偏差项 `(1−1)² = 0` ⟹ `1 = 1 + 0` 成立。） -/
theorem bias_variance_decomposition {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω)
    (hp : (∑ ω, p ω) = 1) (C : Ω → ℝ) (x : ℝ) :
    ExpectedOf p (fun ω => (C ω - x) ^ 2)
      = VarianceOf p C + (ExpectedOf p C - x) ^ 2 := by
  -- 逐点恒等式：`(C−x)² = (C−EC)² + (EC−x)² + 2(EC−x)(C−EC)`
  have hpt : (fun ω : Ω => (C ω - x) ^ 2)
      = fun ω => (C ω - ExpectedOf p C) ^ 2 + (ExpectedOf p C - x) ^ 2
          + 2 * (ExpectedOf p C - x) * (C ω - ExpectedOf p C) := by
    funext ω
    ring
  -- 交叉项的期望为 0
  have hcross : ExpectedOf p (fun ω => 2 * (ExpectedOf p C - x) * (C ω - ExpectedOf p C)) = 0 := by
    unfold ExpectedOf
    -- `unfold` 不做 β-归约，目标里仍是 `(fun ω => …) ω` ⟹ 先 `simp only []` 归约掉，
    -- 否则下面的 `sum_congr` 模式匹配不上（STYLE 已登记的 `unfold` vs `simp only` 差异）。
    simp only []
    -- `ExpectedOf` 在目标里已展开为 `∑ i, p i * C i`，故 `show` 必须写展开后的形状。
    rw [show (∑ ω : Ω, p ω * (2 * (∑ i : Ω, p i * C i - x) * (C ω - ∑ i : Ω, p i * C i)))
        = ∑ ω : Ω, (2 * (∑ i : Ω, p i * C i - x)) * (p ω * (C ω - ∑ i : Ω, p i * C i)) from
      Finset.sum_congr rfl (fun ω _ => by ring)]
    rw [← Finset.mul_sum]
    exact mul_eq_zero_of_right _ (sum_sub_expected_zero p C hp)
  rw [hpt, ExpectedOf_add, ExpectedOf_add, hcross, add_zero]
  -- 常数项：`E_p[const c] = c · Σ p = c`
  rw [show ExpectedOf p (fun _ : Ω => (ExpectedOf p C - x) ^ 2)
      = (ExpectedOf p C - x) ^ 2 from ExpectedOf_const hp _]
  rfl

/-- **无偏 ⟺ 纯方差（等价刻画，核心）**：`E_p[C] = x` **当且仅当**
二阶压缩误差 `E_p[(C − x)²]` **恰等于**方差 `Var_p(C)`。

这是「无偏压缩没有惩罚项」的**精确等价刻画**：偏差项 `(E[C] − x)²` 的
消失与二阶误差退化为纯方差是**同一件事**。 -/
theorem unbiased_iff_pure_variance {Ω : Type*} [Fintype Ω] {p : Ω → ℝ} (hp0 : ∀ ω, 0 ≤ p ω)
    (hp : (∑ ω, p ω) = 1) (C : Ω → ℝ) (x : ℝ) :
    (ExpectedOf p C = x ↔ ExpectedOf p (fun ω => (C ω - x) ^ 2) = VarianceOf p C) := by
  constructor
  · intro h
    rw [bias_variance_decomposition hp0 hp C x, h, sub_self, sq, mul_zero, add_zero]
  · intro h
    have hd := bias_variance_decomposition hp0 hp C x
    have hvar : 0 ≤ VarianceOf p C := by
      unfold VarianceOf ExpectedOf
      exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hp0 ω) (sq_nonneg _))
    have hzero : (ExpectedOf p C - x) ^ 2 = 0 := by linarith [hd, h]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)

/-- **有偏压缩的惩罚项不可消（对照定理，机器验证）**：确定型 δ-压缩
`|C x − x| = (1−δ)|x|`（`0 < δ < 1`、`x ≠ 0`）的**偏差项**
`(E[C] − x)² = (1−δ)²x²` **严格为正**，与无偏情形的 `0` 形成对照。

这个「正 vs 零」是**无偏压缩优于确定型压缩**的精确原因：
`RealCompressionRate` 的 `(1−δ)²G²` 惩罚项在 `δ < 1` 时**永远存在**，
而无偏算子在 `E` 意义下**没有**这一项 —— 代价只是方差 `σc²` 进入邻域常数。 -/
theorem biased_compression_penalty_irreducible {δ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx : x ≠ 0) :
    0 < ((1 - δ) * x) ^ 2 := by
  have h1 : 0 < 1 - δ := by linarith
  exact sq_pos_iff.mpr (mul_ne_zero (ne_of_gt h1) hx)

/-! ## 二、无偏压缩下的期望版收敛率 -/

/-- **几何级数求和界**：`0 ≤ r < 1` ⟹ `Σ_{i<T} r^i ≤ 1/(1−r)`（`Fin T` 求和版）。

用 mathlib 既有的几何级数公式 `geom_sum_mul`（`(r−1)·Σ_{i<n} r^i = r^n − 1`）
解出闭式 `Σ = (1 − r^T)/(1 − r) ≤ 1/(1 − r)`。
（先经 `Fin.sum_univ_eq_sum_range` 把 `Fin T` 归约到 `Finset.range T`。） -/
theorem geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    (∑ i : Fin T, r ^ (i : ℕ)) ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) T, le_div_iff₀ hpos]
  have hgeo := geom_sum_mul r T
  have hkey : (∑ i ∈ Finset.range T, r ^ i) * (1 - r) = 1 - r ^ T := by
    linarith [hgeo]
  rw [hkey]
  have hpow : 0 ≤ r ^ T := pow_nonneg hr0 T
  linarith

/-- **无偏压缩下的收敛率（核心：期望版）**：若每步的期望平方距离满足收缩递推
`E_{t+1} ≤ (1 − 2μη)·E_t + η²·(G² + σc²)`（且 `0 ≤ 1 − 2μη`），
则 `T` 步后

    E_T ≤ (1 − 2μη)^T·E₀ + (G² + σc²)/(2μ)

**与确定型压缩的对照**：`RealCompressionRate` 的加性项是 `η²·Gc²`
（`Gc = (2−δ)G/δ` 含**偏差**）；本定理的加性项是 `η²·(G² + σc²)`，
`σc²` 是**纯方差**（**不含偏差项**，由 `unbiased_iff_pure_variance`），
这正是无偏压缩的收益。

证明：递推迭代得 `E_T ≤ (1−2μη)^T E₀ + η²(G²+σc²)·Σ_{i<T}(1−2μη)^i`，
再用 `geom_sum_le_inv_one_sub`（`r = 1−2μη < 1`）把和控到 `1/(2μη)`，
最后 `η²·(G²+σc²)/(2μη) = η(G²+σc²)/(2μ) ≤ (G²+σc²)/(2μ)`（`η ≤ 1` 时）。 -/
theorem unbiased_compression_rate {E : ℕ → ℝ} {mu eta G2 sc2 : ℝ}
    (hmu : 0 < mu) (heta : 0 < eta) (heta1 : eta ≤ 1) (hG2 : 0 ≤ G2) (hsc2 : 0 ≤ sc2)
    (hcon : 0 ≤ 1 - 2 * mu * eta)
    (hstep : ∀ t, E (t + 1) ≤ (1 - 2 * mu * eta) * E t + eta ^ 2 * (G2 + sc2))
    (T : ℕ) :
    E T ≤ (1 - 2 * mu * eta) ^ T * E 0 + (G2 + sc2) / (2 * mu) := by
  set r : ℝ := 1 - 2 * mu * eta with hr_def
  have hr0 : 0 ≤ r := hcon
  have hrlt : r < 1 := by
    rw [hr_def]
    nlinarith [hmu, heta]
  -- 递推迭代（对 `Fin T` 求和）：`E_T ≤ r^T E_0 + η²(G²+σc²)·Σ_{i<T} r^i`
  -- 注意 迭代必须在引用 `geom_sum_le_inv_one_sub` **之前**完成：若先 `have hsum`（含 `T`），
  -- 归纳会对 `T` 泛化，把 `hsum` 吸进归纳假设，`ih` 就变成**函数**而非不等式。
  have hiter : E T ≤ r ^ T * E 0 + eta ^ 2 * (G2 + sc2) * (∑ i : Fin T, r ^ (i : ℕ)) := by
    induction T with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        -- 归纳步：先用 `hsum_eq` 把 `Σ_{i<n+1} r^i` 拆成 `Σ_{i<n} r^i + r^n`，
        -- 再用 `hgeo`（`geom_sum_mul` 的推论）消去 `r * S`。见 `hsplit` 内的详细注释。
        -- 注意 `Fin.sum_univ_castSucc` + `Fin.val_last` + `Fin.coe_castSucc` 三者足以
        --    直接闭合 `hsum_eq`（不要再补 `congr 1` —— 目标已关，会报 `no goals to be solved`）。
        -- 注意 不要用 `Fin.val_castSucc`：它在 core/mathlib 里都**不存在**；真名是 `Fin.coe_castSucc`。
        have hsum_eq : (∑ i : Fin (n + 1), r ^ (i : ℕ))
            = (∑ i : Fin n, r ^ (i : ℕ)) + r ^ n := by
          rw [Fin.sum_univ_castSucc, Fin.val_last]
          exact congrArg (· + r ^ n)
            (Finset.sum_congr rfl (fun i _ => by rw [Fin.coe_castSucc]))
        have hsplit : r * (r ^ n * E 0 + eta ^ 2 * (G2 + sc2) * (∑ i : Fin n, r ^ (i : ℕ)))
            + eta ^ 2 * (G2 + sc2)
            = r ^ (n + 1) * E 0
              + eta ^ 2 * (G2 + sc2) * (∑ i : Fin (n + 1), r ^ (i : ℕ)) := by
          -- 注意 这一步**不是**纯 ring：需要几何恒等式
          --    `hgeo : r * S = S + r^n - 1`（`S := ∑ i : Fin n, r^i`，`geom_sum_mul` 的推论）。
          --    `ring`/`ring_nf` 都看不到它（关于 S 不是多项式恒等式），`nlinarith` 也不行
          --    （实测失败：目标含 `eta^2` 的非线性项）⟹ 用 **`linear_combination`** 按系数消掉。
          have hgeo : r * (∑ i : Fin n, r ^ (i : ℕ)) = (∑ i : Fin n, r ^ (i : ℕ)) + r ^ n - 1 := by
            rw [Fin.sum_univ_eq_sum_range (fun i => r ^ i) n]
            have h := geom_sum_mul r n
            linarith [h]
          rw [hsum_eq]
          linear_combination (eta ^ 2 * (G2 + sc2)) * hgeo
        calc E (n + 1)
            ≤ r * E n + eta ^ 2 * (G2 + sc2) := by rw [hr_def] at hs ⊢; linarith
          _ ≤ r * (r ^ n * E 0 + eta ^ 2 * (G2 + sc2) * (∑ i : Fin n, r ^ (i : ℕ)))
                + eta ^ 2 * (G2 + sc2) := by
              exact add_le_add_right (mul_le_mul_of_nonneg_left ih hr0) _
          _ = r ^ (n + 1) * E 0
                + eta ^ 2 * (G2 + sc2) * (∑ i : Fin (n + 1), r ^ (i : ℕ)) := hsplit
  have hsum := geom_sum_le_inv_one_sub hr0 hrlt T
  have hne : (1 : ℝ) - r = 2 * mu * eta := by rw [hr_def]; ring
  have hrw : 1 / (1 - r) = 1 / (2 * mu * eta) := by rw [hne]
  have hsum' : (∑ i : Fin T, r ^ (i : ℕ)) ≤ 1 / (2 * mu * eta) := by rw [← hrw]; exact hsum
  have hpos2 : 0 < 2 * mu * eta := by positivity
  calc E T ≤ r ^ T * E 0 + eta ^ 2 * (G2 + sc2) * (∑ i : Fin T, r ^ (i : ℕ)) := hiter
    _ ≤ r ^ T * E 0 + eta ^ 2 * (G2 + sc2) * (1 / (2 * mu * eta)) := by
        refine add_le_add_left ?_ _
        exact mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ ≤ r ^ T * E 0 + (G2 + sc2) / (2 * mu) := by
        have hkey : eta ^ 2 * (G2 + sc2) * (1 / (2 * mu * eta))
            = eta * ((G2 + sc2) / (2 * mu)) := by
          field_simp
          ring
        rw [hkey, hr_def]
        have hle : eta * ((G2 + sc2) / (2 * mu)) ≤ (G2 + sc2) / (2 * mu) := by
          have hnn : 0 ≤ (G2 + sc2) / (2 * mu) := by positivity
          nlinarith [heta1, hnn]
        linarith

/-- **δ 形式（`ε` 邻域 + 显式轮数）**：给定精度 `ε > 0`，若
`(G²+σc²)/(2μ) ≤ ε/2`（方差邻域可控）且
`(1−2μη)^T·E₀ ≤ ε/2`（初值项已衰减），则 `E_T ≤ ε`。

**诚实标注**：`hneigh` / `hinit` 是**显式假设**（本文件不反解 `T` 的对数公式，
那需要 `log` 的显式估计；`RealFedAsync` 已给出同类反解，此处保持
「条件 ⟹ 结论」的干净形式）。 -/
theorem unbiased_epsilon_certificate {E : ℕ → ℝ} {mu eta G2 sc2 eps E0 : ℝ} (T : ℕ)
    (hmu : 0 < mu) (heta : 0 < eta) (heta1 : eta ≤ 1) (hG2 : 0 ≤ G2) (hsc2 : 0 ≤ sc2)
    (hcon : 0 ≤ 1 - 2 * mu * eta)
    (hstep : ∀ t, E (t + 1) ≤ (1 - 2 * mu * eta) * E t + eta ^ 2 * (G2 + sc2))
    (hE0 : E 0 = E0)
    (hneigh : (G2 + sc2) / (2 * mu) ≤ eps / 2)
    (hinit : (1 - 2 * mu * eta) ^ T * E0 ≤ eps / 2) :
    E T ≤ eps := by
  have h := unbiased_compression_rate hmu heta heta1 hG2 hsc2 hcon hstep T
  rw [hE0] at h
  linarith

/-! ## 三、具体随机化压缩算子：rand-k 与 scaled top-k -/

/-- **`k = 1` 的 rand-k（均匀随机坐标 × n）**：均匀随机取一个坐标 `j`，
输出 `n · x j`（其余坐标为 0）。这是「保留 1 个坐标、放大 `n` 倍」的
标准 rand-k 无偏化写法。

期望空间 `Ω = Fin n`（选中的坐标），权重 `p ≡ 1/n`（均匀）。 -/
def randK {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ := (n : ℝ) * x j

/-- **rand-k 无偏**：`E_j[n·x j] = Σ_j (1/n)·n·x j = Σ x j`。

即 `k = 1` 的 rand-k 在**坐标平均**意义下无偏（把 `x` 的所有坐标求和视作
待压缩信号，随机取一个 ×n 是它的无偏估计）。 -/
theorem randK_unbiased {n : ℕ} (hn : (n : ℝ) ≠ 0) (x : Fin n → ℝ) :
    (∑ j : Fin n, (1 / (n : ℝ)) * randK x j) = ∑ j : Fin n, x j := by
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold randK
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hn, one_mul]
/-- **rand-k 方差恒等式**：`k = 1` 时，方差为
`Var_j[n·x j] = n·Σ x² − (Σ x)²`（**恒等式，不是不等式**）。

推导：`E[(n x_j)²] = (1/n)·n²·Σ x² = n·Σ x²`，`(E[n x_j])² = (Σ x)²`，
故 `Var = E[X²] − (E X)² = n·Σx² − (Σx)²`。 -/
theorem randK_variance_eq {n : ℕ} (hn : (n : ℝ) ≠ 0) (x : Fin n → ℝ) :
    (∑ j : Fin n, (1 / (n : ℝ)) * (randK x j - (∑ j' : Fin n, x j')) ^ 2)
      = (n : ℝ) * (∑ j : Fin n, x j ^ 2) - (∑ j : Fin n, x j) ^ 2 := by
  set S : ℝ := ∑ j : Fin n, x j with hS
  -- 展开：`Σ_j (1/n)(n x_j − S)² = n·Σx² − 2S·S + S² = n Σx² − S²`
  have hexp : ∀ j : Fin n, (1 / (n : ℝ)) * (randK x j - S) ^ 2
      = (n : ℝ) * x j ^ 2 - 2 * x j * S + S ^ 2 / (n : ℝ) := by
    intro j
    rw [randK]
    field_simp
    ring
  have hsum1 : (∑ j : Fin n, ((n : ℝ) * x j ^ 2 - 2 * x j * S + S ^ 2 / (n : ℝ)))
      = (n : ℝ) * (∑ j : Fin n, x j ^ 2) - 2 * S * (∑ j : Fin n, x j)
        + (n : ℝ) * (S ^ 2 / (n : ℝ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [show (∑ j : Fin n, 2 * x j * S) = 2 * S * (∑ j : Fin n, x j) by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [show (∑ _j : Fin n, S ^ 2 / (n : ℝ)) = (n : ℝ) * (S ^ 2 / (n : ℝ)) by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
  rw [hS] at hexp hsum1 ⊢
  rw [Finset.sum_congr rfl (fun j _ => hexp j), hsum1]
  field_simp
  ring

/-- **scaled top-k（重要性采样，`k = 1` 单坐标版）**：以概率 `q` 保留 `x`
并除以 `q`，否则输出 `0`。期望空间 `Ω = Bool`（`true` = 保留），
权重 `p true = q`、`p false = 1 − q`。

**无偏性**是重要性采样的核心：`q·(x/q) + (1−q)·0 = x`。 -/
def scaledTopK (x q : ℝ) (keep : Bool) : ℝ := if keep then x / q else 0

/-- **scaled top-k 无偏**：`q·(x/q) + (1−q)·0 = x`（`q ≠ 0`）。 -/
theorem scaledTopK_unbiased (x q : ℝ) (hq : q ≠ 0) :
    q * scaledTopK x q true + (1 - q) * scaledTopK x q false = x := by
  unfold scaledTopK
  simp only [if_true, if_false, mul_zero, add_zero]
  field_simp

/-- **scaled top-k 方差恒等式**：`Var = (1−q)/q · x²`（**恒等式**）。

推导：`E[C²] = q·(x/q)² = x²/q`、`(E C)² = x²`，
故 `Var = x²/q − x² = x²(1−q)/q`。
**`q → 1` 时方差 → 0**（保留概率越高方差越小，符合直觉）。 -/
theorem scaledTopK_variance_eq (x q : ℝ) (hq : 0 < q) :
    q * (scaledTopK x q true - x) ^ 2 + (1 - q) * (scaledTopK x q false - x) ^ 2
      = (1 - q) / q * x ^ 2 := by
  unfold scaledTopK
  simp only [if_true, if_false]
  field_simp
  ring

/-- **通信量换方差的显式权衡（B28 核心结论）**：相对方差 `σc²(λ) = (1−λ)/λ · Σx²`
（`λ = k/n` 是保留比例）满足

    `λ · σc²(λ) = (1 − λ) · Σx²`，

即**方差与保留比例的乘积**是关于 `λ` 的**线性递减**量。

推论（本定理的第二个合取项）：`λ ≥ 1/2` 时 `σc²(λ) ≤ Σx²`（方差不放大）；
**`λ → 1` 时方差 → 0**；`λ → 0` 时发散 —— 这正是「压缩率与方差的权衡」。

（代小整数复核：`λ = 1/2`、`x2 = 4` ⟹ `σc² = 4`；`λ·σc² = 2 = (1−1/2)·4` 成立。） -/
theorem randK_variance_shrinks (x2 : ℝ) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hx2 : 0 ≤ x2) :
    lam * ((1 - lam) / lam * x2) = (1 - lam) * x2 ∧
      (1 / 2 ≤ lam → (1 - lam) / lam * x2 ≤ x2) := by
  refine ⟨by field_simp, ?_⟩
  intro hhalf
  rw [div_mul_eq_mul_div, div_le_iff₀ hlam0]
  nlinarith [hlam1, hx2, hhalf]

/-- **无偏 ≠ 有界方差（诚实标注的机器验证）**：存在**无偏**的随机标量算子，
其方差**无界**（随 `M` 任意增大）——故"相对方差界"是**独立假设**，
不能由无偏性推出。

反例：`Ω = Bool`、`p = (1/2, 1/2)`、`C true = x + M`、`C false = x − M`。
则 `E[C] = x`（**无偏**），但 `Var = M²`（随 `M` 无界）。 -/
theorem unbiased_does_not_imply_bounded_variance (x M : ℝ) :
    ((1 / 2 : ℝ) * (x + M) + (1 / 2 : ℝ) * (x - M) = x) ∧
      ((1 / 2 : ℝ) * ((x + M) - x) ^ 2 + (1 / 2 : ℝ) * ((x - M) - x) ^ 2 = M ^ 2) :=
  ⟨by ring, by ring⟩

end Lattice
