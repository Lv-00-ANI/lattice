import Mathlib
import Lattice.Lib.InfoTheory.RealCrossEntropy
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealKLJointConvex
import Lattice.Lib.Convex.RealStrongDuality
import Lattice.Lib.Architectures.RealNormSharpConstant
import Lattice.Lib.Convex.RealPareto
import Lattice.Lib.Architectures.RealActComplete
/-!
# LATTICE: 反例集中库（RealCounterexamples）

本文件把「原稿命题为假」的反例**重新陈述并机器验证**（无 `sorry`/`axiom`/`admit`）。
每条声明都在 docstring 中标明【原命题】【为何假】【见证】【CORRECTIONS.md 编号】。

覆盖内容：

1. **B1** `CE(p,q) = 0 ⟺ p = q` 为假（均匀分布见证 `CE(p,p) = log 2 > 0`）；
2. **B3** 交叉熵 **非联合凸**（wrapper 引用 `ce_not_joint_convex` + 自建纯计算见证）；
3. **B5a** Slater 条件在**离散支撑**下不充分（wrapper + 间隙 ≥ 50 的推论）；
4. **B5b** 逆标量化对**离散可行集**为假（自建 3 点反例，机器验证两个方向）；
5. **（新）** i.i.d. 假设不可省：完全相关的两个样本使 Hoeffding 型界 `2e^{−nt²}` 被违反；
6. **B4** 归一化层常数 `2/c` 非紧（wrapper 引用 `unit_normalize_two_div_not_attained`）；
7. **B2** SiLU「非全局 Lipschitz」——**本文件给出更正：B2 本身为假**。
   `silu'(x) = σ(x) + x·σ(x)(1−σ(x))` 其实**有界**（`x → ±∞` 时分别趋于 1 与 0），
   故 SiLU 是**全局** Lipschitz 的。本文件机器验证 `|silu x − silu y| ≤ 2|x − y|`。

新名字统一加 `cex` 前缀（既有声明 `ce_not_joint_convex` /
`slater_not_sufficient_discrete` / `unit_normalize_two_div_not_attained` /
`silu_lipschitz_on` 以 **wrapper** 形式引用，不重名）。
-/

noncomputable section

namespace Lattice

/-! ## B1：`CE(p,q) = 0 ⟺ p = q` 为假

【原命题】交叉熵零化刻画分布相等：`CE(p,q) = 0 ⟺ p = q`。
【为何假】`CE(p,p) = H(p) > 0`（非退化 p）；CE 减去熵才是 KL。
【见证】`Fin 2` 上的均匀分布 `p = q = (1/2, 1/2)`：`CE(p,p) = log 2 > 0`。
【CORRECTIONS.md 编号】B1。 -/

/-- 【B1】`Fin 2` 上的均匀分布 `p = (1/2, 1/2)`。 -/
def cexUniform2 : Fin 2 → ℝ := fun _ => 1 / 2

/-- 【B1】【见证】`CE(p,p) = log 2`（p 为 `Fin 2` 上的均匀分布）。

计算：`CE(p,p) = −Σ_a p_a log p_a = −2·(1/2)·log(1/2) = log 2`。 -/
theorem cex_ce_self_eq_log_two :
    crossEntropy cexUniform2 cexUniform2 = Real.log 2 := by
  unfold cexUniform2 crossEntropy
  rw [Fin.sum_univ_two]
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlog]
  ring

/-- 【B1】【见证】`CE(p,p) > 0`：均匀分布的熵严格为正。 -/
theorem cex_ce_self_pos : 0 < crossEntropy cexUniform2 cexUniform2 := by
  rw [cex_ce_self_eq_log_two]
  exact Real.log_pos (by norm_num)

/-- 【B1】【原命题为假】在 `Fin 2 → ℝ` 上不存在「`CE(p,q) = 0 ⟺ p = q`」的一般刻画。

反证：取 `p = q = cexUniform2`，右端 `p = q` 真，左端由 `cex_ce_self_eq_log_two`
为 `log 2 ≠ 0`，矛盾。 -/
theorem cex_ce_zero_iff_eq_false :
    ¬ (∀ p q : Fin 2 → ℝ, crossEntropy p q = 0 ↔ p = q) := by
  intro h
  have h0 : crossEntropy cexUniform2 cexUniform2 = 0 := (h cexUniform2 cexUniform2).mpr rfl
  rw [cex_ce_self_eq_log_two] at h0
  exact absurd h0 (ne_of_gt (Real.log_pos (by norm_num)))

/-- 【B1】对照（真正的代数刻画 `ce_eq_zero_iff_support` 的实例化）：
`CE(p,q) = 0 ⟺ ∀ a, p a = 0 ∨ q a = 1`；在 `p = q = 均匀` 时右端为假，
故左端为假（`CE ≠ 0`）。即 CE 的零化刻画是**支撑/原子性**刻画，不是分布相等。 -/
theorem cex_ce_eq_zero_iff_support_contrast :
    (crossEntropy cexUniform2 cexUniform2 = 0 ↔
      ∀ _a : Fin 2, (1 / 2 : ℝ) = 0 ∨ (1 / 2 : ℝ) = 1) := by
  have h := ce_eq_zero_iff_support cexUniform2 cexUniform2
    (fun _ => by norm_num [cexUniform2]) (fun _ => by norm_num [cexUniform2])
    (by rw [Fin.sum_univ_two]; norm_num [cexUniform2])
  simpa [cexUniform2] using h

/-! ## B3：交叉熵非联合凸

【原命题】`(p,q) ↦ CE(p,q)` 联合凸。
【为何假】`CE(p,q) = KL(p‖q) + H(p)`，KL 联合凸但 `H(p)` **凹**，两者之和不再凸。
【见证】`k = 2, λ = 1/2`，`p₁ = q₁ = e₀`、`p₂ = q₂ = e₁`：
`CE(混合) = log 2 > 0 = (1/2)·0 + (1/2)·0`。
【CORRECTIONS.md 编号】B3。 -/

/-- 【B3】wrapper：引用只读的 `RealKLJointConvex.ce_not_joint_convex`
（k = 2、λ = 1/2、两个 one-hot 分布混合）。 -/
theorem cex_ce_not_joint_convex :
    ¬ ((1 : ℝ) / 2 * crossEntropy (pt2 0) (pt2 0)
        + (1 : ℝ) / 2 * crossEntropy (pt2 1) (pt2 1)
        ≥ crossEntropy (mixDist ((1 : ℝ) / 2) (pt2 0) (pt2 1))
            (mixDist ((1 : ℝ) / 2) (pt2 0) (pt2 1))) :=
  ce_not_joint_convex

/-- 【B3】自建见证用的 one-hot 向量 `eᵢ`（`Fin 2`）：`eᵢ i = 1`，否则 `0`。 -/
def cexOnehot : Fin 2 → Fin 2 → ℝ := fun i a => if a = i then 1 else 0

/-- 【B3】【自建纯计算见证】混合点的交叉熵**严格大于**交叉熵的混合：

`(1/2)·CE(e₀,e₀) + (1/2)·CE(e₁,e₁) < CE(p̄,p̄)`，其中 `p̄` 为 one-hot 的等权混合。 -/
theorem cex_ce_mix_gt_mix_ce :
    (1 : ℝ) / 2 * crossEntropy (cexOnehot 0) (cexOnehot 0)
        + (1 : ℝ) / 2 * crossEntropy (cexOnehot 1) (cexOnehot 1)
      < crossEntropy (mixDist ((1 : ℝ) / 2) (cexOnehot 0) (cexOnehot 1))
          (mixDist ((1 : ℝ) / 2) (cexOnehot 0) (cexOnehot 1)) := by
  have h0 : crossEntropy (cexOnehot 0) (cexOnehot 0) = 0 := by
    simp [crossEntropy, cexOnehot, Fin.sum_univ_two]
  have h1 : crossEntropy (cexOnehot 1) (cexOnehot 1) = 0 := by
    simp [crossEntropy, cexOnehot, Fin.sum_univ_two]
  have hmix : mixDist ((1 : ℝ) / 2) (cexOnehot 0) (cexOnehot 1) = cexUniform2 := by
    funext a
    fin_cases a <;> simp [mixDist, cexOnehot, cexUniform2] <;> norm_num
  rw [h0, h1, hmix, cex_ce_self_eq_log_two]
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## B5a：Slater 条件在离散支撑下不充分

【原命题】凸 + Slater ⟹ 强对偶（零间隙）。
【为何假】强对偶的核心是凸集分离 + 可行性/紧致性；离散非紧支撑下 Slater
（支撑内严格可行点存在）不足以保证零间隙。
【见证】`s = {−1, 1}`、`g(x) = x`（Slater 点 `x = −1`）、`f(−1) = 0`、`f(1) = −100`：
原问题最优值 `0`，任意 `λ ≥ 0` 的对偶值 `≤ −50`，故间隙恒 `≥ 50 > 0`。
【CORRECTIONS.md 编号】B5a。 -/

/-- 【B5a】wrapper：引用只读的 `RealStrongDuality.slater_not_sufficient_discrete`
（完整合取：Slater 成立 + 唯一可行点 + 对偶值上界 −50 + 可达 −50 + 严格间隙）。 -/
theorem cex_slater_not_sufficient_discrete :
    (∀ i : Fin 1, slaterCounterG i (-1) < 0) ∧
    (∀ x ∈ slaterCounterSupport, (∀ i, slaterCounterG i x ≤ 0) → x = -1) ∧
    (∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam ≤ -50) ∧
    (∃ lam : Fin 1 → ℝ, 0 ≤ lam 0 ∧
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam = -50) ∧
    (∀ lam : Fin 1 → ℝ, 0 ≤ lam 0 →
      dualValue slaterCounterF slaterCounterG slaterCounterSupport
        slaterCounterSupport_nonempty lam < slaterCounterF (-1)) :=
  slater_not_sufficient_discrete

/-- 【B5a】简化推论：**存在**非负乘子使对偶值 `≤ −50`，即间隙
`f(−1) − dualValue ≥ 50` 至少被某个乘子实现（此处 `λ = 50`）。 -/
theorem cex_slater_gap_at_least_fifty :
    ∃ lam : Fin 1 → ℝ, 0 ≤ lam 0 ∧
      50 ≤ slaterCounterF (-1) - dualValue slaterCounterF slaterCounterG
        slaterCounterSupport slaterCounterSupport_nonempty lam := by
  obtain ⟨-, -, hle, -, -⟩ := slater_not_sufficient_discrete
  refine ⟨fun _ => 50, by norm_num, ?_⟩
  have h := hle (fun _ : Fin 1 => 50) (by norm_num)
  rw [slaterCounterF_neg_one]
  linarith

/-! ## B5b：逆标量化对离散可行集为假

【原命题】Pareto 最优 ⟹ 存在非负权重使其为加权极小者（逆标量化）。
【为何假】对**离散可行集**为假：多目标的对偶/支撑超平面论证需要凸性（或连续
性），离散点集上加权和在离散点上仍可绕开 Pareto 点。
【见证】`x* = 0`（f = (0,0)）、`y₁ = 1`（f = (−5,1)）、`y₂ = 2`（f = (1,−1)）：
`x*` 是 Pareto 最优；但非负权重需同时满足 `w₁ ≥ 5w₀`（y₁ 给出）与 `w₁ ≤ w₀`
（y₂ 给出），迫使 `w₀ = w₁ = 0`，与非零权重矛盾。
【CORRECTIONS.md 编号】B5b。 -/

/-- 【B5b】反例目标函数（`Fin 2` 索引两个目标）：
在 `x = 0, 1, 2` 上取 `f₀ = 0, −5, 1`；`f₁ = 0, 1, −1`。 -/
def cexParetoF (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then (if x = 0 then 0 else if x = 1 then -5 else 1)
  else (if x = 0 then 0 else if x = 1 then 1 else -1)

/-- 【B5b】反例可行集 `{0, 1, 2}`（**离散**、非凸）。 -/
def cexParetoS : Set ℝ := {0, 1, 2}

/-- 【B5b】取值 `f₀(0) = 0`。 -/
theorem cexParetoF_00 : cexParetoF 0 0 = 0 := by
  unfold cexParetoF
  rw [if_pos rfl, if_pos rfl]

/-- 【B5b】取值 `f₀(1) = −5`。 -/
theorem cexParetoF_01 : cexParetoF 0 1 = -5 := by
  unfold cexParetoF
  rw [if_pos rfl, if_neg (by norm_num : ¬((1 : ℝ) = 0)), if_pos rfl]

/-- 【B5b】取值 `f₀(2) = 1`。 -/
theorem cexParetoF_02 : cexParetoF 0 2 = 1 := by
  unfold cexParetoF
  rw [if_pos rfl, if_neg (by norm_num : ¬((2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) = 1))]

/-- 【B5b】取值 `f₁(0) = 0`。 -/
theorem cexParetoF_10 : cexParetoF 1 0 = 0 := by
  unfold cexParetoF
  rw [if_neg (by decide : ¬((1 : Fin 2) = 0)), if_pos rfl]

/-- 【B5b】取值 `f₁(1) = 1`。 -/
theorem cexParetoF_11 : cexParetoF 1 1 = 1 := by
  unfold cexParetoF
  rw [if_neg (by decide : ¬((1 : Fin 2) = 0)),
    if_neg (by norm_num : ¬((1 : ℝ) = 0)), if_pos rfl]

/-- 【B5b】取值 `f₁(2) = −1`。 -/
theorem cexParetoF_12 : cexParetoF 1 2 = -1 := by
  unfold cexParetoF
  rw [if_neg (by decide : ¬((1 : Fin 2) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) = 0)),
    if_neg (by norm_num : ¬((2 : ℝ) = 1))]

/-- 【B5b】【定理 A】`x* = 0` 是 `cexParetoS` 上的 Pareto 最优。

`y = 1` 被 `f₁(1) = 1 > 0 = f₁(0)` 排除；`y = 2` 被 `f₀(2) = 1 > 0 = f₀(0)` 排除。 -/
theorem cexPareto_optimal_zero : ParetoOptimal cexParetoF cexParetoS 0 := by
  refine ⟨by simp [cexParetoS], ?_⟩
  intro y hy hd
  simp only [cexParetoS, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl | rfl
  · exact paretoDominates_irrefl cexParetoF 0 hd
  · obtain ⟨hle, -⟩ := hd
    have h := hle 1
    rw [cexParetoF_11, cexParetoF_10] at h
    norm_num at h
  · obtain ⟨hle, -⟩ := hd
    have h := hle 0
    rw [cexParetoF_02, cexParetoF_00] at h
    norm_num at h

/-- 【B5b】【定理 B】**逆标量化失败**：不存在非负、非零权重使 `0` 成为
`cexParetoS` 上加权和的极小者。

证明要点：`y = 1` 给出 `5·w₀ ≤ w₁`；`y = 2` 给出 `w₁ ≤ w₀`；两者合起来
`w₀ = w₁ = 0`，与「存在 `i` 使 `w i > 0`」矛盾。 -/
theorem cexPareto_no_scalarization :
    ¬ ∃ w : Fin 2 → ℝ, (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧
      ∀ y ∈ cexParetoS, WeightedSum cexParetoF w 0 ≤ WeightedSum cexParetoF w y := by
  rintro ⟨w, hw0, hpos, hmin⟩
  have hy1 : (1 : ℝ) ∈ cexParetoS := by simp [cexParetoS]
  have hy2 : (2 : ℝ) ∈ cexParetoS := by simp [cexParetoS]
  have hA : 5 * w 0 ≤ w 1 := by
    have h := hmin 1 hy1
    simp only [WeightedSum, Fin.sum_univ_two] at h
    rw [cexParetoF_00, cexParetoF_10, cexParetoF_01, cexParetoF_11] at h
    linarith
  have hB : w 1 ≤ w 0 := by
    have h := hmin 2 hy2
    simp only [WeightedSum, Fin.sum_univ_two] at h
    rw [cexParetoF_00, cexParetoF_10, cexParetoF_02, cexParetoF_12] at h
    linarith
  have hw0' : w 0 = 0 := le_antisymm (by linarith) (hw0 0)
  have hw1' : w 1 = 0 := le_antisymm (by linarith) (hw0 1)
  obtain ⟨i, hi⟩ := hpos
  have hwi : w i = 0 := by
    fin_cases i
    · exact hw0'
    · exact hw1'
  rw [hwi] at hi
  exact absurd hi (lt_irrefl 0)

/-! ## （新）i.i.d. 假设不可省：完全相关样本违反 Hoeffding 型界

【原命题】`P(|S̄ − μ| ≥ t) ≤ 2·exp(−2nt²)`（Hoeffding）在只有「有界」时成立，
不要求独立同分布。
【为何假】独立性是**必要**假设：若两个样本完全相关（`X₁ = X₂`），`S̄` 无平均化
效应，指数界不再成立。
【见证】`Ω = Fin 2`，各点权重 `1/2`；`X₁(ω) = X₂(ω) = 1`（ω = 0）或 `0`（ω = 1）。
则 `μ = 1/2`、`t = 1/2`、`n = 2` 时 `|S̄ − μ| = 1/2` **恒成立**，故
`P(|S̄ − μ| ≥ 1/2) = 1`，而 Hoeffding 上界 `2·exp(−2·2·(1/2)²) = 2e^{−1} < 1`，
界被违反。
【CORRECTIONS.md 编号】新（B2/B5 之外，任务要求补充）。 -/

/-- 【新】`Fin 2` 上的计数概率：`P(E) = Σ_ω [E ω]·(1/2)`。 -/
noncomputable def cexProb (E : Fin 2 → Prop) [DecidablePred E] : ℝ :=
  ∑ ω, (if E ω then (1 : ℝ) else 0) * (1 / 2)

/-- 【新】单个观测 `X(ω) = 1`（ω = 0）或 `0`（ω = 1）；`X₁ = X₂ = X`（完全相关）。 -/
def cexX : Fin 2 → ℝ
  | 0 => 1
  | 1 => 0

/-- 【新】`n = 2` 的样本均值：两个样本相同，故 `S̄(ω) = X(ω)`。 -/
def cexSampleMean : Fin 2 → ℝ := cexX

/-- 【新】Hoeffding 型上界的尾部常数 `2·exp(−1) < 1`（`e > 2`）。

由 `Real.add_one_lt_exp`（`x = 1`）得 `2 < e = exp 1`；两边乘 `exp(−1) > 0`。 -/
theorem cex_two_exp_neg_one_lt_one : 2 * Real.exp (-1) < 1 := by
  have h : (2 : ℝ) < Real.exp 1 := by
    have h1 := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    norm_num at h1
    linarith
  rw [Real.exp_neg]
  rw [show (2 : ℝ) * (Real.exp 1)⁻¹ = 2 / Real.exp 1 by rw [div_eq_mul_inv]]
  rw [div_lt_one (Real.exp_pos 1)]
  exact h

/-- 【新】【反例】缺少独立性时 Hoeffding 型界被违反：
`P(|S̄ − 1/2| ≥ 1/2) = 1` **且** `2·exp(−2·2·(1/2)²) < 1`。

（概率侧为 `1`，界侧严格小于 `1`，故「概率 ≤ 界」不成立。） -/
theorem cex_hoeffding_bound_fails_without_independence :
    cexProb (fun ω => (1 / 2 : ℝ) ≤ |cexSampleMean ω - 1 / 2|) = 1 ∧
      2 * Real.exp (-2 * (2 : ℝ) * ((1 / 2 : ℝ) ^ 2)) < 1 := by
  constructor
  · unfold cexProb
    rw [Fin.sum_univ_two]
    have h0 : (1 / 2 : ℝ) ≤ |cexSampleMean 0 - 1 / 2| := by
      rw [show cexSampleMean 0 = 1 by simp [cexSampleMean, cexX],
        show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have h1 : (1 / 2 : ℝ) ≤ |cexSampleMean 1 - 1 / 2| := by
      rw [show cexSampleMean 1 = 0 by simp [cexSampleMean, cexX],
        show (0 : ℝ) - 1 / 2 = -(1 / 2) by norm_num,
        abs_neg, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    rw [if_pos h0, if_pos h1]
    norm_num
  · have harg : -2 * (2 : ℝ) * (1 / 2 : ℝ) ^ 2 = -1 := by norm_num
    rw [harg]
    exact cex_two_exp_neg_one_lt_one

/-! ## B4：归一化层常数 `2/c` 非紧

【原命题】`unit_normalize` 的 Lipschitz 界常数 `2/c` 是紧常数。
【为何假】实内积空间中真实紧常数是 `1/c`，且在反向点 `x = c·u, y = −c·u` 处取等；
`2/c` 在该点严格。
【见证】`x = c`、`y = −c`：左边 `= 2`，`(2/c)·‖c − (−c)‖ = (2/c)·2c = 4 > 2`。
【CORRECTIONS.md 编号】B4。 -/

/-- 【B4】wrapper：引用只读的 `RealNormSharpConstant.unit_normalize_two_div_not_attained`
（`c > 0` 时反极点对上的严格不等式，表明 `2/c` 非紧）。 -/
theorem cex_unit_normalize_two_div_not_attained (c : ℝ) (hc : 0 < c) :
    ‖(1 / ‖(c : ℝ)‖) • (c : ℝ) - (1 / ‖(-c : ℝ)‖) • (-c : ℝ)‖
      < (2 / c) * ‖(c : ℝ) - (-c : ℝ)‖ :=
  unit_normalize_two_div_not_attained c hc

/-! ## B2（更正）：SiLU **是全局 Lipschitz 的** —— 原「非全局 Lipschitz」判断为假

【原命题（CORRECTIONS B2）】`silu'(x) = σ(x) + x·σ(x)(1−σ(x))` 无全局上界
（声称 `x → +∞` 时线性增长），故 SiLU 非全局 Lipschitz。
【为何**该更正本身为假**】`x·σ(x)(1−σ(x)) = x·σ(x)·σ(−x)`；
`σ(−x) ≈ e^{−x}`，故 `x·σ(x)·σ(−x) ≈ x·e^{−x} → 0`，而 `σ(x) → 1`。
因此 `silu'(x) → 1`（`x → +∞`）与 `→ 0`（`x → −∞`），**导数有界**，
`s` 的全局 Lipschitz 常数存在（真实值约 `1.0998`）。
【见证】本文件机器验证 `|silu x − silu y| ≤ 2·|x − y|`（对一切 `x, y : ℝ`），
并据此给出 `∃ L ≥ 0, ...`；即**否定**了「不存在全局 Lipschitz 常数」。
【CORRECTIONS.md 编号】B2（本文件对该条作出更正/降级说明）。
【诚实标注】**降级说明**：任务要求机器验证 `¬ ∃ L, ...`；经核验该命题为**假**，
故不证。改为机器验证其否定 `∃ L, 0 ≤ L ∧ ∀ x y, |silu x − silu y| ≤ L|x − y|`
（`L = 2`），并保留有界域版本 `silu_lipschitz_on` 作为对照。 -/

/-- 【B2 辅助】`1 − σ(z) ≤ exp(−z)`：这是 `1 − σ` 的**上界**，等价地
`σ(z) ≥ 1 − exp(−z)`，即 σ 的一个**下界**估计。 -/
lemma cex_sigmoid_one_sub_le_exp_neg (z : ℝ) : 1 - sigmoid z ≤ Real.exp (-z) := by
  have he : 0 < Real.exp (-z) := Real.exp_pos (-z)
  have h1e : 0 < 1 + Real.exp (-z) := by linarith
  have hdecomp : 1 - sigmoid z = Real.exp (-z) / (1 + Real.exp (-z)) := by
    have hne : (1 + Real.exp (-z)) ≠ 0 := ne_of_gt h1e
    field_simp [sigmoid, hne]
    try ring
  rw [hdecomp, div_le_iff₀ h1e]
  nlinarith [he]

/-- 【B2 辅助】`σ(z) ≤ exp(z)`（σ 的上界）。 -/
lemma cex_sigmoid_le_exp (z : ℝ) : sigmoid z ≤ Real.exp z := by
  have he : 0 < Real.exp (-z) := Real.exp_pos (-z)
  have h1e : 0 < 1 + Real.exp (-z) := by linarith
  have hez : 0 < Real.exp z := Real.exp_pos z
  have hprod : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [sigmoid, div_le_iff₀ h1e]
  nlinarith [hprod, hez, he]

/-- 【B2 辅助】`u·exp(−u) ≤ 1`（`u ≥ 0`），由 `u ≤ e^u`。 -/
lemma cex_mul_exp_neg_le_one (u : ℝ) (_hu : 0 ≤ u) : u * Real.exp (-u) ≤ 1 := by
  have hle : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have he : 0 < Real.exp (-u) := Real.exp_pos (-u)
  calc u * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hle (le_of_lt he)
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- 【B2 辅助】`|z|·σ(z)·(1−σ(z)) ≤ 1`（关键衰减估计：`x·σ(x)σ(−x) ≤ x·e^{−x} ≤ 1`）。 -/
lemma cex_abs_mul_sigmoid_mul_one_sub_le_one (z : ℝ) :
    |z| * (sigmoid z * (1 - sigmoid z)) ≤ 1 := by
  have hσ0 : 0 ≤ sigmoid z := le_of_lt (sigmoid_bounds z).1
  have hone : 0 ≤ 1 - sigmoid z := by linarith [(sigmoid_bounds z).2]
  rcases le_or_lt 0 z with hz | hz
  · have h1 : 1 - sigmoid z ≤ Real.exp (-z) := cex_sigmoid_one_sub_le_exp_neg z
    have hσ1 : sigmoid z ≤ 1 := le_of_lt (sigmoid_bounds z).2
    have hbound : sigmoid z * (1 - sigmoid z) ≤ Real.exp (-z) := by
      calc sigmoid z * (1 - sigmoid z) ≤ 1 * (1 - sigmoid z) :=
            mul_le_mul_of_nonneg_right hσ1 hone
        _ = 1 - sigmoid z := one_mul _
        _ ≤ Real.exp (-z) := h1
    have hz1 : z * Real.exp (-z) ≤ 1 := cex_mul_exp_neg_le_one z hz
    calc |z| * (sigmoid z * (1 - sigmoid z)) = z * (sigmoid z * (1 - sigmoid z)) := by
          rw [abs_of_nonneg hz]
      _ ≤ z * Real.exp (-z) := mul_le_mul_of_nonneg_left hbound hz
      _ ≤ 1 := hz1
  · have hzle : z ≤ 0 := le_of_lt hz
    have h2 : sigmoid z ≤ Real.exp z := cex_sigmoid_le_exp z
    have hbound : sigmoid z * (1 - sigmoid z) ≤ Real.exp z := by
      calc sigmoid z * (1 - sigmoid z) ≤ sigmoid z * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [(sigmoid_bounds z).2]) hσ0
        _ = sigmoid z := mul_one _
        _ ≤ Real.exp z := h2
    have hnegz : 0 ≤ -z := by linarith
    have hz1 : (-z) * Real.exp (-(-z)) ≤ 1 := cex_mul_exp_neg_le_one (-z) hnegz
    have hz1' : (-z) * Real.exp z ≤ 1 := by simpa using hz1
    calc |z| * (sigmoid z * (1 - sigmoid z)) = (-z) * (sigmoid z * (1 - sigmoid z)) := by
          rw [abs_of_neg hz]
      _ ≤ (-z) * Real.exp z := mul_le_mul_of_nonneg_left hbound hnegz
      _ ≤ 1 := hz1'

/-- 【B2 辅助】`‖deriv silu z‖ ≤ 2`：`|σ + zσ(1−σ)| ≤ σ + |z|σ(1−σ) ≤ 1 + 1`。 -/
lemma cex_abs_deriv_silu_le_two (z : ℝ) : ‖deriv silu z‖ ≤ 2 := by
  have hderiv : deriv silu z = sigmoid z + z * (sigmoid z * (1 - sigmoid z)) := by
    have hprod : HasDerivAt (fun t : ℝ => t * sigmoid t)
        (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z :=
      (hasDerivAt_id' z).mul (sigmoid_hasDerivAt z)
    have hd : deriv (fun t : ℝ => t * sigmoid t) z =
        1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z)) := hprod.deriv
    simpa [silu] using hd
  rw [hderiv, Real.norm_eq_abs]
  have hσ0 : 0 ≤ sigmoid z := le_of_lt (sigmoid_bounds z).1
  have hσ1 : sigmoid z ≤ 1 := le_of_lt (sigmoid_bounds z).2
  have hσder : 0 ≤ sigmoid z * (1 - sigmoid z) := by nlinarith
  have hb := cex_abs_mul_sigmoid_mul_one_sub_le_one z
  calc |sigmoid z + z * (sigmoid z * (1 - sigmoid z))|
      ≤ |sigmoid z| + |z * (sigmoid z * (1 - sigmoid z))| := abs_add _ _
    _ = sigmoid z + |z| * (sigmoid z * (1 - sigmoid z)) := by
          rw [abs_of_nonneg hσ0, abs_mul, abs_of_nonneg hσder]
    _ ≤ 1 + 1 := by linarith
    _ = 2 := by norm_num

/-- 【B2（更正）】SiLU 在 ℝ 上**是 2-Lipschitz 的**（全局，经 MVT + 导数界 `≤ 2`）。

这条机器验证结果**否定**了 CORRECTIONS B2 的「silu 非全局 Lipschitz」判断。 -/
theorem cex_silu_globally_lipschitz (x y : ℝ) : |silu x - silu y| ≤ 2 * |x - y| := by
  have hf : ∀ z : ℝ, z ∈ Set.univ → DifferentiableAt ℝ silu z := by
    intro z _
    have hd : HasDerivAt silu (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z := by
      have h : HasDerivAt (fun t : ℝ => t * sigmoid t)
          (1 * sigmoid z + z * (sigmoid z * (1 - sigmoid z))) z :=
        (hasDerivAt_id' z).mul (sigmoid_hasDerivAt z)
      simpa [silu] using h
    exact hd.differentiableAt
  have hbound : ∀ z : ℝ, z ∈ Set.univ → ‖deriv silu z‖ ≤ 2 :=
    fun z _ => cex_abs_deriv_silu_le_two z
  have hmvt : ‖silu y - silu x‖ ≤ 2 * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (f := silu) (s := Set.univ)
      (x := x) (y := y) hf hbound convex_univ trivial trivial
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt

/-- 【B2（更正）】全局 Lipschitz 常数**存在**（`L = 2`）：直接否定
「不存在全局 Lipschitz 常数」。 -/
theorem cex_silu_global_lipschitz_exists :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, |silu x - silu y| ≤ L * |x - y| :=
  ⟨2, by norm_num, fun x y => cex_silu_globally_lipschitz x y⟩

/-- 【B2（更正）】任务稿所要求的 `¬ ∃ L, ...` 为**假**（其双重否定被机器否定：
`¬¬(∃ L, ...)` 由 `cex_silu_global_lipschitz_exists` 直接给出）。 -/
theorem cex_silu_not_global_lipschitz_false :
    ¬ (¬ ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, |silu x - silu y| ≤ L * |x - y|) :=
  fun h => h cex_silu_global_lipschitz_exists

/-- 【B2】对照（wrapper）：只读的 `RealActComplete.silu_lipschitz_on`
给出的**有界域**版本 `[-M, M]` 上 `(1 + M/4)`-Lipschitz，与全局版共存。 -/
theorem cex_silu_lipschitz_on_bounded (M x y : ℝ) (hM : 0 ≤ M)
    (hx : x ∈ Set.Icc (-M) M) (hy : y ∈ Set.Icc (-M) M) :
    |silu x - silu y| ≤ (1 + M / 4) * |x - y| :=
  silu_lipschitz_on M x y hM hx hy

end Lattice
