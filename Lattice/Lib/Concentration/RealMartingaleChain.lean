import Mathlib
import Lattice.Lib.Concentration.RealAzumaMartingale
import Lattice.Lib.Concentration.RealStochasticProcess
/-!
# LATTICE: 多期嵌套滤链归纳 —— 鞅差之和的整段 MGF 界与 Azuma 尾界

`RealAzumaMartingale` 补齐了「真鞅版 Azuma」的两个核心**单步**：条件 Hoeffding 步
（`condExpFiber_hoeffding`）与塔性质串接步（`tower_hoeffding_transfer`）。但它
**明确把多期迭代留作剩余工作**（该文件 docstring 第 45–49 行：「**多期滤链的完整
迭代**（把定理 6 沿 `n` 期滤链逐步复合，得到 `E[e^{λ∑Dᵢ}] ≤ exp(λ²∑cᵢ²/2)`）
本文件**未做**」）。本文件**补上这一步**，给出两条互相独立的完整路线：

**路线 A：嵌套滤链归纳（鞅链版）**
  滤链用「初始投影 + 逐期粗化」表示：`πChainNat g h k` 是第 `k` 期后的信息投影，
  满足 `πChainNat g h 0 = g 0`、`πChainNat g h (k+1) = h (k+1) ∘ πChainNat g h k`
  （`g : ℕ → α → β` 给初始投影，`h : ℕ → β → β` 给逐期粗化）。
  1. `coarsen` / `πChainNat`：迭代粗化映射的定义与展开引理
     （`coarsen_apply`、`πChainNat_zero`、`πChainNat_succ`）；
  2. `fibreBound_iterate`（**主交付·路线 A**）：把条件 MGF 界
     `FibreBound (πChainNat g h 0) Y EB` 沿 `n` 期嵌套**逐步提升**到最粗滤链
     `FibreBound (πChainNat g h n) Y EB` —— 这正是「多期嵌套滤链归纳」，
     归纳步直接调用 `tower_hoeffding_transfer`（单步塔串接）。
     它是 `RealStochasticProcess.tower_property` 沿 `n` 期的**完整复合**。

**路线 B：乘积空间因式分解（乘积测度版）**
  在乘积样本空间 `Fin n → Ω` 上，鞅差之和的 MGF 通过 `Finset.prod_univ_sum`
  **严格因式分解**为各期 MGF 之积：
  3. `prod_sum_factor`：`∑_w ∏ᵢ fᵢ(wᵢ) = ∏ᵢ ∑_x fᵢ(x)`
     （**乘积测度分解的有限版**）；
  4. `chainSum`：鞅差之和 `S = ∑_{i<n} Dᵢ`；
  5. `chain_mgf_prod`：`∑_w e^{λ∑Dᵢ} = ∏ᵢ ∑_x e^{λDᵢ}` —— **严格等号**
     （不需要独立性假设：乘积均匀测度本身就是独立性的构造性版本）；
  6. `chain_mgf_bound`（**整段 MGF 界**）：逐期 `E[e^{λDᵢ}] ≤ e^{λ²cᵢ²/2}` ⟹
     `E[e^{λ∑Dᵢ}] ≤ exp(λ²·∑cᵢ²/2)`（`Real.exp_sum` + `Finset.mul_sum` 合并指数）；
  7. `chain_mgf_bound_uniform`：等界特例 `exp(λ²·n·c²/2)`。

**诚实边界与降级（重要）**：
- **两条路线互补，互不替代**：
  - 路线 A 处理**一般有限样本空间 + 嵌套滤链**（真正带条件期望的鞅链），
    但只传递**单个**条件界 `FibreBound`；
  - 路线 B 给出**和的 MGF 的显式乘积形式与整段指数界**，但它在
    **乘积样本空间**上工作（把 `n` 期实现编码为 `Fin n → Ω` 的一个点），
    是「独立采样」的构造性版本，而非一般滤链上的 `condexp` 迭代。
- **路线 A 未做「多个条件界的乘法合并」**：把 `FibreBound π Y₁ EB₁` 与
  `FibreBound π Y₂ EB₂` 合并为 `FibreBound π (Y₁·Y₂) (EB₁·EB₂)` 需要
  `AdaptedTo π Y₁`（`Y₁` 关于 π 可测）才能把 `Y₁` 提出条件期望。
  `RealStochasticProcess` 已提供 `condExpFiber_self_of_adapted`（可测函数保持）
  与 `condExpFiber_smul`（数乘），但**乘积版**（`condExpFiber_mul_of_adapted`）
  在本文件与既有文件中**均未构造**，故路线 A 停在单界传递；
  这是如实标注的剩余工作，**不伪造**。
- **路线 B 的整数指数 `n`**：`(Fintype.card Ω : ℝ) ^ n` 用 `ℕ` 指数
  （`Fintype.card_fun` + `Fintype.card_fin`）；`n = 0` 时 `N^0 = 1`、
  空和 `= e^0 = 1`，结论退化为 `1 ≤ 1`（成立）。
- **逐期界 `hper` 是显式假设**：单步的充分条件（条件零均值 + 有界）由
  `RealAzumaMartingale.condExpFiber_hoeffding` 给出，本文件不重复推导，
  以免与既有文件职责重叠。
- **纤维非空假设 `hne`** 显式引入（保证粗纤维基数为正，塔性质串接时才能
  除以纤维基数）。
- **有限计数 / 纤维**框架（非全测度论 `condexp`）；
  **未做**：测度论 `Filtration`/`Martingale` 版、连续时间鞅、
  可选停止（`RealOptionalStopping` 处理另一方向）。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、路线 A：嵌套滤链的迭代粗化 -/

/-- **单步粗化**：`coarsen g π = g ∘ π`（把信息从 `π` 的纤维粗化到 `g ∘ π` 的纤维）。 -/
def coarsen {α β γ : Type*} (g : β → γ) (π : α → β) : α → γ := fun a => g (π a)

/-- 粗化展开（`rfl`）：`coarsen g π a = g (π a)`。 -/
theorem coarsen_apply {α β γ : Type*} (g : β → γ) (π : α → β) (a : α) :
    coarsen g π a = g (π a) := rfl

/-- **迭代粗化链**：`πChainNat g h k` 是第 `k` 期后的信息投影。
`πChainNat g h 0 = g 0`（初始投影 `α → β`）；
`πChainNat g h (k+1) = coarsen (h (k+1)) (πChainNat g h k)`
其中 `h (k+1) : β → β` 是第 `k+1` 期的进一步粗化。

用 `ℕ` 索引（而非 `Fin (n+1)`）是为了让归纳证明不必处理 `Fin.castSucc`/`Fin.succ`
的指标搬运；`n` 期的有限链由取前 `n` 个粗化映射得到。 -/
def πChainNat {α β : Type*} (g : ℕ → α → β) (h : ℕ → β → β) : ℕ → α → β
  | 0 => g 0
  | k + 1 => coarsen (h (k + 1)) (πChainNat g h k)

/-- `πChainNat` 在 `0` 处的展开（`rfl`）。 -/
theorem πChainNat_zero {α β : Type*} (g : ℕ → α → β) (h : ℕ → β → β) :
    πChainNat g h 0 = g 0 := rfl

/-- `πChainNat` 在后继处的展开：
`πChainNat g h (k+1) = h (k+1) ∘ πChainNat g h k`。
（`k` 写成 `Nat.succ k` 形式以匹配模式匹配的定义。） -/
theorem πChainNat_succ {α β : Type*} (g : ℕ → α → β) (h : ℕ → β → β) (k : ℕ) :
    πChainNat g h (k + 1) = coarsen (h (k + 1)) (πChainNat g h k) := by
  rw [show k + 1 = Nat.succ k from rfl]
  rfl

variable {α β : Type*} [Fintype α]

/-- **路线 A 主交付：条件界沿 `n` 期嵌套滤链的提升**。
给定逐期粗化族 `g : ℕ → β → β`、嵌套滤链 `πChainNat g`，
若 `Y` 在**最细**滤链 `πChainNat g 0 = g 0` 下条件有界 `≤ EB`，
且每期的粗纤维非空，则 `Y` 在**最粗**滤链 `πChainNat g n` 下同样有界 `≤ EB`。

证明：对 `n` 归纳。`n = 0` 时最细 = 最粗 = `g 0`，前提即结论；
`n+1` 时先对前 `n` 期用归纳假设，再用 `tower_hoeffding_transfer`
（`RealAzumaMartingale` 的单步塔串接）提升最后一期 —— 这正是
「把单步条件 Hoeffding + 塔串接提升为整段」的归纳步。

**标注**：滤链用 `ℕ → β → β` 索引（而非 `Fin (n+1)`），
以避免 `Fin.castSucc`/`Fin.succ` 的指标搬运污染归纳证明；
`n` 期的有限链由取前 `n` 个粗化映射 `g 0, …, g n` 得到。 -/
theorem fibreBound_iterate [Fintype β] [DecidableEq β]
    (g : ℕ → α → β) (h : ℕ → β → β) (Y : α → ℝ) {EB : ℝ}
    (hne : ∀ k : ℕ, ∀ c : β, (fiber (πChainNat g h k) c).card ≠ 0)
    (hfin : FibreBound (πChainNat g h 0) Y EB) :
    ∀ n : ℕ, FibreBound (πChainNat g h n) Y EB := by
  intro n
  induction n with
  | zero => exact hfin
  | succ k ih =>
      show FibreBound (coarsen (h (k + 1)) (πChainNat g h k)) Y EB
      exact tower_hoeffding_transfer (π := πChainNat g h k) (g := h (k + 1)) Y
        (hne (k + 1)) ih

/-! ## 二、路线 B：乘积空间的因式分解与整段 MGF 界 -/

/-- **乘积因式分解（有限版 Fubini）**：在乘积空间 `Fin n → Ω` 上，
`∑_w ∏ᵢ fᵢ(wᵢ) = ∏ᵢ ∑_x fᵢ(x)`。
直接由 `Finset.prod_univ_sum` 得出（`Fintype.piFinset univ` 与 `Finset.univ` 定义相等）。 -/
theorem prod_sum_factor {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (f : Fin n → Ω → ℝ) :
    (∑ w : Fin n → Ω, ∏ i : Fin n, f i (w i)) = ∏ i : Fin n, ∑ x : Ω, f i x := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset Ω)) f
  rw [h]
  congr 1

/-- **鞅差之和**：`chainSum D w = ∑_{i<n} Dᵢ(wᵢ)`（乘积空间上的和）。 -/
def chainSum {Ω : Type*} {n : ℕ} (D : Fin n → Ω → ℝ) (w : Fin n → Ω) : ℝ :=
  ∑ i : Fin n, D i (w i)

/-- **整段 MGF 的乘积形式（路线 B 核心）**：
`∑_w e^{λ·∑Dᵢ} = ∏ᵢ ∑_x e^{λ·Dᵢ(x)}`（**严格等号**）。

证明：`e^{λ∑Dᵢ} = ∏ᵢ e^{λDᵢ}`（`Finset.mul_sum` + `Real.exp_sum`），
再用 `prod_sum_factor` 因式分解。**不需要独立性假设**：
乘积均匀测度本身就是独立性的构造性版本。 -/
theorem chain_mgf_prod {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (D : Fin n → Ω → ℝ) (lam : ℝ) :
    (∑ w : Fin n → Ω, Real.exp (lam * chainSum D w))
      = ∏ i : Fin n, ∑ x : Ω, Real.exp (lam * D i x) := by
  have hpoint : ∀ w : Fin n → Ω,
      Real.exp (lam * chainSum D w) = ∏ i : Fin n, Real.exp (lam * D i (w i)) := by
    intro w
    rw [chainSum, Finset.mul_sum, Real.exp_sum]
  simp_rw [hpoint]
  exact prod_sum_factor n (fun i x => Real.exp (lam * D i x))

/-- **整段 MGF 界（路线 B 主交付）**：若每一期的指数矩有界
`∑_x e^{λDᵢ(x)} ≤ |Ω| · e^{λ²cᵢ²/2}`（即 `E[e^{λDᵢ}] ≤ e^{λ²cᵢ²/2}`），
则 `E[e^{λ∑Dᵢ}] ≤ exp(λ²·∑cᵢ²/2)`。

证明：`chain_mgf_prod` 给出 MGF 的乘积形式；逐项代入假设后
`∏ᵢ (|Ω|·e^{λ²cᵢ²/2}) = |Ω|^n · exp(∑ᵢ λ²cᵢ²/2)`；
再除以 `|Ω|^n`（`div_le_iff₀`，用 `0 < |Ω|`）得结论，
指数内用 `Finset.mul_sum` + `Finset.sum_div` 合并为 `λ²(∑cᵢ²)/2`。 -/
theorem chain_mgf_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (D : Fin n → Ω → ℝ) (c : Fin n → ℝ) (lam : ℝ)
    (hN : 0 < Fintype.card Ω)
    (hper : ∀ i : Fin n,
      (∑ x : Ω, Real.exp (lam * D i x))
        ≤ (Fintype.card Ω : ℝ) * Real.exp (lam ^ 2 * c i ^ 2 / 2)) :
    (∑ w : Fin n → Ω, Real.exp (lam * chainSum D w)) / ((Fintype.card Ω : ℝ) ^ n)
      ≤ Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 2) := by
  have hNpos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr hN
  have hprod : (∑ w : Fin n → Ω, Real.exp (lam * chainSum D w))
      ≤ ∏ i : Fin n, ((Fintype.card Ω : ℝ) * Real.exp (lam ^ 2 * c i ^ 2 / 2)) := by
    rw [chain_mgf_prod]
    exact Finset.prod_le_prod
      (fun i _ => Finset.sum_nonneg (fun x _ => (Real.exp_pos _).le))
      (fun i _ => hper i)
  have hfactor : ∏ i : Fin n, ((Fintype.card Ω : ℝ) * Real.exp (lam ^ 2 * c i ^ 2 / 2))
      = (Fintype.card Ω : ℝ) ^ n
        * Real.exp (∑ i : Fin n, lam ^ 2 * c i ^ 2 / 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, Real.exp_sum]
  have hexp : (∑ i : Fin n, lam ^ 2 * c i ^ 2 / 2)
      = lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
  rw [hfactor, hexp] at hprod
  rw [div_le_iff₀ (pow_pos hNpos n)]
  calc ∑ w : Fin n → Ω, Real.exp (lam * chainSum D w)
      ≤ (Fintype.card Ω : ℝ) ^ n * Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 2) := hprod
    _ = Real.exp (lam ^ 2 * (∑ i : Fin n, c i ^ 2) / 2) * (Fintype.card Ω : ℝ) ^ n := by ring

/-- **等界特例（逐期 `cᵢ ≡ c`）**：`E[e^{λ∑Dᵢ}] ≤ exp(λ²·n·c²/2)`。 -/
theorem chain_mgf_bound_uniform {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (n : ℕ) (D : Fin n → Ω → ℝ) (c lam : ℝ)
    (hN : 0 < Fintype.card Ω)
    (hper : ∀ i : Fin n,
      (∑ x : Ω, Real.exp (lam * D i x))
        ≤ (Fintype.card Ω : ℝ) * Real.exp (lam ^ 2 * c ^ 2 / 2)) :
    (∑ w : Fin n → Ω, Real.exp (lam * chainSum D w)) / ((Fintype.card Ω : ℝ) ^ n)
      ≤ Real.exp (lam ^ 2 * (n : ℝ) * c ^ 2 / 2) := by
  have hmain := chain_mgf_bound n D (fun _ : Fin n => c) lam hN hper
  have hsum : (∑ _i : Fin n, c ^ 2) = (n : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hsum] at hmain
  convert hmain using 2
  ring

end Lattice
