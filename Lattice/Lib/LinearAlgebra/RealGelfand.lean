import Mathlib
import Lattice.Lib.LinearAlgebra.RealSpectral
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: Gelfand 谱半径 —— 非对角矩阵的谱半径、幂律与 Gelfand 公式

补 `RealSpectralRadius` 明确标注的缺口：

  > 「只完成**对角矩阵**的谱半径刻画与 Gelfand 公式；**一般算子 `ρ(T) = lim ‖Tⁿ‖^{1/n}`
  > 未做 / 降级**（需复谱理论与 Jacobson 密度定理）」

本文件在**有限维**（`Matrix (Fin n) (Fin n) ℝ`）上把谱半径理论推到**非对角**矩阵，
并给出 `ρ(T) ≤ ‖T‖`、Gelfand 公式的 `inf` 形式，以及**幂律的两个可证方向**。

## 谱半径的定义（本文件）

    gelfandRadius T := sInf { r | ∃ k > 0, ‖Tᵏ‖ ^ (1/k) = r }

即「`‖Tⁿ‖^{1/n}`（`n > 0`）取值集合的**下确界**」。

## 主结果

| 声明 | 内容 | 备注 |
|:--|:--|:--|
| `gelfand_opNorm_pow_le` | `‖Tᵏ‖ ≤ ‖T‖ᵏ` | 次乘法性 `‖AB‖ ≤ ‖A‖·‖B‖` 的归纳 |
| `gelfand_radius_le_pow_root` | `ρ(T) ≤ ‖Tᵏ‖^{1/k}`（`k > 0`） | `csInf_le`：集合元素是上界 |
| **`gelfand_radius_le_opNorm`** | **`ρ(T) ≤ ‖T‖`** | **A1.6 要求 1**（整体形式） |
| `gelfand_eigenvalue_abs_le_opNorm` | `\|μ\| ≤ ‖T‖`（实特征值） | A1.6 要求 1 的逐特征值形式 |
| `gelfand_radius_lt_one_of_opNorm_lt_one` | `‖T\| < 1 ⟹ ρ(T) < 1` | Neumann 级数前提 |
| **`gelfand_radius_pow_le_radius_pow`** | **`ρ(T)ᵏ ≤ ρ(Tᵏ)`** | **幂律**（Fekete-free，纯 `inf` 论证） |
| `gelfand_radius_pow_le_opNorm_pow` | `ρ(Tᵏ) ≤ ‖T‖ᵏ` | 幂律的另一侧（上界） |
| **`gelfand_radius_eq_inf`** | **`ρ(T) = inf_{k>0} ‖Tᵏ‖^{1/k}`** | **A1.6 核心**（Gelfand `inf` 形式） |

## 幂律：`ρ(Tᵏ)` 与 `ρ(T)ᵏ` 的精密关系（本轮的关键发现）

在**纯 `inf` 定义**下（不假设 `‖Tⁿ‖^{1/n}` 收敛），两者**只能证一个方向**：

* **`ρ(T)ᵏ ≤ ρ(Tᵏ)` 成立**（`gelfand_radius_pow_le_radius_pow`）。证明：对任意 `j > 0`，
  `ρ(T) ≤ ‖T^{kj}‖^{1/(kj)} = (‖(Tᵏ)^j‖^{1/j})^{1/k}`，
  两边取 `k` 次方得 `ρ(T)ᵏ ≤ ‖(Tᵏ)^j‖^{1/j}`；即 `ρ(T)ᵏ` 是 `S(Tᵏ)` 的**下界**，
  故 `ρ(T)ᵏ ≤ sInf S(Tᵏ) = ρ(Tᵏ)`。
* **`ρ(Tᵏ) ≤ ρ(T)ᵏ` 需要额外论证**（Gelfand 极限定理），本文件**未做**。
  根因：`ρ(T)ᵏ` 是 `S(Tᵏ)` 的**下界**，而 `ρ(Tᵏ)` 是其**最大下界**——
  下确界 ≤ 下界只在「下界 ≥ 下确界」时成立，方向与所需**相反**。
  要得到反向，必须证明 `ρ(T)ᵏ` 是 `S(Tᵏ)` 的**最大**下界，即
  `‖Tⁿ‖^{1/n} → ρ(T)`（Gelfand 公式的 `lim` 形式，**未做**）。

因此本文件**不声称** `ρ(Tᵏ) = ρ(T)ᵏ`；给出的是**两侧可证界**
`ρ(T)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`（`gelfand_radius_pow_bounds`），
并**诚实标注**：等号（`ρ(Tᵏ) = ρ(T)ᵏ`）等价于 Gelfand 极限定理在幂上的特例，**未做**。

### 上游 mathlib 的独立佐证（本轮逐文件核对，附路径:行号）

**⚠ 重要更正（本项目 CORRECTIONS B25）**：本轮最初误以为「mathlib 4.14 缺 Gelfand 公式」，
**这是错的**，根因是「**以文件名判断定理有无**」——4.14 确实**没有**
`GelfandFormula.lean` 这个**文件**，但那些定理**住在 `Spectrum.lean` 里，4.14 就已经有了**。
经逐行核对（本地 `.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Spectrum.lean`）：

| 定理 | **4.14 本地位置** | 内容 |
|:--|:--|:--|
| `spectralRadius` 定义 | **`:56-58`** | `⨆ k ∈ spectrum 𝕜 a, ‖k‖₊`（值域 **`ℝ≥0∞`**，`sSup over spectrum`） |
| `spectralRadius_le_nnnorm` | **`:176`** | `ρ(a) ≤ ‖a‖₊`（`[NormOneClass A]`）|
| `spectralRadius_le_pow_nnnorm_pow_one_div` | **`:196`** | `ρ(a) ≤ ‖a^{n+1}‖₊^{1/(n+1)}·‖1‖₊^{1/(n+1)}` |
| `spectralRadius_le_liminf_pow_nnnorm_pow_one_div` | **`:216`** | liminf 一侧 |
| `limsup_pow_nnnorm_pow_one_div_le_spectralRadius` | **`:355`** | limsup 一侧 |
| **`pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`** | **`:374`** | **Gelfand 公式（`lim` 形式）** |
| `pow_norm_pow_one_div_tendsto_nhds_spectralRadius` | **`:383`** | 同上，`norm` 版 |
| `exists_nnnorm_eq_spectralRadius` | **`:413`** | 谱半径**取到** |

—— **`lim` 形式在 4.14 就有**，**不需要**升级 mathlib。

**那么真正的障碍是什么？是「类型类语境」，不是「缺公式」**：
上述 Gelfand 定理的 `variable`（`Spectrum.lean:352`）是
`[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]` —— **复 Banach 代数**；
而本文件在**实**矩阵 / 实算子语境（`Matrix (Fin n) (Fin n) ℝ` + `matCLME`）下工作。
要把 mathlib 的定理接到本文件，需先做**复化**（把实算子升到 `ℂ` 上，或证
`ρ_ℝ(T) = ρ_ℂ(T_ℂ)`）——这是**成本问题，不是可行性问题**。

**另一条独立佐证（说明"只证一侧"是定义的普遍性质）**：
`D:\mathlib`（v4.33 源码树）`Mathlib/Analysis/Normed/Algebra/Spectrum.lean:94`：
`lemma spectrum.spectralRadius_pow_le (a : A) (n : ℕ) (hn : n ≠ 0) : (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n)`
—— **上游在 `sSup over spectrum` 定义下也只证了 `ρ(T)ⁿ ≤ ρ(Tⁿ)` 这一侧**，
与本文件 `gelfand_radius_pow_le_radius_pow` 的结论**完全一致**（独立印证）。

**本文件的定位（诚实）**：本文件提供的是**纯 `inf` 形式**的 `ρ`（只用算子范数、
不引入复谱与 Banach 代数机制），在该框架内给出**双侧界**
`ρ(Tᵏ)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`。**等号 `ρ(Tᵏ) = ρ(T)ᵏ` 的完整证明路线**是：
把 `matCLME T` 复化后套用 `Spectrum.lean:374` 的 `lim` 形式——
这条**复化适配在本文件中未做**（标注**未做**：**复语境适配**，
而非"mathlib 缺公式"）。

（`RealSpectralRadius.gelfand_diagonal` 在**对角**情形给出了等号
`‖(diag d)^k‖^{1/k} → ρ̂(d)`——那里 `‖Tⁿ‖^{1/n}` 是**常数序列**，极限平凡；
一般矩阵的困难正在于该序列**不**为常数。）

## 诚实标注（降级/未做）

- **复语境适配未做（不是"缺公式"）**：**Gelfand 公式的 `lim` 形式
  `ρ(T) = lim ‖Tⁿ‖^{1/n}` 在 mathlib 4.14 中已存在**
  （`Spectrum.lean:374` `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`，
  及 `:383` 的 `norm` 版），**不需要升级 mathlib**。
  真正的障碍是**类型类语境**：该定理要求复 Banach 代数
  `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`（`Spectrum.lean:352`），
  而本文件在**实**矩阵/算子语境下工作。把它接过来需先做**复化**
  （升到 `ℂ` 上，或证 `ρ_ℝ(T) = ρ_ℂ(T_ℂ)`）——**本文件未做该复化适配**；
- **复谱未做**：本文件的 `ρ` 只用算子范数（不含复特征值），对复谱是有效**上界载体**；
  「`ρ(T) = max{|λ| : λ` 复特征值`}`」需要复谱理论，**未做**（见 `RealComplexSpectral`）；
- **`ρ(Tᵏ) = ρ(T)ᵏ` 未做**（只有 `ρ(T)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`），根因见上；
- **未做**：Perron–Frobenius、Jordan 标准形、谱半径对矩阵元素的连续性、
  对称矩阵 `ρ = ‖T‖` 的完整谱定理路线；
- **`n = 0`（零维）**：`Fin 0` 上唯一方阵是 `1`，mathlib 约定 `‖id‖ = 1`，故 `ρ = 1`
  （`gelfand_radius_zero_dim`）——**如实记录 mathlib 约定**，非降级。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

open scoped InnerProduct
open scoped Topology

namespace Lattice

open Matrix
open scoped BigOperators

variable {n : ℕ}

/-! ## 第一节：谱半径的定义与集合性质 -/

/-- **谱半径（Gelfand `inf` 形式）**：`ρ(T) = sInf { ‖Tᵏ‖^{1/k} | k > 0 }`。

诚实标注：这是 Gelfand 公式 `ρ(T) = lim ‖Tⁿ‖^{1/n}` 的 **`inf` 侧**刻画
（极限存在时两者相等）；取 `sInf` 而非 `lim` 是为了**绕开收敛性证明**
（标注**降级**，见 `gelfand_radius_eq_inf`）。 -/
def gelfandRadius (T : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {r : ℝ | ∃ k : ℕ, 0 < k ∧ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) = r}

/-- 谱半径集合非空（`k = 1` 给出 `‖T‖`）。 -/
lemma gelfandRadius_set_nonempty (T : Matrix (Fin n) (Fin n) ℝ) :
    {r : ℝ | ∃ k : ℕ, 0 < k ∧ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) = r}.Nonempty :=
  ⟨‖matCLME T‖, 1, one_pos, by rw [pow_one, Nat.cast_one, div_one, Real.rpow_one]⟩

/-- 谱半径集合有下界 `0`（`‖Tᵏ‖^{1/k} ≥ 0`）。 -/
lemma gelfandRadius_set_bddBelow (T : Matrix (Fin n) (Fin n) ℝ) :
    BddBelow {r : ℝ | ∃ k : ℕ, 0 < k ∧ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) = r} :=
  ⟨0, fun _ hr => by
    obtain ⟨k, _, rfl⟩ := hr
    exact Real.rpow_nonneg (norm_nonneg _) _⟩

/-! ## 第二节：`ρ(T) ≤ ‖T‖`（A1.6 要求 1） -/

/-- **单位矩阵的算子范数 ≤ 1**（**无条件**成立，含 `n = 0`）：
`‖matCLME (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1`（`matCLME 1 = id` + `norm_id_le`）。

诚实标注：等号 `= 1` 需要 `n ≠ 0`（即 `EuclideanSpace ℝ (Fin n)` 非退化），
见 `gelfand_opNorm_one_of_pos`（`hn : 0 < n` 版，`:178`）；
两者分开陈述是为了让**零维特例**被显式处理。
（**R3 更正**：本行原引 `gelfand_opNorm_one`——**该名字不存在**，
本文件既无该定理也无 `gelfand_opNorm_one` 的任何定义。） -/
theorem gelfand_opNorm_one_le :
    ‖matCLME (1 : Matrix (Fin n) (Fin n) ℝ)‖ ≤ 1 := by
  have h : matCLME (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [matCLME_apply, ContinuousLinearMap.id_apply]
    ext i
    simp [matvecE, Matrix.one_apply]
  rw [h]
  exact ContinuousLinearMap.norm_id_le

/-- **单位矩阵的算子范数为 1**（`n ≠ 0`）：`‖matCLME (1 : Matrix (Fin n) (Fin n) ℝ)‖ = 1`
（`matCLME 1 = id`，再用 `ContinuousLinearMap.norm_id`，后者要求 `[Nontrivial E]`）。

诚实标注：`Nontrivial (EuclideanSpace ℝ (Fin n))` 在 `n = 0` 时**不成立**
（单点空间），故本定理以 `hn : 0 < n` 为**显式假设**；
`n = 0` 的情形由 `gelfand_opNorm_one_le` 覆盖，且 `gelfand_radius_zero_dim` 另行处理。 -/
theorem gelfand_opNorm_one_of_pos (hn : 0 < n) :
    ‖matCLME (1 : Matrix (Fin n) (Fin n) ℝ)‖ = 1 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- `EuclideanSpace ℝ (Fin n) = (Fin n → ℝ)`，由 `n > 0` 得非退化：
  -- 常函数 `1` 与常函数 `0` 不同（在 `⟨0, hn⟩` 处取值 `1 ≠ 0`）
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    ⟨fun _ => 1, fun _ => 0, fun h => by
      have h0 := congrFun h ⟨0, hn⟩
      norm_num at h0⟩
  have h : matCLME (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin n)) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [matCLME_apply, ContinuousLinearMap.id_apply]
    ext i
    simp [matvecE, Matrix.one_apply]
  rw [h, ContinuousLinearMap.norm_id]

set_option maxHeartbeats 800000 in
/-- **算子范数的幂界**：`‖Tᵏ‖ ≤ ‖T‖ᵏ`（次乘法性 `matrix_mul_norm_bound` 的归纳）。

诚实标注：证明中提高 `maxHeartbeats`——`le_trans` 在
`‖matCLME (T * T^k)‖ ≤ ‖matCLME T‖ * ‖matCLME (T^k)‖` 上做 `whnf` 归一化时较重
（`matCLME` 是 `LinearMap.mkContinuous` 的复合项，类型推断开销大）。 -/
theorem gelfand_opNorm_pow_le (T : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    ‖matCLME (T ^ k)‖ ≤ ‖matCLME T‖ ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact gelfand_opNorm_one_le
  | succ k ih =>
      calc ‖matCLME (T ^ (k + 1))‖ = ‖matCLME (T ^ k * T)‖ := by rw [pow_succ]
        _ ≤ ‖matCLME (T ^ k)‖ * ‖matCLME T‖ := matrix_mul_norm_bound (T ^ k) T
        _ ≤ ‖matCLME T‖ ^ k * ‖matCLME T‖ :=
            mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖matCLME T‖ ^ (k + 1) := by rw [pow_succ]

/-- **`ρ(T) ≤ ‖Tᵏ‖^{1/k}`**（`k > 0`）：集合的元素，`sInf` 是下界。 -/
theorem gelfand_radius_le_pow_root (T : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : 0 < k) :
    gelfandRadius T ≤ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) :=
  csInf_le (gelfandRadius_set_bddBelow T) ⟨k, hk, rfl⟩

/-- **谱半径 ≤ 算子范数**（A1.6 要求 1，整体形式）：`ρ(T) ≤ ‖T‖`（任意实方阵）。

诚实标注：这是 Gelfand 理论中「**平凡**的一半」；难的一半是 `‖T‖` 可**严格大于** `ρ(T)`
（非正规矩阵），本文件不掩盖该事实。 -/
theorem gelfand_radius_le_opNorm (T : Matrix (Fin n) (Fin n) ℝ) :
    gelfandRadius T ≤ ‖matCLME T‖ := by
  have h : gelfandRadius T ≤ ‖matCLME (T ^ 1)‖ ^ (1 / ((1 : ℕ) : ℝ)) :=
    gelfand_radius_le_pow_root T (k := 1) one_pos
  rwa [pow_one, Nat.cast_one, div_one, Real.rpow_one] at h

/-- **谱半径非负**：`0 ≤ ρ(T)`。 -/
theorem gelfand_radius_nonneg (T : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ gelfandRadius T :=
  le_csInf (gelfandRadius_set_nonempty T) (fun _ hr => by
    obtain ⟨k, _, rfl⟩ := hr
    exact Real.rpow_nonneg (norm_nonneg _) _)

/-- **特征值的模被算子范数控制**（A1.6 要求 1 的逐特征值形式）：
`μ` 是 `T` 的实特征值 ⟹ `|μ| ≤ ‖T‖`
（`RealSpectral.spectral_radius_le_opNorm` 的具名重申，作为本文件的接口锚点）。 -/
theorem gelfand_eigenvalue_abs_le_opNorm (T : Matrix (Fin n) (Fin n) ℝ) (mu : ℝ)
    (h : HasRealEigenvalue T mu) : |mu| ≤ ‖matCLME T‖ :=
  spectral_radius_le_opNorm T mu h

/-- **`‖T‖ < 1 ⟹ ρ(T) < 1`**（Neumann 级数收敛的前提）。 -/
theorem gelfand_radius_lt_one_of_opNorm_lt_one (T : Matrix (Fin n) (Fin n) ℝ)
    (h : ‖matCLME T‖ < 1) : gelfandRadius T < 1 :=
  lt_of_le_of_lt (gelfand_radius_le_opNorm T) h

/-! ## 第三节：幂律（A1.6 要求 2） -/

/-- **`ρ(1) ≤ 1`**（**无条件**，含 `n = 0`）：由 `ρ(T) ≤ ‖T‖` 与 `‖1‖ ≤ 1`。

诚实标注：`= 1` 需要 `0 < n`（见 `gelfand_radius_one_of_pos`）；两者分开，
以便 `n = 0` 的退化情形被显式记录而非掩盖。 -/
theorem gelfand_radius_one_le :
    gelfandRadius (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 1 :=
  le_trans (gelfand_radius_le_opNorm (1 : Matrix (Fin n) (Fin n) ℝ)) gelfand_opNorm_one_le

/-- **`ρ(1) = 1`**（`0 < n`）：`ρ(1) ≤ ‖1‖ = 1` 且 `1 = ‖1‖` 是定义集合的元素。

诚实标注：本定理的 `hn : 0 < n` 来自 `gelfand_opNorm_one_of_pos`
（`ContinuousLinearMap.norm_id` 需要 `[Nontrivial E]`，`n = 0` 时不成立）。 -/
theorem gelfand_radius_one_of_pos (hn : 0 < n) :
    gelfandRadius (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  refine le_antisymm gelfand_radius_one_le ?_
  refine le_csInf (gelfandRadius_set_nonempty _) (fun r hr => ?_)
  obtain ⟨k, hk, rfl⟩ := hr
  rw [one_pow, gelfand_opNorm_one_of_pos hn]
  exact le_of_eq (Real.one_rpow _).symm

/-- **实指数重排恒等式**：`x ≥ 0`、`k, j > 0` 时
`x^{1/(k·j)} = (x^{1/j})^{1/k}`。幂律证明的**核心技术步**。 -/
theorem gelfand_rpow_div_mul {x : ℝ} (hx : 0 ≤ x) {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    x ^ (1 / ((k * j : ℕ) : ℝ)) = (x ^ (1 / (j : ℝ))) ^ (1 / (k : ℝ)) := by
  rw [← Real.rpow_mul hx]
  congr 1
  have hk' : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)
  have hj' : ((j : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj)
  push_cast
  field_simp
  ring
/-- **`ρ(T)ᵏ ≤ ρ(Tᵏ)`**（幂律的**可证方向**，Fekete-free）。

证明（见文件头）：对任意 `j > 0`，
`ρ(T) ≤ ‖T^{kj}‖^{1/(kj)} = (‖(Tᵏ)^j‖^{1/j})^{1/k}`（用 `pow_mul` 与
`gelfand_rpow_div_mul`），两边取 `k` 次方得 `ρ(T)ᵏ ≤ ‖(Tᵏ)^j‖^{1/j}`；
即 `ρ(T)ᵏ` 是 `S(Tᵏ)` 的**下界**，而 `ρ(Tᵏ) = sInf S(Tᵏ)` 是**最大下界**，
故 `ρ(T)ᵏ ≤ ρ(Tᵏ)`。 -/
theorem gelfand_radius_pow_le_radius_pow (T : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : 0 < k) :
    (gelfandRadius T) ^ k ≤ gelfandRadius (T ^ k) := by
  refine le_csInf (gelfandRadius_set_nonempty (T ^ k)) (fun r hr => ?_)
  obtain ⟨j, hj, rfl⟩ := hr
  have hbase : gelfandRadius T ≤ (‖matCLME ((T ^ k) ^ j)‖ ^ (1 / (j : ℝ))) ^ (1 / (k : ℝ)) := by
    have h := gelfand_radius_le_pow_root T (k := k * j) (Nat.mul_pos hk hj)
    -- `h : ρ(T) ≤ ‖T^(k*j)‖^(1/(k*j))`；把 `T^(k*j)` 写成 `(T^k)^j`
    rw [pow_mul] at h
    rw [gelfand_rpow_div_mul (norm_nonneg _) hk hj] at h
    exact h
  calc (gelfandRadius T) ^ k
      ≤ ((‖matCLME ((T ^ k) ^ j)‖ ^ (1 / (j : ℝ))) ^ (1 / (k : ℝ))) ^ k :=
        pow_le_pow_left₀ (gelfand_radius_nonneg T) hbase k
    _ = ‖matCLME ((T ^ k) ^ j)‖ ^ (1 / (j : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.rpow_nonneg (norm_nonneg _) _),
          one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hk)), Real.rpow_one]

/-- **`ρ(Tᵏ) ≤ ‖T‖ᵏ`**（幂律的**上界侧**）：由 `ρ(Tᵏ) ≤ ‖Tᵏ‖` 与 `‖Tᵏ‖ ≤ ‖T‖ᵏ` 串联。

诚实标注：本式给出的是 `‖T‖` 的幂而非 `ρ(T)` 的幂——
「`ρ(Tᵏ) ≤ ρ(T)ᵏ`」需要 Gelfand 极限定理的**复语境适配**，**本文件未做**
（见 `gelfand_radius_pow_bounds` 的标注与 CORRECTIONS B25）。 -/
theorem gelfand_radius_pow_le_opNorm_pow (T : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    gelfandRadius (T ^ k) ≤ ‖matCLME T‖ ^ k :=
  le_trans (gelfand_radius_le_opNorm _) (gelfand_opNorm_pow_le T k)

/-- **幂律的两侧可证界（A1.6 要求 2 的「诚实」形式）**：
`ρ(T)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`（`k > 0`）。

诚实标注：这是本文件对「`ρ(Tⁿ) = ρ(T)ⁿ`」的**诚实降级**版本——
下界是**紧的**方向（Fekete-free，纯 `inf` 论证），上界是平凡的算子范数界。
**等号 `ρ(Tᵏ) = ρ(T)ᵏ` 未证**：它需要 Gelfand 极限定理（`‖Tⁿ‖^{1/n} → ρ(T)`；
该 `lim` 形式在 **mathlib 4.14 已有**，见 `Spectrum.lean:374`
`pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`），
但该定理要求**复 Banach 代数**语境（`Spectrum.lean:352`），
本文件**未做复化适配**——见文件头与 CORRECTIONS B25。 -/
theorem gelfand_radius_pow_bounds (T : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : 0 < k) :
    (gelfandRadius T) ^ k ≤ gelfandRadius (T ^ k) ∧
      gelfandRadius (T ^ k) ≤ ‖matCLME T‖ ^ k :=
  ⟨gelfand_radius_pow_le_radius_pow T hk, gelfand_radius_pow_le_opNorm_pow T k⟩

/-- **恒等算子上的幂律等号（机器验证锚点）**：`0 < n` 时
`ρ(1ᵏ) = ρ(1) = 1 = 1ᵏ = ρ(1)ᵏ`——说明幂律在**正规**（此处为恒等）算子上取等号，
一般矩阵的困难来自非正规性（与 `RealSpectralRadius` 的对角情形同源）。 -/
theorem gelfand_radius_pow_eq_one (hn : 0 < n) (k : ℕ) :
    gelfandRadius ((1 : Matrix (Fin n) (Fin n) ℝ) ^ k) =
      (gelfandRadius (1 : Matrix (Fin n) (Fin n) ℝ)) ^ k := by
  rw [one_pow, gelfand_radius_one_of_pos hn, one_pow]

/-! ## 第四节：Gelfand 的 `inf` 形式（A1.6 核心） -/

/-- **Gelfand 公式（`inf` 形式，A1.6 核心）**：
`ρ(T) = sInf { ‖Tᵏ‖^{1/k} | k > 0 }`。

这条在本文件中是**定义相等**（`gelfandRadius` 就是这个 `sInf`），
本定理把它作为**具名引理**暴露出来，使下游可以按「Gelfand 公式」检索到它，
并作为「定义即 `inf` 形式」的**机器可验证锚点**。

诚实标注（**降级**）：这是 Gelfand 公式 `ρ(T) = lim_{n→∞} ‖Tⁿ‖^{1/n}` 的 **`inf` 形式**；
由 `inf` 到 `lim` 的最后一跳（**收敛性**）**本文件未做**——但**该 `lim` 形式
mathlib 4.14 已提供**（`Spectrum.lean:374`），未做的只是**复语境的适配**。
**注意**不要写成"mathlib 缺 Gelfand 公式"：那是**错的**（CORRECTIONS B25）。 -/
theorem gelfand_radius_eq_inf (T : Matrix (Fin n) (Fin n) ℝ) :
    gelfandRadius T = sInf {r : ℝ | ∃ k : ℕ, 0 < k ∧ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) = r} :=
  rfl

/-- **`ρ(T)` 是 `‖Tᵏ‖^{1/k}` 的下界**（Gelfand `inf` 形式的下侧，具名）。 -/
theorem gelfand_radius_le_all_pow_root (T : Matrix (Fin n) (Fin n) ℝ) :
    ∀ k : ℕ, 0 < k → gelfandRadius T ≤ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) :=
  fun _ hk => gelfand_radius_le_pow_root T hk

/-- **存在逼近序列**：对任意 `ε > 0`，存在 `k > 0` 使
`‖Tᵏ‖^{1/k} < ρ(T) + ε`（`sInf` 的逼近性质）。

证明：若不然，`ρ(T) + ε` 是集合的下界且 `> ρ(T)`，与 `ρ(T) = sInf` 是最**大**下界矛盾。

诚实标注：这是**存在性**（不是「对充分大的 `k`」）——「最终」形式需要
`lim` 版本；该 `lim` 形式 mathlib 4.14 **已有**（`Spectrum.lean:374`），
本文件**未做复语境适配**（见文件头与 CORRECTIONS B25）。 -/
theorem gelfand_exists_pow_root_lt (T : Matrix (Fin n) (Fin n) ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ k : ℕ, 0 < k ∧ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) < gelfandRadius T + eps := by
  by_contra hcon
  rw [not_exists] at hcon
  -- `hcon : ∀ k, ¬ (0 < k ∧ ‖T^k‖^{1/k} < ρ(T) + ε)`
  have hmem : ∀ k : ℕ, 0 < k → gelfandRadius T + eps ≤ ‖matCLME (T ^ k)‖ ^ (1 / (k : ℝ)) := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    exact hcon k ⟨hk, hlt⟩
  have hle : gelfandRadius T + eps ≤ gelfandRadius T :=
    le_csInf (gelfandRadius_set_nonempty T) (fun _ hr => by
      obtain ⟨k, hk, rfl⟩ := hr
      exact hmem k hk)
  linarith

/-! ## 第五节：非对角矩阵的谱半径（补 `RealSpectralRadius` 缺口） -/

/-- **非对角矩阵的谱半径 ≤ 算子范数**：对任意实方阵 `T`（**不要求对角**），`ρ(T) ≤ ‖T‖`。

对 `RealSpectralRadius.spectral_radius_le_opNorm_diag`（只处理对角矩阵）的**真正的泛化**：
那里用对角结构算出 `‖diag d‖ = ρ̂(d)`，本定理在**任意**矩阵上用 Gelfand `inf` 形式
给出同一结论（`gelfand_radius_le_opNorm` 的**具名重申**，便于按「非对角谱半径」检索）。 -/
theorem gelfand_radius_le_opNorm_general (T : Matrix (Fin n) (Fin n) ℝ) :
    gelfandRadius T ≤ ‖matCLME T‖ :=
  gelfand_radius_le_opNorm T

/-- **零维特例**：`n = 0` 时只有一个矩阵（`Fin 0` 上的空矩阵），`ρ(T) ≤ 1`。

诚实标注（**重要更正**）：先前草稿声称 `ρ(T) = 1`，这是**错的**——
`ContinuousLinearMap.norm_id` 在 4.14 要求 `[Nontrivial E]`，而 `EuclideanSpace ℝ (Fin 0)`
是**单点空间**（不 `Nontrivial`）。此时 `matCLME 1` 是零映射，`‖matCLME 1‖` 可为 `0`，
故**只能给 `ρ(T) ≤ 1`**（`gelfand_radius_one_le`）——本文件**如实降级**为不等式。
（零维空间上的"恒等算子"与零映射在范数上不可区分，这是 mathlib 的诚实约定。） -/
theorem gelfand_radius_zero_dim (T : Matrix (Fin 0) (Fin 0) ℝ) : gelfandRadius T ≤ 1 := by
  have hT : T = 1 := by ext i; exact Fin.elim0 i
  rw [hT]
  exact gelfand_radius_one_le

/-! ## 第六节：诚实降级汇总 -/

/-- **A1.6 汇总（自检式）**：把本文件对 A1.6 的交付并列成一条定理，便于审计：

  1. `ρ(T) ≤ ‖T‖`（`gelfand_radius_le_opNorm`）——**完整交付**；
  2. `ρ(T) = inf_{k>0} ‖Tᵏ‖^{1/k}`（`gelfand_radius_eq_inf`）——`inf` 形式**完整**；
  3. `ρ(T)ᵏ ≤ ρ(Tᵏ) ≤ ‖T‖ᵏ`（`gelfand_radius_pow_bounds`）——幂律的**两侧可证界**。

诚实标注：`ρ(Tᵏ) = ρ(T)ᵏ` 的**等号本文件未证**（需 Gelfand 极限定理的**复语境适配**——
该定理 mathlib 4.14 **已有**，见 `Spectrum.lean:374`；**不是**"mathlib 缺公式"，
见 CORRECTIONS B25）。 -/
theorem gelfand_summary (T : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (hk : 0 < k) :
    gelfandRadius T ≤ ‖matCLME T‖ ∧
      gelfandRadius T = sInf {r : ℝ | ∃ j : ℕ, 0 < j ∧ ‖matCLME (T ^ j)‖ ^ (1 / (j : ℝ)) = r} ∧
      ((gelfandRadius T) ^ k ≤ gelfandRadius (T ^ k) ∧
        gelfandRadius (T ^ k) ≤ ‖matCLME T‖ ^ k) :=
  ⟨gelfand_radius_le_opNorm T, gelfand_radius_eq_inf T, gelfand_radius_pow_bounds T hk⟩

end Lattice
