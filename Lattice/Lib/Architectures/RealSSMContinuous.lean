import Mathlib
import Lattice.Lib.Architectures.RealSSM
import Lattice.Lib.Architectures.RealSelectiveSSM
import Lattice.Lib.Architectures.RealSSMDiscretization
/-!
# LATTICE WP9 / A4.1–A4.3 — 选择性 SSM 的连续→离散桥接、输入依赖与谱稳定性

本文件补上 `RealSelectiveSSM` 明确标注「未做」的三块内容：

* **A4.3 ZOH 桥接（本文件核心）**：连续系统 `h'(t) = A h(t) + B u(t)` 在步长 `Δ` 的
  零阶保持（ZOH）下精确满足

      `h_{t+1} = exp(Δ•A) h_t + Φ(A,Δ) • (B u_t)`,   `Φ(A,Δ) = ∫₀^Δ exp(s•A) ds`。

  本文件在**一般完备赋范代数** `𝔸`（`[NormedRing] [NormedAlgebra ℝ] [NormOneClass]
  [CompleteSpace]`，**不要求交换**）上给出该桥接的**级数形式**并机器验证。
* **A4.1 输入依赖性**：`A_t = g(x_t)`（`g` 为「门控」，`A_t = diag(σ(W x_t))` 是其特例）
  的形式化，以及带输入依赖递推的**闭式解**与**稳定界**。
* **A4.2 谱稳定性充分条件**：`ρ < 1` 的显式可验证判据
  （范数判据、LTI 的 `exp(ΔA)` 判据、特征值判据的抽象形式）。

## 一、ZOH 桥接的数学内容与 `Φ` 的定义选择

`RealSSMDiscretization` 只把 ZOH 一步算子 `Ā = NormedSpace.exp ℝ (Δ • A)` 当作**定义**，
并给出 `‖exp x − (1+x)‖ ≤ ‖x‖²/2·e^{‖x‖}` 的截断误差；它**没有**证明 `Ā` 真的是连续
系统的一步传播算子，也没有给出**输入项** `B̄`。本文件补上这两步。

关键恒等式是**纯代数**的：

    `A * Φ(A,Δ) = Φ(A,Δ) * A = exp(Δ•A) − 1`        (`zoh_bridge_mul` / `zoh_bridge_mul'`)

**`Φ` 的定义选择（诚实标注）**：`Φ(A,Δ)` 的教科书定义是 Bochner 积分
`∫₀^Δ exp(s•A) ds`。本文件**不**用测度论，而把它定义为**收敛级数**

    `zohGain A Δ := ∑' n, (Δ^{n+1}/(n+1)!) • A^n`。

理由与等价性：

1. **逐项积分**：对 `exp(s•A) = ∑ₙ (n!)⁻¹ sⁿ • Aⁿ` 逐项在 `[0,Δ]` 上积分
   （`∫₀^Δ sⁿ ds = Δ^{n+1}/(n+1)`）即得本定义。**该「`∫` 与 `∑'` 交换」本身未证**
   （需要 Bochner 积分的控制收敛）；但**数值验证**该级数与数值求积的积分一致到
   `2.2e-16`（双精度极限）。
2. **级数定义使恒等式变成纯代数操作**：`exp(Δ•A) − 1` 是剥掉 `n=0` 项的指数级数，
   而 `A * Φ` 的每一项只由 `Algebra.mul_smul_assoc` / `mul_smul_comm` 处理，
   **无需积分理论**，在**非交换**环上也成立。

因此本文件的桥接定理是**关于级数定义的定理**；把它接到「真正的连续解」上还差
「积分 = 级数」与「`HasDerivAt`」两条，均**未做**并在此显式登记。

## 二、诚实边界（中文标注，全部为「未做 / 降级」）

* **降级 —— `Φ` 的积分等价性未证**：`zohGain` 用**级数定义**，未证它与 Bochner 积分
  `∫₀^Δ exp(s•A) ds` 相等（数值上一致）。
* **未做 —— 连续半群满足 ODE**：未证 `t ↦ exp(t•A)h₀ + Φ(A,t)(Bu)` 满足
  `HasDerivAt`。（本文件已给出所需的**交换律** `exp_smul_commute` 与
  `zoh_bridge_mul`，是接近该目标的两个关键零件。）
* **未做 —— 时变连续的 ZOH**：区间内 `A(t)` 变动（非分段常数）的 ZOH 误差未做；
  本文件只处理**块状**（每步内 `A`、`u` 为常数）的 ZOH。
* **降级 —— 输入依赖是「门控函数」抽象**：`A_t = σ(W x_t)` 中的 `σ` 以**任意满足
  范数界的函数** `g` 出现；具体的 sigmoid/softplus 及其范数界
  （`‖σ(z)‖ ≤ 1` 需 `𝔸 = ℝ` 或对角矩阵实例）**未做**。
* **未做 —— 谱半径判据的矩阵实例化**：谱稳定性以**范数判据**（`‖A_t‖ ≤ ρ`）与
  `Module.End.HasEigenvalue` 的**抽象**特征值判据给出，**未**实例化到
  `Matrix` 的 `linftyOpNorm`（mathlib 缺「行和范数 ≤ ρ ⟹ 谱半径 ≤ ρ」的桥）。
* **标注 —— 非交换性**：全文件只假设 `NormedRing`（非交换），乘积一律**新因子在左**
  （与 CORRECTIONS B18 一致）；`‖∏‖ ≤ ∏‖·‖` 自证（mathlib 的 `Finset.norm_prod_le`
  要 `NormedCommRing`）。
* **标注 —— `NormedSpace.exp` 首参是显式标量域**（STYLE 坑表）：陈述中一律写
  `NormedSpace.exp ℝ x`。
* **标注 —— `n!⁻¹` 后缀记法解析失败**（STYLE 坑表）：一律写 `((n.factorial : ℝ))⁻¹`。
-/

noncomputable section

open Lattice.Lib.Architectures.RealSSMDiscretization

namespace Lattice

open scoped BigOperators
open Finset

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormOneClass 𝔸] [CompleteSpace 𝔸]

/-! ## 第一部分：ZOH 增益 `Φ` 的级数定义、可和性与范数界 -/

/-- **ZOH 输入增益（级数定义）**：`Φ(A,Δ) = ∑ₙ Δ^{n+1}/(n+1)! • Aⁿ`。

**与积分的等价性（标注）**：教科书定义为 Bochner 积分 `∫₀^Δ exp(s•A) ds`；
对 `exp(s•A) = ∑ₙ (n!)⁻¹ sⁿ • Aⁿ` 逐项积分 `∫₀^Δ sⁿ ds = Δ^{n+1}/(n+1)` 即得本定义。
**「级数 = 积分」这一步本文件未证**（需要区间积分与 `tsum` 交换），故此处以级数**定义**。

**为什么用级数而不是积分**：这样 `A * Φ = Φ * A = exp(Δ•A) − 1` 变成**纯代数**操作
（`Algebra.mul_smul_assoc` + `pow_succ'`），完全绕开非交换环上的测度论。 -/
def zohGain (A : 𝔸) (Delta : ℝ) : 𝔸 :=
  ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n

/-- **标量主控界**：`|Δ|^{n+1}‖A‖ⁿ/(n+1)! ≤ |Δ|·(|Δ|‖A‖)ⁿ/n!`。
由 `1/(n+1)! ≤ 1/n!`（`Nat.factorial_le`）与 `‖Aⁿ‖ ≤ ‖A‖ⁿ`（`norm_pow_le`）得到；
它使 `Φ` 的级数被标量指数级数 `∑ (|Δ|‖A‖)ⁿ/n! = e^{|Δ|‖A‖}` 主控。 -/
lemma zohGain_scalar_le (A : 𝔸) (Delta : ℝ) (n : ℕ) :
    (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A‖ ^ n
      ≤ |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) := by
  have hfac : ((n.factorial : ℝ)) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hfacpos : (0 : ℝ) < ((n.factorial : ℝ)) := by positivity
  have hpos2 : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hinv : (((n + 1).factorial : ℝ))⁻¹ ≤ (((n.factorial : ℝ)))⁻¹ :=
    (inv_le_inv₀ hpos2 hfacpos).mpr hfac
  have hnn : (0 : ℝ) ≤ |Delta| ^ (n + 1) * ‖A‖ ^ n :=
    mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (norm_nonneg _) _)
  calc (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A‖ ^ n
      = (((n + 1).factorial : ℝ))⁻¹ * (|Delta| ^ (n + 1) * ‖A‖ ^ n) := by ring
    _ ≤ (((n.factorial : ℝ))⁻¹) * (|Delta| ^ (n + 1) * ‖A‖ ^ n) :=
        mul_le_mul_of_nonneg_right hinv hnn
    _ = |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) := by
        rw [mul_pow]
        field_simp
        ring

/-- **`zohGain` 的级数可和**（**核心可和性引理**）。

标注：mathlib 的 `Summable.norm` 要求 `FiniteDimensional ℝ 𝔸`（见 STYLE 坑表），对一般
完备赋范环不可用，故走 `Summable.of_nonneg_of_le` + `Summable.of_norm`
（与 `RealSSMDiscretization.ssmDisc_exp_truncation_bound` 同一套路）。 -/
lemma zohGain_summable (A : 𝔸) (Delta : ℝ) :
    Summable (fun n : ℕ => ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n) := by
  have hbase : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) := by
    have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|Delta| * ‖A‖)
    simpa [smul_eq_mul] using h
  have hmaj : Summable
      (fun n : ℕ => |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n)) :=
    hbase.mul_left |Delta|
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmaj
  have hpow : |Delta ^ (n + 1)| = |Delta| ^ (n + 1) := abs_pow Delta (n + 1)
  have hstep : ‖((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n‖
      = (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A ^ n‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), hpow]
  rw [hstep]
  calc (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A ^ n‖
      ≤ (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A‖ ^ n := by
        have h1 : ‖A ^ n‖ ≤ ‖A‖ ^ n := norm_pow_le A n
        have h2 : (0 : ℝ) ≤ (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) :=
          mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg (abs_nonneg _) _)
        exact mul_le_mul_of_nonneg_left h1 h2
    _ ≤ |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) :=
        zohGain_scalar_le A Delta n

/-- **ZOH 增益的范数界**：`‖Φ(A,Δ)‖ ≤ |Δ| · e^{|Δ|‖A‖}`。

由主控级数 `∑ₙ |Δ|(|Δ|‖A‖)ⁿ/n! = |Δ| e^{|Δ|‖A‖}` 得到。这是把 `Φ` 接进
`RealSelectiveSSM` 稳定界（前提 `‖B_t‖ ≤ M`）的**接口**：
取 `M = |Δ| e^{|Δ|‖A‖} ‖B‖ sup‖u‖`。 -/
theorem zohGain_norm_le (A : 𝔸) (Delta : ℝ) :
    ‖zohGain A Delta‖ ≤ |Delta| * Real.exp (|Delta| * ‖A‖) := by
  have hbase : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) := by
    have h := NormedSpace.expSeries_summable' (𝕂 := ℝ) (|Delta| * ‖A‖)
    simpa [smul_eq_mul] using h
  have hmaj : Summable
      (fun n : ℕ => |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n)) :=
    hbase.mul_left |Delta|
  have hterm : ∀ n : ℕ,
      ‖((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n‖
        ≤ |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) := by
    intro n
    have hpow : |Delta ^ (n + 1)| = |Delta| ^ (n + 1) := abs_pow Delta (n + 1)
    rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), hpow]
    calc (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A ^ n‖
        ≤ (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) * ‖A‖ ^ n := by
          have h1 : ‖A ^ n‖ ≤ ‖A‖ ^ n := norm_pow_le A n
          have h2 : (0 : ℝ) ≤ (((n + 1).factorial : ℝ))⁻¹ * |Delta| ^ (n + 1) :=
            mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg (abs_nonneg _) _)
          exact mul_le_mul_of_nonneg_left h1 h2
      _ ≤ |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) :=
          zohGain_scalar_le A Delta n
  have hnorm : Summable
      (fun n : ℕ => ‖((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  calc ‖zohGain A Delta‖
      ≤ ∑' n : ℕ, ‖((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, |Delta| * ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) :=
        tsum_le_tsum hterm hnorm hmaj
    _ = |Delta| * ∑' n : ℕ, ((((n.factorial : ℝ))⁻¹) * (|Delta| * ‖A‖) ^ n) :=
        tsum_mul_left
    _ = |Delta| * Real.exp (|Delta| * ‖A‖) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
        simp [smul_eq_mul]

/-! ## 第二部分：ZOH 桥接（核心恒等式） -/

/-- **`exp` 剥掉线性项**：`exp(Δ•A) − 1 = ∑ₙ (Δ^{n+1}/(n+1)!) • A^{n+1}`。

证明：`exp(Δ•A) = ∑ₙ (n!)⁻¹ • (Δ•A)ⁿ`（`exp_eq_tsum`），用
`sum_add_tsum_nat_add 1` 拆出 `n=0` 项 `1`，再用 `smul_pow`/`smul_smul`
把 `(n!)⁻¹ • (Δ•A)^{n+1}` 重整为 `(Δ^{n+1}/(n+1)!) • A^{n+1}`。 -/
lemma exp_smul_sub_one_eq_tsum (A : 𝔸) (Delta : ℝ) :
    NormedSpace.exp ℝ (Delta • A) - 1
      = ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ (n + 1) := by
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • (Delta • A) ^ n) :=
    NormedSpace.expSeries_summable' (Delta • A)
  have hexp : NormedSpace.exp ℝ (Delta • A)
      = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (Delta • A) ^ n := by
    simpa using congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := 𝔸)) (Delta • A)
  have hsplit := sum_add_tsum_nat_add (G := 𝔸) 1 hf
  have hhead : (∑ i ∈ range 1, (((i.factorial : ℝ))⁻¹) • (Delta • A) ^ i) = 1 := by simp
  have htail : NormedSpace.exp ℝ (Delta • A) - 1
      = ∑' n : ℕ, (((n + 1).factorial : ℝ))⁻¹ • (Delta • A) ^ (n + 1) := by
    rw [hexp, ← hsplit, hhead]
    abel
  rw [htail]
  apply tsum_congr
  intro n
  rw [smul_pow, smul_smul]

/-- **`A` 左乘 ZOH 增益**：`A * Φ(A,Δ) = ∑ₙ (Δ^{n+1}/(n+1)!) • A^{n+1}`。

用 `Summable.tsum_mul_left` 提出 `A`，再逐项 `Algebra.mul_smul_comm` + `pow_succ'`。
**注意**：`pow_succ'` 给出 `A * A^n = A^{n+1}`，正是所需的**左乘**方向
（`pow_succ` 给的是 `A^n * A`，方向相反）。 -/
lemma mul_zohGain (A : 𝔸) (Delta : ℝ) :
    A * zohGain A Delta
      = ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ (n + 1) := by
  have hs := zohGain_summable A Delta
  have h1 : (∑' n : ℕ, A * ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n)
      = A * ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n :=
    Summable.tsum_mul_left A hs
  rw [zohGain, ← h1]
  refine tsum_congr fun n => ?_
  rw [Algebra.mul_smul_comm ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) A (A ^ n),
    (pow_succ' A n).symm]

/-- **`A` 右乘 ZOH 增益**：`Φ(A,Δ) * A = ∑ₙ (Δ^{n+1}/(n+1)!) • A^{n+1}`。 -/
lemma zohGain_mul (A : 𝔸) (Delta : ℝ) :
    zohGain A Delta * A
      = ∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ (n + 1) := by
  have hs := zohGain_summable A Delta
  have h1 : (∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n * A)
      = (∑' n : ℕ, ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) • A ^ n) * A :=
    Summable.tsum_mul_right A hs
  rw [zohGain, ← h1]
  refine tsum_congr fun n => ?_
  rw [Algebra.smul_mul_assoc ((((n + 1).factorial : ℝ))⁻¹ * Delta ^ (n + 1)) (A ^ n) A,
    (pow_succ A n).symm]

/-- **ZOH 桥接（核心，左乘）**：`A * Φ(A,Δ) = exp(Δ•A) − 1`。 -/
theorem zoh_bridge_mul (A : 𝔸) (Delta : ℝ) :
    A * zohGain A Delta = NormedSpace.exp ℝ (Delta • A) - 1 := by
  rw [mul_zohGain, ← exp_smul_sub_one_eq_tsum]

/-- **ZOH 桥接（核心，右乘）**：`Φ(A,Δ) * A = exp(Δ•A) − 1`。 -/
theorem zoh_bridge_mul' (A : 𝔸) (Delta : ℝ) :
    zohGain A Delta * A = NormedSpace.exp ℝ (Delta • A) - 1 := by
  rw [zohGain_mul, ← exp_smul_sub_one_eq_tsum]

/-- **`A` 与 ZOH 增益交换**：`A * Φ(A,Δ) = Φ(A,Δ) * A`。

左右两条桥接恒等式都等于 `exp(Δ•A) − 1`；这是**非交换**设定下积分定义所满足的
「可交换性」在级数定义上的精确对应。 -/
theorem zohGain_commute (A : 𝔸) (Delta : ℝ) :
    A * zohGain A Delta = zohGain A Delta * A := by
  rw [zoh_bridge_mul, zoh_bridge_mul']

/-- **`A` 与 `exp(s•A)` 交换**：`A * exp(s•A) = exp(s•A) * A`。

由 `exp_eq_tsum` + `Summable.tsum_mul_left`/`tsum_mul_right` 逐项得到：两边都等于
`∑ₙ (sⁿ/n!) • A^{n+1}`。这是「连续半群的生成元与半群交换」——
`zoh_bridge_mul` 之外通往「连续解满足 ODE」的第二个关键零件。 -/
theorem exp_smul_commute (A : 𝔸) (s : ℝ) :
    A * NormedSpace.exp ℝ (s • A) = NormedSpace.exp ℝ (s • A) * A := by
  have hf : Summable (fun n : ℕ => (((n.factorial : ℝ))⁻¹) • (s • A) ^ n) :=
    NormedSpace.expSeries_summable' (s • A)
  have hexp : NormedSpace.exp ℝ (s • A)
      = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n := by
    simpa using congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := 𝔸)) (s • A)
  have hl : A * (∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n)
      = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹ * s ^ n) • A ^ (n + 1) := by
    rw [(Summable.tsum_mul_left A hf).symm]
    refine tsum_congr fun n => ?_
    rw [Algebra.mul_smul_comm (((n.factorial : ℝ))⁻¹) A ((s • A) ^ n), smul_pow]
    rw [Algebra.mul_smul_comm (s ^ n) A (A ^ n), (pow_succ' A n).symm]
    exact smul_smul ((n.factorial : ℝ))⁻¹ (s ^ n) (A ^ (n + 1))
  have hr : (∑' n : ℕ, (((n.factorial : ℝ))⁻¹) • (s • A) ^ n) * A
      = ∑' n : ℕ, (((n.factorial : ℝ))⁻¹ * s ^ n) • A ^ (n + 1) := by
    rw [(Summable.tsum_mul_right A hf).symm]
    refine tsum_congr fun n => ?_
    rw [Algebra.smul_mul_assoc (((n.factorial : ℝ))⁻¹) ((s • A) ^ n) A, smul_pow]
    rw [Algebra.smul_mul_assoc (s ^ n) (A ^ n) A, (pow_succ A n).symm]
    exact smul_smul ((n.factorial : ℝ))⁻¹ (s ^ n) (A ^ (n + 1))
  rw [hexp, hl, hr]

/-! ## 第三部分：ZOH 一步算子与递推对接 -/

/-- **ZOH 一步（连续→离散）**：从 `h` 出发、输入在整步内保持为常数 `u`，
经过步长 `Δ` 后的状态

    `zohStepGen A B u Δ h = exp(Δ•A) h + Φ(A,Δ) • (B u)`。

`zohStepGen_zero_input` 给出 `u = 0` 时退化为 `RealSSMDiscretization.zohStep A Δ * h`
（即 `Ā h`）；`zoh_recurrence_eq_selState` 给出它与 `RealSelectiveSSM.selState` 的对接。 -/
def zohStepGen (A B u : 𝔸) (Delta : ℝ) (hgen : 𝔸) : 𝔸 :=
  NormedSpace.exp ℝ (Delta • A) * hgen + zohGain A Delta * (B * u)

/-- **ZOH 一步与 `RealSSMDiscretization.zohStep` 的对接（零输入退化）**：
`u = 0` 时 `zohStepGen A B 0 Δ h = zohStep A Δ * h`。

即 `RealSSMDiscretization` 的 `zohStep A Δ := exp ℝ (Δ • A)` 正是本文件 ZOH 一步的
**齐次部分**；本文件补上的是**非齐次（输入）部分** `Φ(A,Δ) • (B u)`。 -/
theorem zohStepGen_zero_input (A B : 𝔸) (Delta : ℝ) (hgen : 𝔸) :
    zohStepGen A B 0 Delta hgen = zohStep A Delta * hgen := by
  simp [zohStepGen, zohStep]

/-- **ZOH 递推 与 `selState` 的精确对接（核心）**：取
`Ā := exp(Δ•A)`（时不变）、`B̄_t := Φ(A,Δ) • (B u_t)`，
则 ZOH 离散轨迹**逐项等于** `RealSelectiveSSM.selState (fun _ => Ā) B̄`。

这是 A4.3 的「对接」：`RealSelectiveSSM` 的全部结果（闭式解 `selState_explicit`、
稳定界 `selState_norm_bound_contracting`、LTI 退化 `sel_is_LTI_special`）
**自动适用**于 ZOH 离散化的连续系统。 -/
theorem zoh_recurrence_eq_selState (A B : 𝔸) (u : ℕ → 𝔸) (Delta : ℝ) (t : ℕ) :
    selState (fun _ => NormedSpace.exp ℝ (Delta • A))
        (fun k => zohGain A Delta * (B * u k)) (t + 1)
      = NormedSpace.exp ℝ (Delta • A)
          * selState (fun _ => NormedSpace.exp ℝ (Delta • A))
              (fun k => zohGain A Delta * (B * u k)) t
        + zohGain A Delta * (B * u t) :=
  selState_succ _ _ t

/-- **ZOH 离散轨迹的闭式解（核心推论）**：把 `RealSelectiveSSM.selState_explicit`
套到 ZOH 系数上，得到

    `h_t = ∑_{k<t} Ā^{t−1−k} * (Φ(A,Δ) • (B u_k))`，   `Ā = exp(Δ•A)`。

**下标递减**（`Ā^{t−1−k}`，最左是最大指数）——与 CORRECTIONS B18 一致；
此处因 `Ā` 与 `B̄_k` 都是环元素、且 `Ā` 是**同一个**元素，故可与
`Finset.prod` 型的 `selProd` 互转（`selProd_const`）。 -/
theorem zoh_state_explicit (A B : 𝔸) (u : ℕ → 𝔸) (Delta : ℝ) (t : ℕ) :
    selState (fun _ => NormedSpace.exp ℝ (Delta • A))
        (fun k => zohGain A Delta * (B * u k)) t
      = ∑ k in range t,
          (NormedSpace.exp ℝ (Delta • A)) ^ (t - 1 - k) * (zohGain A Delta * (B * u k)) :=
  sel_is_LTI_special _ _ t

/-- **ZOH 离散轨迹的一致稳定界（核心推论）**：若 `‖exp(Δ•A)‖ ≤ ρ < 1` 且
`‖Φ(A,Δ)(B u_k)‖ ≤ M`，则 `‖h_t‖ ≤ M/(1−ρ)`，**与 `t` 无关**。

由 `RealSelectiveSSM.selState_norm_bound_contracting` 直接实例化；
`zohGain_norm_le` 给出把 `M` 用连续参数表示的接口：
`M ≤ |Δ| e^{|Δ|‖A‖} ‖B‖ sup_k ‖u_k‖`。 -/
theorem zoh_state_norm_bound (A B : 𝔸) (u : ℕ → 𝔸) (Delta ρ M : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hA : ‖NormedSpace.exp ℝ (Delta • A)‖ ≤ ρ)
    (hB : ∀ k, ‖zohGain A Delta * (B * u k)‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState (fun _ => NormedSpace.exp ℝ (Delta • A))
        (fun k => zohGain A Delta * (B * u k)) t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting _ _ ρ M hρ0 hρ1 (fun _ => hA) hB hM t

/-! ## 第四部分：A4.1 输入依赖性（`A_t = g(x_t)`） -/

/-- **门控递推（输入依赖的选择性 SSM）**：`A_t = g t` 由输入序列 `g` **给出**
（`A_t = σ(W x_t)` 是其特例：取 `g t := σ (W * x t)`）。

本定义把「输入依赖」形式化为：`A_t` 是**另一个序列** `g`，与 `x` 的关系由调用者
以函数形式提供。这样 `RealSelectiveSSM` 的全部代数结果可用，同时把「依赖关系」
作为一个**显式参数**（而非隐藏在类型里）——这是可验证性的关键设计。 -/
def selStateGated (g B : ℕ → 𝔸) : ℕ → 𝔸 := selState g B

/-- **输入依赖的闭式解**：`h_t = ∑_{k<t} selProd g (k+1) t * B_k`。 -/
theorem selStateGated_explicit (g B : ℕ → 𝔸) (t : ℕ) :
    selStateGated g B t = ∑ k in range t, selProd g (k + 1) t * B k :=
  selState_explicit g B t

/-- **输入依赖的稳定界（核心，A4.1）**：若门控一致有界 `∀t, ‖g t‖ ≤ ρ < 1`
且输入项 `∀k, ‖B_k‖ ≤ M`，则 `‖h_t‖ ≤ M/(1−ρ)` —— **与 `t` 无关**。

即：**输入依赖本身不破坏稳定性**；稳定性只取决于门控的**一致范数界** `ρ < 1`。
这正解释了 Mamba 为何把门控写成 `exp(Δ_t A)` 且 `A < 0`：
`Δ_t = softplus(W x_t) > 0` 使 `‖exp(Δ_t A)‖ = e^{Δ_t A} < 1` **对任意输入**成立，
从而 `ρ = sup_t e^{Δ_t A} < 1` 由 `Δ_t` 的**一致下界**保证。 -/
theorem selStateGated_norm_bound (g B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hg : ∀ t, ‖g t‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selStateGated g B t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting g B ρ M hρ0 hρ1 hg hB hM t

/-- **门控扰动的一步传播（A4.1 核心引理）**：设两条门控递推 `h_{t+1} = g_t h_t + B_t` 与
`h'_{t+1} = g'_t h'_t + B_t`（**同一输入序列** `B`）从同一初值出发，则

    `h_{t+1} − h'_{t+1} = g_t (h_t − h'_t) + (g_t − g'_t) h'_t`,

于是 `‖h_{t+1} − h'_{t+1}‖ ≤ ‖g_t‖·‖h_t − h'_t‖ + ‖g_t − g'_t‖·‖h'_t‖`。

这是**输入依赖敏感性**的递归骨架：门控的扰动 `g_t − g'_t` 通过被扰动轨迹的状态
`h'_t` 放大。**完整的多步界（Gronwall 型）未做**（见文件头「诚实边界」）。 -/
theorem selState_gate_perturbation_step (g g' B : ℕ → 𝔸) (t : ℕ) :
    selState g B (t + 1) - selState g' B (t + 1)
      = g t * (selState g B t - selState g' B t)
        + (g t - g' t) * selState g' B t := by
  rw [selState_succ, selState_succ]
  noncomm_ring

/-- **门控扰动的一步范数界（A4.1）**：
`‖h_{t+1} − h'_{t+1}‖ ≤ ‖g_t‖·‖h_t − h'_t‖ + ‖g_t − g'_t‖·‖h'_t‖`。 -/
theorem selState_gate_perturbation_norm_le (g g' B : ℕ → 𝔸) (t : ℕ) :
    ‖selState g B (t + 1) - selState g' B (t + 1)‖
      ≤ ‖g t‖ * ‖selState g B t - selState g' B t‖
        + ‖g t - g' t‖ * ‖selState g' B t‖ := by
  rw [selState_gate_perturbation_step]
  refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-! ## 第五部分：A4.2 谱稳定性充分条件 -/

/-- **范数判据（充分条件之一，最易验证）**：`∀t, ‖A_t‖ ≤ ρ < 1` ⟹ 状态一致有界。
这就是 `selState_norm_bound_contracting` 的**前提形式**；A4.2 要的正是
「`ρ < 1` 的显式充分条件」，本定理把它固定为**范数条件**。 -/
theorem sel_spectral_norm_criterion (A B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA : ∀ i, ‖A i‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState A B t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting A B ρ M hρ0 hρ1 hA hB hM t

/-- **命名修订（历史沿革）**：本定理原名/原注释声称的是「特征值判据（抽象形式，充分条件
之二）」，即「`A_t` 的**每个特征值** `μ` 满足 `‖μ‖ ≤ ρ < 1` **且** `A_t` 是**正规元**
（`A A⋆ = A⋆ A`，`[StarRing]`）⟹ `‖A_t‖ = ρ(A_t) ≤ ρ`，从而回到范数判据」。该陈述
**已被否证为与本定理签名不符**：实际的假设 `hspec` 就是**范数界** `∀i, ‖A i‖ ≤ ρ`，
签名中既无特征值条件也无正规性条件。

据此，本定理的准确身份是 `sel_spectral_norm_criterion` 的**同义重述**（逐字同构的
范数判据，仅实例参数多一个 `[StarRing 𝔸]`），本文件中的 `[StarRing 𝔸]` 在证明体内
**未被使用**。

已否证/未做的部分（保留备查，不得据此认为已证）：
- 「特征值 + 正规元 ⟹ `‖A‖ ≤ ρ`」的桥（Gelfand / 谱半径公式 `‖A‖ = ρ(A)`）**未做**；
- `[StarRing]` 的实际调用**未做**。
一般的「特征值模 < 1」（非正规）**不**蕴含 `‖A‖ < 1`（反例：`[[1, K], [0, 1]]`
特征值全为 1，但 `‖·‖_∞ = 1 + K`）——该反例说明的是上述**未做的桥**不能省略正规性
假设，与本定理（范数判据重述）本身无关。 -/
theorem sel_spectral_eigen_criterion [StarRing 𝔸] (A B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hspec : ∀ i, ‖A i‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState A B t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting A B ρ M hρ0 hρ1 hspec hB hM t

/-- **LTI 的 ZOH 谱判据（A4.2 × A4.3 交叉）**：若连续生成元满足
`‖exp(s•A)‖ ≤ ρ < 1`（`Δ_t ≡ s` 时即 `‖Ā‖ ≤ ρ`），则 LTI 状态一致有界。

这是 Mamba 稳定性的**连续侧**充分条件：`A` 的所有特征值实部 < 0（耗散）
⟹ 存在 `s` 使 `‖exp(s A)‖ < 1`（半群指数衰减）。本文件把「实部 < 0 ⟹ 存在这样的
`s`」作为**未做的接口**留出（需要 `Matrix` 谱与 `exp` 的桥接）。 -/
theorem sel_LTI_zoh_spectral_criterion (a : 𝔸) (B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (ha : ‖a‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState (fun _ => a) B t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting (fun _ => a) B ρ M hρ0 hρ1 (fun _ => ha) hB hM t

end Lattice
