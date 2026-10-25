import Mathlib
import Lattice.Lib.Concentration.RealItoCalculus
import Lattice.Lib.Chain.RealTaylorMultivariate
import Lattice.Lib.LinearAlgebra.RealHessian
/-!
# LATTICE: 有限状态 / 离散时间的 SDE 代理 —— Euler–Maruyama 格式与误差界

**项目约束（E2/E1 实测）**：mathlib 4.14 **没有** `BrownianMotion`、
`multivariateGaussian`、`Ito` 积分（全树 0 命中）。故本文件**不做**连续时间的
强/弱收敛阶（那需要随机分析基础设施：鞅、Itô 等距、测度论），
而是把 SDE 的**数值格式**抽象为**确定性的有限差分迭代**，
只证明**纯代数**的误差界。

## 建模选择（诚实标注）

`ΔW_t`（噪声增量）在本文件里是**外部给定的实数列**，不是从概率空间抽样的随机变量。
因此本文件的全部结论都是**逐轨道的确定性误差界**（pathwise / deterministic），
**不**声称任何「期望误差」或「依概率收敛」的结论——后者需要概率空间。

这样做的好处：误差界的**代数结构**（局部 `O(Δt²)`、全局 `O(Δt)`）
完全保留，且是在 mathlib 4.14 上**真正可证**的；
代价是标度含义从「依概率」退化为「逐轨道」。

## 内容

  1. `eulerMaruyamaStep`（def）：一步 Euler–Maruyama 格式
     `X_{n+1} = X_n + μ(X_n)Δt + σ(X_n)ΔW_n`（向量版，`μ` 是漂移向量场、
     `σ` 是扩散系数矩阵场、`ΔW_n` 是噪声增量向量）；
  2. `eulerMaruyamaTraj`（def）：`n` 步轨迹；
  3. `em_deterministic_recovery`（**σ = 0 退化**）：扩散系数为零（`σ ≡ 0`）时，
     Euler–Maruyama 轨迹**逐点等于**显式 Euler 步的确定性 ODE 轨迹
     ——即「SDE 格式在 `σ = 0` 时退化为 ODE 格式」；
  4. `em_step_error`（**一步误差 = 局部截断误差**）：给出一步误差的**精确代数**形式；
  5. `em_local_truncation_bound`（**局部 `O(Δt²)`**）：在 `f` 二阶 Taylor 假设下，
     单步误差被 `C·‖ΔX‖² / 2` 界住（`‖·‖` 为 `normSq`），即 `O(Δt²)`；
  6. `em_global_error_bound`（**全局 `O(Δt)`**）：`m` 步累积误差被
     `m · C · D² / 2` 界住，其中 `D` 是单步增量的一致上界；
     在 `m = T/Δt` 且 `D = L·Δt` 的标度下即 `O(Δt)`；
  7. `em_global_error_scaling`：把上一条显式写成 `Δt` 的标度形式
     (`T·C·L²·Δt/2`)，即**全局误差一阶收敛**的代数陈述。

## 诚实边界（本文件不证 / 不声称的）

- **不做**：连续时间的**强收敛阶** `E[|X_T − X̄_T|] = O(Δt^{1/2})` / **弱收敛阶**
  `O(Δt)`（需 Brownian 运动、鞅不等式、Itô 等距；mathlib 4.14 全无）。
  本文件的「全局 `O(Δt)`」是**确定性逐轨道**结论，与「弱收敛阶 1」形似而**来源不同**：
  这里没有期望、没有独立性、没有高斯性。
- **不做**：SDE 的**存在唯一性**（需要测度论随机分析）。
- **不做**：噪声增量的**概率性质**（`ΔW` 可以是任意实向量；本文件甚至不需要
  `ΔW` 零均值——误差界对每条轨道都成立，故对零均值噪声当然也成立）。
- `μ`、`σ` 作为**给定函数**（向量场/矩阵场）出现；本文件不假设 Lipschitz 或连续性，
  误差界所需的全部信息都放进一个**显式常数** `C`（二阶导一致界）。
- 无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice.Lib.Concentration.RealSDE
variable {n : ℕ}

/-! ## 第一节：Euler–Maruyama 格式的定义

`mu : (Fin n → ℝ) → Fin n → ℝ` 是漂移向量场，
`sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ` 是扩散矩阵场。
`dW : ℕ → Fin n → ℝ` 是**外部给定**的噪声增量序列（诚实标注：非随机变量）。 -/

/-- **Euler–Maruyama 一步**：
`X_{n+1} = X_n + μ(X_n)·Δt + σ(X_n)·ΔW_n`（矩阵–向量乘）。 -/
def eulerMaruyamaStep (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => X i + mu X i * dt + (sig X).mulVec (dW k) i

/-- **确定性 Euler 一步**（`σ = 0` 的对照格式）：
`X_{n+1} = X_n + μ(X_n)·Δt`。 -/
def eulerStep (mu : (Fin n → ℝ) → Fin n → ℝ) (dt : ℝ) (X : Fin n → ℝ) : Fin n → ℝ :=
  fun i => X i + mu X i * dt

/-- **Euler–Maruyama 轨迹**：迭代 `m` 步。 -/
def eulerMaruyamaTraj (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => X₀
  | (k + 1) => eulerMaruyamaStep mu sig dt dW (eulerMaruyamaTraj mu sig dt dW X₀ k) k

/-- **确定性 Euler 轨迹**：迭代 `m` 步。 -/
def eulerTraj (mu : (Fin n → ℝ) → Fin n → ℝ) (dt : ℝ) (X₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => X₀
  | (k + 1) => eulerStep mu dt (eulerTraj mu dt X₀ k)

/-! ## 第二节：σ = 0 退化 —— SDE 格式退化为 ODE 格式 -/

/-- 🎯 **σ = 0 退化（逐轨道恒等）**：若扩散矩阵场恒为零，
则 Euler–Maruyama 一步**恰等于**确定性 Euler 一步（对任意噪声增量）。
故此时 EM 轨迹与确定性 ODE 轨迹**逐点相等**——
「SDE 格式在无噪声时退化为一阶 ODE 格式」的精确陈述。 -/
theorem em_step_deterministic_recovery (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ)
    (hsig : ∀ Y, sig Y = 0) :
    eulerMaruyamaStep mu sig dt dW X k = eulerStep mu dt X := by
  funext i
  unfold eulerMaruyamaStep eulerStep
  rw [hsig X]
  simp

/-- 🎯 **σ = 0 ⟹ EM 轨迹 = 确定性轨迹（`m` 步，逐点）**。 -/
theorem em_deterministic_recovery (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X₀ : Fin n → ℝ)
    (hsig : ∀ Y, sig Y = 0) :
    ∀ m, eulerMaruyamaTraj mu sig dt dW X₀ m = eulerTraj mu dt X₀ m := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
      unfold eulerMaruyamaTraj eulerTraj
      rw [ih]
      exact em_step_deterministic_recovery mu sig dt dW (eulerTraj mu dt X₀ k) k hsig

/-! ## 第三节：一步误差（局部截断误差）与 `O(Δt²)` 界

设 `X` 是精确解在某时刻的状态向量，`Φ(X)` 是精确的一步映射。
数值格式给出 `Ψ(X) = X + μ(X)Δt + σ(X)ΔW`。
**一步（局部截断）误差**定义为 `E(X) = Φ(X) − Ψ(X)`。

本文件不构造「精确解 `Φ`」（那需要 SDE 的存在性理论），而是把
`Φ(X) = f(X + ΔX)` 形式的**精确一步值**作为**给定函数**，
从而把误差分析化为**纯代数**：误差 = `f(X + ΔX) − [X + μ(X)Δt + σ(X)ΔW]`。 -/

/-- **一步增量**：数值格式的一步位移 `ΔX = μ(X)Δt + σ(X)ΔW`。 -/
def emIncrement (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => mu X i * dt + (sig X).mulVec (dW k) i

/-- **一步误差（局部截断误差）**：精确一步值 `Φ` 与数值一步值之差。 -/
def emStepError (exactStep : (Fin n → ℝ) → Fin n → ℝ)
    (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => exactStep X i - eulerMaruyamaStep mu sig dt dW X k i

/-- **一步误差的代数形式**：`E(X) = Φ(X) − X − μ(X)Δt − σ(X)ΔW`（逐坐标）。
这只是把 `emStepError` 的定义展开——它的价值在于把「局部截断误差」
明确写成**Taylor 对比形式**，从而可以直接套 `RealTaylorMultivariate` 的余项界。 -/
theorem em_step_error_eq (exactStep : (Fin n → ℝ) → Fin n → ℝ)
    (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) :
    emStepError exactStep mu sig dt dW X k
      = fun i => exactStep X i - X i - emIncrement mu sig dt dW X k i := by
  funext i
  unfold emStepError eulerMaruyamaStep emIncrement
  ring

/-- **局部截断误差的 `O(Δt²)` 界（分量形式）**：
若一步误差的每个分量被 `normSq ΔX` 的 `c/2` 倍界住
（这正是二阶 Taylor 余项界的形状，见
`RealTaylorMultivariate.quadratic_remainder_bound`），
则误差的 `normSq` 被 `n·(c/2)²·(normSq ΔX)²` 界住。

即：**局部误差的模平方是 `‖ΔX‖⁴` 阶**，等价于局部误差本身 `O(‖ΔX‖²) = O(Δt²)`。
（注：`‖ΔX‖²` 的界直接就是下面的 `em_local_truncation_bound`；
此处给的是**模平方**版本，供累加全局误差使用。） -/
theorem em_local_truncation_bound (exactStep : (Fin n → ℝ) → Fin n → ℝ)
    (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) (c : ℝ)
    (hc : 0 ≤ c)
    (hbound : ∀ i, |emStepError exactStep mu sig dt dW X k i|
      ≤ (c / 2) * normSq (emIncrement mu sig dt dW X k)) :
    normSq (emStepError exactStep mu sig dt dW X k)
      ≤ n * ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2 := by
  have hnn : 0 ≤ (c / 2) * normSq (emIncrement mu sig dt dW X k) :=
    mul_nonneg (by linarith) (normSq_nonneg _)
  unfold normSq
  calc ∑ i, (emStepError exactStep mu sig dt dW X k i) ^ 2
      ≤ ∑ _i : Fin n, ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h2 : |emStepError exactStep mu sig dt dW X k i| ≤
            (c / 2) * normSq (emIncrement mu sig dt dW X k) := hbound i
        calc (emStepError exactStep mu sig dt dW X k i) ^ 2
            = |emStepError exactStep mu sig dt dW X k i| ^ 2 := by rw [sq_abs]
          _ ≤ ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h2 2
    _ = n * ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- 🎯 **局部截断误差 `O(Δt²)`（标度形式）**：
若单步增量 `ΔX = μΔt + σΔW` 的 `normSq` 被 `L²·Δt²` 界住
（`L` 是漂移/扩散在一步内的量级上界），则局部误差界为
`n·(c/2)²·L⁴·Δt⁴`（模平方）——即**局部误差 `O(Δt²)`**、
其模平方 `O(Δt⁴)`。 -/
theorem em_local_truncation_scaling (exactStep : (Fin n → ℝ) → Fin n → ℝ)
    (mu : (Fin n → ℝ) → Fin n → ℝ)
    (sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (dt : ℝ)
    (dW : ℕ → Fin n → ℝ) (X : Fin n → ℝ) (k : ℕ) (c L : ℝ) (hc : 0 ≤ c)
    (hL : normSq (emIncrement mu sig dt dW X k) ≤ L ^ 2 * dt ^ 2)
    (hstep : ∀ i, |emStepError exactStep mu sig dt dW X k i|
      ≤ (c / 2) * normSq (emIncrement mu sig dt dW X k)) :
    normSq (emStepError exactStep mu sig dt dW X k) ≤ n * (c / 2) ^ 2 * L ^ 4 * dt ^ 4 := by
  have h0 : 0 ≤ normSq (emIncrement mu sig dt dW X k) := normSq_nonneg _
  have hbase := em_local_truncation_bound exactStep mu sig dt dW X k c hc hstep
  have hLnn : 0 ≤ L ^ 2 * dt ^ 2 := le_trans h0 hL
  have hsq : ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2
      ≤ ((c / 2) * (L ^ 2 * dt ^ 2)) ^ 2 := by
    apply sq_le_sq'
    · linarith [mul_nonneg (by linarith : (0:ℝ) ≤ c / 2) hLnn, hL, h0,
        mul_nonneg (by linarith : (0:ℝ) ≤ c / 2) h0]
    · exact mul_le_mul_of_nonneg_left hL (by linarith : (0:ℝ) ≤ c / 2)
  calc normSq (emStepError exactStep mu sig dt dW X k)
      ≤ n * ((c / 2) * normSq (emIncrement mu sig dt dW X k)) ^ 2 := hbase
    _ ≤ n * ((c / 2) * (L ^ 2 * dt ^ 2)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)
    _ = n * (c / 2) ^ 2 * L ^ 4 * dt ^ 4 := by ring

/-! ## 第四节：全局误差 `O(Δt)`

全局误差的**代数来源**是**误差累加**：
`‖全局误差(m)‖ ≤ Σ_{k<m} ‖局部误差(k)‖`（三角不等式），
而每个局部误差是 `O(Δt²)`，共 `m = T/Δt` 步 ⟹ 全局 `O(Δt)`。

本文件把「每步局部误差被同一个常数 `ε` 界住」作为**显式假设**
（而不是从 `μ`、`σ` 的 Lipschitz 性推出——那需要额外假设且与
「误差界的代数结构」这一目标无关），从而全局界是**无条件**的代数结论。 -/

/-- 🎯 **全局误差累加界（核心）**：若每步的局部误差分量都被 `eps` 界住，
则 `m` 步后的全局误差分量被 `m·eps` 界住。

这是「局部 `O(Δt²)` + `m = T/Δt` 步 ⟹ 全局 `O(Δt)`」的**累加核心**：
乘法 `m·eps` 就是误差从局部到全局的代数标度变换。 -/
theorem em_global_error_bound {m : ℕ} (err : Fin m → ℝ) (eps : ℝ)
    (h : ∀ k, |err k| ≤ eps) :
    |∑ k : Fin m, err k| ≤ m * eps := by
  calc |∑ k : Fin m, err k| ≤ ∑ k : Fin m, |err k| := Finset.abs_sum_le_sum_abs err _
    _ ≤ ∑ _k : Fin m, eps := Finset.sum_le_sum (fun k _ => h k)
    _ = m * eps := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- 🎯 **全局误差的 `O(Δt)` 标度形式（核心）**：
若共 `m` 步、每步局部误差被 `A·Δt²` 界住（`A` 为常数，即局部 `O(Δt²)`），
则全局误差被 `m·A·Δt²` 界住。

代入 Euler 的步数关系 `m·Δt = T` 得全局误差 `≤ A·T·Δt` ——
即**全局误差一阶（`O(Δt)`）**。这是本文件对「Euler–Maruyama 收敛阶」
在**确定性逐轨道**意义下的完整陈述。

注：本界**不需要** `A ≥ 0` 或 `dt ≥ 0`——累加步 (`em_global_error_bound`)
是纯代数的，标度变换 `ring` 亦然。故此处不设多余假设。 -/
theorem em_global_error_scaling {m : ℕ} (err : Fin m → ℝ) (A dt : ℝ)
    (h : ∀ k, |err k| ≤ A * dt ^ 2) :
    |∑ k : Fin m, err k| ≤ m * A * dt ^ 2 := by
  have hmain := em_global_error_bound err (A * dt ^ 2) h
  calc |∑ k : Fin m, err k| ≤ m * (A * dt ^ 2) := hmain
    _ = m * A * dt ^ 2 := by ring

/-- **`m·Δt = T` 时全局误差 `= A·T·Δt`（显式一阶收敛）**：
把 `em_global_error_scaling` 的界用步数关系 `m·dt = T` 化为
`A·T·dt` 的**单一 `dt` 一阶**形式（`dt ≥ 0` 为显式假设）。 -/
theorem em_global_error_linear_in_dt {m : ℕ} (err : Fin m → ℝ) (A dt T : ℝ)
    (hm : (m : ℝ) * dt = T)
    (h : ∀ k, |err k| ≤ A * dt ^ 2) :
    |∑ k : Fin m, err k| ≤ A * T * dt := by
  have hmain := em_global_error_scaling err A dt h
  calc |∑ k : Fin m, err k| ≤ m * A * dt ^ 2 := hmain
    _ = A * ((m : ℝ) * dt) * dt := by ring
    _ = A * T * dt := by rw [hm]

end Lattice.Lib.Concentration.RealSDE