import Lattice.Lib.Optim.RealGradDescent
import Lattice.Lib.Architectures.RealOperatorNorm
import Mathlib

/-!
# LATTICE: SGD 动量（重球法）在平方损失上的收敛 —— 无动量 GD 的二阶递推泛化

RealGradDescent 的梯度下降更新

    x' = x - (2η)·A†(A·x - b)

是「无动量」一阶方法。本文件把它泛化到**重球（Polyak 动量）**二阶递推：

    v'  = μ·v + (2η)·A†(A·x - b)      （μ ≥ 0 动量系数）
    x'  = x - v'

μ = 0 时 v' = (2η)·A†(A·x-b)，x' = x - (2η)·A†(A·x-b)，精确退化为 GDUpdate
（momentum_gd_recovery）。

**误差恒等式（向量版，核心）**：误差 e = A·x - b 满足二阶递推的精确恒等式
（momentum_error_recurrence_step，GD_error_identity 的动量泛化）：

    e' = (1 - (2η)·A∘A†)·e + μ·(e - e_prev)      （e_prev = A·(x+v) - b）

展开 v' 的定义即 A·v' = μ·(e - e_prev) + (2η)·AA†·e（注意 x + v = x_prev）。

**单步收缩**（momentum_step_contraction / momentum_step_contraction_max）：

    ‖e'‖ ≤ (‖1-2η·AA†‖ + μ)·‖e‖ + μ·‖e_prev‖
    ‖e'‖ ≤ (‖1-2η·AA†‖ + 2μ)·max(‖e‖, ‖e_prev‖)

诚实修正：max 形式的系数是 ‖T‖ + 2μ 而非 ‖T‖ + μ —— 三角不等式只能给出
‖e - e_prev‖ ≤ ‖e‖ + ‖e_prev‖，无法给出 ≤ max 界（‖T‖ + μ 版本不成立）。

**收敛（本文件主结果）**：
  · 向量版（momentum_iterate_converges）：误差对 (e_t, e_{t-1}) 视为状态，
    加权范数 W_t = ‖e_t‖ + γ·‖e_{t-1}‖（γ = (1-c₀)/2）以系数
    c = (c₀ + 2μ + 1)/2 < 1 收缩（条件 c₀ + 2μ < 1），连接
    RealConvergence.contraction_converges 得 ε-终止；
  · 标量版（scalar_momentum_converges）：A = a : ℝ 时二阶线性递推
    e_{t+1} = (1 - 2ηa²)·e_t + μ·(e_t - e_{t-1})，若 0 ≤ μ 且
    |1 - 2ηa² + μ| + μ < 1（μ = 0 时退化为 |1-2ηa²| < 1，即
    RealGradDescent 的标量谱条件），则加权范数
    W_t = |e_t| + γ·|e_{t-1}|（γ = (μ + 1 - |1-2ηa²+μ|)/2）以系数
    c = (|1-2ηa²+μ| + μ + 1)/2 < 1 收缩 ⟹ |e_t| → 0 且 ε-终止。

诚实边界：
  · 动量收缩条件（c₀ + 2μ < 1 / |1-2ηa²+μ| + μ < 1）比无动量谱条件略强，
    反映重球法「动量加速以更紧的步长-动量联合条件为代价」；充分条件，
    非最优（谱半径条件可放宽，但需要特征值理论，超出本文件范围）；
  · 标量版完整闭环；向量版同样闭环（状态加权范数收缩）；
  · 全程无 sorry/axiom/admit；唯一数值假设是 μ 范围与谱界。
-/

noncomputable section

namespace Lattice

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-! ## 动量更新：v' = μ·v + (2η)·A†(Ax-b)，x' = x - v' -/

def MomentumUpdate (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v x : E) : E :=
  x - (μ • v + (2 * η : 𝕜) • A.adjoint (A x - b))

/-- 状态对 (v, x) 的一步转移：(v', x')，v' = μ·v + (2η)·A†(Ax-b)，x' = x - v'。-/
def MomentumState (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (p : E × E) : E × E :=
  (μ • p.1 + (2 * η : 𝕜) • A.adjoint (A p.2 - b),
   p.2 - (μ • p.1 + (2 * η : 𝕜) • A.adjoint (A p.2 - b)))

/-- 状态对迭代：pair (n+1) = MomentumState (pair n)。-/
def MomentumIterate (A : E →L[𝕜] F) (b : F) (η μ : ℝ) : ℕ → E × E → E × E
  | 0, p => p
  | n + 1, p => MomentumState A b η μ (MomentumIterate A b η μ n p)

/-- 第 n 步的速度 v_n（初始 v₀ 与 x₀）。-/
def MomentumV (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) (n : ℕ) : E :=
  (MomentumIterate A b η μ n (v0, x0)).1

/-- 第 n 步的位置 x_n。-/
def MomentumX (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) (n : ℕ) : E :=
  (MomentumIterate A b η μ n (v0, x0)).2

omit [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- 动量版的平方误差（对应 GDError）：‖A·x_n - b‖²。-/
def MomentumError (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) (n : ℕ) : ℝ :=
  ‖A (MomentumX A b η μ v0 x0 n) - b‖ ^ 2

/-! ## 定理一：μ = 0 退化为 GDUpdate
动量更新在无动量时精确等于 RealGradDescent.GDUpdate（特例回收）。-/

lemma momentum_gd_recovery (A : E →L[𝕜] F) (b : F) (η : ℝ) (v x : E) :
    MomentumUpdate A b η 0 v x = GDUpdate A b η x := by
  simp [MomentumUpdate, GDUpdate]

/-! ## 定理二：误差恒等式（向量版，核心）
e' = (1 - (2η)·A∘A†)·e + μ·(e - e_prev)，e = A·x - b，e_prev = A·(x+v) - b。
这是 GD_error_identity 的动量泛化：展开 v' 定义，A·v' = μ·(e - e_prev) + (2η)·AA†·e。-/

lemma momentum_error_recurrence_step (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v x : E) :
    A (MomentumUpdate A b η μ v x) - b =
      ((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b)
      + μ • ((A x - b) - (A (x + v) - b)) := by
  unfold MomentumUpdate
  -- A·v = A·(x+v) - A·x（x + v = x_prev）
  have hav : A v = A (x + v) - A x := by
    calc
      A v = A v + A x - A x := by abel
      _ = A (x + v) - A x := by
        rw [← A.map_add]
        abel
  -- A (μ•v) = μ•(A v)（ℝ 作用穿过 𝕜-线性算子）
  have hsmul : A (μ • v) = μ • A v := by
    calc
      A (μ • v) = A ((μ : 𝕜) • v) := by rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
      _ = (μ : 𝕜) • A v := A.map_smul (μ : 𝕜) v
      _ = μ • A v := by rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  -- μ•(A(x+v) - Ax) = -μ•(Ax - A(x+v))
  have hneg : μ • (A (x + v) - A x) = -(μ • (A x - A (x + v))) := by
    rw [← neg_sub (A x) (A (x + v)), smul_neg]
  calc
    A (x - (μ • v + (2 * η : 𝕜) • A.adjoint (A x - b))) - b
        = (A x - A (μ • v + (2 * η : 𝕜) • A.adjoint (A x - b))) - b := by
          rw [A.map_sub]
    _ = (A x - (μ • A v + (2 * η : 𝕜) • A (A.adjoint (A x - b)))) - b := by
          rw [A.map_add, hsmul, A.map_smul]
    _ = (A x - (μ • A v + (2 * η : 𝕜) • (A ∘L A.adjoint) (A x - b))) - b := by
          rw [← ContinuousLinearMap.comp_apply]
    _ = (A x - b) - (μ • A v + (2 * η : 𝕜) • (A ∘L A.adjoint) (A x - b)) := by
          abel
    _ = (A x - b) - (2 * η : 𝕜) • (A ∘L A.adjoint) (A x - b) + μ • (A x - A (x + v)) := by
          rw [hav, hneg]
          abel
    _ = ((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b)
          + μ • ((A x - b) - (A (x + v) - b)) := by
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have harg : A x - A (x + v) = (A x - b) - (A (x + v) - b) := by abel
          rw [harg]

/-! ## 定理三：单步收缩（两项界）
‖e'‖ ≤ (c + μ)·‖e‖ + μ·‖e_prev‖（谱界 ‖1-2η·AA†‖ ≤ c，三角不等式直接可证）。-/

theorem momentum_step_contraction (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v x : E) (c : ℝ)
    (hμ0 : 0 ≤ μ) (hspec : ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (MomentumUpdate A b η μ v x) - b‖ ≤ (c + μ) * ‖A x - b‖ + μ * ‖A (x + v) - b‖ := by
  rw [momentum_error_recurrence_step A b η μ v x]
  calc
    ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b)
        + μ • ((A x - b) - (A (x + v) - b))‖
        ≤ ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) (A x - b)‖
          + ‖μ • ((A x - b) - (A (x + v) - b))‖ := norm_add_le _ _
    _ ≤ c * ‖A x - b‖ + μ * ‖(A x - b) - (A (x + v) - b)‖ := by
          exact add_le_add
            (le_trans (ContinuousLinearMap.le_opNorm _ (A x - b))
              (mul_le_mul_of_nonneg_right hspec (norm_nonneg (A x - b))))
            (by simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0])
    _ ≤ c * ‖A x - b‖ + μ * (‖A x - b‖ + ‖A (x + v) - b‖) := by
          exact add_le_add_left (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hμ0) _
    _ = (c + μ) * ‖A x - b‖ + μ * ‖A (x + v) - b‖ := by ring

/-! ## 定理四：单步收缩（max 形式，诚实系数 c + 2μ）
‖e'‖ ≤ (c + 2μ)·max(‖e‖, ‖e_prev‖)。注意系数是 c + 2μ 而非 c + μ
（‖e - e_prev‖ ≤ ‖e‖ + ‖e_prev‖ 只能给出 c + 2μ）。-/

theorem momentum_step_contraction_max (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v x : E) (c : ℝ)
    (hμ0 : 0 ≤ μ) (hspec : ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c) :
    ‖A (MomentumUpdate A b η μ v x) - b‖ ≤ (c + 2 * μ) * max (‖A x - b‖) (‖A (x + v) - b‖) := by
  have hc0 : 0 ≤ c := le_trans (norm_nonneg _) hspec
  have hcm0 : 0 ≤ c + μ := add_nonneg hc0 hμ0
  calc
    ‖A (MomentumUpdate A b η μ v x) - b‖ ≤ (c + μ) * ‖A x - b‖ + μ * ‖A (x + v) - b‖ :=
      momentum_step_contraction A b η μ v x c hμ0 hspec
    _ ≤ (c + μ) * max (‖A x - b‖) (‖A (x + v) - b‖)
        + μ * max (‖A x - b‖) (‖A (x + v) - b‖) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left (‖A x - b‖) (‖A (x + v) - b‖)) hcm0)
            (mul_le_mul_of_nonneg_left (le_max_right (‖A x - b‖) (‖A (x + v) - b‖)) hμ0)
    _ = (c + 2 * μ) * max (‖A x - b‖) (‖A (x + v) - b‖) := by ring

/-! ## 误差对：e_t = A·x_t - b，e_{t-1} = A·(x_t + v_t) - b
（x_t + v_t = x_{t-1}：v_t = x_{t-1} - x_t）。-/

def MomentumErrPair (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) (n : ℕ) : F × F :=
  (A (MomentumX A b η μ v0 x0 n) - b,
   A (MomentumX A b η μ v0 x0 n + MomentumV A b η μ v0 x0 n) - b)

/-! ## 引理：误差对的二阶递推（状态向量形式）
(e_{t+1}, e_t) = (T·e_t + μ·(e_t - e_{t-1}), e_t)，T = 1 - 2η·AA†。
即动量步在 E×E 状态上是线性算子（状态向量收缩的精确恒等式）。-/

lemma momentum_err_pair_recurrence (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) :
    ∀ n : ℕ,
      MomentumErrPair A b η μ v0 x0 (n + 1) =
        (((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint))
            (A (MomentumX A b η μ v0 x0 n) - b)
          + μ • ((A (MomentumX A b η μ v0 x0 n) - b)
              - (A (MomentumX A b η μ v0 x0 n + MomentumV A b η μ v0 x0 n) - b)),
         A (MomentumX A b η μ v0 x0 n) - b) := by
  intro n
  unfold MomentumErrPair MomentumX MomentumV
  set X : E × E := MomentumIterate A b η μ n (v0, x0) with hX
  have hstep' : MomentumIterate A b η μ (n + 1) (v0, x0) = MomentumState A b η μ X := by
    rw [hX]
    rfl
  rw [hstep']
  apply Prod.ext
  · -- 第一分量：e_{n+1} = T·e_n + μ·(e_n - e_{n-1})（momentum_error_recurrence_step）
    simpa [MomentumState, MomentumUpdate] using momentum_error_recurrence_step A b η μ X.1 X.2
  · -- 第二分量：x_{n+1} + v_{n+1} = x_n
    have hv : (MomentumState A b η μ X).2 + (MomentumState A b η μ X).1 = X.2 := by
      simp [MomentumState]
    rw [hv]

/-! ## 定理五：动量迭代收敛（向量版，ε-终止）
谱界 ‖1-2η·AA†‖ ≤ c₀ 且 c₀ + 2μ < 1，0 ≤ μ：
误差对在加权范数 W_t = ‖e_t‖ + γ·‖e_{t-1}‖（γ = (1-c₀)/2）下以
c = (c₀ + 2μ + 1)/2 < 1 收缩 ⟹ ∀ ε > 0，∃ n，‖A·x_n - b‖ < ε。
连接 RealConvergence.contraction_converges。-/

theorem momentum_iterate_converges (A : E →L[𝕜] F) (b : F) (η μ : ℝ) (v0 x0 : E) (c0 : ℝ)
    (hc0n : 0 ≤ c0) (hμ0 : 0 ≤ μ) (hs : c0 + 2 * μ < 1)
    (hspec : ‖(1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)‖ ≤ c0) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖A (MomentumX A b η μ v0 x0 n) - b‖ < ε := by
  let γ : ℝ := (1 - c0) / 2
  let c : ℝ := c0 + μ + γ
  let W : ℕ → ℝ := fun n =>
    ‖(MomentumErrPair A b η μ v0 x0 n).1‖ + γ * ‖(MomentumErrPair A b η μ v0 x0 n).2‖
  have hγ0 : 0 ≤ γ := by
    dsimp [γ]
    nlinarith [hs, hμ0]
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [hc0n, hμ0, hγ0]
  have hc1 : c < 1 := by
    dsimp [c, γ]
    nlinarith [hs]
  have hμcγ : μ ≤ c * γ := by
    have hdiff : 0 ≤ c * γ - μ := by
      dsimp [c, γ]
      have hcalc : (c0 + μ + (1 - c0) / 2) * ((1 - c0) / 2) - μ =
          (1 + c0) * (1 - c0 - 2 * μ) / 4 := by ring
      rw [hcalc]
      have h1 : 0 ≤ 1 + c0 := by nlinarith [hc0n]
      have h2 : 0 ≤ 1 - c0 - 2 * μ := by nlinarith [hs]
      have hprod : 0 ≤ (1 + c0) * (1 - c0 - 2 * μ) := mul_nonneg h1 h2
      nlinarith [hprod]
    nlinarith
  have hWstep : ∀ n : ℕ, W (n + 1) ≤ c * W n := by
    intro n
    dsimp [W]
    rw [momentum_err_pair_recurrence A b η μ v0 x0 n]
    set e : F := (MomentumErrPair A b η μ v0 x0 n).1 with he
    set eprev : F := (MomentumErrPair A b η μ v0 x0 n).2 with heprev
    have htri : ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) e + μ • (e - eprev)‖
        ≤ (c0 + μ) * ‖e‖ + μ * ‖eprev‖ := by
      calc
        ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) e + μ • (e - eprev)‖
            ≤ ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) e‖
              + ‖μ • (e - eprev)‖ := norm_add_le _ _
        _ ≤ c0 * ‖e‖ + μ * ‖e - eprev‖ := by
              exact add_le_add
                (le_trans (ContinuousLinearMap.le_opNorm _ e)
                  (mul_le_mul_of_nonneg_right hspec (norm_nonneg e)))
                (by simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ0])
        _ ≤ c0 * ‖e‖ + μ * (‖e‖ + ‖eprev‖) := by
              exact add_le_add_left (mul_le_mul_of_nonneg_left (norm_sub_le e eprev) hμ0) _
        _ = (c0 + μ) * ‖e‖ + μ * ‖eprev‖ := by ring
    calc
      ‖((1 : F →L[𝕜] F) - (2 * η : 𝕜) • (A ∘L A.adjoint)) e + μ • (e - eprev)‖ + γ * ‖e‖
          ≤ ((c0 + μ) * ‖e‖ + μ * ‖eprev‖) + γ * ‖e‖ := add_le_add_right htri _
      _ = (c0 + μ + γ) * ‖e‖ + μ * ‖eprev‖ := by ring
      _ ≤ (c0 + μ + γ) * ‖e‖ + c * γ * ‖eprev‖ := by
            exact add_le_add_left (mul_le_mul_of_nonneg_right hμcγ (norm_nonneg eprev)) _
      _ = c * (‖e‖ + γ * ‖eprev‖) := by
            dsimp [c]
            ring
  have hWnonneg : ∀ n : ℕ, 0 ≤ W n := by
    intro n
    dsimp [W]
    exact add_nonneg (norm_nonneg _) (mul_nonneg hγ0 (norm_nonneg _))
  have hconv := contraction_converges c hc0 hc1 hWstep hWnonneg
  intro ε hε
  rcases hconv ε hε with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle : ‖A (MomentumX A b η μ v0 x0 n) - b‖ ≤ W n := by
    simp [W, MomentumErrPair]
    exact mul_nonneg hγ0 (norm_nonneg _)
  exact lt_of_le_of_lt hle hn

/-! ## 标量动量：A = a : ℝ（乘以标量系数 a 的线性算子）
误差 e_n = a·x_n - b 满足二阶线性递推
e_{n+1} = (1 - 2ηa²)·e_n + μ·(e_n - e_{n-1})。-/

def ScalarMomStep (a b η μ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (μ * p.1 + 2 * η * a * (a * p.2 - b),
   p.2 - (μ * p.1 + 2 * η * a * (a * p.2 - b)))

def ScalarMomIterate (a b η μ : ℝ) : ℕ → ℝ × ℝ → ℝ × ℝ
  | 0, p => p
  | n + 1, p => ScalarMomStep a b η μ (ScalarMomIterate a b η μ n p)

def ScalarMomV (a b η μ : ℝ) (v0 x0 : ℝ) (n : ℕ) : ℝ :=
  (ScalarMomIterate a b η μ n (v0, x0)).1

def ScalarMomX (a b η μ : ℝ) (v0 x0 : ℝ) (n : ℕ) : ℝ :=
  (ScalarMomIterate a b η μ n (v0, x0)).2

def ScalarMomErr (a b η μ : ℝ) (v0 x0 : ℝ) (n : ℕ) : ℝ :=
  a * ScalarMomX a b η μ v0 x0 n - b

/-- 误差对 (e_n, e_{n-1})，e_{n-1} = a·(x_n + v_n) - b = a·x_{n-1} - b。-/
def ScalarMomErrPair (a b η μ : ℝ) (v0 x0 : ℝ) (n : ℕ) : ℝ × ℝ :=
  (ScalarMomErr a b η μ v0 x0 n, a * (ScalarMomX a b η μ v0 x0 n + ScalarMomV a b η μ v0 x0 n) - b)

lemma scalar_mom_step_fst (a b η μ : ℝ) (p : ℝ × ℝ) :
    (ScalarMomStep a b η μ p).1 = μ * p.1 + 2 * η * a * (a * p.2 - b) := rfl

lemma scalar_mom_step_snd (a b η μ : ℝ) (p : ℝ × ℝ) :
    (ScalarMomStep a b η μ p).2 = p.2 - (μ * p.1 + 2 * η * a * (a * p.2 - b)) := rfl

/-! ## 引理：v_{n+1} = x_n - x_{n+1}（速度是位置差分） -/

lemma scalar_mom_v_prev (a b η μ : ℝ) (v0 x0 : ℝ) :
    ∀ n : ℕ, ScalarMomV a b η μ v0 x0 (n + 1) = ScalarMomX a b η μ v0 x0 n - ScalarMomX a b η μ v0 x0 (n + 1) := by
  intro n
  set X : ℝ × ℝ := ScalarMomIterate a b η μ n (v0, x0) with hX
  have hstep' : ScalarMomIterate a b η μ (n + 1) (v0, x0) = ScalarMomStep a b η μ X := by
    rw [hX]
    rfl
  unfold ScalarMomV ScalarMomX
  rw [hstep', scalar_mom_step_fst, scalar_mom_step_snd]
  ring

/-! ## 引理：误差对第二分量（errPair (n+1) = (e_{n+1}, e_n)） -/

lemma scalar_mom_err_pair_snd (a b η μ : ℝ) (v0 x0 : ℝ) :
    ∀ n : ℕ, (ScalarMomErrPair a b η μ v0 x0 (n + 1)).2 = ScalarMomErr a b η μ v0 x0 n := by
  intro n
  set X : ℝ × ℝ := ScalarMomIterate a b η μ n (v0, x0) with hX
  have hstep' : ScalarMomIterate a b η μ (n + 1) (v0, x0) = ScalarMomStep a b η μ X := by
    rw [hX]
    rfl
  unfold ScalarMomErrPair ScalarMomErr ScalarMomX ScalarMomV
  rw [hstep', scalar_mom_step_fst, scalar_mom_step_snd]
  ring

/-! ## 引理：误差对的二阶递推（配对形式）
(e_{n+1}, e_n) = ((α+μ)·e_n - μ·e_{n-1}, e_n)，α = 1 - 2ηa²。-/

lemma scalar_mom_err_pair_recurrence (a b η μ : ℝ) (v0 x0 : ℝ) :
    ∀ n : ℕ, ScalarMomErrPair a b η μ v0 x0 (n + 1) =
      ((1 - 2 * η * a ^ 2 + μ) * (ScalarMomErrPair a b η μ v0 x0 n).1
        - μ * (ScalarMomErrPair a b η μ v0 x0 n).2, (ScalarMomErrPair a b η μ v0 x0 n).1) := by
  intro n
  set X : ℝ × ℝ := ScalarMomIterate a b η μ n (v0, x0) with hX
  have hstep' : ScalarMomIterate a b η μ (n + 1) (v0, x0) = ScalarMomStep a b η μ X := by
    rw [hX]
    rfl
  unfold ScalarMomErrPair ScalarMomErr ScalarMomX ScalarMomV
  rw [hstep', scalar_mom_step_fst, scalar_mom_step_snd]
  ext <;> ring

/-! ## 定理六：标量动量误差递推（核心恒等式的标量形式）
e_{n+2} = (1 - 2ηa²)·e_{n+1} + μ·(e_{n+1} - e_n)（全部 n ≥ 0）。-/

lemma momentum_error_recurrence (a b η μ : ℝ) (v0 x0 : ℝ) :
    ∀ n : ℕ,
      ScalarMomErr a b η μ v0 x0 (n + 2) =
        (1 - 2 * η * a ^ 2) * ScalarMomErr a b η μ v0 x0 (n + 1)
          + μ * (ScalarMomErr a b η μ v0 x0 (n + 1) - ScalarMomErr a b η μ v0 x0 n) := by
  intro n
  have hpr := scalar_mom_err_pair_recurrence a b η μ v0 x0 (n + 1)
  have h1 : (ScalarMomErrPair a b η μ v0 x0 (n + 2)).1 =
      (1 - 2 * η * a ^ 2 + μ) * (ScalarMomErrPair a b η μ v0 x0 (n + 1)).1
        - μ * (ScalarMomErrPair a b η μ v0 x0 (n + 1)).2 := by
    simpa using congrArg Prod.fst hpr
  have he2 : (ScalarMomErrPair a b η μ v0 x0 (n + 1)).2 = ScalarMomErr a b η μ v0 x0 n :=
    scalar_mom_err_pair_snd a b η μ v0 x0 n
  calc
    ScalarMomErr a b η μ v0 x0 (n + 2)
        = (ScalarMomErrPair a b η μ v0 x0 (n + 2)).1 := rfl
    _ = (1 - 2 * η * a ^ 2 + μ) * (ScalarMomErrPair a b η μ v0 x0 (n + 1)).1
          - μ * (ScalarMomErrPair a b η μ v0 x0 (n + 1)).2 := h1
    _ = (1 - 2 * η * a ^ 2 + μ) * ScalarMomErr a b η μ v0 x0 (n + 1)
          - μ * ScalarMomErr a b η μ v0 x0 n := by
          rw [he2]
          rfl
    _ = (1 - 2 * η * a ^ 2) * ScalarMomErr a b η μ v0 x0 (n + 1)
          + μ * (ScalarMomErr a b η μ v0 x0 (n + 1) - ScalarMomErr a b η μ v0 x0 n) := by ring

/-! ## 定理七：标量二阶递推的收缩收敛（加权范数，独立于动量序列）
任意序列 p : ℕ → ℝ×ℝ 满足 p(n+1) = ((α+μ)·p(n).1 - μ·p(n).2, p(n).1)，
0 ≤ μ 且 |α+μ| + μ < 1 ⟹ |p(n).1| → 0（ε-终止）。
加权范数 W_t = |p(t).1| + γ·|p(t).2|，γ = (μ + 1 - |α+μ|)/2，
系数 c = (|α+μ| + μ + 1)/2 < 1；连接 contraction_converges。-/

theorem scalar_second_order_converges {p : ℕ → ℝ × ℝ} (α μ : ℝ)
    (hstep : ∀ n : ℕ, p (n + 1) = ((α + μ) * (p n).1 - μ * (p n).2, (p n).1))
    (hμ0 : 0 ≤ μ) (hs : |α + μ| + μ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, |(p n).1| < ε := by
  let γ : ℝ := (μ + 1 - |α + μ|) / 2
  let c : ℝ := |α + μ| + γ
  let W : ℕ → ℝ := fun n => |(p n).1| + γ * |(p n).2|
  have hs0 : 0 ≤ |α + μ| := abs_nonneg _
  have hslt : |α + μ| < 1 - μ := by nlinarith [hs]
  have h1m : 0 ≤ 1 - μ := by nlinarith [hs, hs0]
  have hs2 : |α + μ| ^ 2 ≤ (1 - μ) ^ 2 := by
    exact sq_le_sq' (by nlinarith [hs0, h1m]) (le_of_lt hslt)
  have hγ0 : 0 ≤ γ := by
    dsimp [γ]
    have hnum : 0 ≤ μ + 1 - |α + μ| := by nlinarith [hslt, hμ0]
    nlinarith
  have hc0 : 0 ≤ c := by
    dsimp [c]
    nlinarith [hs0, hγ0]
  have hc1 : c < 1 := by
    dsimp [c, γ]
    nlinarith [hs]
  have hμcγ : μ ≤ c * γ := by
    have hdiff : 0 ≤ c * γ - μ := by
      dsimp [c, γ]
      have hcalc : (|α + μ| + (μ + 1 - |α + μ|) / 2) * ((μ + 1 - |α + μ|) / 2) - μ =
          ((1 - μ) ^ 2 - |α + μ| ^ 2) / 4 := by ring
      rw [hcalc]
      nlinarith [hs2]
    nlinarith
  have hWstep : ∀ n : ℕ, W (n + 1) ≤ c * W n := by
    intro n
    dsimp [W]
    rw [hstep n]
    have htri : |(α + μ) * (p n).1 - μ * (p n).2| ≤ |α + μ| * |(p n).1| + μ * |(p n).2| := by
      calc
        |(α + μ) * (p n).1 - μ * (p n).2|
            = |(α + μ) * (p n).1 + -(μ * (p n).2)| := by rw [sub_eq_add_neg]
        _ ≤ |(α + μ) * (p n).1| + |-(μ * (p n).2)| := abs_add _ _
        _ = |(α + μ) * (p n).1| + |μ * (p n).2| := by rw [abs_neg]
        _ = |α + μ| * |(p n).1| + |μ| * |(p n).2| := by rw [abs_mul, abs_mul]
        _ = |α + μ| * |(p n).1| + μ * |(p n).2| := by rw [abs_of_nonneg hμ0]
    calc
      |(α + μ) * (p n).1 - μ * (p n).2| + γ * |(p n).1|
          ≤ (|α + μ| * |(p n).1| + μ * |(p n).2|) + γ * |(p n).1| := add_le_add_right htri _
      _ = (|α + μ| + γ) * |(p n).1| + μ * |(p n).2| := by ring
      _ ≤ (|α + μ| + γ) * |(p n).1| + c * γ * |(p n).2| := by
            exact add_le_add_left (mul_le_mul_of_nonneg_right hμcγ (abs_nonneg (p n).2)) _
      _ = c * (|(p n).1| + γ * |(p n).2|) := by
            dsimp [c]
            ring
  have hWnonneg : ∀ n : ℕ, 0 ≤ W n := by
    intro n
    dsimp [W]
    exact add_nonneg (abs_nonneg _) (mul_nonneg hγ0 (abs_nonneg _))
  have hconv := contraction_converges c hc0 hc1 hWstep hWnonneg
  intro ε hε
  rcases hconv ε hε with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hle : |(p n).1| ≤ W n := by
    dsimp [W]
    exact le_add_of_nonneg_right (mul_nonneg hγ0 (abs_nonneg (p n).2))
  exact lt_of_le_of_lt hle hn

/-! ## 定理八：标量动量收敛（ε-终止）
0 ≤ μ 且 |1 - 2ηa² + μ| + μ < 1 ⟹ ∀ ε > 0，∃ n，|a·x_n - b| < ε。-/

theorem scalar_momentum_converges (a b η μ : ℝ) (v0 x0 : ℝ)
    (hμ0 : 0 ≤ μ) (hs : |1 - 2 * η * a ^ 2 + μ| + μ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, |ScalarMomErr a b η μ v0 x0 n| < ε := by
  have hconv := scalar_second_order_converges (α := 1 - 2 * η * a ^ 2) (μ := μ)
    (p := ScalarMomErrPair a b η μ v0 x0)
    (scalar_mom_err_pair_recurrence a b η μ v0 x0) hμ0 hs
  intro ε hε
  rcases hconv ε hε with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [ScalarMomErrPair] using hn

/-! ## 定理九：标量动量收敛（平方误差形式，对应 GDError 的 ‖·‖²）
同样条件下 ∀ ε > 0，∃ n，|a·x_n - b|² < ε。-/

theorem scalar_momentum_converges_sq (a b η μ : ℝ) (v0 x0 : ℝ)
    (hμ0 : 0 ≤ μ) (hs : |1 - 2 * η * a ^ 2 + μ| + μ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, |ScalarMomErr a b η μ v0 x0 n| ^ 2 < ε := by
  intro ε hε
  let m : ℝ := min ε 1
  have hm0 : 0 < m := by
    dsimp [m]
    exact lt_min hε zero_lt_one
  rcases (scalar_momentum_converges a b η μ v0 x0 hμ0 hs m hm0) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hm1 : m ≤ 1 := by
    dsimp [m]
    exact min_le_right ε 1
  have hmε : m ≤ ε := by
    dsimp [m]
    exact min_le_left ε 1
  have hsq : |ScalarMomErr a b η μ v0 x0 n| ^ 2 < m ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (abs_nonneg _) hn
  calc
    |ScalarMomErr a b η μ v0 x0 n| ^ 2 < m ^ 2 := hsq
    _ ≤ ε := by
      -- m² = m·m ≤ ε·1 = ε（m ≤ ε，m ≤ 1，0 ≤ m，0 ≤ ε）
      have hm0' : 0 ≤ m := le_of_lt hm0
      have hε0 : 0 ≤ ε := le_of_lt hε
      have hmul : m * m ≤ ε * 1 := mul_le_mul_of_nonneg' hmε hm1 hm0' hε0
      nlinarith

/-! ## 注：闭环语义
  无动量（μ=0）：MomentumUpdate 精确回收 GDUpdate（momentum_gd_recovery）；
  标量谱条件 |1-2ηa²| < 1 是 μ=0 时动量条件的退化；
  误差恒等式（向量版）→ 单步收缩 → 状态加权范数收缩（向量/标量）
  → RealConvergence.contraction_converges ⟹ ε-终止。
  动量（μ>0）的代价：收缩条件收紧为 |1-2ηa²+μ| + μ < 1（标量）/
  c₀ + 2μ < 1（向量）—— 充分条件，诚实标注。-/

end Lattice
