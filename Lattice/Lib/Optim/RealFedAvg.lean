import Lattice.Lib.Convex.RealSubgradientDescent
import Lattice.Lib.Optim.RealStrongConvex
import Mathlib

/-!
# LATTICE: 联邦平均（FedAvg）的收敛与异质性误差界

联邦学习：m 个客户端各自在本地做几步更新，服务器对本地参数做**加权平均**：

    θ_i ← localUpdate η θ g_i = θ − η·g_i
    θ   ← fedAvgUpdate w θ_loc = Σ_i w_i·θ_i     （Σ_i w_i = 1）

## 主结果

1. **无通信 ⟹ FedAvg = 本地 GD/SGD**（`fedAvg_as_sgd`）：所有客户端同 θ、同局部梯度、
   权重和为 1 时，加权平均退化为单个 GD 步；并给出迭代形式
   `fedAvgIterate = SubgradientIterate`（`fedAvgIterate_eq_gd`）。
2. **同质数据 ⟹ 收缩**（`fedAvg_contraction`）：在 `StrongConvex μ f g` + `Smooth L f g`
   （步长 1/L）下，FedAvg 一轮把函数值差距收缩 `(1 − μ/L)` 倍，因而线性收敛
   （`fedAvg_linear_rate`）与 ε-终止（`fedAvg_converges`）—— 直接回收
   `RealStrongConvex` / `RealGradDescent` 的结论。
3. **异质性误差界**（`heterogeneity_error`）：凸组合界

       |Σ_i w_i·g_i − ḡ| ≤ Σ_i w_i·|g_i − ḡ|

   即「平均梯度偏离全局梯度」不超过客户端梯度的加权离散度。
4. **带异质性的单步界**（`fedAvg_rate`）：若实际用的方向 `d_t` 与真实梯度 `g(x_t)` 相差
   `|d_t − g(x_t)| ≤ ζ`（有界异质性），则

       ‖x_{t+1} − x*‖ ≤ ‖P_t‖ + ηζ,    P_t = x_t − η·g(x_t) − x*
       ‖P_t‖² ≤ ‖x_t − x*‖² − 2η(f x_t − f x*) + η²G²
       ‖x_{t+1} − x*‖² ≤ ‖x_t − x*‖² − 2η(f x_t − f x*) + 2ηζ‖x_t − x*‖ + η²(G+ζ)²

   即异质性以 `2ηζ·‖x_t − x*‖` 的加性项进入单步界（`ηζD` 量级），并给出累积漂移界
   （`fedAvg_drift_linear`）：`‖x_T − x*‖ ≤ ‖x_0 − x*‖ + T·η·(G+ζ)` —— 异质性使
   距离不再收缩而是线性漂移，这正是 FedAvg 需要「异质性有界 + 步长衰减」的原因。

## 诚实边界

- 定理 2/3 是**同质**（所有客户端共享同一目标 f 与梯度选择 g）情形；真实 FedAvg 的
  异质数据下不存在全局步的收缩，本文件的诚实处理是把异质性显式量化为上述加性项，
  而不是声称异质情形也收缩。
- 定理 4 的 `ζ`（有界异质性）是显式假设；`fedAvg_drift_linear` 只给漂移上界，
  不给 O(1/√T) 下降率（那需要异质性随时间消失或步长衰减，属于后续工作）。
- 定标量 ℝ 一维，权重 `w : Fin m → ℝ` 非负、和为 1。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、定义：本地更新与联邦平均 -/

/-- 客户端本地更新：`θ' = θ − η·g`。 -/
def localUpdate (η θ g : ℝ) : ℝ := θ - η * g

/-- 联邦平均：`Σ_i w_i·θ_i`（权重和应为 1）。 -/
def fedAvgUpdate {m : ℕ} (w : Fin m → ℝ) (θloc : Fin m → ℝ) : ℝ :=
  ∑ i, w i * θloc i

/-- FedAvg 迭代轨迹（每轮所有客户端从当前 θ 出发做本地更新再平均）。 -/
def fedAvgIterate {m : ℕ} (w : Fin m → ℝ) (η : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, θ => θ
  | (n + 1), θ =>
      fedAvgUpdate w (fun _ => localUpdate η (fedAvgIterate w η g n θ) (g (fedAvgIterate w η g n θ)))

lemma localUpdate_eq_subgradient_step (η θ g : ℝ) :
    localUpdate η θ g = subgradient_descent_step η θ g := rfl

/-! ## 二、无通信 ⟹ FedAvg 退化为本地 GD/SGD -/

/-- **`fedAvg_as_sgd`**：所有客户端同 θ、同局部梯度 g，权重和为 1 ⟹
    FedAvg 一步精确等于一个 GD 步 `θ − η·g`。 -/
theorem fedAvg_as_sgd {m : ℕ} (w : Fin m → ℝ) (η θ g : ℝ)
    (hw : (∑ i, w i) = 1) :
    fedAvgUpdate w (fun _ => localUpdate η θ g) = localUpdate η θ g := by
  unfold fedAvgUpdate
  rw [← Finset.sum_mul, hw, one_mul]

/-- 单客户端特例：m = 1、w ≡ 1 时 FedAvg = 本地更新。 -/
theorem fedAvg_single_client (η θ g : ℝ) :
    fedAvgUpdate (fun _ : Fin 1 => (1 : ℝ)) (fun _ => localUpdate η θ g) =
      localUpdate η θ g := by
  apply fedAvg_as_sgd
  simp

/-- **迭代形式的退化**：权重和为 1 时 `fedAvgIterate = SubgradientIterate`
    （FedAvg 的每一轮都是同一个 GD 步）。 -/
theorem fedAvgIterate_eq_gd {m : ℕ} (w : Fin m → ℝ) (η : ℝ) (g : ℝ → ℝ)
    (hw : (∑ i, w i) = 1) :
    ∀ n : ℕ, ∀ θ : ℝ, fedAvgIterate w η g n θ = SubgradientIterate g η n θ := by
  intro n
  induction n with
  | zero => intro θ; rfl
  | succ n ih =>
      intro θ
      rw [fedAvgIterate, fedAvg_as_sgd w η _ _ hw, ih θ]
      rfl

/-! ## 三、异质性误差界（凸组合） -/

/-- **异质性误差界**：非负权重、和为 1 时，
    `|Σ_i w_i·g_i − ḡ| ≤ Σ_i w_i·|g_i − ḡ|`。 -/
theorem heterogeneity_error {m : ℕ} (w : Fin m → ℝ) (g : Fin m → ℝ) (gbar : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hws : (∑ i, w i) = 1) :
    |fedAvgUpdate w g - gbar| ≤ ∑ i, w i * |g i - gbar| := by
  have hdecomp : fedAvgUpdate w g - gbar = ∑ i, w i * (g i - gbar) := by
    unfold fedAvgUpdate
    have h1 : gbar = (∑ i, w i) * gbar := by rw [hws, one_mul]
    conv_lhs => rw [h1]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hdecomp]
  calc
    |∑ i, w i * (g i - gbar)| ≤ ∑ i, |w i * (g i - gbar)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |g i - gbar| :=
      Finset.sum_congr rfl (fun i _ => by rw [abs_mul, abs_of_nonneg (hw0 i)])

/-! ## 四、同质数据 ⟹ 收缩、线性率、ε-终止 -/

/-- **`fedAvg_contraction`**：同质数据（所有客户端梯度都是 `g θ`）下，FedAvg 一轮
    把函数值差距收缩 `(1 − μ/L)` 倍（步长 η = 1/L，强凸 + 光滑）。 -/
theorem fedAvg_contraction {m : ℕ} (w : Fin m → ℝ) {f g : ℝ → ℝ} {μ L : ℝ}
    (hw : (∑ i, w i) = 1) (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L)
    (hSC : StrongConvex μ f g) (hSM : Smooth L f g) {xstar : ℝ} (hg0 : g xstar = 0)
    (θ : ℝ) :
    f (fedAvgUpdate w (fun _ => localUpdate (1 / L) θ (g θ))) - f xstar ≤
      (1 - μ / L) * (f θ - f xstar) := by
  rw [fedAvg_as_sgd w (1 / L) θ (g θ) hw]
  exact strong_convex_contraction hμ hL hμL hSC hSM hg0 θ

/-- **线性收敛率**：同质 FedAvg 的差距按 `(1 − μ/L)ⁿ` 几何衰减。 -/
theorem fedAvg_linear_rate {m : ℕ} (w : Fin m → ℝ) {f g : ℝ → ℝ} {μ L : ℝ}
    (hw : (∑ i, w i) = 1) (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L)
    (hSC : StrongConvex μ f g) (hSM : Smooth L f g) {xstar : ℝ} (hg0 : g xstar = 0)
    (θ0 : ℝ) :
    ∀ n : ℕ, f (fedAvgIterate w (1 / L) g n θ0) - f xstar ≤
      (1 - μ / L) ^ n * (f θ0 - f xstar) := by
  intro n
  rw [fedAvgIterate_eq_gd w (1 / L) g hw n θ0]
  exact gd_linear_rate hμ hL hμL hSC hSM hg0 θ0 n

/-- **ε-终止**：同质 FedAvg 收敛到最优值（连接 `RealConvergence` 语义）。 -/
theorem fedAvg_converges {m : ℕ} (w : Fin m → ℝ) {f g : ℝ → ℝ} {μ L : ℝ}
    (hw : (∑ i, w i) = 1) (hμ : 0 < μ) (hL : 0 < L) (hμL : μ ≤ L)
    (hSC : StrongConvex μ f g) (hSM : Smooth L f g) {xstar : ℝ} (hg0 : g xstar = 0)
    (θ0 : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, f (fedAvgIterate w (1 / L) g n θ0) - f xstar < ε := by
  intro ε hε
  rcases gd_converges hμ hL hμL hSC hSM hg0 θ0 ε hε with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rwa [fedAvgIterate_eq_gd w (1 / L) g hw n θ0]

/-! ## 五、异质情形：加性异质性项进入单步界

模型：第 t 步实际使用的方向 `d_t` 与真实梯度 `g(x_t)` 的偏离被 `ζ` 界住
（`|d_t − g(x_t)| ≤ ζ`），更新 `x_{t+1} = x_t − η·d_t`。 -/

/-- 带噪方向的范数界：`|d_t| ≤ G + ζ`。 -/
theorem direction_bound {d g : ℕ → ℝ} (G ζ : ℝ)
    (hd : ∀ t : ℕ, |d t - g t| ≤ ζ) (hG : ∀ t : ℕ, |g t| ≤ G) (t : ℕ) :
    |d t| ≤ G + ζ := by
  have h1 : |d t| ≤ |d t - g t| + |g t| := by
    have h := abs_add (d t - g t) (g t)
    simpa using h
  linarith [hd t, hG t, h1]

/-- 分离噪声：`‖x_{t+1} − x*‖ ≤ ‖x_t − η·g(x_t) − x*‖ + η·ζ`。 -/
lemma norm_step_split {g : ℝ → ℝ} {x : ℕ → ℝ} (d : ℕ → ℝ) (xstar η ζ : ℝ)
    (hη : 0 ≤ η) (hd : ∀ t : ℕ, |d t - g (x t)| ≤ ζ)
    (hstep : ∀ t : ℕ, x (t + 1) = x t - η * d t) (t : ℕ) :
    ‖x (t + 1) - xstar‖ ≤ ‖x t - xstar - η * g (x t)‖ + η * ζ := by
  have hAeq : x (t + 1) - xstar
      = (x t - xstar - η * g (x t)) - η * (d t - g (x t)) := by
    rw [hstep t]
    ring
  rw [hAeq]
  calc
    ‖(x t - xstar - η * g (x t)) - η * (d t - g (x t))‖
        ≤ ‖x t - xstar - η * g (x t)‖ + ‖η * (d t - g (x t))‖ := norm_sub_le _ _
    _ = ‖x t - xstar - η * g (x t)‖ + η * ‖d t - g (x t)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hη]
    _ ≤ ‖x t - xstar - η * g (x t)‖ + η * ζ := by
          have hE : ‖d t - g (x t)‖ ≤ ζ := by
            rw [Real.norm_eq_abs]
            exact hd t
          exact add_le_add_left (mul_le_mul_of_nonneg_left hE hη) _

/-- 分离梯度：`‖x_t − η·g(x_t) − x*‖ ≤ ‖x_t − x*‖ + η·G`。 -/
lemma norm_grad_split {g : ℝ → ℝ} {x : ℕ → ℝ} (xstar η G : ℝ) (hη : 0 ≤ η)
    (hG : ∀ t : ℕ, |g (x t)| ≤ G) (t : ℕ) :
    ‖x t - xstar - η * g (x t)‖ ≤ ‖x t - xstar‖ + η * G := by
  have hB : ‖g (x t)‖ ≤ G := by
    rw [Real.norm_eq_abs]
    exact hG t
  calc
    ‖x t - xstar - η * g (x t)‖ ≤ ‖x t - xstar‖ + ‖η * g (x t)‖ := norm_sub_le _ _
    _ = ‖x t - xstar‖ + η * ‖g (x t)‖ := by rw [norm_mul, Real.norm_of_nonneg hη]
    _ ≤ ‖x t - xstar‖ + η * G := add_le_add_left (mul_le_mul_of_nonneg_left hB hη) _

/-- **`fedAvg_rate`（异质性单步界）**：`hsub` 给真实次梯度，`d` 是实际用的方向
    （偏差 ≤ ζ），则单步平方距离满足

    `‖x_{t+1} − x*‖² ≤ ‖x_t − x*‖² − 2η(f x_t − f x*) + 2ηζ‖x_t − x*‖ + η²(G+ζ)²`。 -/
theorem fedAvg_rate {f g : ℝ → ℝ} {x : ℕ → ℝ} (d : ℕ → ℝ) (xstar η G ζ : ℝ)
    (hsub : ∀ t : ℕ, Subgradient f (x t) (g (x t)))
    (hη : 0 ≤ η) (_hG0 : 0 ≤ G) (hζ0 : 0 ≤ ζ)
    (hG : ∀ t : ℕ, |g (x t)| ≤ G)
    (hd : ∀ t : ℕ, |d t - g (x t)| ≤ ζ)
    (hstep : ∀ t : ℕ, x (t + 1) = x t - η * d t) (t : ℕ) :
    ‖x (t + 1) - xstar‖ ^ 2 ≤ ‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar)
      + 2 * η * ζ * ‖x t - xstar‖ + η ^ 2 * (G + ζ) ^ 2 := by
  have hnorm : ‖x (t + 1) - xstar‖ ≤ ‖x t - xstar - η * g (x t)‖ + η * ζ :=
    norm_step_split d xstar η ζ hη hd hstep t
  have hPsq : ‖x t - xstar - η * g (x t)‖ ^ 2 ≤
      ‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar) + η ^ 2 * G ^ 2 := by
    have h := subgradient_descent_norm_decrease (hsub t) xstar η hη
    simp only [subgradient_descent_step] at h
    have hB : ‖g (x t)‖ ≤ G := by
      rw [Real.norm_eq_abs]
      exact hG t
    have hBsq : ‖g (x t)‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
    have h2 : η ^ 2 * ‖g (x t)‖ ^ 2 ≤ η ^ 2 * G ^ 2 :=
      mul_le_mul_of_nonneg_left hBsq (sq_nonneg η)
    have hsame : ‖x t - η * g (x t) - xstar‖ ^ 2 = ‖x t - xstar - η * g (x t)‖ ^ 2 := by
      ring_nf
    rw [hsame] at h
    linarith [h, h2]
  have hPbound : ‖x t - xstar - η * g (x t)‖ ≤ ‖x t - xstar‖ + η * G :=
    norm_grad_split xstar η G hη hG t
  have hsq : ‖x (t + 1) - xstar‖ ^ 2 ≤
      (‖x t - xstar - η * g (x t)‖ + η * ζ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcross : 2 * (η * ζ) * ‖x t - xstar - η * g (x t)‖ ≤
      2 * (η * ζ) * (‖x t - xstar‖ + η * G) := by
    apply mul_le_mul_of_nonneg_left hPbound
    nlinarith [hη, hζ0]
  have hexp : (‖x t - xstar - η * g (x t)‖ + η * ζ) ^ 2
      = ‖x t - xstar - η * g (x t)‖ ^ 2 + 2 * (η * ζ) * ‖x t - xstar - η * g (x t)‖
        + (η * ζ) ^ 2 := by ring
  have hbridge : (‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar) + η ^ 2 * G ^ 2)
        + 2 * (η * ζ) * (‖x t - xstar‖ + η * G) + (η * ζ) ^ 2
      = ‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar)
        + 2 * η * ζ * ‖x t - xstar‖ + η ^ 2 * (G + ζ) ^ 2 := by ring
  calc
    ‖x (t + 1) - xstar‖ ^ 2
        ≤ (‖x t - xstar - η * g (x t)‖ + η * ζ) ^ 2 := hsq
    _ = ‖x t - xstar - η * g (x t)‖ ^ 2 + 2 * (η * ζ) * ‖x t - xstar - η * g (x t)‖
          + (η * ζ) ^ 2 := hexp
    _ ≤ (‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar) + η ^ 2 * G ^ 2)
          + 2 * (η * ζ) * (‖x t - xstar‖ + η * G) + (η * ζ) ^ 2 :=
          add_le_add (add_le_add hPsq hcross) le_rfl
    _ = ‖x t - xstar‖ ^ 2 - 2 * η * (f (x t) - f xstar)
          + 2 * η * ζ * ‖x t - xstar‖ + η ^ 2 * (G + ζ) ^ 2 := hbridge

/-- 单步范数漂移（异质性代价）：`‖x_{t+1} − x*‖ ≤ ‖x_t − x*‖ + η(G+ζ)`。 -/
theorem fedAvg_drift_step {g : ℝ → ℝ} {x : ℕ → ℝ} (d : ℕ → ℝ) (xstar η G ζ : ℝ)
    (hη : 0 ≤ η) (_hG0 : 0 ≤ G) (_hζ0 : 0 ≤ ζ)
    (hG : ∀ t : ℕ, |g (x t)| ≤ G)
    (hd : ∀ t : ℕ, |d t - g (x t)| ≤ ζ)
    (hstep : ∀ t : ℕ, x (t + 1) = x t - η * d t) (t : ℕ) :
    ‖x (t + 1) - xstar‖ ≤ ‖x t - xstar‖ + η * (G + ζ) := by
  have h1 := norm_step_split d xstar η ζ hη hd hstep t
  have h2 := norm_grad_split xstar η G hη hG t
  linarith

/-- **累积漂移界**：单步漂移 `‖x_{t+1} − x*‖ ≤ ‖x_t − x*‖ + η(G+ζ)` ⟹
    `‖x_T − x*‖ ≤ ‖x_0 − x*‖ + T·η·(G+ζ)` —— 异质性使距离线性漂移。 -/
theorem fedAvg_drift_linear {x : ℕ → ℝ} (xstar η G ζ : ℝ)
    (hinc : ∀ t : ℕ, ‖x (t + 1) - xstar‖ ≤ ‖x t - xstar‖ + η * (G + ζ)) :
    ∀ T : ℕ, ‖x T - xstar‖ ≤ ‖x 0 - xstar‖ + (T : ℝ) * η * (G + ζ) := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
      calc
        ‖x (T + 1) - xstar‖ ≤ ‖x T - xstar‖ + η * (G + ζ) := hinc T
        _ ≤ (‖x 0 - xstar‖ + (T : ℝ) * η * (G + ζ)) + η * (G + ζ) := by linarith
        _ = ‖x 0 - xstar‖ + ((T : ℝ) + 1) * η * (G + ζ) := by ring
        _ = ‖x 0 - xstar‖ + ((T + 1 : ℕ) : ℝ) * η * (G + ζ) := by
              rw [Nat.cast_add, Nat.cast_one]

/-! ## 注：闭环语义
  本地更新（localUpdate）→ 联邦平均（fedAvgUpdate）→
  无通信退化为 GD（fedAvg_as_sgd / fedAvgIterate_eq_gd）→
  同质收缩/线性率/ε-终止（fedAvg_contraction / fedAvg_linear_rate / fedAvg_converges）→
  异质性误差（heterogeneity_error，凸组合界）→
  异质单步界与线性漂移（fedAvg_rate / fedAvg_drift_linear）。
  诚实假设：有界异质性 ζ；同质收缩回收 RealStrongConvex/RealGradDescent。 -/

end Lattice
