import Mathlib
import Lattice.Lib.Architectures.RealLoop
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 循环/递归架构的端到端界 —— RNN 隐状态收缩与输入遗忘

控制流循环（RealLoop 不变量 / RealConvergence ε-终止）在**循环神经网络**
上的架构实例化：RNN 层把同一个转移映射反复作用（权重在时间轴上共享），
是「循环 = 迭代」的模型语义。

模型（RNN 单步）：
  `RNNStep φ W U h x = φ (W h + U x)`
其中 φ 是 Lipschitz 激活（ReLU/tanh/sigmoid 的有界 Lipschitz 抽象），
W 是循环权重（隐状态到隐状态），U 是输入权重（输入到隐状态）。
轨迹 `rnnState φ W U h0 xs`：初始隐状态 h0，输入序列 xs。

定理链（模型无关，任意范数空间 X）：

  1. `rnn_step_lipschitz`：固定输入下单步是 `Lφ·‖W‖`-Lipschitz
     （`le_opNorm` + 激活 Lipschitz）；
  2. `rnn_hidden_contraction`（核心）：**隐状态对初值的遗忘**——
     同一输入序列下两条轨迹的初值差经 n 步被压缩为
     `‖hₙ − hₙ'‖ ≤ (Lφ·‖W‖)ⁿ·‖h₀ − h₀'‖`；ρ = Lφ·‖W‖ < 1 即指数遗忘；
  3. `rnn_input_error_bound`：**输入扰动经 n 步的放大界**——
     每步输入差 ≤ δ 时 `‖hₙ − hₙ'‖ ≤ ρⁿ‖h₀−h₀'‖ + (Σᵢ<ₙ ρⁱ)·(Lφ·Lu·δ)`
     （由通用几何递减引理 `geometric_error_decay` 给出）；
  4. `rnn_stability_bound`：上式的闭式——ρ < 1 时
     `‖hₙ − hₙ'‖ ≤ ((1−ρⁿ)/(1−ρ))·(Lφ·Lu·δ)`（几何级数 `geom_sum_eq`）；
  5. `rnn_forget_bound`：**远期输入影响指数衰减**——两条轨迹仅在第 k 步的
     输入不同（差 ≤ δ）而初值与其余输入相同，则 m 步之后
     `‖h_{k+1+m} − g_{k+1+m}‖ ≤ ρᵐ·(Lφ·Lu·δ)`（一次性输入误差只放大 ρᵐ 倍）；
  6. `loop_model_contraction`：隐状态映射 `h ↦ φ(W h + U x)` 是
     `ρ = Lφ·‖W‖`-Lipschitz；ρ < 1 时为严格收缩；
  7. `loop_converges_to_fixed_point`：对不动点 p，迭代误差 ≤ ρⁿ‖h₀−p‖
     （几何收敛率）；
  8. `loop_iterate_convergence`（接 RealConvergence）：ρ < 1 ⟹ 两条迭代
     轨迹最终 ε-接近（`contraction_converges` 的循环模型实例）。

  注：以上 1–8 条编号即各定理在本文件中的实际声明顺序，定理名亦可直接
  用于交叉引用；其中 `loop_fixed_point_unique`（ρ < 1 ⟹ 不动点至多一个，
  即 Banach 的「唯一」一半）在 `loop_model_contraction` 之后、
  `loop_converges_to_fixed_point` 之前声明，原头注曾把它编号为第 7 条、
  与后继条目编号错位，现按实际顺序重排。

诚实假设（均显式标注）：
  · `hφ : ∀a b, ‖φ a − φ b‖ ≤ Lφ·‖a−b‖`：激活是 Lφ-Lipschitz（ReLU=1、
    tanh=1、sigmoid=1/4 等有界导数的抽象）；
  · `hLφ : 0 ≤ Lφ`、`hLu : 0 ≤ Lu`：Lipschitz 常数取非负（不失一般性）；
  · `hU : ∀x, ‖U x‖ ≤ Lu·‖x‖`：输入权重范数界（等价 ‖U‖ ≤ Lu）；
  · `hδ : ∀k, ‖xs k − ys k‖ ≤ δ`：输入序列逐点差有界（全时间轴，比「前 n
    步有界」更强、陈述更简；放大界只用到前 n 步，故是对结论安全的加强）；
  · ρ = Lφ·‖W‖ 的收缩性（ρ < 1）只在需要遗忘/收敛的定理中显式假设；
    不含收缩假设的定理（定理 1/2/3）对任意 ρ 成立；
  · **不动点存在性未证明**：`loop_fixed_point_unique` 只证唯一性；存在性
    在完备空间上由 Banach 不动点定理给出（RealBanach 路线），本文件不假设
    也不使用完备性，避免为单纯循环模型引入拓扑完备假设。**该缺口已由同
    项目的下游文件闭合**：`RealLoopFixedPointExistence.loop_fixed_point_exists`
    / `loop_fixed_point_existsUnique` 在 `[CompleteSpace X]` 下给出存在性
    （及存在唯一性）的机器验证证明，并在该文件中自称闭合 `RealLoopModel`
    的「不动点存在性未证」；本文件自身仍不引入完备性。
  · 本节迭代收敛定理（`loop_converges_to_fixed_point` 与
    `loop_iterate_convergence`）使用 `RealLoop.iterate`（其空间类型固定在
    `Type` 层，与 RealConvergence 的循环骨架一致），故这两条在 `Type` 层
    陈述；其余定理对任意宇宙的范数空间成立。
全部证明无 sorry / axiom / admit。

模型无关：任意范数空间 X、任意 Lipschitz 激活、任意 n（时间步数）。
-/

noncomputable section

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## RNN 单步与轨迹 -/

/-- RNN 单步：`h' = φ (W h + U x)`。φ 为激活，W 为循环权重，U 为输入权重。 -/
def RNNStep (φ : X → X) (W U : X →L[ℝ] X) (h x : X) : X :=
  φ (W h + U x)

/-- 隐状态映射（固定输入 x）：`h ↦ φ (W h + U x)`（RealLoop.iterate 的步函数）。 -/
def loopStepMap (φ : X → X) (W U : X →L[ℝ] X) (x : X) : X → X :=
  fun h => RNNStep φ W U h x

/-- 轨迹：`rnnState φ W U h0 xs 0 = h0`，第 n+1 步用输入 `xs n`。 -/
def rnnState (φ : X → X) (W U : X →L[ℝ] X) (h0 : X) (xs : ℕ → X) : ℕ → X
  | 0 => h0
  | n + 1 => RNNStep φ W U (rnnState φ W U h0 xs n) (xs n)

/-! ## 定理零（引理）：单步 Lipschitz（固定输入）
`‖RNNStep φ W U h x − RNNStep φ W U g x‖ ≤ (Lφ·‖W‖)·‖h−g‖`。 -/

lemma rnn_step_lipschitz (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (h g x : X) :
    ‖RNNStep φ W U h x - RNNStep φ W U g x‖ ≤ (Lφ * ‖W‖) * ‖h - g‖ := by
  have hsub : (W h + U x) - (W g + U x) = W (h - g) := by
    rw [show (W h + U x) - (W g + U x) = W h - W g by abel, map_sub]
  calc
    ‖RNNStep φ W U h x - RNNStep φ W U g x‖
        = ‖φ (W h + U x) - φ (W g + U x)‖ := by rfl
    _ ≤ Lφ * ‖(W h + U x) - (W g + U x)‖ := hφ _ _
    _ = Lφ * ‖W (h - g)‖ := by rw [hsub]
    _ ≤ Lφ * (‖W‖ * ‖h - g‖) := mul_le_mul_of_nonneg_left (W.le_opNorm (h - g)) hLφ
    _ = (Lφ * ‖W‖) * ‖h - g‖ := by ring

/-! ## 定理零'（引理）：单步 Lipschitz（输入也可变）
不同输入 x、y 时单步差 ≤ ρ‖h−g‖ + (Lφ·Lu)‖x−y‖（三角不等式 + 输入范数界）。 -/

lemma rnn_step_input_lipschitz (φ : X → X) (W U : X →L[ℝ] X) (Lφ Lu : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (_hLu : 0 ≤ Lu)
    (hU : ∀ x, ‖U x‖ ≤ Lu * ‖x‖) (h g x y : X) :
    ‖RNNStep φ W U h x - RNNStep φ W U g y‖
      ≤ (Lφ * ‖W‖) * ‖h - g‖ + (Lφ * Lu) * ‖x - y‖ := by
  have hsub : (W h + U x) - (W g + U y) = W (h - g) + U (x - y) := by
    rw [map_sub, map_sub]
    abel
  have hUxy : ‖U (x - y)‖ ≤ Lu * ‖x - y‖ := hU (x - y)
  have hWxy : ‖W (h - g)‖ ≤ ‖W‖ * ‖h - g‖ := W.le_opNorm (h - g)
  calc
    ‖RNNStep φ W U h x - RNNStep φ W U g y‖
        = ‖φ (W h + U x) - φ (W g + U y)‖ := by rfl
    _ ≤ Lφ * ‖(W h + U x) - (W g + U y)‖ := hφ _ _
    _ = Lφ * ‖W (h - g) + U (x - y)‖ := by rw [hsub]
    _ ≤ Lφ * (‖W (h - g)‖ + ‖U (x - y)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hLφ
    _ ≤ Lφ * (‖W‖ * ‖h - g‖ + Lu * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hWxy hUxy) hLφ
    _ = (Lφ * ‖W‖) * ‖h - g‖ + (Lφ * Lu) * ‖x - y‖ := by ring

/-! ## 引理：几何和递推 `Σ_{i<n+1} ρⁱ = 1 + ρ·Σ_{i<n} ρⁱ`（`sum_range_succ'`）。 -/

lemma geom_sum_range_succ (ρ : ℝ) (n : ℕ) :
    (∑ i in Finset.range (n + 1), ρ ^ i) = 1 + ρ * (∑ i in Finset.range n, ρ ^ i) := by
  have hsum : (∑ i in Finset.range n, ρ ^ (i + 1)) = ∑ i in Finset.range n, ρ * ρ ^ i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [Finset.sum_range_succ', Finset.mul_sum, hsum]
  ring

/-! ## 几何递减引理（通用骨架）：`e(n+1) ≤ ρ·e(n) + c·δ` ⟹ 显式上界
误差递推的解 `e n ≤ ρⁿ·E + (Σᵢ<ₙ ρⁱ)·(c·δ)`；这是「一步收缩 + 每步注入」
的非齐次版本，供输入扰动放大界（定理三）使用。 -/

lemma geometric_error_decay (ρ c E δ : ℝ) (hρ0 : 0 ≤ ρ) (e : ℕ → ℝ)
    (he0 : e 0 ≤ E) (hstep : ∀ n, e (n + 1) ≤ ρ * e n + c * δ) :
    ∀ n, e n ≤ ρ ^ n * E + (∑ i in Finset.range n, ρ ^ i) * (c * δ) := by
  intro n
  induction n with
  | zero => simpa using he0
  | succ n ih =>
      calc
        e (n + 1) ≤ ρ * e n + c * δ := hstep n
        _ ≤ ρ * (ρ ^ n * E + (∑ i in Finset.range n, ρ ^ i) * (c * δ)) + c * δ :=
              add_le_add (mul_le_mul_of_nonneg_left ih hρ0) le_rfl
        _ = ρ ^ (n + 1) * E
              + (∑ i in Finset.range (n + 1), ρ ^ i) * (c * δ) := by
              rw [geom_sum_range_succ ρ n, pow_succ]
              ring

/-! ## 定理一：隐状态对初值的遗忘（核心）
同一输入序列下，两条轨迹的初值差经 n 步压缩为 ρⁿ：ρ = Lφ·‖W‖。
ρ < 1 时初值信息指数遗忘。 -/

theorem rnn_hidden_contraction (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (h0 g0 : X) (xs : ℕ → X) (n : ℕ) :
    ‖rnnState φ W U h0 xs n - rnnState φ W U g0 xs n‖
      ≤ (Lφ * ‖W‖) ^ n * ‖h0 - g0‖ := by
  have hρ0 : 0 ≤ Lφ * ‖W‖ := mul_nonneg hLφ (norm_nonneg W)
  induction n with
  | zero => simp [rnnState]
  | succ n ih =>
      have hstep := rnn_step_lipschitz φ W U Lφ hφ hLφ
        (rnnState φ W U h0 xs n) (rnnState φ W U g0 xs n) (xs n)
      have hunfold : rnnState φ W U h0 xs (n + 1)
          = RNNStep φ W U (rnnState φ W U h0 xs n) (xs n) := by simp [rnnState]
      have hunfold' : rnnState φ W U g0 xs (n + 1)
          = RNNStep φ W U (rnnState φ W U g0 xs n) (xs n) := by simp [rnnState]
      calc
        ‖rnnState φ W U h0 xs (n + 1) - rnnState φ W U g0 xs (n + 1)‖
            = ‖RNNStep φ W U (rnnState φ W U h0 xs n) (xs n)
                - RNNStep φ W U (rnnState φ W U g0 xs n) (xs n)‖ := by rw [hunfold, hunfold']
        _ ≤ (Lφ * ‖W‖) * ‖rnnState φ W U h0 xs n - rnnState φ W U g0 xs n‖ := hstep
        _ ≤ (Lφ * ‖W‖) * ((Lφ * ‖W‖) ^ n * ‖h0 - g0‖) :=
              mul_le_mul_of_nonneg_left ih hρ0
        _ = (Lφ * ‖W‖) ^ (n + 1) * ‖h0 - g0‖ := by ring

/-! ## 定理二：输入扰动经 n 步的放大界（递归形式）
每步输入差 ≤ δ ⟹ `‖hₙ − hₙ'‖ ≤ ρⁿ‖h₀−h₀'‖ + (Σᵢ<ₙ ρⁱ)·(Lφ·Lu·δ)`。 -/

theorem rnn_input_error_bound (φ : X → X) (W U : X →L[ℝ] X) (Lφ Lu δ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (hLu : 0 ≤ Lu)
    (hU : ∀ x, ‖U x‖ ≤ Lu * ‖x‖)
    (h0 g0 : X) (xs ys : ℕ → X) (n : ℕ)
    (hδ : ∀ k, ‖xs k - ys k‖ ≤ δ) :
    ‖rnnState φ W U h0 xs n - rnnState φ W U g0 ys n‖
      ≤ (Lφ * ‖W‖) ^ n * ‖h0 - g0‖
        + (∑ i in Finset.range n, (Lφ * ‖W‖) ^ i) * ((Lφ * Lu) * δ) := by
  have hρ0 : 0 ≤ Lφ * ‖W‖ := mul_nonneg hLφ (norm_nonneg W)
  have hc0 : 0 ≤ Lφ * Lu := mul_nonneg hLφ hLu
  have hstep : ∀ k, ‖rnnState φ W U h0 xs (k + 1) - rnnState φ W U g0 ys (k + 1)‖
      ≤ (Lφ * ‖W‖) * ‖rnnState φ W U h0 xs k - rnnState φ W U g0 ys k‖
        + (Lφ * Lu) * δ := by
    intro k
    have hunfold : rnnState φ W U h0 xs (k + 1)
        = RNNStep φ W U (rnnState φ W U h0 xs k) (xs k) := by simp [rnnState]
    have hunfold' : rnnState φ W U g0 ys (k + 1)
        = RNNStep φ W U (rnnState φ W U g0 ys k) (ys k) := by simp [rnnState]
    have hk := rnn_step_input_lipschitz φ W U Lφ Lu hφ hLφ hLu hU
      (rnnState φ W U h0 xs k) (rnnState φ W U g0 ys k) (xs k) (ys k)
    have hk' : ‖rnnState φ W U h0 xs (k + 1) - rnnState φ W U g0 ys (k + 1)‖
        ≤ (Lφ * ‖W‖) * ‖rnnState φ W U h0 xs k - rnnState φ W U g0 ys k‖
          + (Lφ * Lu) * ‖xs k - ys k‖ := by rw [hunfold, hunfold']; exact hk
    exact hk'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hδ k) hc0))
  have hmain := geometric_error_decay (Lφ * ‖W‖) (Lφ * Lu) ‖h0 - g0‖ δ hρ0
    (fun k => ‖rnnState φ W U h0 xs k - rnnState φ W U g0 ys k‖)
    (by simp [rnnState]) hstep
  exact hmain n

/-! ## 定理三：输入扰动经 n 步的放大界（闭式，ρ < 1）
ρ < 1 时几何和 `Σᵢ<ₙ ρⁱ = (1−ρⁿ)/(1−ρ)`，得放大因子闭式：
`‖hₙ − hₙ'‖ ≤ ((1−ρⁿ)/(1−ρ))·(Lφ·Lu·δ)`（初值相同）。
ρ < 1 时总放大因子 ≤ 1/(1−ρ)（几何有界，输入扰动不累积发散）。 -/

theorem rnn_stability_bound (φ : X → X) (W U : X →L[ℝ] X) (Lφ Lu δ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (hLu : 0 ≤ Lu)
    (hU : ∀ x, ‖U x‖ ≤ Lu * ‖x‖)
    (hρ1 : Lφ * ‖W‖ < 1)
    (h0 : X) (xs ys : ℕ → X) (n : ℕ)
    (hδ : ∀ k, ‖xs k - ys k‖ ≤ δ) :
    ‖rnnState φ W U h0 xs n - rnnState φ W U h0 ys n‖
      ≤ ((1 - (Lφ * ‖W‖) ^ n) / (1 - Lφ * ‖W‖)) * ((Lφ * Lu) * δ) := by
  have hb := rnn_input_error_bound φ W U Lφ Lu δ hφ hLφ hLu hU h0 h0 xs ys n hδ
  have h1 : ‖rnnState φ W U h0 xs n - rnnState φ W U h0 ys n‖
      ≤ (∑ i in Finset.range n, (Lφ * ‖W‖) ^ i) * ((Lφ * Lu) * δ) := by
    simpa using hb
  have hgeom : (∑ i in Finset.range n, (Lφ * ‖W‖) ^ i)
      = (1 - (Lφ * ‖W‖) ^ n) / (1 - Lφ * ‖W‖) := by
    rw [geom_sum_eq (by linarith : Lφ * ‖W‖ ≠ 1) n]
    rw [div_eq_div_iff (by linarith : (Lφ * ‖W‖ - 1) ≠ 0) (by linarith : (1 - Lφ * ‖W‖) ≠ 0)]
    ring
  rw [hgeom] at h1
  exact h1

/-! ## 引理：输入前缀相同 ⟹ 隐状态相同（归纳） -/

lemma rnnState_eq_of_eq_prefix (φ : X → X) (W U : X →L[ℝ] X) (h0 g0 : X)
    (xs ys : ℕ → X) :
    ∀ k, h0 = g0 → (∀ j, j < k → xs j = ys j) →
      rnnState φ W U h0 xs k = rnnState φ W U g0 ys k := by
  intro k
  induction k with
  | zero => intro heq _; simpa [rnnState] using heq
  | succ k ih =>
      intro heq hxs
      have hunfold : rnnState φ W U h0 xs (k + 1)
          = RNNStep φ W U (rnnState φ W U h0 xs k) (xs k) := by simp [rnnState]
      have hunfold' : rnnState φ W U g0 ys (k + 1)
          = RNNStep φ W U (rnnState φ W U g0 ys k) (ys k) := by simp [rnnState]
      rw [hunfold, hunfold', ih heq (fun j hj => hxs j (by omega)), hxs k (by omega)]

/-! ## 定理四：远期输入影响指数衰减（一次输入扰动的遗忘）
两条轨迹同初值、仅在时刻 k 的输入不同（差 ≤ δ）、其余输入全同：
m 步之后差 ≤ ρᵐ·(Lφ·Lu·δ)——第 k 步的输入误差只被其后 m 步线性放大。 -/

theorem rnn_forget_bound (φ : X → X) (W U : X →L[ℝ] X) (Lφ Lu δ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (hLu : 0 ≤ Lu)
    (hU : ∀ x, ‖U x‖ ≤ Lu * ‖x‖)
    (h0 : X) (xs ys : ℕ → X) (k m : ℕ)
    (hk : ‖xs k - ys k‖ ≤ δ)
    (hxs : ∀ j, j ≠ k → xs j = ys j) :
    ‖rnnState φ W U h0 xs (k + 1 + m) - rnnState φ W U h0 ys (k + 1 + m)‖
      ≤ (Lφ * ‖W‖) ^ m * ((Lφ * Lu) * δ) := by
  have hρ0 : 0 ≤ Lφ * ‖W‖ := mul_nonneg hLφ (norm_nonneg W)
  have hc0 : 0 ≤ Lφ * Lu := mul_nonneg hLφ hLu
  have hsame : rnnState φ W U h0 xs k = rnnState φ W U h0 ys k :=
    rnnState_eq_of_eq_prefix φ W U h0 h0 xs ys k rfl (fun j hj => hxs j (by omega))
  -- 第 k+1 步：一次输入差注入，大小 ≤ Lφ·Lu·δ
  have hE : ‖rnnState φ W U h0 xs (k + 1) - rnnState φ W U h0 ys (k + 1)‖
      ≤ (Lφ * Lu) * δ := by
    have hunfold : rnnState φ W U h0 xs (k + 1)
        = RNNStep φ W U (rnnState φ W U h0 xs k) (xs k) := by simp [rnnState]
    have hunfold' : rnnState φ W U h0 ys (k + 1)
        = RNNStep φ W U (rnnState φ W U h0 ys k) (ys k) := by simp [rnnState]
    have hstep := rnn_step_input_lipschitz φ W U Lφ Lu hφ hLφ hLu hU
      (rnnState φ W U h0 xs k) (rnnState φ W U h0 ys k) (xs k) (ys k)
    rw [hunfold, hunfold']
    calc
      ‖RNNStep φ W U (rnnState φ W U h0 xs k) (xs k)
          - RNNStep φ W U (rnnState φ W U h0 ys k) (ys k)‖
          ≤ (Lφ * ‖W‖) * ‖rnnState φ W U h0 xs k - rnnState φ W U h0 ys k‖
              + (Lφ * Lu) * ‖xs k - ys k‖ := hstep
      _ = (Lφ * Lu) * ‖xs k - ys k‖ := by simp [hsame]
      _ ≤ (Lφ * Lu) * δ := mul_le_mul_of_nonneg_left hk hc0
  -- 之后 m 步：输入全同 ⟹ 每步压缩 ρ
  have hdecay : ∀ m, ‖rnnState φ W U h0 xs (k + 1 + m) - rnnState φ W U h0 ys (k + 1 + m)‖
      ≤ (Lφ * ‖W‖) ^ m * ((Lφ * Lu) * δ) := by
    intro m
    induction m with
    | zero => simpa using hE
    | succ m ih =>
        have hidx : k + 1 + (m + 1) = k + 1 + m + 1 := by omega
        have hunfold : rnnState φ W U h0 xs (k + 1 + m + 1)
            = RNNStep φ W U (rnnState φ W U h0 xs (k + 1 + m)) (xs (k + 1 + m)) := by
          simp [rnnState]
        have hunfold' : rnnState φ W U h0 ys (k + 1 + m + 1)
            = RNNStep φ W U (rnnState φ W U h0 ys (k + 1 + m)) (xs (k + 1 + m)) := by
          simp [rnnState, (hxs (k + 1 + m) (by omega)).symm]
        have hstep := rnn_step_lipschitz φ W U Lφ hφ hLφ
          (rnnState φ W U h0 xs (k + 1 + m)) (rnnState φ W U h0 ys (k + 1 + m))
          (xs (k + 1 + m))
        rw [hidx, hunfold, hunfold']
        calc
          ‖RNNStep φ W U (rnnState φ W U h0 xs (k + 1 + m)) (xs (k + 1 + m))
              - RNNStep φ W U (rnnState φ W U h0 ys (k + 1 + m)) (xs (k + 1 + m))‖
              ≤ (Lφ * ‖W‖) * ‖rnnState φ W U h0 xs (k + 1 + m)
                  - rnnState φ W U h0 ys (k + 1 + m)‖ := hstep
          _ ≤ (Lφ * ‖W‖) * ((Lφ * ‖W‖) ^ m * ((Lφ * Lu) * δ)) :=
                mul_le_mul_of_nonneg_left ih hρ0
          _ = (Lφ * ‖W‖) ^ (m + 1) * ((Lφ * Lu) * δ) := by ring
  exact hdecay m

/-! ## 定理五：隐状态映射是收缩（RealLoop 步函数的 Lipschitz 性）
`h ↦ φ(W h + U x)` 是 `ρ = Lφ·‖W‖`-Lipschitz。 -/

theorem loop_model_contraction (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (x : X) :
    ∀ h g, ‖loopStepMap φ W U x h - loopStepMap φ W U x g‖ ≤ (Lφ * ‖W‖) * ‖h - g‖ := by
  intro h g
  simpa [loopStepMap] using rnn_step_lipschitz φ W U Lφ hφ hLφ h g x

/-! ## 定理六：ρ < 1 ⟹ 不动点至多一个（唯一性）
若 p、q 都是隐状态映射的不动点，则 `‖p−q‖ ≤ ρ‖p−q‖` 且 1−ρ > 0 ⟹ p = q。 -/

theorem loop_fixed_point_unique (φ : X → X) (W U : X →L[ℝ] X) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ1 : Lφ * ‖W‖ < 1) (x p q : X)
    (hp : loopStepMap φ W U x p = p) (hq : loopStepMap φ W U x q = q) : p = q := by
  have hlip := loop_model_contraction φ W U Lφ hφ hLφ x p q
  rw [hp, hq] at hlip
  have hpos : 0 < 1 - Lφ * ‖W‖ := by linarith
  have hle : (1 - Lφ * ‖W‖) * ‖p - q‖ ≤ 0 := by nlinarith [hlip]
  have hd0 : ‖p - q‖ ≤ 0 := by nlinarith [hle, hpos]
  have hd : ‖p - q‖ = 0 := le_antisymm hd0 (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hd)

/-! ## 迭代收敛（接 RealLoop.iterate 与 RealConvergence）
（即文件头定理链第 7–8 条，紧随 `loop_fixed_point_unique` 之后）
`RealLoop.iterate`（及 `RealConvergence` 的循环骨架）在 `Type` 层陈述，
故本节在 `Type` 层给出迭代收敛（对任意 Type 层范数空间成立）。 -/

section IterateLink

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- 辅助：`f p = p` ⟹ `iterate f n p = p`（不动点迭代仍不动）。 -/
lemma iterate_fixed_point (f : Y → Y) (p : Y) (hp : f p = p) :
    ∀ n, iterate f n p = p := by
  intro n
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      show iterate f n (f p) = p
      rw [hp, ih]

omit [NormedSpace ℝ Y] in
/-- 辅助：Lipschitz 映射的迭代是 Lⁿ-Lipschitz（`iterate_step_swap`）。 -/
lemma iterate_lipschitz (f : Y → Y) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ a b, ‖f a - f b‖ ≤ L * ‖a - b‖) :
    ∀ n a b, ‖iterate f n a - iterate f n b‖ ≤ L ^ n * ‖a - b‖ := by
  intro n
  induction n with
  | zero => intro a b; simp [iterate]
  | succ n ih =>
      intro a b
      have hswap : iterate f n (f a) = f (iterate f n a) := iterate_step_swap f n a
      have hswap' : iterate f n (f b) = f (iterate f n b) := iterate_step_swap f n b
      have hunfold : iterate f (n + 1) a = iterate f n (f a) := by simp [iterate]
      have hunfold' : iterate f (n + 1) b = iterate f n (f b) := by simp [iterate]
      rw [hunfold, hunfold', hswap, hswap']
      calc
        ‖f (iterate f n a) - f (iterate f n b)‖
            ≤ L * ‖iterate f n a - iterate f n b‖ := hf _ _
        _ ≤ L * (L ^ n * ‖a - b‖) := mul_le_mul_of_nonneg_left (ih a b) hL
        _ = L ^ (n + 1) * ‖a - b‖ := by ring

/-- 迭代对不动点的几何收敛率 `‖Tⁿ h₀ − p‖ ≤ ρⁿ·‖h₀ − p‖`（文件头定理链第 7 条）。 -/
theorem loop_converges_to_fixed_point (φ : Y → Y) (W U : Y →L[ℝ] Y) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ) (x : Y)
    (h0 p : Y) (hp : loopStepMap φ W U x p = p) (n : ℕ) :
    ‖iterate (loopStepMap φ W U x) n h0 - p‖
      ≤ (Lφ * ‖W‖) ^ n * ‖h0 - p‖ := by
  have hρ0 : 0 ≤ Lφ * ‖W‖ := mul_nonneg hLφ (norm_nonneg W)
  have hlip : ∀ a b, ‖loopStepMap φ W U x a - loopStepMap φ W U x b‖ ≤ (Lφ * ‖W‖) * ‖a - b‖ :=
    loop_model_contraction φ W U Lφ hφ hLφ x
  have hiter := iterate_lipschitz (loopStepMap φ W U x) (Lφ * ‖W‖) hρ0 hlip n h0 p
  have hfix : iterate (loopStepMap φ W U x) n p = p := iterate_fixed_point _ p hp n
  rw [hfix] at hiter
  exact hiter

/-- ρ < 1 ⟹ 两条迭代轨迹最终 ε-接近（接 `contraction_converges`；文件头定理链第 8 条）。 -/
theorem loop_iterate_convergence (φ : Y → Y) (W U : Y →L[ℝ] Y) (Lφ : ℝ)
    (hφ : ∀ a b, ‖φ a - φ b‖ ≤ Lφ * ‖a - b‖) (hLφ : 0 ≤ Lφ)
    (hρ0 : 0 ≤ Lφ * ‖W‖) (hρ1 : Lφ * ‖W‖ < 1) (x h0 g0 : Y) :
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ, ‖iterate (loopStepMap φ W U x) n h0
        - iterate (loopStepMap φ W U x) n g0‖ < ε := by
  have hlip : ∀ a b,
      ‖loopStepMap φ W U x a - loopStepMap φ W U x b‖ ≤ (Lφ * ‖W‖) * ‖a - b‖ :=
    loop_model_contraction φ W U Lφ hφ hLφ x
  refine contraction_converges (Lφ * ‖W‖) hρ0 hρ1 ?_ ?_
  · intro n
    have hswap : iterate (loopStepMap φ W U x) n (loopStepMap φ W U x h0)
        = loopStepMap φ W U x (iterate (loopStepMap φ W U x) n h0) :=
      iterate_step_swap _ n h0
    have hswap' : iterate (loopStepMap φ W U x) n (loopStepMap φ W U x g0)
        = loopStepMap φ W U x (iterate (loopStepMap φ W U x) n g0) :=
      iterate_step_swap _ n g0
    have hunfold : iterate (loopStepMap φ W U x) (n + 1) h0
        = iterate (loopStepMap φ W U x) n (loopStepMap φ W U x h0) := by simp [iterate]
    have hunfold' : iterate (loopStepMap φ W U x) (n + 1) g0
        = iterate (loopStepMap φ W U x) n (loopStepMap φ W U x g0) := by simp [iterate]
    rw [hunfold, hunfold', hswap, hswap']
    exact hlip _ _
  · intro n
    exact norm_nonneg _

end IterateLink

end Lattice
