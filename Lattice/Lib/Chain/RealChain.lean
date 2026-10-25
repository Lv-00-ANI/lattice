import Mathlib

/-!
# LATTICE: 完整模型前向链 —— n 层 Lipschitz 链的端到端误差传播

把 RealBlock 的 2/3 层块组合推广为**任意 n 层完整前向链**
（transformer 结构线的收官：单组件证明 → 多层全链）：

  1. ChainFwd：n 层前向（层 0..n-1 依次作用），模型无关；
  2. chainN_error_bound：每层 Lipschitz（常数 Ls i）⟹ 端到端
     误差 ≤ (∏ᵢ Ls i)·‖x − y‖（Lipschitz 常数连乘，归纳）；
  3. chain_edit_locality：第 k 层入口扰动 δ ⟹ 端到端变化
     ≤ (∏_{j<n−k} Ls(k+j))·‖δ‖（编辑局部性的 n 层版，外层放大）。

实例化路径（组件 Lipschitz 常数，各文件已证）：
  · 注意力：凸组合 ⟹ L ≤ 1（convComb_norm_bound）
  · 残差：L ≤ ‖F‖ + 1（residual 系列）
  · FFN：软掩码有效线性 ⟹ L ≤ max‖Wᵢ·sᵢ‖（softMask_FFN_effective）
  · 规范化：缩放不变（ScaleInvariantNorm 族）
  · 编辑：Lipschitz 界（edit_output_bound_scalar）
将这些常数代入 chainN_error_bound 即得完整模型前向链的端到端误差界。

模型无关：任意范数空间 X、任意 Lipschitz 层、任意层数 n。
-/

noncomputable section

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 前向链：n 层依次作用（层 0..n-1） -/

def ChainFwd (Fs : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => Fs n (ChainFwd Fs n x)

/-! ## 尾部链：从第 k 层开始（层 k..n-1） -/

def ChainTail (Fs : ℕ → X → X) (k n : ℕ) (x : X) : X :=
  ChainFwd (fun j => Fs (k + j)) (n - k) x

/-! ## 定理一：n 层链端到端误差界（核心）
每层 Lipschitz（Ls i）⟹ 端到端误差 ≤ (∏ᵢ Ls i)·‖x − y‖。-/

omit [NormedSpace ℝ X] in
theorem chainN_error_bound (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n : ℕ)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i) :
    ∀ x y, ‖ChainFwd Fs n x - ChainFwd Fs n y‖ ≤ (∏ i in Finset.range n, Ls i) * ‖x - y‖ := by
  induction n with
  | zero =>
      intro x y
      simp [ChainFwd]
  | succ n ih =>
      intro x y
      -- 归纳假设：限制到前 n 层
      have ih' := ih (fun i hi => hL i (by omega)) (fun i hi => hL0 i (by omega))
      -- 第 n 层 Lipschitz
      have hstep : ‖Fs n (ChainFwd Fs n x) - Fs n (ChainFwd Fs n y)‖
          ≤ Ls n * ‖ChainFwd Fs n x - ChainFwd Fs n y‖ :=
        hL n (by omega) _ _
      calc
        ‖Fs n (ChainFwd Fs n x) - Fs n (ChainFwd Fs n y)‖
            ≤ Ls n * ‖ChainFwd Fs n x - ChainFwd Fs n y‖ := hstep
        _ ≤ Ls n * ((∏ i in Finset.range n, Ls i) * ‖x - y‖) := by
              exact mul_le_mul_of_nonneg_left (ih' x y) (hL0 n (by omega))
        _ = (∏ i in Finset.range (n + 1), Ls i) * ‖x - y‖ := by
              rw [Finset.prod_range_succ]
              ring

/-! ## 定理二：链编辑局部性（n 层版）
在第 k 层入口注入扰动 δ，经层 k..n-1 传播：
端到端变化 ≤ (∏_{j<n−k} Ls(k+j))·‖δ‖（外层常数连乘放大）。-/

theorem chain_edit_locality (Fs : ℕ → X → X) (Ls : ℕ → ℝ) (n k : ℕ) (hk : k < n) (δ : X)
    (hL : ∀ i, i < n → ∀ x y, ‖Fs i x - Fs i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i) (x : X) :
    ‖ChainTail Fs k n (x + δ) - ChainTail Fs k n x‖
        ≤ (∏ j in Finset.range (n - k), Ls (k + j)) * ‖δ‖ := by
  unfold ChainTail
  -- 平移：尾部链 = 以 (Fs∘k) 为层的 (n-k) 层链
  have hshift : ∀ j, j < n - k → ∀ x y,
      ‖Fs (k + j) x - Fs (k + j) y‖ ≤ Ls (k + j) * ‖x - y‖ := by
    intro j hj x y
    exact hL (k + j) (by omega) x y
  have hshift0 : ∀ j, j < n - k → 0 ≤ Ls (k + j) := by
    intro j hj
    exact hL0 (k + j) (by omega)
  have hb := chainN_error_bound (fun j => Fs (k + j)) (fun j => Ls (k + j)) (n - k)
    hshift hshift0 (x + δ) x
  simpa using hb

/-! ## 定理三：两层特例（与 RealBlock.compose_error_propagation 一致，向量版）
‖g(fx) − g(fy)‖ ≤ (Lg·Lf)·‖x − y‖。-/

omit [NormedSpace ℝ X] in
theorem chain2_special (f g : X → X) (Lf Lg : ℝ)
    (hf : ∀ x y, ‖f x - f y‖ ≤ Lf * ‖x - y‖) (hg : ∀ x y, ‖g x - g y‖ ≤ Lg * ‖x - y‖)
    (hLg : 0 ≤ Lg) :
    ∀ x y, ‖g (f x) - g (f y)‖ ≤ (Lg * Lf) * ‖x - y‖ := by
  intro x y
  calc
    ‖g (f x) - g (f y)‖ ≤ Lg * ‖f x - f y‖ := hg (f x) (f y)
    _ ≤ Lg * (Lf * ‖x - y‖) := mul_le_mul_of_nonneg_left (hf x y) hLg
    _ = (Lg * Lf) * ‖x - y‖ := by ring

/-! ## 注：与单层一致（n=1 时 ∏ 退化）
chainN_error_bound 在 n=1 时给出 ‖Fs 0 x − Fs 0 y‖ ≤ Ls 0·‖x−y‖
（∏ range 1 = Ls 0），恰是单层 Lipschitz 假设本身——n 层链是单层
性质的归纳闭包，不是新假设。-/

end Lattice
