import Lattice.Lib.Chain.RealChain
import Mathlib

/-!
# LATTICE: 链权重编辑的端到端界 —— 编辑线收束到完整模型

RealChain（链骨架）+ 编辑（ROME/MEMIT/LoRA 权重编辑）的收束：
在 n 层链的第 k 层把权重 W_k 编辑为 W_k'（‖W_k' − W_k‖ ≤ q），
端到端输出变化被**外层 Lipschitz 常数连乘 × 编辑量**控制：

    ‖编辑后输出 − 原输出‖ ≤ (∏_{j<n−k−1} L_{k+1+j}) · q · ‖x_k‖

其中 x_k 是编辑层的输入（前 k 层输出）。

  1. chain_split_at：链在第 k 层分裂（前 k 层 ∘ 层 k ∘ 尾部链）——
     编辑局部性的结构基础；
  2. chain_weight_edit_bound：单层权重编辑（‖Δ_k‖ ≤ q）⟹ 端到端界
     = 外层放大 × q‖x_k‖（衔接 chain_edit_locality 入口扰动版）。

闭环：ROME/MEMIT/LoRA 的权重编辑（‖Δ‖ 界已证）⟹ 代入本定理 ⟹
完整模型端到端编辑误差界——编辑线、结构线、链骨架三线汇合。

模型无关：任意范数空间 X、任意 Lipschitz 层、任意编辑层 k。
-/

noncomputable section

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 引理：链在第 k 层分裂
ChainFwd n x = ChainTail (k+1) n (F_k (ChainFwd k x))（前 k 层 ∘ 层 k ∘ 尾部）。-/

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma chain_split_at (Fs : ℕ → X → X) (n k : ℕ) (hk : k < n) (x : X) :
    ChainFwd Fs n x = ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x)) := by
  induction n with
  | zero =>
      exact False.elim (Nat.not_lt_zero k hk)
  | succ n ih =>
      by_cases hnk : k < n
      · -- k < n：递归展开（尾部链在 n 层再走一步）
        calc
          ChainFwd Fs (n + 1) x = Fs n (ChainFwd Fs n x) := rfl
          _ = Fs n (ChainTail Fs (k + 1) n (Fs k (ChainFwd Fs k x))) := by rw [ih hnk]
          _ = ChainTail Fs (k + 1) (n + 1) (Fs k (ChainFwd Fs k x)) := by
                unfold ChainTail
                -- (n+1)-(k+1) = (n-(k+1))+1（n ≥ k+1）
                have hm : (n + 1) - (k + 1) = (n - (k + 1)) + 1 := by omega
                rw [hm]
                -- ChainFwd F' (m+1) y = F' m (ChainFwd F' m y)，F' m = Fs (k+1+m) = Fs n
                have harg : k + 1 + (n - (k + 1)) = n := by omega
                have hF : (fun j : ℕ => Fs (k + 1 + j)) (n - (k + 1)) = Fs n := by
                  change Fs (k + 1 + (n - (k + 1))) = Fs n
                  rw [harg]
                rw [ChainFwd]
                rw [← hF]
      · -- ¬k < n ⟹ k = n（编辑层即最后一层）：尾部链为空
        have hkn : k = n := by omega
        subst k
        simp [ChainTail, ChainFwd]

/-! ## 定理：链权重编辑的端到端界
在第 k 层把权重 W_k 编辑为 W_k'（‖W_k'−W_k‖ ≤ q），
端到端变化 ≤ (∏_{j<n−k−1} L_{k+1+j}) · q·‖x_k‖（x_k 为编辑层输入）。-/

theorem chain_weight_edit_bound (Ws : ℕ → X →L[ℝ] X) (Ls : ℕ → ℝ) (n k : ℕ)
    (hk : k + 1 < n) (q : ℝ) (x0 : X) (Wk' : X →L[ℝ] X)
    (hL : ∀ i, i < n → ∀ x y, ‖Ws i x - Ws i y‖ ≤ Ls i * ‖x - y‖)
    (hL0 : ∀ i, i < n → 0 ≤ Ls i)
    (hΔ : ‖Wk' - Ws k‖ ≤ q) :
    ‖ChainTail (fun i x => Ws i x) (k + 1) n (Wk' (ChainFwd (fun i x => Ws i x) k x0))
      - ChainFwd (fun i x => Ws i x) n x0‖
      ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * (q * ‖ChainFwd (fun i x => Ws i x) k x0‖) := by
  -- 编辑层输入 x_k = 前 k 层输出
  let x_k : X := ChainFwd (fun i x => Ws i x) k x0
  -- 编辑层输出 = 原输出 + 扰动：Wk' x_k = Ws k x_k + (Wk' - Ws k) x_k
  have hdelta : Wk' x_k = Ws k x_k + (Wk' - Ws k) x_k := by
    have hw : Ws k + (Wk' - Ws k) = Wk' := by abel
    calc
      Wk' x_k = (Ws k + (Wk' - Ws k)) x_k := by rw [hw]
      _ = Ws k x_k + (Wk' - Ws k) x_k := rfl
  -- 单层扰动界：‖(Wk' - Ws k) x_k‖ ≤ q·‖x_k‖
  have hq : ‖(Wk' - Ws k) x_k‖ ≤ q * ‖x_k‖ := by
    calc
      ‖(Wk' - Ws k) x_k‖ ≤ ‖Wk' - Ws k‖ * ‖x_k‖ :=
        (Wk' - Ws k).le_opNorm x_k
      _ ≤ q * ‖x_k‖ := mul_le_mul_of_nonneg_right hΔ (norm_nonneg _)
  -- 尾部链在 (Ws k x_k + δ) 处的入口扰动界（chain_edit_locality）
  have hloc := chain_edit_locality (fun i x => Ws i x) Ls n (k + 1) hk
    ((Wk' - Ws k) x_k) hL hL0 (Ws k x_k)
  -- 原链在第 k 层分裂
  have hsplit := chain_split_at (fun i x => Ws i x) n k (by omega : k < n) x0
  calc
    ‖ChainTail (fun i x => Ws i x) (k + 1) n (Wk' x_k)
        - ChainFwd (fun i x => Ws i x) n x0‖
        = ‖ChainTail (fun i x => Ws i x) (k + 1) n (Ws k x_k + (Wk' - Ws k) x_k)
            - ChainTail (fun i x => Ws i x) (k + 1) n (Ws k x_k)‖ := by
          rw [hsplit, hdelta]
    _ ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * ‖(Wk' - Ws k) x_k‖ := hloc
    _ ≤ (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * (q * ‖x_k‖) := by
          exact mul_le_mul_of_nonneg_left hq
            (Finset.prod_nonneg (by
              intro j hj
              -- j < n-(k+1) ⟹ k+1+j < n（Nat 减法先转加法）
              have hlt : k + 1 + j < n := by
                have hsub : n - (k + 1) + (k + 1) = n := Nat.sub_add_cancel (le_of_lt hk)
                have hjr : j + (k + 1) < n := by
                  have : j + (k + 1) < (n - (k + 1)) + (k + 1) :=
                    Nat.add_lt_add_right (by simpa using hj) (k + 1)
                  rwa [hsub] at this
                omega
              exact hL0 (k + 1 + j) hlt))
    _ = (∏ j in Finset.range (n - (k + 1)), Ls (k + 1 + j)) * (q * ‖ChainFwd (fun i x => Ws i x) k x0‖) := by
          rfl

/-! ## 注：三线汇合
  ROME/MEMIT/LoRA 权重编辑给出 ‖Δ‖ 界（edit_output_bound_scalar 等）⟹
  代入本定理（‖W_k'−W_k‖ ≤ q）⟹ 完整模型端到端编辑误差界
  = 外层 Lipschitz 连乘 × 编辑量——编辑线、结构线、链骨架（RealChain）
  的收束；编辑在最后一层（k+1 = n）时尾部链为空，误差 ≤ q‖x_k‖
  （∏ 空 = 1 的退化特例）。-/

end Lattice
