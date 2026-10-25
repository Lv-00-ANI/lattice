/-
# LATTICE: RealSiluSplit — S4：h = σ(L_g)·L_u 的极限离散（真强算子）

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）
> 对应工程 `e25_s3_split`（**工程编号，仓库外**，非本仓库命题名；全库**未证**其存在）
> σ 为抽象「已知强算子」（SiLU 实例化时令 σ := SiLU）。
> Pₙ 为 σ 的有限多项式逼近；余项界 ⇒ T2 `LimitDiscrete`。

强算子构造子：Lin、Poly、σ、Mul。无查表。

## 诚实边界（**标注**）

⭐ σ 仍是**抽象函数参数**（**未做** SiLU 实例化）；具体的 Taylor 系数与真余项常数
**未证**，接 `RealTaylorMultivariate` 属**后续工作**（该文件只有一/二阶，
真正的 n 阶界**留待**接线 mathlib `taylor_mean_remainder_bound`）。
本文件只给**结构传递**：乘法 × 多项式逼近。
⭐ 该 `Z^(n+1)/(n+1)!` 形式要求 σ 光滑（`n+1` 阶可导），**超出**非光滑激活（如 ReLU）的适用范围。
-/

import Mathlib.Data.Real.Basic
import Lattice.Lib.Chain.RealLimitDiscrete
namespace RealSiluSplit

open RealLimitDiscrete

/-- 多项式在紧致区间对 σ 的逼近 + 余项 εₙ → 0（T2 数据）。 -/
structure PolyApproxOn (σ : ℝ → ℝ) (P : ℝ → ℝ) (Z : ℝ) (eps : Nat → ℝ) : Prop where
  bound : ∀ n z, |z| ≤ Z → |σ z - P z| ≤ eps n
  eps_to : ∀ ε : ℝ, 0 < ε → ∃ N : Nat, ∀ n : Nat, N ≤ n → eps n < ε

/-- **T2 实例（已证）**：σ(L_g)·L_u ≡lim P(L_g)·L_u，误差 ≤ M·εₙ → 0。 -/
theorem mul_split_limit_discrete
    (σ P : ℝ → ℝ) (Lg Lu : ℝ → ℝ) (X : ℝ → Prop)
    (Z M : ℝ) (eps : Nat → ℝ)
    (hLg : ∀ x, X x → |Lg x| ≤ Z)
    (hLu : ∀ x, X x → |Lu x| ≤ M)
    (hM : 0 ≤ M)
    (hPA : PolyApproxOn σ P Z eps) :
    LimitDiscrete (fun a b : ℝ => abs (a - b))
      (fun x => σ (Lg x) * Lu x)
      (fun _n x => P (Lg x) * Lu x)
      X
      (fun n => M * eps n) := by
  refine ⟨?_, ?_⟩
  · intro n x hx
    have e1 : σ (Lg x) * Lu x - P (Lg x) * Lu x = (σ (Lg x) - P (Lg x)) * Lu x :=
      (sub_mul (σ (Lg x)) (P (Lg x)) (Lu x)).symm
    have e2 : abs (σ (Lg x) - P (Lg x)) ≤ eps n := hPA.bound n (Lg x) (hLg x hx)
    have e3 : abs (Lu x) ≤ M := hLu x hx
    calc abs (σ (Lg x) * Lu x - P (Lg x) * Lu x)
          = abs ((σ (Lg x) - P (Lg x)) * Lu x) := by rw [e1]
        _ = abs (σ (Lg x) - P (Lg x)) * abs (Lu x) := abs_mul _ _
        _ = abs (Lu x) * abs (σ (Lg x) - P (Lg x)) := mul_comm _ _
        _ ≤ M * eps n := mul_le_mul e3 e2 (abs_nonneg _) hM
  · intro ε hε
    by_cases hM0 : M = 0
    · refine ⟨0, ?_⟩
      intro n _
      have : (0 : ℝ) * eps n = 0 := zero_mul _
      rw [hM0, zero_mul]
      exact hε
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      have hεM : 0 < ε / M := div_pos hε hMpos
      obtain ⟨N, hN⟩ := hPA.eps_to (ε / M) hεM
      refine ⟨N, ?_⟩
      intro n hn
      have : eps n < ε / M := hN n hn
      calc M * eps n < M * (ε / M) := mul_lt_mul_of_pos_left this hMpos
        _ = ε := by rw [mul_div_cancel₀]; exact ne_of_gt hMpos

/-! 诚实边界：σ 的具体 Taylor 系数与真余项常数接 `RealTaylorMultivariate` 属**后续工作**（**未证**）；
本文件给出**结构 T2**（乘法 × 多项式逼近传递），**未做** SiLU 实例化。
强算子：σ、Poly、Lin、Mul。无查表。`eps → 0` 腿在此为**显式假设**（PolyApproxOn.eps_to）。 -/

end RealSiluSplit
