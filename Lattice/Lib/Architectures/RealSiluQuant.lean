/-
# LATTICE: RealSiluQuant — 定量 T2：σ(L_g)·L_u ≡lim Pₙ(L_g)·L_u，误差 ≤ ML·M·Z^{n+1}/(n+1)!

> 分支：`theory/op-split`（作者 **yjh051108**，经远端拉取获得；本仓库**不是**其作者）
> 高数：拉格朗日余项 × 乘积有界 ⇒ 一致误差界；阶乘压过幂 ⇒ n→∞ 时误差→0。

## 诚实边界（**标注**）

⭐ 本文件是**组装**（把 `RealSiluRemainder` 的 ε→0 腿接到 `RealSiluSplit` 的结构 T2 上），
**未做**新的数学内容。`hbound`（`|σ z − P z| ≤ M·Z^(n+1)/(n+1)!`）为**传入假设**，
**未证**，**留待**接线 mathlib `taylor_mean_remainder_bound`。
⭐ 下面的 `e25`/`e26` 是**工程编号（仓库外）**，全库**未证**其存在。
-/

import Lattice.Lib.Architectures.RealSiluRemainder
namespace RealSiluQuant

open RealLimitDiscrete RealSiluSplit RealSiluRemainder

/-- **定量 T2（已证）**：
    |σ z − P z| ≤ M·Z^{n+1}/(n+1)!  且  |L_u| ≤ ML
    ⟹  |σ(L_g x)·L_u x − P(L_g x)·L_u x| ≤ ML·M·Z^{n+1}/(n+1)! → 0。 -/
theorem mul_split_quant
    (σ P : ℝ → ℝ) (Lg Lu : ℝ → ℝ) (X : ℝ → Prop)
    (Z M ML : ℝ)
    (hM : 0 ≤ M) (hML : 0 ≤ ML)
    (hLg : ∀ x, X x → |Lg x| ≤ Z)
    (hLu : ∀ x, X x → |Lu x| ≤ ML)
    (hbound : ∀ n z, |z| ≤ Z →
      |σ z - P z| ≤ M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) :
    LimitDiscrete (fun a b : ℝ => abs (a - b))
      (fun x => σ (Lg x) * Lu x)
      (fun _n x => P (Lg x) * Lu x)
      X
      (fun n => ML * (M * Z ^ (n + 1) / ((n + 1).factorial : ℝ))) := by
  have hPA : PolyApproxOn σ P Z (fun n => M * Z ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    polyApprox_eps_to σ P Z M hM hbound
  exact mul_split_limit_discrete σ P Lg Lu X Z ML
    (fun n => M * Z ^ (n + 1) / ((n + 1).factorial : ℝ))
    hLg hLu hML hPA

/-! 与 `e25`/`e26`（**工程编号，仓库外**）对齐：σ:=SiLU，P:=Pₙ 泰勒多项式，
M:=sup|SiLU^(n+1)| 型常数，ML:=sup|⟨w_u,·⟩|。代入后即「用 n 阶多项式，误差 ≤ ML·M·Z^(n+1)/(n+1)!」。
**无 sorry**。诚实边界：`hbound` 为**显式假设**（**未证**）；SiLU 实例化**未做**，**留待**后续工作。 -/

end RealSiluQuant
