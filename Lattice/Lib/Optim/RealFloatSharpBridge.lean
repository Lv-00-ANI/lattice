/-
# LATTICE: K-01 —— 紧 Lipschitz 常数族 × 浮点舍入族（**同一载体**）

本文件把两族**从未互 import** 的定理接起来（实测：`RealRMSNormSharpness` 与
`RealFloatFormat` 之间零 import，与 `三期22-B` §1.5 的实测一致）：

  · **常数族（B 端）**：`rmsNormE_sqrt_lipschitz`（`RealRMSNormSharpness.lean:94`）
    —— RMSNorm 的**紧** Lipschitz 常数 `√n / c`，载体 `EuclideanSpace ℝ (Fin n)`；
  · **需求族（A 端）**：`op_error_propagation`（`RealFloatFormat.lean:164`）
    —— 带**自由常数** `κ` 的误差传播需求，载体 `ℝ → ℝ`。

## 接法：一次"载体搬运"，但正确的搬法是**把舍入读作扰动**

`RealFloatFormat` 的误差项 `F.eps * |x| + F.tiny` 里 `eps/tiny : ℝ` 而 RMSNorm 侧
`x` 是向量，**不能直接相乘** —— 这是 K-01 的真实接口区别
（`三期22-B` §1.2 判定为"一次真实的值域搬运"，而不是"$`|·`$ 读作范数"）。

但那次搬运的正确做法**不是**把 `RoundOp` 泛化到向量（那会改动被 8 个模块 import 的
`RealFloatFormat`，触发 R2 风险），而是**把舍入读作同一载体上的扰动**：

    x' 满足 ‖x' − x‖ ≤ F.eps * ‖x‖ + F.tiny

此时"误差传播 ≤ 条件数 × 单位舍入"就化归为 **`κ` 乘上扰动尺度**，
且**与载体无关**（任意伪度量空间即可）—— 于是 B 端的紧常数 `√n/c` 可以**逐字**代入 `κ`。
这是本文件相对 `三期22-B` 的**核心简化**：搬运段退化为一个引理。

## 主结果

1. `k01_op_error_of_disturbance`（**核心桥**）：`κ`-Lipschitz 的 `f` 在扰动输入下
   `dist (f x') (f x) ≤ κ * δ`（任意伪度量空间，**零新假设**）；
2. `k01_rmsNorm_lipschitz_dist`：RMSNorm 的紧常数 `√n/c` 的**距离形式**，
   载体与 B 端逐字一致，供核心桥消费；
3. `k01_rmsNorm_float_error_bound`（**K-01 目标**）：
   `dist (RMSNorm x') (RMSNorm x) ≤ (√n/c) * (F.eps * ‖x‖ + F.tiny)`，
   前提 `c > 0`、`c ≤ ‖x‖`、`c ≤ ‖x'`` **逐字保留**（判据 T3）；
4. `k01_rmsNorm_constant_not_improvable`（**判据 T2：常数唯一性**）：
   `√n/c` 不是任取的上界 —— 任何有效常数 `K` 必满足 `√n/c ≤ K`；
5. `k01_relaxed_constant_also_connects`（**负对照 NC-3**）：把 `√n/c` 换成松弛的
   `2√n/c` **同样能接上** —— 证明"能接"本身**不是**判据（`三期22-B` §4.2 NC-3），
   必须配 4 才能声称"紧"。

## 诚实边界（逐条显式）

- 本文件**不改动** `RealFloatFormat.lean` / `RealRMSNormSharpness.lean`（零 diff，R2 缓解）；
- **零新 `axiom` / `sorry` / `admit`**；`κ` 的自由性、`c > 0`、`c ≤ ‖x‖`、`c ≤ ‖x'``
  均**逐字**出现在签名中（T3），未藏进类型类或 `simp`；
- ⚠ **不声称**覆盖 `γ/β` 仿射项与 `ε` 变体的常数
  （`RealRMSNormSharpness.lean:325-326` 逐字标注"未做"，判据 §4.3 K-01④）；
- ⚠ **不声称**"扰动建模"等价于 IEEE-754 逐位语义：`RoundOp` 本身即显式公理式抽象
  （`RealFloatFormat.lean:99-105`：无舍入模式、无 NaN/Inf、无指数偏置），
  本文件**沿用**该抽象，既不新增也不强化它；
- 本文件**不**给出 `RoundOp F` 的实例（`RealIEEE754.ieee_satisfies_roundOp` 可提供，
  本文件不需要它）；
- ⚠ `k01_rmsNorm_float_error_bound` 的 `x'` 是**抽象扰动点**，
  条件 `c ≤ ‖x'`` 是**显式假设**（该条件是 B 端紧常数 `√n/c` 的适用条件，
  为复用 `k01_rmsNorm_lipschitz_dist` 而**逐字保留**自 `rmsNormE_sqrt_lipschitz`，
  并非搬运舍入算子所引入的额外假设）；
  本文件**不声称**某个具体舍入算子总能满足它。
-/

import Mathlib
import Lattice.Lib.Architectures.RealRMSNormSharpness
import Lattice.Lib.Quantization.RealFloatFormat
noncomputable section

namespace Lattice

/-! ## 一、核心桥：扰动形式的误差传播（载体无关） -/

/-- **`k01_op_error_of_disturbance`（核心桥）**：若 `f` 满足
`dist (f x) (f y) ≤ κ * dist x y`（`κ ≥ 0`），则对任意扰动输入 `x'`（`dist x' x ≤ δ`）有
`dist (f x') (f x) ≤ κ * δ`。

这是 `RealFloatFormat.op_error_propagation`（`:164`）的**载体无关形式**：
把"输入经舍入"读作"输入被扰动 `δ`"，`κ` 保持自由 —— 于是常数族的紧常数可逐字代入。
陈述在任意伪度量空间上，故不预设任何范数/内积结构。 -/
theorem k01_op_error_of_disturbance {α : Type*} [PseudoMetricSpace α]
    (f : α → α) (κ δ : ℝ) (hκ : 0 ≤ κ)
    (hf : ∀ x y : α, dist (f x) (f y) ≤ κ * dist x y)
    {x x' : α} (hδ : dist x' x ≤ δ) :
    dist (f x') (f x) ≤ κ * δ := by
  calc dist (f x') (f x) ≤ κ * dist x' x := hf x' x
    _ ≤ κ * δ := mul_le_mul_of_nonneg_left hδ hκ

/-! ## 二、常数族供给：RMSNorm 紧常数 `√n/c` 的距离形式 -/

/-- **`k01_rmsNorm_lipschitz_dist`**：RMSNorm 在 `{‖·‖ ≥ c}` 上是 `(√n/c)`-Lipschitz
的**距离形式**（`dist` 版本），载体与 B 端**逐字一致**，供核心桥消费。
由 `RealRMSNormSharpness.rmsNormE_sqrt_lipschitz`（`:94`）+ `dist_eq_norm` 直接得到。 -/
theorem k01_rmsNorm_lipschitz_dist {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    dist (rmsNormE x) (rmsNormE y) ≤ (Real.sqrt n / c) * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  exact rmsNormE_sqrt_lipschitz x y c hc hx hy

/-! ## 三、K-01 目标：舍入输入下的 RMSNorm 误差界 -/

/-- **`k01_rmsNorm_float_error_bound`（K-01 目标）**：设浮点格式 `F`，`c > 0`，
`x` 与扰动点 `x'` 均满足 `c ≤ ‖·‖`，且扰动尺度
`dist x' x ≤ F.eps * ‖x‖ + F.tiny`（这就是 `RoundOp.err_bound` 的形状，
只是把标量 `|x|` 换成同一载体上的 `‖x‖`）。则

    dist (RMSNorm x') (RMSNorm x) ≤ (√n/c) * (F.eps * ‖x‖ + F.tiny)

即 **误差放大 = 紧 Lipschitz 常数 × 单位舍入**。这是 K-01 的 C 端结论：
`κ` 由 B 端的**紧**常数 `√n/c` 填入（而非自由），扰动由 A 端的舍入形状给出。 -/
theorem k01_rmsNorm_float_error_bound (F : FloatFormat) {n : ℕ}
    (c : ℝ) (hc : 0 < c) (x x' : EuclideanSpace ℝ (Fin n))
    (hx : c ≤ ‖x‖) (hx' : c ≤ ‖x'‖)
    (hδ : dist x' x ≤ F.eps * ‖x‖ + F.tiny) :
    dist (rmsNormE x') (rmsNormE x) ≤ (Real.sqrt n / c) * (F.eps * ‖x‖ + F.tiny) := by
  have hκ : 0 ≤ Real.sqrt n / c := div_nonneg (Real.sqrt_nonneg n) (le_of_lt hc)
  calc dist (rmsNormE x') (rmsNormE x)
      ≤ (Real.sqrt n / c) * dist x' x := k01_rmsNorm_lipschitz_dist x' x c hc hx' hx
    _ ≤ (Real.sqrt n / c) * (F.eps * ‖x‖ + F.tiny) :=
        mul_le_mul_of_nonneg_left hδ hκ

/-! ## 四、判据 T2：常数 `√n/c` 的**唯一性**（不是任取的上界） -/

/-- **`k01_rmsNorm_constant_not_improvable`（判据 T2）**：`n > 0`、`c > 0` 时，
任何有效的 Lipschitz 常数 `K`（即对 `{‖·‖ ≥ c}` 上所有点对成立）必满足 `√n/c ≤ K`。

这把"K-01 的 `κ` 恰好是 `√n/c`"从事后观察变成**可证事实**：
`κ` **不可能更小**，故 K-01 的常数是**紧的**而非松弛的。 -/
theorem k01_rmsNorm_constant_not_improvable {n : ℕ} (hn : 0 < n) (c K : ℝ)
    (hc : 0 < c)
    (hK : ∀ x y : EuclideanSpace ℝ (Fin n), c ≤ ‖x‖ → c ≤ ‖y‖ →
      ‖rmsNormE x - rmsNormE y‖ ≤ K * ‖x - y‖) :
    Real.sqrt n / c ≤ K :=
  (rmsNormE_constant_iff hn c K hc).mp hK

/-! ## 五、负对照 NC-3：松弛常数**同样能接** ⟹ "能接"不是判据 -/

/-- **`k01_relaxed_constant_also_connects`（负对照 NC-3）**：把 K-01 的常数从紧的
`√n/c` 换成松弛的 `2√n/c`，**结论照样成立**（因为松弛界也是有效 Lipschitz 界）。

注意 **这正是阴性说明**（`三期22-B` §4.2 NC-3）：**光有"能接"不足以证明接得对** ——
只有配上 §四 的唯一性才是真正的判据。本文件保留该负对照，以免读者把
"K-01 能接上"误读为"K-01 的常数是紧的"。 -/
theorem k01_relaxed_constant_also_connects (F : FloatFormat) {n : ℕ}
    (c : ℝ) (hc : 0 < c) (x x' : EuclideanSpace ℝ (Fin n))
    (hx : c ≤ ‖x‖) (hx' : c ≤ ‖x'‖)
    (hδ : dist x' x ≤ F.eps * ‖x‖ + F.tiny) :
    dist (rmsNormE x') (rmsNormE x) ≤ (2 * Real.sqrt n / c) * (F.eps * ‖x‖ + F.tiny) := by
  -- 注意 **实测修复**：本负对照**不能**用严格不等式 `√n/c < 2√n/c` —— 它在 `n = 0` 处
  -- **不成立**（`√0 = 0`，两边相等）。改用**非严格** `≤`：对所有 `n` 成立，结论不变。
  -- （该缺陷由 `lean-lock.ps1 RealFloatSharpBridge.lean` 的真实编译诊断发现：
  --   `error: unsolved goals ... ⊢ x = 0`；静态审读看不出 `n = 0` 的退化。）
  have hle : Real.sqrt n / c ≤ 2 * Real.sqrt n / c := by
    have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
    have h3 : 0 ≤ Real.sqrt n / c := div_nonneg hs (le_of_lt hc)
    have h2 : 2 * Real.sqrt n / c - Real.sqrt n / c = Real.sqrt n / c := by ring
    linarith
  calc dist (rmsNormE x') (rmsNormE x)
      ≤ (Real.sqrt n / c) * (F.eps * ‖x‖ + F.tiny) :=
        k01_rmsNorm_float_error_bound F c hc x x' hx hx' hδ
    _ ≤ (2 * Real.sqrt n / c) * (F.eps * ‖x‖ + F.tiny) :=
        mul_le_mul_of_nonneg_right hle
          (add_nonneg (mul_nonneg F.eps_nonneg (norm_nonneg x)) F.tiny_nonneg)

end Lattice
