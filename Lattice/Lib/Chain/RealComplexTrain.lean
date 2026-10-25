import Mathlib

/-!
# LATTICE: 复数域上的梯度下降（ℂ ≅ ℝ²）

神经网络里的复数训练（复权重、FFT 卷积、RoPE 的复数形式、以及"把 ℝ² 当成 ℂ"的
等变网络）本质上是在 ℂ 上做梯度下降。本文件把这一层形式化，并给出三条硬结论：

  1. **ℂ 内积**（= `Re(z·conj w)`）的基本代数性质，以及 Cauchy–Schwarz
     `cInner z w ^ 2 ≤ normSq z * normSq w`；
  2. **坐标分解**：复数一步 `cgd eta g z = z - (eta:ℂ)*g` 在实部/虚部上
     **恰好是两次独立的实数梯度下降**（`cgd_re` / `cgd_im`）；
  3. **收缩性**：若梯度映射的实部与虚部分别是 `L`-Lipschitz 的，则一步更新的
     范数平方收缩常数为 `(1 + eta·L)²`：
       `normSq (cgd eta g z - cgd eta g w) ≤ (1 + eta·L)^2 * normSq (z - w)`。

**诚实边界**：
- 本文件给出的收缩常数是 **`(1 + eta·L)²`（增长型）**，它**不是**收缩到 0；真正的
  收敛需要"梯度范数随距离衰减"或"损失强凸"的额外结构。与 `RealConvergence.contraction_converges`
  的衔接（把 `(1+eta·L)² < 1` 与不动点存在性连起来）**未做**，已在 docstring 标注；
- 只做**定步长**梯度下降；**共轭梯度方向 / Wirtinger 微积分（把 ℂ 当作标量域求导）
  未做**——本文件的立场是"ℂ 只是 ℝ² 的记号"，不引入 Wirtinger 导数；
- 梯度映射 `g` 是**抽象给定**的（模型无关），不构造任何具体损失的梯度。

无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 复数内积 -/

/-- ℂ ≅ ℝ² 上的实内积（ℝ-双线性，仅对**实**标量齐次，见 `cInner_smul_real_left`；
对 ℂ-标量**不**齐次，故不是 ℂ 上的内积）：`cInner z w = Re(z)·Re(w) + Im(z)·Im(w)`
（等于 `Re(z·conj w)`）。 -/
def cInner (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

/-- `cInner` 与 `Re(z·conj w)` 一致。 -/
theorem cInner_eq_re_mul_conj (z w : ℂ) : cInner z w = (z * starRingEnd ℂ w).re := by
  unfold cInner
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- 对称性。 -/
theorem cInner_comm (z w : ℂ) : cInner z w = cInner w z := by
  unfold cInner
  ring

/-- 自身内积等于 `normSq`（即模的平方）。 -/
theorem cInner_self_eq_normSq (z : ℂ) : cInner z z = Complex.normSq z := by
  unfold cInner
  rw [Complex.normSq_apply]

/-- 自身内积非负。 -/
theorem cInner_self_nonneg (z : ℂ) : 0 ≤ cInner z z := by
  rw [cInner_self_eq_normSq]
  exact Complex.normSq_nonneg z

/-- 加法左线性。 -/
theorem cInner_add_left (z₁ z₂ w : ℂ) :
    cInner (z₁ + z₂) w = cInner z₁ w + cInner z₂ w := by
  unfold cInner
  rw [Complex.add_re, Complex.add_im]
  ring

/-- 实标量左齐次。 -/
theorem cInner_smul_real_left (r : ℝ) (z w : ℂ) :
    cInner ((r : ℂ) * z) w = r * cInner z w := by
  unfold cInner
  rw [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Cauchy–Schwarz（复数版）**：`⟨z,w⟩² ≤ ‖z‖²‖w‖²`。 -/
theorem cInner_sq_le (z w : ℂ) :
    cInner z w ^ 2 ≤ Complex.normSq z * Complex.normSq w := by
  unfold cInner
  rw [Complex.normSq_apply, Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re * w.im - z.im * w.re)]

/-- 由 Cauchy–Schwarz 得到的内积上界（用模的乘积表述）。 -/
theorem cInner_le_abs_mul_abs (z w : ℂ) :
    cInner z w ≤ Complex.abs z * Complex.abs w := by
  have h := cInner_sq_le z w
  have hb : 0 ≤ Complex.abs z * Complex.abs w :=
    mul_nonneg (Complex.abs.nonneg z) (Complex.abs.nonneg w)
  have h2 : cInner z w ^ 2 ≤ (Complex.abs z * Complex.abs w) ^ 2 := by
    rw [mul_pow, Complex.sq_abs, Complex.sq_abs]
    exact h
  exact le_of_sq_le_sq h2 hb

/-! ## 复数梯度下降步与坐标分解 -/

/-- 复数梯度下降一步：`z ↦ z - eta · g z`。 -/
def cgd (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ := z - (eta : ℂ) * g z

/-- **实部就是实数梯度下降**。 -/
theorem cgd_re (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    (cgd eta g z).re = z.re - eta * (g z).re := by
  unfold cgd
  rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **虚部就是实数梯度下降**。 -/
theorem cgd_im (eta : ℝ) (g : ℂ → ℂ) (z : ℂ) :
    (cgd eta g z).im = z.im - eta * (g z).im := by
  unfold cgd
  rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- 零梯度是不动点。 -/
theorem cgd_zero_grad (eta : ℝ) (z : ℂ) : cgd eta (fun _ => 0) z = z := by
  unfold cgd
  simp

/-- 零步长是不动点。 -/
theorem cgd_zero_eta (g : ℂ → ℂ) (z : ℂ) : cgd 0 g z = z := by
  unfold cgd
  simp

/-! ## 一维收缩引理与复数收缩 -/

/-- 一维收缩平方界：`|B| ≤ L|A|`、`eta, L ≥ 0` ⟹ `(A - eta·B)² ≤ (1 + eta·L)²·A²`。 -/
theorem scalar_contraction_sq {A B eta L : ℝ} (heta : 0 ≤ eta) (_hL : 0 ≤ L)
    (hB : |B| ≤ L * |A|) :
    (A - eta * B) ^ 2 ≤ (1 + eta * L) ^ 2 * A ^ 2 := by
  have h1 : A - eta * B ≤ |A| + eta * |B| := by
    have h2 := neg_le_abs (eta * B)
    rw [abs_mul, abs_of_nonneg heta] at h2
    have h3 := le_abs_self A
    linarith
  have h2 : eta * B - A ≤ |A| + eta * |B| := by
    have h3 := le_abs_self (eta * B)
    rw [abs_mul, abs_of_nonneg heta] at h3
    have h4 := neg_le_abs A
    linarith
  have hc : |A - eta * B| ≤ |A| + eta * |B| := abs_sub_le_iff.mpr ⟨h1, h2⟩
  have hb : |A| + eta * |B| ≤ (1 + eta * L) * |A| := by
    have h5 := mul_le_mul_of_nonneg_left hB heta
    have h6 : 0 ≤ |A| := abs_nonneg A
    nlinarith [h5, h6]
  have hle : |A - eta * B| ≤ (1 + eta * L) * |A| := le_trans hc hb
  calc (A - eta * B) ^ 2 = |A - eta * B| ^ 2 := (sq_abs _).symm
    _ ≤ ((1 + eta * L) * |A|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = (1 + eta * L) ^ 2 * |A| ^ 2 := by ring
    _ = (1 + eta * L) ^ 2 * A ^ 2 := by rw [sq_abs]

/-- **复数收缩**：实部与虚部分别 `L`-Lipschitz ⟹ 一步更新的范数平方增长不超过
`(1 + eta·L)²` 倍。 -/
theorem cgd_contraction_sq {g : ℂ → ℂ} {eta L : ℝ} (heta : 0 ≤ eta) (hL : 0 ≤ L)
    (hre : ∀ z w : ℂ, |(g z).re - (g w).re| ≤ L * |z.re - w.re|)
    (him : ∀ z w : ℂ, |(g z).im - (g w).im| ≤ L * |z.im - w.im|) (z w : ℂ) :
    Complex.normSq (cgd eta g z - cgd eta g w)
      ≤ (1 + eta * L) ^ 2 * Complex.normSq (z - w) := by
  have hrediff : (cgd eta g z - cgd eta g w).re
      = (z.re - w.re) - eta * ((g z).re - (g w).re) := by
    rw [Complex.sub_re, cgd_re, cgd_re]
    ring
  have himdiff : (cgd eta g z - cgd eta g w).im
      = (z.im - w.im) - eta * ((g z).im - (g w).im) := by
    rw [Complex.sub_im, cgd_im, cgd_im]
    ring
  have h1 := scalar_contraction_sq (A := z.re - w.re) (B := (g z).re - (g w).re)
    heta hL (hre z w)
  have h2 := scalar_contraction_sq (A := z.im - w.im) (B := (g z).im - (g w).im)
    heta hL (him z w)
  rw [Complex.normSq_apply, hrediff, himdiff, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  nlinarith [h1, h2]

end Lattice
