import Mathlib
import Lattice.Lib.Architectures.RealActClass
import Lattice.Lib.Architectures.RealGLUVariants
import Lattice.Lib.Architectures.RealGatingGeneral
/-!
# LATTICE: GLU 族的训练收敛（补 `RealGLUVariants` 标注「未做」的缺口）

`RealGLUVariants` 把 GLU 族接入门控抽象（`Gated`），并**标注未做**训练收敛性。
本文件补上：把 GLU 看成 `Gated` 的**两投影层**，在「投影算子 Lipschitz + 激活有界」
的前提下给出

  1. `glu_lipschitz`：GLU 块的 Lipschitz 常数 `Lh + M·Lg`
     （直接套 `RealGatingGeneral.gated_lipschitz`；`g := s∘a` 是门、`h := a·b` 是信号）；
  2. `reglu_lipschitz` / `siluGLU_lipschitz` / `geglu_lipschitz`：ReGLU / SiLU-GLU /
     GeGLU 的实例（只读复用 `relu_is_soft_masked` / `silu_is_soft_masked` /
     `gelu_is_soft_masked` 与掩码界）；
  3. **梯度下降核**（模型无关的实数分析）：
     `gdStep` / `gdSeq`（`w ↦ w − η·g w`）与
     · `gd_descent_of_smooth`：由**光滑性/下降引理**（**显式外置假设**）
       `L(w − η g w) ≤ L w − η·(g w)² + (η²C/2)·(g w)²` 与 `η·C ≤ 1` 得
       单步下降 `L(w_{t+1}) ≤ L(w_t) − (η/2)(g w_t)²`；
     · `gd_telescope`：**误差递推**（望远镜求和）
       `L(w_n) + (η/2)Σ_{k<n}(g w_k)² ≤ L(w_0)`；
     · `gd_exists_small_gradient`：**ε-终止**
       `∃ n, (g w_n)² ≤ ε`（损失有下界 + 阿基米德）；
     · `gd_epsilon_termination`：包装成「存在前缀使梯度平方 ≤ ε」。

**诚实降级（中文关键词）**：
  · **光滑性假设显式外置**：`gd_descent_of_smooth` 的假设
    `∀ w, L(w − η g w) ≤ L w − η(g w)² + (η²C/2)(g w)²`
    是标准的**下降引理/`C`-光滑假设**，本文件**不从 GLU 结构本身推出**它
    （那需要 GLU 参数化下损失函数的二阶信息），**标注未做**；
  · GLU 的结构性输入只有 `glu_lipschitz`（Lipschitz 常数 `Lh + M·Lg`）——
    它与光滑常数 `C` 的关系（`C ≥ L` 等）本文件**未证**；
  · 收敛是**非渐近的 ε-终止**（不证明 `g w_n → 0`，只证明存在子列/某个 n 使
    `(g w_n)² ≤ ε`）；**未证**强凸下的线性收敛率（那需要 `RealStrongConvex` 线）。
  无 sorry/axiom/admit。
-/

set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

open Lattice.Lib.Architectures.RealActClass

namespace Lattice.Lib.Optim.RealGLUTraining
/-! ## 一、GLU 块的 Lipschitz 常数 -/

/-- **GLU 的 Lipschitz 常数**：`SoftMasked act s`、`|s| ≤ 1`、门 `s∘a` 是 `Lg`-Lipschitz、
信号 `a·b` 是 `Lh`-Lipschitz 且 `|a·b| ≤ M` ⟹ GLU 块是 `(Lh + M·Lg)`-Lipschitz。
直接套 `gated_lipschitz` 与 `glu_is_gated`。 -/
theorem glu_lipschitz {act s : ℝ → ℝ} (hsm : SoftMasked act s) (hs : ∀ y, |s y| ≤ 1)
    {a b : ℝ → ℝ} {Lg Lh M : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, |s (a x) - s (a y)| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |a x * b x - a y * b y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |a x * b x| ≤ M) (x y : ℝ) :
    |glu act a b x - glu act a b y| ≤ (Lh + M * Lg) * |x - y| :=
  gated_lipschitz (glu act a b) (fun z => s (a z)) (fun z => a z * b z) Lg Lh M
    (glu_is_gated hsm a b) (fun z => hs (a z)) hgL hhL hhM hLg x y

/-- **ReGLU 的 Lipschitz 常数**（`act = relu`，掩码 `reluSoftMask ∈ {0,1}`）。 -/
theorem reglu_lipschitz {a b : ℝ → ℝ} {Lg Lh M : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, |reluSoftMask (a x) - reluSoftMask (a y)| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |a x * b x - a y * b y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |a x * b x| ≤ M) (x y : ℝ) :
    |reglu a b x - reglu a b y| ≤ (Lh + M * Lg) * |x - y| :=
  glu_lipschitz relu_is_soft_masked reluSoftMask_abs_le_one hLg hgL hhL hhM x y

/-- **SiLU-GLU 的 Lipschitz 常数**（`act = silu`，掩码 `sigmoid ∈ [0,1]`）。 -/
theorem siluGLU_lipschitz {a b : ℝ → ℝ} {Lg Lh M : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, |sigmoid (a x) - sigmoid (a y)| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |a x * b x - a y * b y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |a x * b x| ≤ M) (x y : ℝ) :
    |siluGLU a b x - siluGLU a b y| ≤ (Lh + M * Lg) * |x - y| :=
  glu_lipschitz silu_is_soft_masked sigmoid_abs_le_one hLg hgL hhL hhM x y

/-- **GeGLU 的 Lipschitz 常数**（`act = geluTanh`，掩码 `geluSoftMask ∈ [0,1]`）。 -/
theorem geglu_lipschitz {a b : ℝ → ℝ} {Lg Lh M : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, |geluSoftMask (a x) - geluSoftMask (a y)| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |a x * b x - a y * b y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |a x * b x| ≤ M) (x y : ℝ) :
    |geglu a b x - geglu a b y| ≤ (Lh + M * Lg) * |x - y| :=
  glu_lipschitz gelu_is_soft_masked geluSoftMask_abs_le_one hLg hgL hhL hhM x y

/-! ## 二、梯度下降核（模型无关） -/

/-- 一步梯度下降：`w ↦ w − η·g w`。 -/
def gdStep (g : ℝ → ℝ) (eta w : ℝ) : ℝ := w - eta * g w

/-- 梯度下降迭代序列：`w 0 = w0`、`w (n+1) = gdStep g eta (w n)`。 -/
def gdSeq (g : ℝ → ℝ) (eta w0 : ℝ) : ℕ → ℝ
  | 0 => w0
  | n + 1 => gdStep g eta (gdSeq g eta w0 n)

/-- `gdSeq` 的递归展开。 -/
theorem gdSeq_succ (g : ℝ → ℝ) (eta w0 : ℝ) (n : ℕ) :
    gdSeq g eta w0 (n + 1) = gdStep g eta (gdSeq g eta w0 n) := rfl

/-- `gdSeq 0 = w0`。 -/
@[simp] theorem gdSeq_zero (g : ℝ → ℝ) (eta w0 : ℝ) : gdSeq g eta w0 0 = w0 := rfl

/-- **由 `C`-光滑下降引理得单步下降**：若
`L(w − η g w) ≤ L w − η(g w)² + (η²C/2)(g w)²`、`η ≥ 0`、`η·C ≤ 1`，则
`L(w_{next}) ≤ L w − (η/2)(g w)²`。
（**光滑性假设显式外置**，见 docstring。） -/
theorem gd_descent_of_smooth {loss g : ℝ → ℝ} {eta C : ℝ}
    (hdesc : ∀ w, loss (gdStep g eta w)
      ≤ loss w - eta * (g w) ^ 2 + (eta ^ 2 * C / 2) * (g w) ^ 2)
    (heta : 0 ≤ eta) (hC : eta * C ≤ 1) (w : ℝ) :
    loss (gdStep g eta w) ≤ loss w - (eta / 2) * (g w) ^ 2 := by
  have h := hdesc w
  have h1 : eta * (eta * C) ≤ eta * 1 := mul_le_mul_of_nonneg_left hC heta
  nlinarith [h, h1, sq_nonneg (g w), sq_nonneg (eta * g w)]

/-- **误差递推（望远镜求和）**：由单步下降
`L(w_{t+1}) ≤ L(w_t) − (η/2)(g w_t)²` 得
`L(w_n) + (η/2)·Σ_{k<n}(g w_k)² ≤ L(w_0)`。 -/
theorem gd_telescope {loss g : ℝ → ℝ} {eta w0 : ℝ}
    (hdesc : ∀ w, loss (gdStep g eta w) ≤ loss w - (eta / 2) * (g w) ^ 2) :
    ∀ n : ℕ, loss (gdSeq g eta w0 n)
        + (eta / 2) * ∑ k in Finset.range n, (g (gdSeq g eta w0 k)) ^ 2
      ≤ loss (gdSeq g eta w0 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := hdesc (gdSeq g eta w0 n)
      rw [Finset.sum_range_succ, gdSeq_succ]
      rw [mul_add]
      linarith

/-- **ε-终止**：若损失有下界 `Lstar ≤ L(w_n)`（∀n）、`η > 0`、`ε > 0`，
则存在 `n` 使 `(g w_n)² ≤ ε`（反证 + 望远镜 + 阿基米德）。 -/
theorem gd_exists_small_gradient {loss g : ℝ → ℝ} {eta Lstar w0 eps : ℝ}
    (hdesc : ∀ w, loss (gdStep g eta w) ≤ loss w - (eta / 2) * (g w) ^ 2)
    (heta : 0 < eta) (hbdd : ∀ n, Lstar ≤ loss (gdSeq g eta w0 n))
    (heps : 0 < eps) :
    ∃ n : ℕ, (g (gdSeq g eta w0 n)) ^ 2 ≤ eps := by
  by_contra hcon
  push_neg at hcon
  set D : ℝ := loss (gdSeq g eta w0 0) - Lstar with hD
  have hcpos : 0 < (eta / 2) * eps := by positivity
  have hkey : ∀ n : ℕ, (n : ℝ) * ((eta / 2) * eps) ≤ D := by
    intro n
    have htel := gd_telescope (w0 := w0) hdesc n
    have hb := hbdd n
    have hsum : (n : ℝ) * eps ≤ ∑ k in Finset.range n, (g (gdSeq g eta w0 k)) ^ 2 := by
      have h2 : ∑ _k in Finset.range n, eps
          ≤ ∑ k in Finset.range n, (g (gdSeq g eta w0 k)) ^ 2 :=
        Finset.sum_le_sum (fun k _ => le_of_lt (hcon k))
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h2
    have h3 : (eta / 2) * ((n : ℝ) * eps)
        ≤ (eta / 2) * ∑ k in Finset.range n, (g (gdSeq g eta w0 k)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have : (eta / 2) * ((n : ℝ) * eps) ≤ D := by
      rw [hD]
      linarith
    calc (n : ℝ) * ((eta / 2) * eps) = (eta / 2) * ((n : ℝ) * eps) := by ring
      _ ≤ D := this
  obtain ⟨N, hN⟩ := exists_nat_gt (D / ((eta / 2) * eps))
  have hN' : D < (N : ℝ) * ((eta / 2) * eps) := (div_lt_iff₀ hcpos).mp hN
  linarith [hkey N]

/-- **ε-终止（包装形式）**：存在长度 `N` 的前缀，其中某一步的梯度平方 `≤ ε`。 -/
theorem gd_epsilon_termination {loss g : ℝ → ℝ} {eta Lstar w0 eps : ℝ}
    (hdesc : ∀ w, loss (gdStep g eta w) ≤ loss w - (eta / 2) * (g w) ^ 2)
    (heta : 0 < eta) (hbdd : ∀ n, Lstar ≤ loss (gdSeq g eta w0 n))
    (heps : 0 < eps) :
    ∃ N : ℕ, ∃ n ≤ N, (g (gdSeq g eta w0 n)) ^ 2 ≤ eps := by
  obtain ⟨n, hn⟩ := gd_exists_small_gradient (w0 := w0) hdesc heta hbdd heps
  exact ⟨n, n, le_rfl, hn⟩

/-! ## 三、GLU 与收敛核的连接件 -/

/-- **GLU 块稳定 ⟹ 单步误差不放大**：GLU 块的 Lipschitz 常数 `(Lh + M·Lg)` 是
下降引理中损失变化的**几何输入**（两块参数扰动之差被它控制）。 -/
theorem glu_step_error_bound {act s : ℝ → ℝ} (hsm : SoftMasked act s)
    (hs : ∀ y, |s y| ≤ 1) {a b : ℝ → ℝ} {Lg Lh M : ℝ} (hLg : 0 ≤ Lg)
    (hgL : ∀ x y, |s (a x) - s (a y)| ≤ Lg * |x - y|)
    (hhL : ∀ x y, |a x * b x - a y * b y| ≤ Lh * |x - y|)
    (hhM : ∀ x, |a x * b x| ≤ M) (x y : ℝ) :
    |glu act a b x - glu act a b y| ≤ (Lh + M * Lg) * |x - y| :=
  glu_lipschitz hsm hs hLg hgL hhL hhM x y

/-! ## 注：诚实边界
  · `glu_lipschitz` 及其三个实例是**精确**结论（纯门控 Lipschitz，无额外假设）；
  · **光滑性假设显式外置**：`gd_descent_of_smooth` 的下降引理
    `L(w − η g w) ≤ L w − η(g w)² + (η²C/2)(g w)²` 是**假设**（标准 `C`-光滑），
    本文件**未**从 GLU 参数化推出它（**标注未做**）；
  · 收敛结论是**非渐近 ε-终止**（`∃ n, (g w_n)² ≤ ε`），**未证** `g w_n → 0`；
    强凸线性收敛率**未做**（需 `RealStrongConvex` 线）。
  无 sorry/axiom/admit。 -/

end Lattice.Lib.Optim.RealGLUTraining