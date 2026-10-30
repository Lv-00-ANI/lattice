import Mathlib
import Lattice.Core.Net

/-!
# `Lattice.Core.StackDerivative` — **`affineAct` 对输入的导数（`P2-02` 的第一级）**

## 为什么从这里开始

`P2-02` 要的是 `netLoss` 对**参数**的梯度。**而参数只通过 `netAct` 进入损失**，所以第一级是
**「单层的 `affineAct` 对输入可微」**——**而它的导数是 `W` 本身（作为连续线性映射）。**

## 形状

`affineAct L x = fun j => (∑ i, L.W i j * x i) + L.b j`。
**它是「线性部分 + 常数」**：

```lean
affineCLM L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)   -- 线性部分
affineAct L x = affineCLM L x + L.b            -- 等式
HasFDerivAt (affineAct L) (affineCLM L) x      -- 导数
```

⚠ **`x` 是【输入】，不是参数。** **本文件证的是「对输入」，而 `P2-02` 真正要的是「对 `(W, b)`」**——
**两者的线性映射不同（对输入是 `W` 作用，对 `(W,b)` 是 `x` 作用），所以这是第一级而不是全部。**

⚠ **`relu` 的折点**：本文件**只处理仿射层**，所以不受 `relu` 在 `0` 处不可导的影响。
**但任何把 `netAct` 当成「处处可微」的陈述都必须在 `relu` 的折点外成立**——**那条前提还没有写。**
-/

namespace Lattice.Core

/-- **单层的线性部分**：`x ↦ fun j => ∑ i, W i j * x i`。

**作为连续线性映射**——连续性来自「有限个「常数乘坐标投影」之和」。 -/
noncomputable def affineCLM {n : ℕ} (L : AffineLayer (Fin n)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) where
  toFun := fun x j => ∑ i, L.W i j * x i
  map_add' := by
    intro x y
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  cont := by
    fun_prop

/-- **`affineAct` 是「线性部分 + 偏置」**——`affineCLM` 之所以有用，全靠这条等式。 -/
theorem affineAct_eq_affineCLM_add {n : ℕ} (L : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    affineAct L x = affineCLM L x + L.b :=
  rfl

/-- ⭐ **`affineAct L` 对输入可微**，导数是 `affineCLM L`。

**由「线性映射的导数 + 加常数」得到**，而 `affineAct` 按定义就是那两个的复合。 -/
theorem hasFDerivAt_affineAct {n : ℕ} (L : AffineLayer (Fin n)) (x : Fin n → ℝ) :
    HasFDerivAt (affineAct L) (affineCLM L) x := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => affineCLM L y + L.b) (affineCLM L) x :=
    (affineCLM L).hasFDerivAt.add_const (L.b)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun y => (affineAct_eq_affineCLM_add L y).symm))

end Lattice.Core
