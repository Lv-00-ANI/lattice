import Mathlib

/-!
# `Lattice.Lib.Optim.RealVectorGD` — **标准 GD 收敛链的向量化**

## 为什么单独一个文件

`Lib/Optim/RealGLUTraining.lean` 里已经有一整套标量 GD 收敛链：

| 定理 | 内容 |
|:--|:--|
| `gdStep` / `gdSeq` | `w ↦ w − η·g w` 与其迭代，**在 `ℝ` 上** |
| `gd_descent_of_smooth` | 光滑性外置为假设 ⇒ 单步下降 `− (η/2)(gw)²` |
| `gd_telescope` | `L(w_n) + (η/2)Σ_{k<n}(gw_k)² ≤ L(w_0)` |
| `gd_exists_small_gradient` | ε-终止 |

**本文件把这四条推广到 `Fin n → ℝ`。** 不修改原文件——**它的载体是 `ℝ`，混入向量会让它主题模糊**；
而且**标量版与向量版都保留，是因为它们各自是可读的**：标量版是小而完整的证明，向量版多一层求和。

## 推广要换哪一个量

**损失仍是标量**（`loss : (Fin n → ℝ) → ℝ`），**所以望远镜与阿基米德论证完全不变。**
**唯一要换的是「梯度平方」这个量**：从 `(g w) ^ 2` 变成

```lean
normSq v = ∑ i, (v i) ^ 2
```

⚠ **这与库里的 `sqNorm`（`Lib/Linear/PenaltyVector`）是同一个函数。** 本文件不 import 它，
**因为那会让 `Lib/Optim` 依赖 `Lib/Linear` 为了一行定义**；**而 `normSq` 在这里是局部的、
专门服务于 GD 论证的记号。** 若将来有人要合并，**它们逐字相同，合并是机械的。**

**关键技巧**：`nlinarith` 把 `normSq (g w)` 当作**原子**，所以标量版里
`nlinarith [h, h1, sq_nonneg (g w)]` 在向量版里变成 `nlinarith [h, h1, normSq_nonneg (g w)]`——
**证明的形状完全不变。**
-/

namespace Lattice.Lib.Optim.VectorGD

/-- **向量平方范数**：`∑ i, (v i) ^ 2`。 -/
noncomputable def normSq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- **平方范数非负**——`nlinarith` 需要它作为原子事实。 -/
theorem normSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ normSq v :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

/-- 一步梯度下降（向量）：`w ↦ w − η·g w`，逐分量。 -/
noncomputable def vecGdStep {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) (eta : ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w i - eta * g w i

/-- 梯度下降迭代序列（向量）。 -/
noncomputable def vecGdSeq {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) (eta : ℝ)
    (w0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => w0
  | k + 1 => vecGdStep g eta (vecGdSeq g eta w0 k)

/-- `vecGdSeq` 的递归展开。 -/
theorem vecGdSeq_succ {n : ℕ} (g : (Fin n → ℝ) → (Fin n → ℝ)) (eta : ℝ)
    (w0 : Fin n → ℝ) (k : ℕ) :
    vecGdSeq g eta w0 (k + 1) = vecGdStep g eta (vecGdSeq g eta w0 k) := rfl

/-- ⭐ **由 `C`-光滑下降引理得单步下降**——`gd_descent_of_smooth` 的向量版。

**证明与标量版逐字相同**：`nlinarith` 只看见 `normSq (g w)` 这个原子。 -/
theorem vec_gd_descent_of_smooth {n : ℕ} {loss : (Fin n → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin n → ℝ)} {eta C : ℝ}
    (hdesc : ∀ w, loss (vecGdStep g eta w)
      ≤ loss w - eta * normSq (g w) + (eta ^ 2 * C / 2) * normSq (g w))
    (heta : 0 ≤ eta) (hC : eta * C ≤ 1) (w : Fin n → ℝ) :
    loss (vecGdStep g eta w) ≤ loss w - (eta / 2) * normSq (g w) := by
  have h := hdesc w
  have h1 : eta * (eta * C) ≤ eta * 1 := mul_le_mul_of_nonneg_left hC heta
  nlinarith [h, h1, normSq_nonneg (g w)]

/-- ⭐⭐ **误差递推（望远镜求和）**——`gd_telescope` 的向量版。

**结构完全不变**：损失是标量，所以 `linarith` 只看 `normSq` 这个原子。 -/
theorem vec_gd_telescope {n : ℕ} {loss : (Fin n → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin n → ℝ)} {eta : ℝ} {w0 : Fin n → ℝ}
    (hdesc : ∀ w, loss (vecGdStep g eta w) ≤ loss w - (eta / 2) * normSq (g w)) :
    ∀ m : ℕ, loss (vecGdSeq g eta w0 m)
        + (eta / 2) * ∑ k in Finset.range m, normSq (g (vecGdSeq g eta w0 k))
      ≤ loss (vecGdSeq g eta w0 0) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := hdesc (vecGdSeq g eta w0 m)
      rw [Finset.sum_range_succ, vecGdSeq_succ]
      rw [mul_add]
      linarith

/-- ⭐⭐ **ε-终止**——`gd_exists_small_gradient` 的向量版。

损失有下界 + `η > 0` + `ε > 0` ⇒ 存在 `m` 使 `normSq (g w_m) ≤ ε`。
**阿基米德论证与标量版相同**：每个 `m` 都有 `m·(η/2)·ε ≤ D`，而 `m` 任意大时矛盾。 -/
theorem vec_gd_exists_small_gradient {n : ℕ} {loss : (Fin n → ℝ) → ℝ}
    {g : (Fin n → ℝ) → (Fin n → ℝ)} {eta Lstar : ℝ} {w0 : Fin n → ℝ} {eps : ℝ}
    (hdesc : ∀ w, loss (vecGdStep g eta w) ≤ loss w - (eta / 2) * normSq (g w))
    (heta : 0 < eta) (hbdd : ∀ m, Lstar ≤ loss (vecGdSeq g eta w0 m))
    (heps : 0 < eps) :
    ∃ m : ℕ, normSq (g (vecGdSeq g eta w0 m)) ≤ eps := by
  by_contra hcon
  push_neg at hcon
  -- every iterate's gradient mass exceeds `eps`, so the telescoped sum grows with `m`
  have hsum : ∀ m : ℕ, (m : ℝ) * eps
      ≤ ∑ k in Finset.range m, normSq (g (vecGdSeq g eta w0 k)) := by
    intro m
    have hconst : (m : ℝ) * eps = ∑ _k in Finset.range m, eps := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hconst]
    exact Finset.sum_le_sum (fun k _ => le_of_lt (hcon k))
  have htel := vec_gd_telescope (loss := loss) (g := g) (eta := eta) (w0 := w0) hdesc
  set D : ℝ := loss (vecGdSeq g eta w0 0) - Lstar with hD
  have hcoef : 0 < (eta / 2) * eps := by positivity
  -- the telescoped bound forces `m * ((eta/2) * eps) ≤ D` for EVERY `m`
  have hbound : ∀ m : ℕ, (m : ℝ) * ((eta / 2) * eps) ≤ D := by
    intro m
    have h1 := htel m
    have h2 := hbdd m
    have h3 := hsum m
    have h4 : (eta / 2) * ((m : ℝ) * eps)
        ≤ (eta / 2) * ∑ k in Finset.range m, normSq (g (vecGdSeq g eta w0 k)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : (eta / 2) * ∑ k in Finset.range m, normSq (g (vecGdSeq g eta w0 k)) ≤ D := by
      simp only [hD]
      linarith
    calc (m : ℝ) * ((eta / 2) * eps) = (eta / 2) * ((m : ℝ) * eps) := by ring
      _ ≤ D := le_trans h4 h5
  -- but `Nat` is unbounded, so some `m` violates it
  obtain ⟨m, hm⟩ := exists_nat_gt (D / ((eta / 2) * eps))
  have hmul : D < (m : ℝ) * ((eta / 2) * eps) := by
    have h1 : D / ((eta / 2) * eps) * ((eta / 2) * eps) = D :=
      div_mul_cancel₀ _ (ne_of_gt hcoef)
    calc D = D / ((eta / 2) * eps) * ((eta / 2) * eps) := h1.symm
      _ < (m : ℝ) * ((eta / 2) * eps) := mul_lt_mul_of_pos_right hm hcoef
  have := hbound m
  linarith

end Lattice.Lib.Optim.VectorGD
