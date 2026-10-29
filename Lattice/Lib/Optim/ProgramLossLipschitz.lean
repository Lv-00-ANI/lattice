import Mathlib
import Lattice.Runtime.ProgramLipschitz
import Lattice.Lib.Penalty.QuadraticLocallyLipschitz

/-!
# `Lattice.Lib.Optim.ProgramLossLipschitz` — **程序损失的 Lipschitz 界：两条独立链在此汇合**

## 为什么这个文件是「桥」

库里此前有两段互不相连的机器：

| 段 | 内容 | 在哪 |
|:--|:--|:--|
| **A** | `evalProgram` 的 Lipschitz 界：`|Δ| ≤ L ^ p.length · δ` | `Runtime/ProgramLipschitz`（第 77 轮） |
| **B** | 平方和在有界集上的 Lipschitz 界：`2R · ∑ |Δ|` | `Lib/Penalty/QuadraticLocallyLipschitz`（第 79 轮） |

**B 一直没有消费者，A 也没有。** 本文件把两者接起来：**「程序 + 平方损失」作为函数值也是 Lipschitz 的**，
**常数是 `4·B·n·L ^ p.length`**。

## 为什么是【函数值】的 Lipschitz，而不是【梯度】的光滑性

`Lib/Optim/RealGLUTraining.gd_descent_of_smooth` 需要 `Smooth C loss g`，**那要求 `g` 是 `loss` 的梯度**。
**本库没有「程序的梯度」**（`P2-02` 的 AD 未做）。**所以那座桥不能按 `Smooth` 写。**

**能写的是更弱但成立的东西**：`|loss x − loss x'| ≤ C · δ`，**其中 `δ` 是输入的逐分量偏差。**
**这不是收敛工具**（收敛需要梯度），**而是「扰动下损失如何变化」**——**鲁棒性、证书、以及
「训练步长不能保证下降，但能保证损失变化有界」这类陈述的前件。**

## 假设的形状

- **`B`** 同时界住 **程序输出** 与 **目标**：`|evalProgram x p j| ≤ B`、`|target j| ≤ B`。
  **这是必要前提**：平方损失对输出的绝对大小二次敏感，**没有 `B` 它无界**（第 78 轮已证 `sq_not_lipschitz`）。
- **`L`** 是每层 Lipschitz 常数的公共上界，`IsLipschitzInstr L i`。

⚠ **`B` 不能从 `δ` 推出**：`evalProgram x p` 与 `evalProgram x' p` 可以同时很大，
**而 `δ` 只约束它们的差。** 这与 `DistLipschitz` 里 `hpts` 必要是同一件事。
-/

namespace Lattice.Lib.Optim.ProgramLossLipschitz

open Lattice.Lift.ProgramAST

/-- ⭐⭐ **平方损失是 Lipschitz 的**：程序输出与目标之差被 `B` 界住时，

`|∑ j, (out x j − t j)² − ∑ j, (out x' j − t j)²| ≤ 4·B·n·(L ^ p.length · δ)`。

**两条链在这里汇合**：
- `evalProgram_lipschitz` 给出每个分量的差 `≤ L ^ p.length · δ`；
- `sum_sq_lipschitz_on_bounded` 把它抬到平方和上。

**`4·B·n`** = `2·R·n` 其中 `R = 2B`（因为差的每个分量被 `2B` 界住）。 -/
theorem programLoss_lipschitz {n : ℕ} (p : LayerProgram n) {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (h : ∀ i ∈ p, IsLipschitzInstr L i) (target : Fin n → ℝ)
    (x x' : Fin n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hx : ∀ k : Fin n, |x k - x' k| ≤ δ)
    (hBx : ∀ j : Fin n, |evalProgram x p j| ≤ B)
    (hBx' : ∀ j : Fin n, |evalProgram x' p j| ≤ B)
    (ht : ∀ j : Fin n, |target j| ≤ B) :
    |(∑ j, (evalProgram x p j - target j) ^ 2)
        - (∑ j, (evalProgram x' p j - target j) ^ 2)|
      ≤ 4 * B * (n : ℝ) * (L ^ p.length * δ) := by
  -- the two difference vectors
  set f : Fin n → ℝ := fun j => evalProgram x p j - target j with hf
  set g : Fin n → ℝ := fun j => evalProgram x' p j - target j with hg
  -- each component is bounded by `2B`
  have hBf : ∀ j : Fin n, |f j| ≤ 2 * B := by
    intro j
    have h1 : |f j| ≤ |evalProgram x p j| + |target j| := by
      have := abs_add (evalProgram x p j) (-(target j))
      simpa only [hf, sub_eq_add_neg, abs_neg] using this
    linarith [hBx j, ht j]
  have hBg : ∀ j : Fin n, |g j| ≤ 2 * B := by
    intro j
    have h1 : |g j| ≤ |evalProgram x' p j| + |target j| := by
      have := abs_add (evalProgram x' p j) (-(target j))
      simpa only [hg, sub_eq_add_neg, abs_neg] using this
    linarith [hBx' j, ht j]
  -- the per-component difference is bounded by the program's Lipschitz bound
  have hstep : ∀ j : Fin n, |f j - g j| ≤ L ^ p.length * δ := by
    intro j
    have := evalProgram_lipschitz (n := n) L hL p h x x' δ hδ hx j
    simpa only [hf, hg, sub_sub_sub_cancel_right] using this
  -- the sum of squares is `2·(2B)`-Lipschitz in the difference vector
  have hmain := Lattice.Lib.Penalty.sum_sq_lipschitz_on_bounded f g (R := 2 * B)
    (by linarith) hBf hBg
  -- and the difference vector's mass is at most `n` times the per-component bound
  have hmass : ∑ j, |f j - g j| ≤ (n : ℝ) * (L ^ p.length * δ) := by
    calc ∑ j, |f j - g j| ≤ ∑ _j : Fin n, L ^ p.length * δ :=
          Finset.sum_le_sum (fun j _ => hstep j)
      _ = (n : ℝ) * (L ^ p.length * δ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfac : 0 ≤ 2 * (2 * B) := by linarith
  calc |(∑ j, (evalProgram x p j - target j) ^ 2)
        - (∑ j, (evalProgram x' p j - target j) ^ 2)|
      = |(∑ j, (f j) ^ 2) - (∑ j, (g j) ^ 2)| := by
        simp only [hf, hg]
    _ ≤ 2 * (2 * B) * ∑ j, |f j - g j| := hmain
    _ ≤ 2 * (2 * B) * ((n : ℝ) * (L ^ p.length * δ)) :=
        mul_le_mul_of_nonneg_left hmass hfac
    _ = 4 * B * (n : ℝ) * (L ^ p.length * δ) := by ring

end Lattice.Lib.Optim.ProgramLossLipschitz
