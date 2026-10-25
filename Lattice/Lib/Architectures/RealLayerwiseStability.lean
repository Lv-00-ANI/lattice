import Mathlib

/-!
# LATTICE: 残差流的**谱范数版**逐层稳定性（架构方向，W8-3）

## 建立什么

`RealModelChain` 走的是「块复合的**函数** Lipschitz 常数连乘」路线。本文件做的是
**结构不同**的一件事：把残差流 `z_{l+1} = z_l + F_l(z_l)` 的**线性化**写成
`I + J_l`（`J_l` 是**连续线性算子**），并对**算子范数**给出：

1. `resJac_opNorm_le`：`‖I + J‖ ≤ 1 + ‖J‖`（单层砖块，`J = 0` 时取等）；
2. `resJac_chain_le`：**链式谱放大界**——按**递归**（避开 `Finset.prod` 对
   `CommMonoid` 的要求，因算子复合**不交换**）定义复合算子链，
   证明 `‖Chain m‖ ≤ ∏ (1 + a_l)`；
3. ⭐ `weierstrass_prod_le`（**核心新增**）：`a_l ≥ 0`、`Σ a_l < 1` ⟹
   `∏(1 + a_l) ≤ 1/(1 - Σ a_l)`——**和 vs 积的转换**（纯标量）；
4. ⭐ `resJac_chain_le_inv_one_sub_sum`：2 与 3 复合，
   **`Σ a_l < 1` 时残差流的谱放大一致有界**（与层数 `m` 无关）；
5. `resJac_chain_le_exp_sum`：`∏(1+a_l) ≤ exp(Σ a_l)`（**不要求 `Σ a_l < 1`**）；
6. `resJac_each_lt_one`：由 `0 ≤ a_l` 与 `Σ a_l < 1` **推出** `a_l < 1`；
7. `resJac_growth_comparison`：残差链 `∏(1+a_l)` vs 裸链 `∏ a_l` 的**方向性**对照。

## 依赖什么

纯 `Mathlib`。**不** import 正在被改动的模块。

## 与 `RealModelChain` **不重复**的具体说明

- `RealModelChain`：`‖Block(x) - Block(y)‖ ≤ Lb·‖x - y‖`（**逐点**、**函数** Lipschitz）；
- 本文件：`‖Chain m‖ ≤ …`（**线性算子复合**、**算子范数**），
  核心结论 `∏(1+a_l) ≤ 1/(1 - Σa_l)` 是**和 ⟹ 积有界**的转换——
  `RealModelChain` 只有 `Lb^m` 纯乘积，**没有**这一条。

## 不做什么（诚实边界）

- **不**声称「残差流 = 线性化」：`J l` 是**显式给定**的连续线性算子，
  其与真实非线性前向的关系**未**证明；
- **不**涉及激活函数的具体 Lipschitz 常数、BatchNorm / LayerNorm 的谱效应；
- **不**涉及无限层（全部是**有限** `m` 步递归）。

## ⚠ 边界取等检查

- `Σ a_l < 1` **必须严格**：`Σ a_l = 1` 时右端 `1/(1-1) = 1/0` 是垃圾值，
  而左端 `∏(1+a_l) ≥ 1 + Σ a_l = 2 > 1`——**取等号处命题为假**。
  见证：`m = 1`、`a_0 = 1`、`J_0 = 1`（`E = ℝ`）：`‖I + J_0‖ = 2`，
  而 `1/(1-1)` 在 `ℝ` 上求值为 `0`（除零垃圾），`2 ≤ 0` 为**假**。
- `0 ≤ a_l` **不可省**：取 `a = (-0.4, -0.4)`（`Σ a = -0.8 < 1` 成立）、`J = 0`：
  左端 `‖I‖ = 1`，右端 `∏(1+a_l) = 0.36`，`1 ≤ 0.36` 为**假**。
- **下界与上界都显式**：本文件带 `0 ≤ a l`（下界）与 `Σ a l < 1`（总上界），
  **不**单独假设 `a l ≤ 1`——它由前者**推出**（`resJac_each_lt_one`）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **残差块的线性化**：`resJac J = 1 + J`（恒等 + 扰动）。 -/
def resJac (J : E →L[ℝ] E) : E →L[ℝ] E := 1 + J

/-- **单层谱放大界**：`‖I + J‖ ≤ 1 + ‖J‖`。

**它比定义多说了什么**：`I + J` 是**算子和**，其范数不能直接读作范数之和
（那正是本条要证的三角不等式）。`J = 0` 时**取等**。 -/
theorem resJac_opNorm_le (J : E →L[ℝ] E) : ‖resJac J‖ ≤ 1 + ‖J‖ := by
  unfold resJac
  refine le_trans (norm_add_le (1 : E →L[ℝ] E) J) ?_
  have hle : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  linarith

/-- **残差链的递归定义**：`Chain 0 = I`、`Chain (m+1) = resJac (J m) * Chain m`。

⚠ **为什么用递归而非 `Finset.prod`**：算子复合**不交换**，
`Finset.prod` 需要 `CommMonoid`（`E →L[ℝ] E` 在复合下只有 `Monoid`），
故链式乘积必须按**固定次序**递归定义。这是本文件与 `RealModelChain`（纯标量乘法）
在**技术形态**上的差别之一。 -/
def resJacChain (J : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => 1
  | m + 1 => resJac (J m) * resJacChain J m

/-- **链式谱放大界**：`∀ l < m, 0 ≤ a l`、`∀ l < m, ‖J l‖ ≤ a l` ⟹
`‖resJacChain J m‖ ≤ ∏ l ∈ Finset.range m, (1 + a l)`。

**它比定义多说了什么**：把**算子复合**的范数（子乘性，逐步放大）与
**标量乘积**的上界对齐。这是 `RealModelChain` 的 `Lb^m` 骨架在**算子范数**下的
对应物，但假设形态不同：那里是「每块函数 Lipschitz 常数 `≤ Lb`」（**统一常数**），
这里是「每个 `J l` 的算子范数 `≤ a l`」（**逐层可不同**）。

⚠ **`0 ≤ a l` 不可省**：`J = 0`、`a = -3` 时 `‖I‖ = 1 ≤ -2` 为**假**。 -/
theorem resJac_chain_le (J : ℕ → E →L[ℝ] E) (a : ℕ → ℝ) (m : ℕ)
    (ha : ∀ l, l < m → 0 ≤ a l) (hJ : ∀ l, l < m → ‖J l‖ ≤ a l) :
    ‖resJacChain J m‖ ≤ ∏ l ∈ Finset.range m, (1 + a l) := by
  induction m with
  | zero =>
      show ‖(1 : E →L[ℝ] E)‖ ≤ ∏ l ∈ Finset.range 0, (1 + a l)
      simp only [Finset.range_zero, Finset.prod_empty]
      exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
      have ha' : ∀ l, l < m → 0 ≤ a l := fun l hl => ha l (by omega)
      have hJ' : ∀ l, l < m → ‖J l‖ ≤ a l := fun l hl => hJ l (by omega)
      have ham : 0 ≤ a m := ha m (by omega)
      rw [Finset.prod_range_succ]
      show ‖resJac (J m) * resJacChain J m‖
          ≤ (∏ l ∈ Finset.range m, (1 + a l)) * (1 + a m)
      calc ‖resJac (J m) * resJacChain J m‖
          ≤ ‖resJac (J m)‖ * ‖resJacChain J m‖ := norm_mul_le _ _
        _ ≤ (1 + a m) * ∏ l ∈ Finset.range m, (1 + a l) :=
            mul_le_mul (le_trans (resJac_opNorm_le (J m))
                (by linarith [hJ m (by omega : m < m + 1)]))
              (ih ha' hJ') (norm_nonneg _) (by linarith)
        _ = (∏ l ∈ Finset.range m, (1 + a l)) * (1 + a m) := by ring

/-- **每个 `a_l` 都严格小于 `1`**（由 `0 ≤ a_l` 与 `Σ a_l < 1` **推出**）。

**它比定义多说了什么**：显式给出「**下界 + 总和上界 ⟹ 逐个上界**」这一步。
⚠ 去掉 `0 ≤ a l` 后本引理为**假**（`a = (-5, 5.5)`：`Σ a = 0.5 < 1`
但 `a 1 = 5.5 > 1`）。 -/
theorem resJac_each_lt_one (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ l ∈ s, 0 ≤ a l)
    (hsum : (∑ l ∈ s, a l) < 1) {l : ℕ} (hl : l ∈ s) : a l < 1 := by
  have hsingle : a l ≤ ∑ l' ∈ s, a l' :=
    Finset.single_le_sum (fun l' hl' => ha l' hl') hl
  linarith

/-- ⭐ **核心新增：有限 Weierstrass 不等式（和 vs 积的转换）**。

`∀ l ∈ s, 0 ≤ a_l`、`Σ_{l∈s} a_l < 1` ⟹
`∏_{l∈s} (1 + a_l) ≤ 1 / (1 - Σ_{l∈s} a_l)`。

**它比定义多说了什么（本文件最重要的实质内容）**：
无残差链的放大是 `∏ a_l`（**乘积**，`a_l < 1` 时随层数**指数消失**）；
残差链的放大是 `∏ (1 + a_l) ≤ 1/(1 - Σ a_l)`（**和**，`Σ a_l < 1` 时 `≤ 2`）。
故**残差把「指数衰减」换成「一致有界」**——深度可训练的定量机制。
`RealModelChain` 只有 `Lb^m` 的纯乘积，**没有**这条转换。

**证明**：归纳步只需证 `(1+a)/(1-S) ≤ 1/(1-S-a)`，
等价于 `(1+a)(1-S-a) ≤ 1-S`，即 `-a² - a·S ≤ 0`，由 `a ≥ 0`、`S ≥ 0` 成立。

⚠ **`Σ a_l < 1` 严格不可省**、**`0 ≤ a_l` 不可省**：见证见文件头。 -/
theorem weierstrass_prod_le (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ l ∈ s, 0 ≤ a l)
    (hsum : (∑ l ∈ s, a l) < 1) :
    ∏ l ∈ s, (1 + a l) ≤ 1 / (1 - ∑ l ∈ s, a l) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons l s hls ih =>
      rw [Finset.prod_cons hls, Finset.sum_cons hls] at *
      have ha' : ∀ l' ∈ s, 0 ≤ a l' := fun l' hl' => ha l' (Finset.mem_cons_of_mem hl')
      have hl0 : 0 ≤ a l := ha l (Finset.mem_cons_self l s)
      have hSt : 0 ≤ ∑ l' ∈ s, a l' := Finset.sum_nonneg ha'
      have hsum_t : (∑ l' ∈ s, a l') < 1 := by linarith
      have hden_t : 0 < 1 - ∑ l' ∈ s, a l' := by linarith
      have hden_i : 0 < 1 - (a l + ∑ l' ∈ s, a l') := by linarith
      calc (1 + a l) * ∏ l' ∈ s, (1 + a l')
          ≤ (1 + a l) * (1 / (1 - ∑ l' ∈ s, a l')) :=
            mul_le_mul_of_nonneg_left (ih ha' hsum_t) (by linarith)
        _ ≤ 1 / (1 - (a l + ∑ l' ∈ s, a l')) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) hden_i]
            nlinarith [hl0, hSt, hden_t]

/-- ⭐ **残差流的谱放大一致有界（本文件的收官定理）**。

`∀ l < m, 0 ≤ a l`、`∀ l < m, ‖J l‖ ≤ a l`、`Σ_{l<m} a l < 1` ⟹
`‖resJacChain J m‖ ≤ 1 / (1 - Σ_{l<m} a l)`。

**它比定义多说了什么**：把 `resJac_chain_le`（乘法形态）与
`weierstrass_prod_le`（和 ⟹ 积）**复合**，得到**与层数 `m` 无关**的一致界。
这回答了一个**工程问题**：「加深残差网络是否必然放大扰动？」
——**否**，只要 `Σ a_l < 1`（**总扰动预算**）。

⚠ **`Σ a_l < 1` 是「总预算」而非「逐层预算」**：本定理允许单层 `a_l` 接近 `1`，
只要**总和**受控——这正是与 `RealModelChain` 的 `Lb^m` 的关键差别。 -/
theorem resJac_chain_le_inv_one_sub_sum (J : ℕ → E →L[ℝ] E) (a : ℕ → ℝ) (m : ℕ)
    (ha : ∀ l, l < m → 0 ≤ a l) (hJ : ∀ l, l < m → ‖J l‖ ≤ a l)
    (hsum : (∑ l ∈ Finset.range m, a l) < 1) :
    ‖resJacChain J m‖ ≤ 1 / (1 - ∑ l ∈ Finset.range m, a l) :=
  le_trans (resJac_chain_le J a m ha hJ)
    (weierstrass_prod_le (Finset.range m) a (fun l hl => ha l (Finset.mem_range.mp hl)) hsum)

/-- **指数形态的上界（不要求 `Σ a_l < 1`）**：
`∀ l < m, 0 ≤ a l`、`‖J l‖ ≤ a l` ⟹ `‖resJacChain J m‖ ≤ exp(Σ_{l<m} a l)`。

**它比定义多说了什么**：给出**适用范围更广**的界——`Σ a_l` 可以**任意大**
（不需要 `< 1`），界仍有限且显式。代价是界更松。
**证明**：`1 + x ≤ exp x`（`Real.add_one_le_exp`）逐项 + `Real.exp_sum`。

**与上一条的关系**：上一条在 `Σ a_l < 1` 时**更紧**，本条在 `Σ a_l ≥ 1` 时
**仍然有效**——两者**互补**，不是重复。 -/
theorem resJac_chain_le_exp_sum (J : ℕ → E →L[ℝ] E) (a : ℕ → ℝ) (m : ℕ)
    (ha : ∀ l, l < m → 0 ≤ a l) (hJ : ∀ l, l < m → ‖J l‖ ≤ a l) :
    ‖resJacChain J m‖ ≤ Real.exp (∑ l ∈ Finset.range m, a l) := by
  refine le_trans (resJac_chain_le J a m ha hJ) ?_
  calc ∏ l ∈ Finset.range m, (1 + a l) ≤ ∏ l ∈ Finset.range m, Real.exp (a l) :=
        Finset.prod_le_prod (fun l hl => by linarith [ha l (Finset.mem_range.mp hl)])
          (fun l _ => by rw [add_comm]; exact Real.add_one_le_exp (a l))
    _ = Real.exp (∑ l ∈ Finset.range m, a l) := by rw [Real.exp_sum]

/-- **残差 vs 无残差的放大对照**：`a_l ≥ 0` ⟹ `∏_{l∈s} a_l ≤ ∏_{l∈s} (1 + a_l)`。

**它比定义多说了什么**：把「残差链的放大」与「裸链的放大」放在**同一标尺**上，
并**断言不等号方向**：残差**从不**比裸链更小（它是「加回恒等」的代价）。
⚠ **不等式方向是本对照的实质内容**：若写成 `≥` 则为**假**
（`a = (1,1)`：`∏ a = 1 < ∏(1+a) = 4`）。
⚠ **`0 ≤ a_l` 不可省**：`a = (-3, -3)` 时 `∏ a = 9 > ∏(1+a) = 4`，**方向反转**。 -/
theorem resJac_growth_comparison (s : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ l ∈ s, 0 ≤ a l) :
    ∏ l ∈ s, a l ≤ ∏ l ∈ s, (1 + a l) :=
  Finset.prod_le_prod (fun l hl => ha l hl) (fun l _ => by linarith)

end Lattice
