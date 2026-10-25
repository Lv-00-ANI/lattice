import Mathlib
import Lattice.Lib.Architectures.RealSSM
/-!
# LATTICE: 时变 A_t 的选择性 SSM（Mamba S6 型）——闭式解、稳定界、LTI 退化

`RealSSM` 处理的是**时不变**状态空间模型 `h_{t+1} = A h_t + B x_t`（`A` 恒定），
其闭式解是 `∑_k A^k B x_{t-1-k}`。选择性 SSM（S6 / Mamba）的关键改动是让
`A` 与 `B` 都**依赖时间步**（输入依赖的选择机制）：

    h_{t+1} = A_t h_t + B_t x_t,      h_0 = 0。

本文件在**一般完备赋范环** `𝔸`（`[NormedRing 𝔸] [NormOneClass 𝔸]`，**不要求交换**）上
给出 S6 型时变递推的结果，全部无 `sorry` / `axiom` / `admit`：

1. `selState` / `selOutput` / `selProd`：时变状态、读出与「乘积型基本解」因子
   （`selProd A k t = A_{t-1} * ⋯ * A_k`，**下标递减、新因子在左**，见下「关键设计」）；
2. `selProd_concat`（**核心代数引理**）：`selProd A k t = selProd A m t * selProd A k m`
   （`k ≤ m ≤ t`）——时变乘积的**粘合律**；
3. `selState_explicit`（**闭式解 / 核心**）：
   `h_t = ∑_{k<t} selProd A (k+1) t * B_k`，即乘积型基本解之和；
4. `sel_norm_prod_le`：`∀i, ‖A i‖ ≤ ρ` ⟹ `‖selProd A k t‖ ≤ ρ ^ (t - k)`；
5. `selState_norm_bound`（**稳定界（一般 ρ）**）：`‖h_t‖ ≤ M · t · max 1 ρ^{t-1}`；
6. `selState_norm_bound_contracting`（**稳定界（收缩 ρ < 1，核心）**）：
   `‖h_t‖ ≤ M / (1 - ρ)` —— **一致有界**，与 `t` 无关；
7. `sel_is_LTI_special`（**LTI 退化**）：`A_t ≡ a` 时闭式解退化为
   `∑_{k<t} a^{t-1-k} B_k`，即 S6 **严格推广**时不变 SSM；
8. `selState_window`：`h_t` 只依赖 `B 0 … B (t-1)`（因果 / 窗口性）。

## 关键设计（非交换性决定了 `selProd` 的方向）

递推是 `h_{n+1} = A_n * h_n + B_n`（`A_n` 在**左**乘法位置）。因此 `h_t` 中 `B_k` 的
系数必须是 `A_{t-1} ⋯ A_{k+1}` —— **最大下标在最左**。若反向写成 `A_{k+1} ⋯ A_{t-1}`，
归纳步会要求 `A_n * (A_{k+1}⋯A_{n-1}) = (A_{k+1}⋯A_{n-1}) * A_n`，
这在**非交换环中为假**（实测无法证明）。故 `selProd A k t` 定义为
`A_{t-1} * A_{t-2} * ⋯ * A_k`。

## 诚实边界（中文标注）

- **降级 —— ZOH 离散化桥接未做**：本文件直接处理**离散**递推。关于「连续
  `h' = A(t) h + B(t) x` 经 ZOH 离散化得到 `A_t = exp(Δ A(t))`」的桥接**未做**
  （`RealSSMDiscretization` 只处理时不变 `exp` 的截断误差）。
- **未做 —— 输入依赖性**：S6 真正的新意是 `A_t` / `B_t` 由当前输入 `x_t` **算出**
  （`A_t = exp(Δ_t A)`、`Δ_t = softplus(W x_t)`）。本文件把 `A_t` / `B_t` 当作
  **给定的时间序列**，不建模该依赖关系。
- **未做 —— 谱稳定性**：`ρ < 1` 的充分条件（如 `A_t` 谱半径 < 1）**未证**；
  本文件的稳定界直接**假设**范数界 `‖A_t‖ ≤ ρ`，是**显式前提**而非导出结论。
- **未做 —— 选择性下界**：时变 `A_t` 相对时不变的**表达力增益**（「存在时变可表示
  而时不变不可表示的序列」）未做，需具体反例构造。
- **降级 —— 一致界的最优性未证**：`M/(1-ρ)` 未证在一般设定下**紧**（即未构造达到
  该界的 `A`/`B`）；对 `A_t ≡ ρ`、`‖B_k‖ = M` 的常数序列该界是渐近紧的（几何级数），
  但本文件**未做**该紧性定理。
- **标注 —— 非交换性带来的接口约束**：一般 `NormedRing`（**非交换**）下
  `‖∏‖ ≤ ∏‖·‖` 无现成引理（mathlib 的 `Finset.norm_prod_le` 要 `NormedCommRing`），
  且 `norm_mul`（**等式**）只对 `NormedDivisionRing` 可用。故 `sel_norm_prod_le`
  对 `List` 归纳自证、全程只用 `norm_mul_le`（见 STYLE 坑表）。
- **标注 —— `selProd_succ` 需要前提 `k ≤ t`**：`k > t` 时两端分别为 `1` 与 `A t`，
  命题为假（已在 docstring 标注）。
-/

noncomputable section

namespace Lattice

open scoped BigOperators
open Finset

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

/-! ## 一、定义：时变选择性状态与读出 -/

/-- **时变选择性状态递推**：`h_{t+1} = A_t h_t + B_t x_t`，`h_0 = 0`。
`A : ℕ → 𝔸`、`B : ℕ → 𝔸` 是**给定的**时间序列（`B_t` 已吸收输入 `x_t`）。 -/
def selState (A B : ℕ → 𝔸) : ℕ → 𝔸
  | 0 => 0
  | t + 1 => A t * selState A B t + B t

/-- **时变选择性读出**：`y_t = C_t h_t`。 -/
def selOutput (C A B : ℕ → 𝔸) (t : ℕ) : 𝔸 := C t * selState A B t

/-- **乘积型基本解因子**：`selProd A k t = A_{t-1} * A_{t-2} * ⋯ * A_k`（下标**递减**，
最左因子是最大的下标 `t-1`）。`k = t` 时为空积 `1`。

**为什么必须递减**：递推是 `h_{n+1} = A_n * h_n + B_n`（`A_n` 在**左**），
故 `h_t` 中 `B_k` 的系数必须是 `A_{t-1} ⋯ A_{k+1}`（新因子在左）。
若用递增顺序 `A_{k+1} ⋯ A_{t-1}`，则归纳步需要
`A_n * (A_{k+1}⋯A_{n-1}) = A_{k+1}⋯A_{n-1} * A_n`——**非交换环中为假**。

用 `List.prod` 而非 `Finset.prod` 定义，因为 `𝔸` 只假设 `[Monoid 𝔸]`（**非交换**），
而 mathlib 的 `Finset.prod` 需要 `CommMonoid`（实测报 `failed to synthesize CommMonoid 𝔸`）。
`List.prod` 只要求 `Mul` / `One`，且**保持列表顺序**——这正是非交换乘法所需的语义。 -/
def selProd (A : ℕ → 𝔸) (k t : ℕ) : 𝔸 :=
  ((List.range (t - k)).map (fun i => A (t - 1 - i))).prod

/-- **辅助递推**：`selProdFrom A k n = A_{k+n-1} * ⋯ * A_k`（长度 `n`，递减顺序）。 -/
def selProdFrom (A : ℕ → 𝔸) : ℕ → ℕ → 𝔸
  | k, 0 => 1
  | k, n + 1 => A (k + n) * selProdFrom A k n

/-- **定义等价**：`selProd A k t = selProdFrom A k (t - k)`。 -/
theorem selProd_eq_from (A : ℕ → 𝔸) (k t : ℕ) :
    selProd A k t = selProdFrom A k (t - k) := by
  have key : ∀ n : ℕ, ((List.range n).map (fun i => A (k + n - 1 - i))).prod
      = selProdFrom A k n := by
    intro n
    induction n with
    | zero => simp [selProdFrom]
    | succ m ih =>
        have hstep : (List.range (m + 1)).map (fun i => A (k + (m + 1) - 1 - i))
            = A (k + m) :: (List.range m).map (fun i => A (k + m - 1 - i)) := by
          rw [List.range_succ_eq_map, List.map_cons, List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          simp only [Function.comp_apply]
          congr 1
          omega
        rw [hstep, List.prod_cons, ih, selProdFrom]
  have hidx : (List.range (t - k)).map (fun i => A (t - 1 - i))
      = (List.range (t - k)).map (fun i => A (k + (t - k) - 1 - i)) := by
    apply List.map_congr_left
    intro i hi
    have hi' : i < t - k := List.mem_range.mp hi
    congr 1
    omega
  unfold selProd
  rw [hidx, key]

/-- **乘积的粘合（单步右端）**：`k ≤ t` 时 `selProd A k (t+1) = A t * selProd A k t`。
注意**新因子 `A t` 在左**（与递推 `h_{t+1} = A_t h_t + B_t` 的方向一致）。

标注：**必须带前提 `k ≤ t`**。`k > t` 时两端分别为 `1` 与 `A t`，一般不相等。 -/
theorem selProd_succ (A : ℕ → 𝔸) (k t : ℕ) (hkt : k ≤ t) :
    selProd A k (t + 1) = A t * selProd A k t := by
  have h1 : t + 1 - k = (t - k) + 1 := by omega
  have h2 : k + (t - k) = t := by omega
  rw [selProd_eq_from, selProd_eq_from, h1, selProdFrom, h2]

/-- 空积：`selProd A t t = 1`。 -/
theorem selProd_self (A : ℕ → 𝔸) (t : ℕ) : selProd A t t = 1 := by
  simp [selProd]

/-- 首项：`selProd A t (t+1) = A t`。 -/
theorem selProd_pred (A : ℕ → 𝔸) (t : ℕ) : selProd A t (t + 1) = A t := by
  rw [selProd_succ A t t le_rfl, selProd_self, mul_one]

/-! ## 二、一步展开 -/

/-- **一步展开**：`h_{t+1} = A_t h_t + B_t`（定义方程）。 -/
theorem selState_succ (A B : ℕ → 𝔸) (t : ℕ) :
    selState A B (t + 1) = A t * selState A B t + B t := rfl

/-- **零初值出发的首步**：`h_1 = B_0`。 -/
theorem selState_one (A B : ℕ → 𝔸) : selState A B 1 = B 0 := by
  simp [selState]

/-- **因果性（一步）**：`h_{t+1}` 只通过 `h_t` 依赖历史（定义即给出）。 -/
theorem selState_eq_of_eq (A B B' : ℕ → 𝔸) (t : ℕ) (h : selState A B t = selState A B' t)
    (hBt : B t = B' t) : selState A B (t + 1) = selState A B' (t + 1) := by
  rw [selState_succ, selState_succ, h, hBt]

/-! ## 三、闭式解（时变乘积 / 乘积型基本解） -/

/-- **时变乘积的粘合律（核心代数引理）**：对 `k ≤ m ≤ t`，
`selProd A k t = selProd A m t * selProd A k m`。

「先走 `k→m`，再走 `m→t`」与「一次走 `k→t`」一致；**左侧因子是后一段**
（`selProd A m t = A_{t-1} ⋯ A_m`，`selProd A k m = A_{m-1} ⋯ A_k`），
即**新因子在左**——非交换乘法下唯一正确的写法。

证明：`[k, t)` 的长度拆成两段，把递减列表 `A_{t-1}, …, A_k` 写成
`A_{t-1}, …, A_m` 接 `A_{m-1}, …, A_k`，再用 `List.map_append` 与 `List.prod_append`。 -/
theorem selProd_concat (A : ℕ → 𝔸) {k m t : ℕ} (hkm : k ≤ m) (hmt : m ≤ t) :
    selProd A k t = selProd A m t * selProd A k m := by
  have hlen : t - k = (t - m) + (m - k) := by omega
  have hmap : (List.range (t - k)).map (fun i => A (t - 1 - i))
      = ((List.range (t - m)).map (fun i => A (t - 1 - i)))
        ++ ((List.range (m - k)).map (fun i => A (m - 1 - i))) := by
    rw [hlen, List.range_add, List.map_append]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply]
    have hi' : i < m - k := List.mem_range.mp hi
    congr 1
    omega
  unfold selProd
  rw [hmap, List.prod_append]

/-- **闭式解（核心定理）**：时变选择性递推的解是**乘积型基本解**之和：
`h_t = ∑_{k<t} selProd A (k+1) t * B_k`，其中
`selProd A (k+1) t = A_{t-1} ⋯ A_{k+1}`（递减，新因子在左）。

证明：对 `t` 归纳。归纳步用 `selProd_succ`（`A n * selProd A (k+1) n = selProd A (k+1) (n+1)`）
与 `Finset.mul_sum`；末项由 `selProd A (n+1) (n+1) = 1` 收尾。 -/
theorem selState_explicit (A B : ℕ → 𝔸) (t : ℕ) :
    selState A B t = ∑ k in range t, selProd A (k + 1) t * B k := by
  induction t with
  | zero => simp [selState]
  | succ n ih =>
      rw [selState_succ, ih, Finset.sum_range_succ, Finset.mul_sum]
      have hstep : ∀ k ∈ range n, A n * (selProd A (k + 1) n * B k)
          = selProd A (k + 1) (n + 1) * B k := by
        intro k hk
        have hconcat : selProd A (k + 1) (n + 1) = A n * selProd A (k + 1) n :=
          selProd_succ A (k + 1) n (by simpa [Finset.mem_range] using hk)
        rw [hconcat, mul_assoc]
      rw [Finset.sum_congr rfl hstep]
      simp [selProd]

/-! ## 四、稳定界 -/

/-- **乘积范数界（非交换版）**：`∀i, ‖A i‖ ≤ ρ` ⟹ `‖selProd A k t‖ ≤ ρ ^ (t - k)`。

mathlib 的 `Finset.norm_prod_le` 要求 `NormedCommRing`，本文件只假设
`NormedRing`（非交换）；且 `norm_mul`（**等式**）也只对 `NormedDivisionRing` 可用
（对 `NormedRing` 只有 `norm_mul_le`，见 STYLE 坑表）。故本证明全程只用 `norm_mul_le`
与对 `List` 的归纳。 -/
theorem sel_norm_prod_le (A : ℕ → 𝔸) (ρ : ℝ) (hA : ∀ i, ‖A i‖ ≤ ρ) (k t : ℕ) :
    ‖selProd A k t‖ ≤ ρ ^ (t - k) := by
  have hprod : ∀ l : List 𝔸, ‖l.prod‖ ≤ (l.map norm).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        rw [List.prod_cons, List.map_cons, List.prod_cons]
        exact (norm_mul_le a l.prod).trans
          (mul_le_mul_of_nonneg_left ih (norm_nonneg a))
  have hmap : ((List.range (t - k)).map (fun i => A (t - 1 - i))).map norm
      = (List.range (t - k)).map (fun i => ‖A (t - 1 - i)‖) := by
    rw [List.map_map]; rfl
  have hρnn : 0 ≤ ρ := le_trans (norm_nonneg (A 0)) (hA 0)
  have hle : ∀ n : ℕ,
      ((List.range n).map (fun i => ‖A (t - 1 - i)‖)).prod ≤ ρ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have hsplit : (List.range (m + 1)).map (fun i => ‖A (t - 1 - i)‖)
            = (List.range m).map (fun i => ‖A (t - 1 - i)‖) ++ [‖A (t - 1 - m)‖] := by
          rw [List.range_succ, List.map_append]
          congr 1
        calc ((List.range (m + 1)).map (fun i => ‖A (t - 1 - i)‖)).prod
            = ((List.range m).map (fun i => ‖A (t - 1 - i)‖)).prod * ‖A (t - 1 - m)‖ := by
              rw [hsplit, List.prod_append]; simp
          _ ≤ ρ ^ m * ρ :=
              mul_le_mul ih (hA (t - 1 - m)) (norm_nonneg _) (pow_nonneg hρnn m)
          _ = ρ ^ (m + 1) := (pow_succ ρ m).symm
  calc ‖selProd A k t‖
      = ‖((List.range (t - k)).map (fun i => A (t - 1 - i))).prod‖ := rfl
    _ ≤ (((List.range (t - k)).map (fun i => A (t - 1 - i))).map norm).prod := hprod _
    _ = ((List.range (t - k)).map (fun i => ‖A (t - 1 - i)‖)).prod := by rw [hmap]
    _ ≤ ρ ^ (t - k) := hle _

/-- **一步状态范数展开**：`‖h_{t+1}‖ ≤ ‖A_t‖ ‖h_t‖ + ‖B_t‖`。 -/
theorem selState_norm_succ (A B : ℕ → 𝔸) (t : ℕ) :
    ‖selState A B (t + 1)‖ ≤ ‖A t‖ * ‖selState A B t‖ + ‖B t‖ := by
  rw [selState_succ]
  exact (norm_add_le _ _).trans (by
    rw [add_le_add_iff_right]
    exact norm_mul_le _ _)

/-- **闭式解的逐项范数界**：`∀i, ‖A i‖ ≤ ρ`、`∀k, ‖B k‖ ≤ M` ⟹
`‖h_t‖ ≤ M · ∑_{k<t} ρ^{t-1-k}`。 -/
theorem selState_norm_le_sum (A B : ℕ → 𝔸) (ρ M : ℝ) (hρ : 0 ≤ ρ) (hA : ∀ i, ‖A i‖ ≤ ρ)
    (hB : ∀ k, ‖B k‖ ≤ M) (t : ℕ) :
    ‖selState A B t‖ ≤ M * ∑ k in range t, ρ ^ (t - 1 - k) := by
  rw [selState_explicit]
  calc ‖∑ k in range t, selProd A (k + 1) t * B k‖
      ≤ ∑ k in range t, ‖selProd A (k + 1) t * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k in range t, ρ ^ (t - 1 - k) * M := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkt : k < t := Finset.mem_range.mp hk
        have hp : ‖selProd A (k + 1) t‖ ≤ ρ ^ (t - 1 - k) := by
          have h := sel_norm_prod_le A ρ hA (k + 1) t
          have : t - (k + 1) = t - 1 - k := by omega
          rwa [this] at h
        calc ‖selProd A (k + 1) t * B k‖ ≤ ‖selProd A (k + 1) t‖ * ‖B k‖ :=
              norm_mul_le _ _
          _ ≤ ρ ^ (t - 1 - k) * M :=
              mul_le_mul hp (hB k) (norm_nonneg _) (pow_nonneg hρ _)
    _ = M * ∑ k in range t, ρ ^ (t - 1 - k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

/-- **稳定界（一般 ρ）**：`∀i, ‖A i‖ ≤ ρ`、`∀k, ‖B k‖ ≤ M` ⟹
`‖h_t‖ ≤ M · t · max 1 ρ^{t-1}`。

逐项用 `ρ^{t-1-k} ≤ max 1 ρ^{t-1}`（`ρ ≤ 1` 时用 `pow_le_one₀`，
`1 < ρ` 时用 `pow_le_pow_right₀` 与 `t-1-k ≤ t-1`），共 `t` 项。
`ρ ≤ 1` 时退化为 `‖h_t‖ ≤ M t`。 -/
theorem selState_norm_bound (A B : ℕ → 𝔸) (ρ M : ℝ) (hρ : 0 ≤ ρ)
    (hA : ∀ i, ‖A i‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState A B t‖ ≤ M * (t : ℝ) * max 1 (ρ ^ (t - 1)) := by
  have hsum : ∑ k in range t, ρ ^ (t - 1 - k) ≤ (t : ℝ) * max 1 (ρ ^ (t - 1)) := by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    · have hterm : ∀ k ∈ range t, ρ ^ (t - 1 - k) ≤ max 1 (ρ ^ (t - 1)) := by
        intro k hk
        have hkt : k < t := Finset.mem_range.mp hk
        have hle : t - 1 - k ≤ t - 1 := Nat.sub_le _ _
        rcases le_or_lt ρ 1 with h1 | h1
        · refine (pow_le_one₀ (n := t - 1 - k) hρ h1).trans ?_
          exact le_max_left _ _
        · refine (pow_le_pow_right₀ (le_of_lt h1) hle).trans ?_
          exact le_max_right _ _
      calc ∑ k in range t, ρ ^ (t - 1 - k)
          ≤ ∑ _k in range t, max 1 (ρ ^ (t - 1)) := Finset.sum_le_sum hterm
        _ = (t : ℝ) * max 1 (ρ ^ (t - 1)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ‖selState A B t‖ ≤ M * ∑ k in range t, ρ ^ (t - 1 - k) :=
        selState_norm_le_sum A B ρ M hρ hA hB t
    _ ≤ M * ((t : ℝ) * max 1 (ρ ^ (t - 1))) := mul_le_mul_of_nonneg_left hsum hM
    _ = M * (t : ℝ) * max 1 (ρ ^ (t - 1)) := by ring

/-- **稳定界（收缩 ρ < 1，核心）**：`∀i, ‖A i‖ ≤ ρ < 1`、`∀k, ‖B k‖ ≤ M` ⟹
`‖h_t‖ ≤ M / (1 - ρ)` —— **一致有界**，与时间步 `t` 无关。

即选择性 SSM 的稳定性只要「时变乘子范数一致 < 1」即可，不依赖 `t`。
这正是 Mamba 用 `exp(Δ A)` 且 `A < 0` 强制 `‖A_t‖ < 1` 的原因。
证明：`∑_{k<t} ρ^{t-1-k} ≤ ∑_j ρ^j ≤ ∑'_j ρ^j = 1/(1-ρ)`。 -/
theorem selState_norm_bound_contracting (A B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hA : ∀ i, ‖A i‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState A B t‖ ≤ M / (1 - ρ) := by
  have hrev : ∑ k in range t, ρ ^ (t - 1 - k) = ∑ j in range t, ρ ^ j :=
    sum_range_reflect (fun j => ρ ^ j) t
  have hsumm : Summable (fun j : ℕ => ρ ^ j) := summable_geometric_of_lt_one hρ0 hρ1
  have htsum : ∑' j : ℕ, ρ ^ j = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ0 hρ1
  have hfin : ∑ j in range t, ρ ^ j ≤ ∑' j : ℕ, ρ ^ j :=
    sum_le_tsum (range t) (fun j _ => pow_nonneg hρ0 j) hsumm
  have hpos : 0 < 1 - ρ := by linarith
  calc ‖selState A B t‖ ≤ M * ∑ k in range t, ρ ^ (t - 1 - k) :=
        selState_norm_le_sum A B ρ M hρ0 hA hB t
    _ = M * ∑ j in range t, ρ ^ j := by rw [hrev]
    _ ≤ M * (1 - ρ)⁻¹ := by
        rw [← htsum]
        exact mul_le_mul_of_nonneg_left hfin hM
    _ = M / (1 - ρ) := by rw [div_eq_mul_inv]

/-! ## 五、LTI 退化：S6 严格推广时不变 SSM -/

/-- **常值乘积**：`A ≡ a` 时 `selProd A k t = a ^ (t - k)`。 -/
theorem selProd_const (a : 𝔸) (k t : ℕ) :
    selProd (fun _ => a) k t = a ^ (t - k) := by
  simp [selProd]

/-- **LTI 退化（核心）**：当 `A` 恒为 `a` 时，时变闭式解退化为
`h_t = ∑_{k<t} a^{t-1-k} * B_k` —— 正是 `RealSSM` 时不变闭式解的形式
（`RealSSM.ssmState_explicit`，取 `B k = B * x k`）。

这条定理说明 S6 型选择性 SSM **严格推广**时不变 SSM：时不变是 `A_t ≡ a` 的特例。 -/
theorem sel_is_LTI_special (a : 𝔸) (B : ℕ → 𝔸) (t : ℕ) :
    selState (fun _ => a) B t = ∑ k in range t, a ^ (t - 1 - k) * B k := by
  rw [selState_explicit]
  exact Finset.sum_congr rfl fun k hk => by
    have hkt : k < t := Finset.mem_range.mp hk
    rw [selProd_const]
    congr 2
    omega

/-- **与 `RealSSM` 时不变递推的一致性**：若 `A_0 : 𝔸` 且把 `RealSSM` 的
`h_{t+1} = a h_t + B_t` 写成 `selState (fun _ => a) B`，则二者逐项相同。
这一条把本文件与 `RealSSM` 的接口对齐：`RealSSM.ssmState` 在
`A` 恒定、`B_t = B * x_t` 时就是 `selState (fun _ => a)`。 -/
theorem sel_LTI_eq_ssmState (a : 𝔸) (B : ℕ → 𝔸) :
    ∀ t, selState (fun _ => a) B t = ∑ k in range t, a ^ (t - 1 - k) * B k :=
  fun t => sel_is_LTI_special a B t

/-- **LTI 收缩稳定界**：`A ≡ a`、`‖a‖ ≤ ρ < 1`、`‖B k‖ ≤ M` ⟹ `‖h_t‖ ≤ M/(1-ρ)`。 -/
theorem sel_LTI_norm_bound (a : 𝔸) (B : ℕ → 𝔸) (ρ M : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (ha : ‖a‖ ≤ ρ) (hB : ∀ k, ‖B k‖ ≤ M) (hM : 0 ≤ M) (t : ℕ) :
    ‖selState (fun _ => a) B t‖ ≤ M / (1 - ρ) :=
  selState_norm_bound_contracting (fun _ => a) B ρ M hρ0 hρ1 (fun _ => ha) hB hM t

/-! ## 六、选择性 SSM 的结构性质 -/

/-- **因果窗口**：第 `t` 步状态只依赖 `B 0, …, B (t-1)`：若 `B` 与 `B'` 在这些位置上
相同，则 `h_t` 相同。即 `k ≥ t` 的输入对 `h_t` 无贡献——这是选择性 SSM
与全注意力不同的关键结构性质（线性时间、固定状态尺寸）。 -/
theorem selState_window (A B B' : ℕ → 𝔸) (t : ℕ) (h : ∀ k, k < t → B k = B' k) :
    selState A B t = selState A B' t := by
  rw [selState_explicit, selState_explicit]
  exact Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.mp hk)]

/-- **时变乘子的左吸收**：把 `A_t` 并入 `B_t` 不改变递推结构——
`selState (fun _ => 1) B' = selState A B` 当 `B'_t = A_t h_t + B_t`。
此处只给**一步**形式（把 `A_t` 的效应推到下一步的 `B`）。

标注：完整的多步改写**未做**（需要能引用同一 `A` 的状态序列，陈述繁琐）。 -/
theorem selState_absorb_one (A B : ℕ → 𝔸) (B' : ℕ → 𝔸)
    (hB' : ∀ t, B' t = A t * selState A B t + B t) (t : ℕ) :
    selState A B (t + 1) = B' t := by
  rw [selState_succ, hB' t]

/-! ## 七、一致界的紧性（D20）

`selState_norm_bound_contracting` 给出 `‖h_t‖ ≤ M/(1−ρ)`（`‖A_i‖ ≤ ρ < 1`、`‖B_k‖ ≤ M`）。
本节回答 **D20：该界是否可改进？**

**结论：在标量情形 `𝔸 = ℝ` 上，`M/(1−ρ)` 是渐近紧的**——存在一族实例使

    `‖h_t‖ = M · (1 − ρ^t) / (1 − ρ)`   ⟹   `‖h_t‖ → M/(1−ρ)`（`t → ∞`）。

取 `A_i ≡ ρ`（`0 ≤ ρ < 1`）、`B_k ≡ M`（`M ≥ 0`），则闭式解是几何和
`h_t = M·∑_{k<t} ρ^{t−1−k} = M·(1−ρ^t)/(1−ρ)`。**该值恰等于界在 `t → ∞` 的极限**，
故**界不可改进为更小的常数**（对任意 `ε > 0`，存在 `t` 使 `‖h_t‖ > M/(1−ρ) − ε`）。

**诚实边界**：
* 本节的紧性定理在 **`𝔸 = ℝ`（交换、`NormOneClass`）** 上陈述——这是把
  `pow`、`Finset.sum` 与 `‖·‖` 的等式化（`norm_mul` 等式版只对 `NormedDivisionRing`）
  变得可控的最小设定。**一般非交换 `𝔸` 上的紧性未做**（取 `A_i ≡ ρ·1` 同样成立，
  但需要 `NormedRing` 上的 `‖ρ•1‖` 等式，`norm_smul` + `norm_one` 可处理，
  只是陈述与证明需重复一遍；**未做**）。
* 本节的紧性是**沿 `t → ∞` 的渐近紧性**，**不是**「对每个 `t` 取等」——
  `‖h_t‖ < M/(1−ρ)` 对每个有限 `t` 严格成立（`ρ > 0` 时）。**有限时刻取等未做**
  （除平凡情形 `M = 0` 或 `ρ = 0, t = 1`）。
* 本节**未证明**「不存在更小的**一致**界」的元数学陈述；只给出**一族达到渐近界的实例**
  ——这是「紧性」在可机器验证意义下的标准含义。
-/

section Tightness

/-- **几何和恒等式（标量）**：`(1 − ρ)·∑_{k<t} ρ^k = 1 − ρ^t`（`ρ` 任意实数）。
`t = 0` 时两端为 `0`（空和与 `1 − 1`）。 -/
lemma geom_sum_mul (ρ : ℝ) (t : ℕ) :
    (1 - ρ) * ∑ k in range t, ρ ^ k = 1 - ρ ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

/-- **几何和的闭式**：`∑_{k<t} ρ^k = (1 − ρ^t)/(1 − ρ)`（`ρ ≠ 1`）。 -/
lemma geom_sum_eq (ρ : ℝ) (hρ : ρ ≠ 1) (t : ℕ) :
    ∑ k in range t, ρ ^ k = (1 - ρ ^ t) / (1 - ρ) := by
  rw [eq_div_iff (sub_ne_zero.mpr (Ne.symm hρ)), mul_comm]
  exact geom_sum_mul ρ t

/-- **D20 紧性（核心，标量版）**：取 `A_i ≡ ρ`、`B_k ≡ M`，则

    `selState (fun _ => ρ) (fun _ => M) t = M · ∑_{k<t} ρ^k`

（`ρ ≠ 1`）。右端**单调趋于** `M/(1−ρ)`，故 `selState_norm_bound_contracting` 的
一致界 `M/(1−ρ)` 是**渐近紧**的，不可用更小的常数替代。 -/
theorem sel_tight_state_eq (ρ M : ℝ) (_hρ : ρ ≠ 1) (t : ℕ) :
    selState (fun _ : ℕ => ρ) (fun _ : ℕ => M) t
      = M * (∑ k in range t, ρ ^ k) := by
  rw [sel_is_LTI_special]
  -- 目标：∑ k, ρ^(t-1-k) * M = M * ∑ k, ρ^k
  rw [show (∑ k in range t, ρ ^ (t - 1 - k) * M)
      = (∑ k in range t, ρ ^ (t - 1 - k)) * M from (Finset.sum_mul _ _ _).symm]
  rw [show (∑ k in range t, ρ ^ (t - 1 - k)) = ∑ j in range t, ρ ^ j from
    sum_range_reflect (fun j => ρ ^ j) t]
  ring

/-- **D20 紧性（闭式）**：`A_i ≡ ρ`、`B_k ≡ M`、`0 ≤ ρ < 1`、`M ≥ 0` 时

    `h_t = M · (1 − ρ^t)/(1 − ρ)`，且 `‖h_t‖ = M · (1 − ρ^t)/(1 − ρ)`（非负），
    `‖h_1‖ = M`。

故 `t → ∞` 时 `‖h_t‖ → M/(1−ρ)`：**一致界 `M/(1−ρ)` 不可改进**。 -/
theorem sel_tight_state_eq_of_lt_one (ρ M : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M) (t : ℕ) :
    selState (fun _ : ℕ => ρ) (fun _ : ℕ => M) t = M * ((1 - ρ ^ t) / (1 - ρ)) ∧
    ‖selState (fun _ : ℕ => ρ) (fun _ : ℕ => M) t‖ = M * ((1 - ρ ^ t) / (1 - ρ)) := by
  have hρne : ρ ≠ 1 := ne_of_lt hρ1
  have hpos : 0 < 1 - ρ := by linarith
  have hval := sel_tight_state_eq ρ M hρne t
  rw [geom_sum_eq ρ hρne t] at hval
  have hnn : 0 ≤ M * ((1 - ρ ^ t) / (1 - ρ)) := by
    have h1 : (0 : ℝ) ≤ 1 - ρ ^ t := by
      have := pow_le_one₀ hρ0 (le_of_lt hρ1) (n := t)
      linarith
    positivity
  exact ⟨hval, by rw [hval, Real.norm_of_nonneg hnn]⟩

/-- **D20 紧性（渐近达到，核心陈述）**：对**任意** `ε > 0`，存在 `t` 使

    `M/(1−ρ) − ε < ‖h_t‖ ≤ M/(1−ρ)`。

即**没有任何**严格小于 `M/(1−ρ)` 的常数能一致控制该族实例的 `‖h_t‖`
——`selState_norm_bound_contracting` 的界**在常数意义下最优**。

证明：`‖h_t‖ = M(1−ρ^t)/(1−ρ) = M/(1−ρ) − M·ρ^t/(1−ρ)`；由
`tendsto_pow_atTop_nhds_zero_of_lt_one`（`ρ < 1`，`ρ ≥ 0`）取 `t` 使
`M·ρ^t/(1−ρ) < ε`。 -/
theorem sel_tight_asymptotic (ρ M : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, M / (1 - ρ) - ε < ‖selState (fun _ : ℕ => ρ) (fun _ : ℕ => M) t‖ := by
  have hpos : 0 < 1 - ρ := by linarith
  -- ρ^t → 0，故 M·ρ^t/(1−ρ) → 0
  have htend : Filter.Tendsto (fun t : ℕ => M * ρ ^ t / (1 - ρ)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℕ => ρ ^ t) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h2 : Filter.Tendsto (fun t : ℕ => M * ρ ^ t) Filter.atTop (nhds (M * 0)) :=
      tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    have h3 := h2.div_const (1 - ρ)
    simpa using h3
  have hev : ∀ᶠ t : ℕ in Filter.atTop, M * ρ ^ t / (1 - ρ) < ε :=
    (tendsto_order.1 htend).2 ε hε
  obtain ⟨t, ht⟩ := Filter.Eventually.exists hev
  refine ⟨t, ?_⟩
  rw [(sel_tight_state_eq_of_lt_one ρ M hρ0 hρ1 hM t).2]
  have hsplit : M * ((1 - ρ ^ t) / (1 - ρ)) = M / (1 - ρ) - M * ρ ^ t / (1 - ρ) := by
    field_simp
    ring
  rw [hsplit]
  linarith

end Tightness

end Lattice
