import Mathlib

/-!
# LATTICE: 无穷维 / 可变长度泛化 —— 长度依赖前向链的界与可数维截断收敛

固定长度结果向**可变长度 / 无穷维**的诚实推广。本文件只做可在 mathlib 4.14
上完整证明的部分，并把「真正的无穷维完整版」明确标为后续工作：

  1. **长度依赖前向链**：`varLengthChain F n` = 层 `F 0, …, F n−1` 依次复合
     （结构递归，长度 n 可变）；`lengthBound L n = L ^ n`；
  2. **长度 n 的显式界**：每层满足 `‖F i x‖ ≤ L·‖x‖`（L ≥ 0）⟹
     `‖varLengthChain F n x‖ ≤ L ^ n · ‖x‖`（**界显式含 n**）；
  3. **界关于长度单调**：`1 ≤ L ⟹ Monotone (lengthBound L)`（`n ≤ m ⟹ L^n ≤ L^m`）；
  4. **组件常数组装的界单调**：每层常数 `c i ≥ 1` 逐层相乘
     `compBound c n = ∏_{i<n} c i`，则 `Monotone (compBound c)`——
     异构层常数的界也关于长度单调；
  5. **可数维 ℓ² 型截断收敛**：`a : ℕ → ℝ`，`a n ≥ 0` 且所有有限截断
     `Σ_{n<N} a n ≤ C` ⟹ `Summable a` 且 `∑' n, a n ≤ C`
     （`summable_of_sum_range_le` + `Real.tsum_le_of_sum_range_le`）——
     有限截断的界在无穷维极限处收敛不漏；
  6. **长度泛化**：给定 `1 ≤ L`，长度 n 的界可被任意更长长度 m ≥ n 的界控制
     （`length_generalization`），把「固定长度结论」推广到整个长度族。

诚实边界（**后续工作，本文件未证**）：
  * 真正的希尔伯特空间无穷直和/算子范数版本（`ℓ²(ℕ)` 上的有界算子与
    一致长度极限）需要 Mathlib 的 `lp` 空间与算子理论，属后续模块；
  * 本文件的「无穷维」部分是 ℓ² 型**可数维正项截断**结论（对所有有限截断
    一致有界 ⟹ 收敛），不含紧性/完备性等算子层面主张；
  * 未声称任何未证明的无穷维紧性或不变量。

诚实性：所有定理只引用 mathlib 4.14 现成引理，无 sorry/axiom/admit。
模型无关：任意赋范空间 E、任意层族、任意常数族、任意非负可和列。
-/

noncomputable section

namespace Lattice

/-! ## 第一节：长度依赖前向链（可变长度） -/

/-- 长度依赖前向链：`varLengthChain F n x` = 把层 `F 0, F 1, …, F (n−1)`
自内向外依次作用于 x（`F 0` 最先作用，`F (n−1)` 最后）。
长度 n 是参数，故同一层族可对任意长度求值（可变长度泛化的载体）。 -/
def varLengthChain {E : Type*} (F : ℕ → E → E) : ℕ → E → E
  | 0 => fun x => x
  | n + 1 => fun x => F n (varLengthChain F n x)

@[simp]
theorem varLengthChain_zero {E : Type*} (F : ℕ → E → E) (x : E) :
    varLengthChain F 0 x = x := rfl

@[simp]
theorem varLengthChain_succ {E : Type*} (F : ℕ → E → E) (n : ℕ) (x : E) :
    varLengthChain F (n + 1) x = F n (varLengthChain F n x) := rfl

variable {E : Type*} [NormedAddCommGroup E]

/-- 长度界：`lengthBound L n = L ^ n`（长度 n 的显式界因子）。 -/
def lengthBound (L : ℝ) (n : ℕ) : ℝ := L ^ n

/-! ## 第二节：长度 n 的显式界 -/

/-- **长度 n 的界**（显式含 n）：每层 `‖F i x‖ ≤ L·‖x‖`（L ≥ 0）⟹
`‖varLengthChain F n x‖ ≤ L ^ n · ‖x‖`。
归纳每一层消耗一个因子 L，n 层给出 L^n——界显式含长度 n，
这是「可变序列长度」控制的核心形式。 -/
theorem varLength_error_bound (F : ℕ → E → E) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ i x, ‖F i x‖ ≤ L * ‖x‖) (n : ℕ) (x : E) :
    ‖varLengthChain F n x‖ ≤ lengthBound L n * ‖x‖ := by
  induction n with
  | zero => simp [lengthBound]
  | succ n ih =>
    rw [varLengthChain_succ]
    calc
      ‖F n (varLengthChain F n x)‖ ≤ L * ‖varLengthChain F n x‖ := hF n _
      _ ≤ L * (lengthBound L n * ‖x‖) := mul_le_mul_of_nonneg_left ih hL
      _ = lengthBound L (n + 1) * ‖x‖ := by
        rw [lengthBound, lengthBound, pow_succ]
        ring

/-- 长度 n 的界的等价写法（展开 `lengthBound`）：`‖·‖ ≤ L ^ n · ‖x‖`。 -/
theorem varLength_error_bound_pow (F : ℕ → E → E) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ i x, ‖F i x‖ ≤ L * ‖x‖) (n : ℕ) (x : E) :
    ‖varLengthChain F n x‖ ≤ L ^ n * ‖x‖ := by
  have h := varLength_error_bound F L hL hF n x
  simpa [lengthBound] using h

/-! ## 第三节：界关于长度单调 -/

/-- **界关于长度单调**：`1 ≤ L ⟹ Monotone (lengthBound L)`，
即 `n ≤ m ⟹ lengthBound L n ≤ lengthBound L m`。
（「长度更长、界不更小」——可变长度控制的基本单调性。） -/
theorem bound_monotone_in_length (L : ℝ) (hL : 1 ≤ L) :
    Monotone (lengthBound L) := by
  intro n m h
  unfold lengthBound
  exact pow_le_pow_right₀ hL h

/-- 单调性的显式形式：`1 ≤ L` 且 `n ≤ m` ⟹ `L ^ n ≤ L ^ m`。 -/
theorem lengthBound_le_of_le (L : ℝ) (hL : 1 ≤ L) {n m : ℕ} (h : n ≤ m) :
    lengthBound L n ≤ lengthBound L m :=
  bound_monotone_in_length L hL h

/-! ## 第四节：组件常数组装的界关于长度单调 -/

/-- 组件常数组装的界：`compBound c n = ∏_{i<n} c i`
（异构层常数逐层相乘；`c i = L` 时退化为 `L^n = lengthBound L n`）。 -/
def compBound (c : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i in Finset.range n, c i

/-- 递推：`compBound c (n+1) = compBound c n * c n`。 -/
theorem compBound_succ (c : ℕ → ℝ) (n : ℕ) :
    compBound c (n + 1) = compBound c n * c n := by
  simp [compBound, Finset.prod_range_succ]

/-- `compBound c n` 非负（每层常数非负）。 -/
theorem compBound_nonneg (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (n : ℕ) :
    0 ≤ compBound c n :=
  Finset.prod_nonneg (fun i _ => hc i)

/-- **组件常数组装的界关于长度单调**：每层常数 `c i ≥ 1` ⟹
`Monotone (compBound c)`。证明：逐步 `compBound c (n+1) = compBound c n * c n
≥ compBound c n * 1 = compBound c n`，再由 `monotone_nat_of_le_succ`。 -/
theorem compBound_monotone (c : ℕ → ℝ) (hc : ∀ i, 1 ≤ c i) :
    Monotone (compBound c) := by
  apply monotone_nat_of_le_succ
  intro n
  have hnn : 0 ≤ compBound c n :=
    compBound_nonneg c (fun i => le_trans zero_le_one (hc i)) n
  rw [compBound_succ]
  calc
    compBound c n = compBound c n * 1 := by ring
    _ ≤ compBound c n * c n := mul_le_mul_of_nonneg_left (hc n) hnn

/-- 异构常数版长度界：每层 `‖F i x‖ ≤ c i · ‖x‖`（`c i ≥ 0`）⟹
`‖varLengthChain F n x‖ ≤ compBound c n · ‖x‖`
（`varLength_error_bound` 的逐层常数推广；`c` 常数组装的界）。 -/
theorem varLength_error_bound_hetero (F : ℕ → E → E) (c : ℕ → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hF : ∀ i x, ‖F i x‖ ≤ c i * ‖x‖) (n : ℕ) (x : E) :
    ‖varLengthChain F n x‖ ≤ compBound c n * ‖x‖ := by
  induction n with
  | zero => simp [compBound]
  | succ n ih =>
    rw [varLengthChain_succ]
    have hnn : 0 ≤ compBound c n := compBound_nonneg c hc n
    calc
      ‖F n (varLengthChain F n x)‖ ≤ c n * ‖varLengthChain F n x‖ := hF n _
      _ ≤ c n * (compBound c n * ‖x‖) := mul_le_mul_of_nonneg_left ih (hc n)
      _ = compBound c (n + 1) * ‖x‖ := by
        rw [compBound_succ]
        ring

/-- 异构常数版界关于长度单调的推论：`c i ≥ 1` 时，`n ≤ m` ⟹
`compBound c n ≤ compBound c m`（可变长度下界的单调控制）。 -/
theorem compBound_le_of_le (c : ℕ → ℝ) (hc : ∀ i, 1 ≤ c i) {n m : ℕ} (h : n ≤ m) :
    compBound c n ≤ compBound c m :=
  compBound_monotone c hc h

/-! ## 第五节：可数维 ℓ² 型截断收敛（有限截断的界在极限处不漏） -/

/-- **无穷和界（可数维 ℓ² 型）**：非负列 `a` 的**所有**有限截断
`Σ_{n<N} a n ≤ C` ⟹ `a` 可和且 `∑' n, a n ≤ C`。
即有限维截断的界在无穷维极限处一致保持（截断界不漏到极限之外）。
（`summable_of_sum_range_le` + `Real.tsum_le_of_sum_range_le`。） -/
theorem infinite_sum_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (C : ℝ)
    (hC : ∀ N, ∑ n in Finset.range N, a n ≤ C) :
    Summable a ∧ ∑' n, a n ≤ C :=
  ⟨summable_of_sum_range_le ha hC, Real.tsum_le_of_sum_range_le ha hC⟩

/-- 部分和关于截断长度单调（非负列）：`N ↦ Σ_{n<N} a n` 单调不减。
这是「可变长度」在无穷维方向的对应物。 -/
theorem partial_sum_monotone (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Monotone (fun N => ∑ n in Finset.range N, a n) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (ha N)

/-- 有限截断 ≤ 无穷和（非负可和列）：`Σ_{n<N} a n ≤ ∑' n, a n`。
（`sum_le_tsum`；截断界被无穷和支配。） -/
theorem infinite_sum_truncation_le_tsum (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : Summable a) (N : ℕ) :
    ∑ n in Finset.range N, a n ≤ ∑' n, a n :=
  sum_le_tsum (Finset.range N) (fun i _ => ha i) h

/-! ## 第六节：长度泛化（固定长度 ⟹ 任意长度） -/

/-- **长度泛化**：设 `1 ≤ L` 且每层 `‖F i x‖ ≤ L·‖x‖`，则
长度 n 的链被**任意更长长度** m ≥ n 的界控制：
`‖varLengthChain F n x‖ ≤ L ^ m · ‖x‖`（`n ≤ m`）。
即固定长度结论自动推广到整个长度族（可变序列长度的统一界）。 -/
theorem length_generalization (F : ℕ → E → E) (L : ℝ) (hL : 1 ≤ L)
    (hF : ∀ i x, ‖F i x‖ ≤ L * ‖x‖) (x : E) {n m : ℕ} (h : n ≤ m) :
    ‖varLengthChain F n x‖ ≤ L ^ m * ‖x‖ := by
  have h1 : ‖varLengthChain F n x‖ ≤ lengthBound L n * ‖x‖ :=
    varLength_error_bound F L (le_trans zero_le_one hL) hF n x
  have h2 : lengthBound L n ≤ lengthBound L m := lengthBound_le_of_le L hL h
  calc
    ‖varLengthChain F n x‖ ≤ lengthBound L n * ‖x‖ := h1
    _ ≤ lengthBound L m * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
    _ = L ^ m * ‖x‖ := by rw [lengthBound]

/-- 长度泛化（异构常数组装版）：`c i ≥ 1`、每层 `‖F i x‖ ≤ c i·‖x‖` ⟹
`n ≤ m ⟹ ‖varLengthChain F n x‖ ≤ compBound c m · ‖x‖`。 -/
theorem length_generalization_hetero (F : ℕ → E → E) (c : ℕ → ℝ)
    (hc : ∀ i, 1 ≤ c i) (hF : ∀ i x, ‖F i x‖ ≤ c i * ‖x‖) (x : E) {n m : ℕ}
    (h : n ≤ m) :
    ‖varLengthChain F n x‖ ≤ compBound c m * ‖x‖ := by
  have h1 : ‖varLengthChain F n x‖ ≤ compBound c n * ‖x‖ :=
    varLength_error_bound_hetero F c (fun i => le_trans zero_le_one (hc i)) hF n x
  have h2 : compBound c n ≤ compBound c m := compBound_le_of_le c hc h
  calc
    ‖varLengthChain F n x‖ ≤ compBound c n * ‖x‖ := h1
    _ ≤ compBound c m * ‖x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg x)

/-! ## 注：无穷维闭环（诚实边界）
  可变长度由 `varLengthChain`（长度参数）+ `varLength_error_bound`（显式含 n 的界）
  + `bound_monotone_in_length`/`compBound_monotone`（界关于长度单调）刻画；
  可数维方向由 `infinite_sum_bound`（有限截断一致有界 ⟹ 收敛且界保持）
  + `partial_sum_monotone` + `infinite_sum_truncation_le_tsum` 刻画；
  `length_generalization` 把固定长度结果推广到任意长度族。
  **未做（后续）**：ℓ²(ℕ) 上的有界算子范数、无穷层复合的一致收敛/紧性，
  以及 operator-norm 层的无穷维完整版——需 Mathlib `lp` 与算子理论支持。 -/

end Lattice
