import Mathlib
import Lattice.Lib.Architectures.RealMatrixNorm
/-!
# LATTICE: Toeplitz 与 circulant 结构矩阵

在 `RealMatrixNorm`（Frobenius 范数 `frobeniusNorm`）之上，研究两类经典**结构矩阵**：

  1. **Toeplitz 矩阵** `toeplitz t i j = t (j - i)`（`ℤ` 上的平移不变量）：
     - `toeplitz_apply`（定义展开）、`toeplitz_diag`（对角线 = `t 0`）；
     - `toeplitz_transpose`：`(toeplitz t)ᵀ = toeplitz (fun k => t (-k))`；
     - `toeplitz_symmetric`：`t` 偶（`∀ k, t (-k) = t k`）⟹ Toeplitz 矩阵对称；
     - `frobeniusNorm_toeplitz_sq`：Frobenius 平方的定义展开
       `(frobeniusNorm (toeplitz t))^2 = ∑ i, ∑ j, t (j - i)^2`；
     - `toeplitz_row_sum_le_band`：**逐对角计数**形式——若 `t` 在带 `s : Finset ℤ`
       外为零，则每行的平方和 ≤ `∑_{k∈s} t k^2`（用 `∑ j, t (j-i)^2` 经
       平移 `j ↦ j - i` 与带 `s` 的子集比较）；
     - `toeplitz_band_bound`：带外为零 ⟹
       `(frobeniusNorm (toeplitz t))^2 ≤ n * ∑_{k∈band} t k^2`（带 `band = Icc (-w) w`）。
  2. **circulant 矩阵** `circulant c i j = c ((j + n - i) mod n)`（`[NeZero n]`）：
     - `circulant_eq_sub`：定义为 `%` 形式，但同时等于群运算形式 `c (j - i)`
       （`Fin n` 在 `[NeZero n]` 下是加法群）；其值层面的桥接由辅助引理
       `circulant_val_eq` 给出（**修复**：原稿的裸 `omega` 在 mathlib 4.14 上
       无法看穿 `%` 语义而失败，现改用 `Fin.coe_int_sub_eq_mod` +
       `Int.ofNat_emod` + `Int.add_mul_emod_self` 的显式 ℤ 路线）；
     - `circulant_mulVec`：`(circulant c) *ᵥ x = fun i => ∑ k, c k * x (i + k)`
       （循环卷积重指标，用 `Equiv.addRight` 做平移）；
     - `circulant_row_sum`：`∑ j, c (j - i)^2 = ∑ k, c k^2`（每行恰是 `c` 的一个重排）；
     - `circulant_frobenius_sq`：**主交付**闭形式
       `(frobeniusNorm (circulant c))^2 = n * ∑ k, c k^2`；
     - `circulant_constant_vector`：全 1 向量是特征向量，特征值 `∑ k, c k`。

诚实标注（无 sorry / axiom / admit）：
- **circulant 的离散 Fourier 对角化（DFT 特征基）未证/未做**：mathlib 4.14 未提供
  可直接使用的 circulant 特征分解/DFT 基，故本文件**不陈述**任何 DFT 对角化结论，
  只证明不含 `Complex.exp` 的纯代数事实（重指标、范数闭形式、全 1 特征向量）；
- `toeplitz_band_bound` 给出的是**带内平方和**形式的界，不是 `n * (2w+1) * max` 这种
  显式 `(2w+1)` 计数形式——该 sharper 计数（需 `Finset.card_Icc` 型基数引理）**未做**；
  本文件以带外为零 + 带内平方和作为**降级**的诚实版本；
- Toeplitz 部分只做转置对称性，未做 Hermitian/正定/谱等更一层的结构；
- 未声称 circulant 与 Toeplitz 之外的（如 Hankel、Vandermonde）结构。
-/

noncomputable section

namespace Lattice

open Matrix
open scoped BigOperators

/-! ## 一、Toeplitz 矩阵 -/

/-- Toeplitz 矩阵：`toeplitz t i j = t (j - i)`，即元素只依赖 (`Fin` 指标提升到 `ℤ` 后的)
下标差 `j - i`。 -/
def toeplitz {n : ℕ} (t : ℤ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => t ((j : ℤ) - (i : ℤ))

/-- 定义展开（`rfl`）：`toeplitz t i j = t (j - i)`。 -/
theorem toeplitz_apply {n : ℕ} (t : ℤ → ℝ) (i j : Fin n) :
    toeplitz t i j = t ((j : ℤ) - (i : ℤ)) := rfl

/-- 对角线元素：`toeplitz t i i = t 0`。 -/
theorem toeplitz_diag {n : ℕ} (t : ℤ → ℝ) (i : Fin n) : toeplitz t i i = t 0 := by
  simp [toeplitz]

/-- 转置把参数 `t` 变为 `fun k => t (-k)`：`(toeplitz t)ᵀ = toeplitz (fun k => t (-k))`。

**修复**：右端 `toeplitz (fun k => t (-k))` 无法由参数推出维数 `n`（报
`don't know how to synthesize implicit argument 'n'`），故显式钉住类型
`Matrix (Fin n) (Fin n) ℝ`。 -/
theorem toeplitz_transpose {n : ℕ} (t : ℤ → ℝ) :
    (toeplitz t : Matrix (Fin n) (Fin n) ℝ)ᵀ
      = (toeplitz (fun k => t (-k)) : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [Matrix.transpose_apply, toeplitz]
  congr 1
  exact (neg_sub (j : ℤ) (i : ℤ)).symm

/-- **对称性**：若 `t` 为偶函数（`∀ k, t (-k) = t k`），则 `toeplitz t` 对称
（`(toeplitz t)ᵀ = toeplitz t`）。 -/
theorem toeplitz_symmetric {n : ℕ} (t : ℤ → ℝ) (h : ∀ k, t (-k) = t k) :
    (toeplitz t : Matrix (Fin n) (Fin n) ℝ)ᵀ
      = (toeplitz t : Matrix (Fin n) (Fin n) ℝ) := by
  rw [toeplitz_transpose]
  ext i j
  exact h ((j : ℤ) - (i : ℤ))
/-- Frobenius 平方的定义展开：
`(frobeniusNorm (toeplitz t))^2 = ∑ i, ∑ j, t (j - i)^2`。 -/
theorem frobeniusNorm_toeplitz_sq {n : ℕ} (t : ℤ → ℝ) :
    (frobeniusNorm (toeplitz t : Matrix (Fin n) (Fin n) ℝ)) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, t ((j : ℤ) - (i : ℤ)) ^ 2 := by
  rw [frobeniusNorm_sq]
  rfl

/-- **逐对角计数（行形式）**：给定 `s : Finset ℤ`，若 `t` 在 `s` 外为零，
则 Toeplitz 矩阵每一行的平方和 ≤ `∑_{k∈s} t k^2`。
证明：行和经平移 `j ↦ (j:ℤ) - (i:ℤ)` 成为 `s` 的一个子多重集上的和
（`Finset.sum_image` 重指标 + `Finset.sum_subset` 丢掉零项 + 子集单调）。 -/
theorem toeplitz_row_sum_le_band {n : ℕ} (t : ℤ → ℝ) (i : Fin n) (s : Finset ℤ)
    (hw : ∀ k : ℤ, k ∉ s → t k = 0) :
    ∑ j : Fin n, t ((j : ℤ) - (i : ℤ)) ^ 2 ≤ ∑ k in s, t k ^ 2 := by
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin n)), ∀ y ∈ (Finset.univ : Finset (Fin n)),
      (x : ℤ) - (i : ℤ) = (y : ℤ) - (i : ℤ) → x = y := by
    intro x _ y _ h
    have h1 : (x : ℤ) = (y : ℤ) := by
      have := congrArg (fun z : ℤ => z + (i : ℤ)) h
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    have h2 : x.val = y.val := by exact_mod_cast h1
    exact Fin.ext h2
  have hzero : ∀ k ∈ (Finset.univ.image (fun j : Fin n => (j : ℤ) - (i : ℤ))),
      k ∉ (Finset.univ.image (fun j : Fin n => (j : ℤ) - (i : ℤ))) ∩ s → t k ^ 2 = 0 := by
    intro k hk hkns
    have hks : k ∉ s := fun hks => hkns (Finset.mem_inter.mpr ⟨hk, hks⟩)
    rw [hw k hks]
    ring
  -- **修复**：`Finset.sum_image` 的形参顺序是 `(g : γ → α)`（映射）与 `(f : α → β)`（被求和函数），
  -- 原稿的 `(g := fun k : ℤ => t k ^ 2)` 误把被求和函数喂给了映射位，报
  -- `t k ^ 2 has type ℝ but is expected to have type Fin n`；此处改为 `(g := 映射)` + `(f := 被求和函数)`。
  calc ∑ j : Fin n, t ((j : ℤ) - (i : ℤ)) ^ 2
      = ∑ k in Finset.univ.image (fun j : Fin n => (j : ℤ) - (i : ℤ)), t k ^ 2 :=
        (Finset.sum_image (s := (Finset.univ : Finset (Fin n)))
          (g := fun j : Fin n => (j : ℤ) - (i : ℤ)) (f := fun k : ℤ => t k ^ 2) hinj).symm
    _ = ∑ k in (Finset.univ.image (fun j : Fin n => (j : ℤ) - (i : ℤ))) ∩ s, t k ^ 2 :=
        (Finset.sum_subset (fun x hx => (Finset.mem_inter.mp hx).1) hzero).symm
    _ ≤ ∑ k in s, t k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_inter.mp hx).2)
          (fun k _ _ => sq_nonneg _)

/-- **带界（Toeplitz 的 `band` 形式）**：若 `t` 在带 `Icc (-w) w` 外为零，
则 `(frobeniusNorm (toeplitz t))^2 ≤ n * ∑_{k∈Icc (-w) w} t k^2`。
（逐行用 `toeplitz_row_sum_le_band`，再对 `n` 行求和。）

**修复**：`frobeniusNorm` 的两个维数指标 `{m n : ℕ}` 相互独立，
`frobeniusNorm (toeplitz t)` 无法仅由参数推出方阵维数（报
`don't know how to synthesize implicit argument 'n'`），故此处用
`(toeplitz t : Matrix (Fin n) (Fin n) ℝ)` 显式钉住 `m = n = n`。 -/
theorem toeplitz_band_bound {n : ℕ} (t : ℤ → ℝ) (w : ℕ)
    (hw : ∀ k : ℤ, k ∉ Finset.Icc (-(w : ℤ)) (w : ℤ) → t k = 0) :
    (frobeniusNorm (toeplitz t : Matrix (Fin n) (Fin n) ℝ)) ^ 2
      ≤ (n : ℝ) * ∑ k in Finset.Icc (-(w : ℤ)) (w : ℤ), t k ^ 2 := by
  rw [frobeniusNorm_toeplitz_sq]
  calc ∑ i : Fin n, ∑ j : Fin n, t ((j : ℤ) - (i : ℤ)) ^ 2
      ≤ ∑ _i : Fin n, ∑ k in Finset.Icc (-(w : ℤ)) (w : ℤ), t k ^ 2 :=
        Finset.sum_le_sum (fun i _ => toeplitz_row_sum_le_band t i _ hw)
    _ = (n : ℝ) * ∑ k in Finset.Icc (-(w : ℤ)) (w : ℤ), t k ^ 2 := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-! ## 二、circulant 矩阵 -/

/-- circulant 矩阵（循环矩阵）：`circulant c i j = c ((j + n - i) mod n)`，
即第 `i` 行是 `c` 循环右移 `i` 位。要求 `[NeZero n]` 以免除 `n = 0` 的证明义务。 -/
def circulant {n : ℕ} [NeZero n] (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => c ⟨((j : ℕ) + n - (i : ℕ)) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

/-- 定义展开（`rfl`）。 -/
theorem circulant_apply {n : ℕ} [NeZero n] (c : Fin n → ℝ) (i j : Fin n) :
    circulant c i j
      = c ⟨((j : ℕ) + n - (i : ℕ)) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩ := rfl

/-- **值的桥接引理**：`(j - i : Fin n)` 的自然数值等于 `%` 定义中用到的
`(j + n - i) % n`。证明路线：两边都提升到 `ℤ`（左端用 `Fin.coe_int_sub_eq_mod`，
右端用 `Int.ofNat_emod` + `Nat.cast_sub`），再用 `Int.add_mul_emod_self` 消去
多出的一个 `n`，最后 `Nat.cast_injective` 降回 `ℕ`。
（原稿此处用裸 `omega`，在 mathlib 4.14 上**实测失败**——它无法看穿 `%` 的语义。） -/
theorem circulant_val_eq {n : ℕ} [NeZero n] (i j : Fin n) :
    ((j - i : Fin n) : ℕ) = ((j : ℕ) + n - (i : ℕ)) % n := by
  have hij : (i : ℕ) ≤ (j : ℕ) + n := by have := i.isLt; omega
  have h4 : (((j - i : Fin n) : ℕ) : ℤ) = (((j : ℤ) - (i : ℤ)) % n) := by
    rw [Fin.coe_int_sub_eq_mod]
  have h6 : ((((j : ℕ) + n - (i : ℕ)) % n : ℕ) : ℤ)
      = (((j : ℤ) - (i : ℤ)) % n) := by
    rw [Int.ofNat_emod ((j : ℕ) + n - (i : ℕ)) n, Nat.cast_sub hij]
    push_cast
    rw [show (j : ℤ) + (n : ℤ) - (i : ℤ) = ((j : ℤ) - (i : ℤ)) + 1 * (n : ℤ) by ring,
      Int.add_mul_emod_self]
  exact Nat.cast_injective (h4.trans h6.symm)

/-- **`%` 定义 = 群运算定义**：`circulant c i j = c (j - i)`，
其中 `j - i` 是 `[NeZero n]` 下 `Fin n` 的加法群减法。
证明：两边作为 `Fin n` 相等（`Fin.ext` + `circulant_val_eq`），再 `congr`。 -/
theorem circulant_eq_sub {n : ℕ} [NeZero n] (c : Fin n → ℝ) (i j : Fin n) :
    circulant c i j = c (j - i) := by
  unfold circulant
  congr 1
  apply Fin.ext
  exact (circulant_val_eq i j).symm

/-- **循环卷积重指标**：`(circulant c) *ᵥ x = fun i => ∑ k, c k * x (i + k)`。
用 `Equiv.addRight i` 把 `∑ j, c (j - i) * x j` 重指标为 `∑ k, c k * x (i + k)`。 -/
theorem circulant_mulVec {n : ℕ} [NeZero n] (c : Fin n → ℝ) (x : Fin n → ℝ) :
    (circulant c) *ᵥ x = fun i : Fin n => ∑ k : Fin n, c k * x (i + k) := by
  funext i
  show (∑ j : Fin n, circulant c i j * x j) = ∑ k : Fin n, c k * x (i + k)
  have hrew : (∑ j : Fin n, circulant c i j * x j)
      = ∑ j : Fin n, c (j - i) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [circulant_eq_sub]
  rw [hrew]
  have h := Equiv.sum_comp (Equiv.addRight i) (fun j : Fin n => c (j - i) * x j)
  rw [← h]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (Equiv.addRight i) k = k + i from rfl, show k + i - i = k by abel,
      add_comm k i]

/-- **每行是 `c` 的重排**：`∑ j, c (j - i)^2 = ∑ k, c k^2`。 -/
theorem circulant_row_sum {n : ℕ} [NeZero n] (c : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, c (j - i) ^ 2 = ∑ k : Fin n, c k ^ 2 := by
  have h := Equiv.sum_comp (Equiv.addRight i) (fun j : Fin n => c (j - i) ^ 2)
  calc ∑ j : Fin n, c (j - i) ^ 2
      = ∑ k : Fin n, c ((Equiv.addRight i) k - i) ^ 2 := h.symm
    _ = ∑ k : Fin n, c k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [show (Equiv.addRight i) k = k + i from rfl, show k + i - i = k by abel]

/-- **主交付：circulant 的 Frobenius 范数闭形式**
`(frobeniusNorm (circulant c))^2 = n * ∑ k, c k^2`。
证明：逐行重排（`circulant_row_sum`）后每行贡献 `∑ k, c k^2`，共 `n` 行。 -/
theorem circulant_frobenius_sq {n : ℕ} [NeZero n] (c : Fin n → ℝ) :
    (frobeniusNorm (circulant c)) ^ 2 = (n : ℝ) * ∑ k : Fin n, c k ^ 2 := by
  rw [frobeniusNorm_sq]
  calc ∑ i : Fin n, ∑ j : Fin n, (circulant c i j) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, c (j - i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [circulant_eq_sub]
    _ = ∑ _i : Fin n, ∑ k : Fin n, c k ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact circulant_row_sum c i
    _ = (n : ℝ) * ∑ k : Fin n, c k ^ 2 := by
        simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-- **全 1 向量是 circulant 的特征向量**（特征值为 `c` 之和）：
`(circulant c) *ᵥ (fun _ => 1) = fun _ => ∑ k, c k`。
由 `circulant_mulVec` 与 `∑ k, c k * 1 = ∑ k, c k` 直接得到。 -/
theorem circulant_constant_vector {n : ℕ} [NeZero n] (c : Fin n → ℝ) :
    (circulant c) *ᵥ (fun _ : Fin n => (1 : ℝ)) = fun _ : Fin n => ∑ k : Fin n, c k := by
  rw [circulant_mulVec]
  funext i
  apply Finset.sum_congr rfl
  intro k _
  ring

end Lattice
