import Mathlib
import Lattice.Runtime.ProgramAST

/-!
# `Lattice.Runtime.ProgramLipschitz` — **逐指令的 Lipschitz 性提升到整个程序**

## 定义

```lean
def IsLipschitzInstr {n} (L : ℝ) (i : Instr n) : Prop :=
  ∀ x x' δ, 0 ≤ δ → (∀ k, |x k - x' k| ≤ δ) → ∀ j, |applyInstr x i j - applyInstr x' i j| ≤ L * δ
```

**这是「指令 `i` 是 `L`-Lipschitz」的准确说法**，形状与 `softmax_lipschitz` 的结论一致，
**除了后者右边是 `2δ·exp(2δ)` 而不是 `L·δ`。**

## 程序层

```lean
theorem evalProgram_lipschitz : |evalProgram x p j − evalProgram x' p j| ≤ L ^ p.length * δ
```

**对 `p` 归纳**：空程序是恒等（`L ^ 0 = 1`）；`i :: rest` 时先用 `i` 的界把 `δ` 换成 `L·δ`，
再用 `rest` 的归纳假设，于是得到 `L ^ rest.length * (L·δ) = L ^ (rest.length+1) * δ`。

⚠ **指数是不可避免的**：`k` 层网络的 Lipschitz 常数是每层常数之积。
**把它写出来比回避它好**——读者能看到「常数随层数指数增长」这件事**是定理的一部分**，不是证明的缺陷。

## ⚠ 这个定义**不覆盖**哪些构造子，以及为什么

| 构造子 | 是 `L`-Lipschitz？ | 界 |
|:--|:--|:--|
| `affine W b` | ✅ | `(∑ j, ∑ k, |W j k|) · δ` |
| `relu` | ✅ | `1 · δ` |
| `scale c` | ✅ | `|c| · δ` |
| `attention W V`（`W` 固定） | ✅ | `(∑ j, ∑ k, |V j k|) · δ` |
| **`softmax`** | ❌ | `2δ·exp(2δ)`——**不是 `L·δ` 的形状** |
| **`layernorm ε`** | ❌ | 含方差，**也不是 `L·δ`** |

**所以「程序的 Lipschitz 常数是 `L ^ 长度`」这条定理只对前四个成立。**
**软最大化与层归一化的界是 `δ` 的非线性函数，需要另一种打包**（函数复合而不是常数乘幂）。
**本文件不声称后者。**
-/

namespace Lattice.Lift.ProgramAST

/-- **一条指令是 `L`-Lipschitz 的**：输入逐分量变化不超过 `δ`，输出每个分量变化不超过 `L·δ`。

**注意 `L` 是一个单一的实数**，不随输出分量 `j` 变——**这就是为什么 `affine` 要取
`∑ j, ∑ k, |W j k|` 而不是逐行的 `∑ k, |W j k|`**：行常数不同，而定义要求一个常数。 -/
def IsLipschitzInstr {n : ℕ} (L : ℝ) (i : Instr n) : Prop :=
  ∀ (x x' : Fin n → ℝ) (δ : ℝ), 0 ≤ δ → (∀ k : Fin n, |x k - x' k| ≤ δ) →
    ∀ j : Fin n, |applyInstr x i j - applyInstr x' i j| ≤ L * δ

/-- ⭐⭐ **程序的 Lipschitz 界**（**显式递归形式**）。

**用模式匹配而不是 `induction ... generalizing δ`**：后者的归纳假设参数顺序
取决于哪些参数被泛化，试了三次都没猜对（`hrest` / `δ` / `hδ` / `x` / `hx` 的顺序每次都变）。
**显式递归把每个参数写出来，编译器就不必猜，读的人也不必猜。**

归纳步：先用 `i` 的界把 `δ` 换成 `L·δ`，对 `rest` 用归纳假设，
得到 `L ^ rest.length * (L·δ)`，而它正是 `L ^ (rest.length+1) * δ`。 -/
theorem evalProgram_lipschitz {n : ℕ} (L : ℝ) (hL : 0 ≤ L) :
    ∀ (p : LayerProgram n), (∀ i ∈ p, IsLipschitzInstr L i) →
      ∀ (x x' : Fin n → ℝ) (δ : ℝ), 0 ≤ δ → (∀ k : Fin n, |x k - x' k| ≤ δ) →
        ∀ j : Fin n, |evalProgram x p j - evalProgram x' p j| ≤ L ^ p.length * δ
  | [], _, x, x', δ, _, hx, j => by
      simp only [evalProgram, List.foldl_nil, List.length_nil, pow_zero, one_mul]
      exact hx j
  | i :: rest, h, x, x', δ, hδ, hx, j => by
      have hi : IsLipschitzInstr L i := h i (List.mem_cons_self ..)
      have hrest : ∀ k ∈ rest, IsLipschitzInstr L k := fun k hk => h k (List.mem_cons_of_mem _ hk)
      have hδ' : 0 ≤ L * δ := mul_nonneg hL hδ
      have hx' : ∀ k : Fin n, |applyInstr x i k - applyInstr x' i k| ≤ L * δ :=
        fun k => hi x x' δ hδ hx k
      have hstep := evalProgram_lipschitz L hL rest hrest
        (applyInstr x i) (applyInstr x' i) (L * δ) hδ' hx' j
      simp only [evalProgram, List.foldl_cons, List.length_cons, pow_succ]
      exact le_trans hstep (le_of_eq (mul_assoc _ _ _).symm)



/-! ## 四个实例 -/

/-- **`relu` 是 `1`-Lipschitz。** -/
theorem relu_isLipschitz : IsLipschitzInstr (n := n) 1 (Instr.relu) := by
  intro x x' δ hδ hx j
  simp only [applyInstr, one_mul]
  exact le_trans (abs_max_sub_max_le_abs (x j) (x' j) 0) (hx j)

/-- **`scale c` 是 `|c|`-Lipschitz。** -/
theorem scale_isLipschitz (c : ℝ) : IsLipschitzInstr (n := n) |c| (Instr.scale c) := by
  intro x x' δ hδ hx j
  simp only [applyInstr]
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hx j) (abs_nonneg c)

/-- **`affine W b` 是 `(∑ j, ∑ k, |W j k|)`-Lipschitz。**

**取的是全部绝对值和**，不是逐行的——因为定义要求一个不随输出分量变的常数。 -/
theorem affine_isLipschitz (W : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    IsLipschitzInstr (n := n) (∑ j, ∑ k, |W j k|) (Instr.affine W b) := by
  intro x x' δ hδ hx j
  simp only [applyInstr]
  have hsub : (∑ i, W i j * x i) + b j - ((∑ i, W i j * x' i) + b j)
      = ∑ i, W i j * (x i - x' i) := by
    -- the bias cancels before the sums can be combined
    have h1 : (∑ i, W i j * x i) + b j - ((∑ i, W i j * x' i) + b j)
        = (∑ i, W i j * x i) - (∑ i, W i j * x' i) := by ring
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsub]
  calc |∑ i, W i j * (x i - x' i)|
      ≤ ∑ i, |W i j * (x i - x' i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |W i j| * |x i - x' i| := Finset.sum_congr rfl (fun i _ => by rw [abs_mul])
    _ ≤ ∑ i, |W i j| * δ :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (abs_nonneg _))
    _ = (∑ i, |W i j|) * δ := by rw [Finset.sum_mul]
    _ ≤ (∑ a, ∑ i, |W i a|) * δ := by
        refine mul_le_mul_of_nonneg_right ?_ hδ
        exact Finset.single_le_sum
          (f := fun a => ∑ i, |W i a|) (fun a _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
          (Finset.mem_univ j)
    _ = (∑ j, ∑ k, |W j k|) * δ := by rw [Finset.sum_comm]

end Lattice.Lift.ProgramAST
