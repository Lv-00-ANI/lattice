import Mathlib
import Lattice.Lib.Compiler.ReversibilityCriterion
import Lattice.Lib.Compiler.IRWeightsBridge

/-!
# **判据在真实链路上的两个实例**（阶段 K，P6 / O-3）

## 为什么要补这两个实例

**第 942 轮的 `reversibility_criterion` 是一个判据：**

```
compile 单射  ⟺  存在 extract 使 extract ∘ compile = id
```

**已有的两个实例是 `convertVec`（线性，单射）与 ReLU（折叠，非单射）。**
**=> 但它们都不是**这条链路本身**的类型。**

**本文件把判据用在第 964–965 轮建立的**真实链路**上，给出**一正一负**两个实例：**

| 方向 | 陈述 | 含义 |
|:--|:--|:--|
| **正** | **`encodeGrid` 可逆** | **网格函数 → 权重向量**无损**，提取就是 `decodeGrid`** |
| **负** | **`gridEval` 在 `[0,1]` 上**非单射** | **权重向量 → 行为**有损**：单位区间看不到 `n` 之后的系数** |

**=> 于是「符号 ⇄ 权重」的**两个方向**各有精确判决：**
**符号 → 权重可以无损（单射编码），但权重 → 符号**不可能无损**（行为不决定全部权重）。**

## 负向实例为什么重要

**第 944–965 轮证明了「分段族能一致逼近到任意精度」——这是**正向**（符号 → 权重）。**
**=> 负向从未被陈述：**能不能从行为反推出权重？**

**=> 本文件的答案：**在 `[0,1]` 上不能**，因为 `segmentIndex n x ≤ n`，
所以索引 `n+1` 及其之后的系数**从不被读取**。
两个只在 `n+1` 处不同的网格函数在 `[0,1]` 上给出**同一个函数**。**

**=> 由判据的否证方向，**不存在**从 `[0,1]` 上的行为恢复权重的提取器。**

**=> 这就是审计所说「真正的难点只有 符号⇄权重 这一跳」的一个**精确、可验证**的内容：
反向不是难在算法，而是难在**信息不在那里**。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`encodeGrid_has_extract`** | **⭐⭐ 显式提取：`decodeGrid`** |
| **`encodeGrid_reversible_by_criterion`** | **⭐⭐⭐ 判据的正向实例** |
| **`segmentIndex_le_on_unit`** | **⭐⭐ `x ∈ [0,1]` 时 `segmentIndex n x ≤ n`** |
| **`gridEval_unit_not_injective`** | **⭐⭐⭐ 负向：行为不决定权重** |
| **`gridWeights_not_extractable`** | **⭐⭐⭐ 判据的否证方向：无提取器** | -/

namespace Lattice.Lib.Compiler.ReversibilityChain

open Set
open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.PiecewiseUniform
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler.ReversibilityCriterion

/-- **⭐⭐ 编码的显式提取就是 `decodeGrid`。**

**=> 第 965 轮的往返恒等直接给出左逆。** -/
theorem encodeGrid_has_extract :
    ∃ extract : Lattice.Core.IR.IRWeights → (ℕ → Segment),
      ∀ g, extract (encodeGrid g) = g :=
  ⟨decodeGrid, decodeGrid_encodeGrid⟩

/-- **⭐⭐⭐ 判据的**正向**实例：`encodeGrid` 单射，故有提取。**

**=> 这条把第 965 轮的 `encodeGrid_injective` 与第 942 轮的判据接起来：
「可逆」不再需要逐个构造提取器，而是由单射性**自动**得到。**

**★ `Inhabited (ℕ → Segment)` 在此**就地**提供（`Segment` 未声明全局实例，
与第 960 轮的处置一致：不为此添加全局实例）。** -/
theorem encodeGrid_reversible_by_criterion :
    ∃ extract : Lattice.Core.IR.IRWeights → (ℕ → Segment),
      ∀ g, extract (encodeGrid g) = g := by
  haveI : Inhabited (ℕ → Segment) := ⟨fun _ => ⟨0, 0⟩⟩
  exact (reversibility_criterion encodeGrid).mp encodeGrid_injective

/-- **⭐⭐ 单位区间上分段索引不超过 `n`。**

**=> `x < 1` 时 `segmentIndex n x < n`（第 955 轮）；
`x = 1` 时 `segmentIndex n 1 = n`（第 959 轮）。**
**=> 于是 `[0,1]` 上的求值**只读索引 `0..n`**。** -/
theorem segmentIndex_le_on_unit (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    segmentIndex n x ≤ n := by
  rcases eq_or_lt_of_le hx.2 with h1 | hlt
  · rw [h1, segmentIndex_at_one]
  · exact le_of_lt (segmentIndex_lt n hn x hx.1 hlt)

/-- **⭐⭐⭐ 负向：`[0,1]` 上的行为**不决定**权重向量。**

**=> 反例：只在索引 `n+1` 处不同的两个网格函数，
在 `[0,1]` 上给出**同一个函数**（因为该索引从不被读取）。** -/
theorem gridEval_unit_not_injective (n : ℕ) (hn : 0 < n) :
    ¬ Function.Injective
        (fun g : ℕ → Segment => fun x : Icc (0 : ℝ) 1 => gridEval g n x.1) := by
  intro hinj
  let g : ℕ → Segment := fun _ => ⟨0, 0⟩
  let h : ℕ → Segment := fun k => if k = n + 1 then ⟨1, 1⟩ else ⟨0, 0⟩
  have hne : g ≠ h := by
    intro he
    have hpt := congrFun he (n + 1)
    have hl : g (n + 1) = ⟨0, 0⟩ := rfl
    have hr : h (n + 1) = ⟨1, 1⟩ := by
      unfold h
      exact if_pos rfl
    rw [hl, hr] at hpt
    exact absurd hpt (by simp)
  apply hne
  refine hinj ?_
  funext x
  have hk' : segmentIndex n x.1 ≠ n + 1 := by
    have := segmentIndex_le_on_unit n hn x.1 x.2
    omega
  show (g (segmentIndex n x.1)).eval x.1 = (h (segmentIndex n x.1)).eval x.1
  have hg : g (segmentIndex n x.1) = ⟨0, 0⟩ := rfl
  have hh : h (segmentIndex n x.1) = ⟨0, 0⟩ := by
    unfold h
    exact if_neg hk'
  rw [hg, hh]

/-- **⭐⭐⭐ 判据的**否证方向**：在 `[0,1]` 上，**不存在**恢复权重的提取器。**

**=> 这是本文件的核心结论：**
**「权重 → 行为 → 权重」这条回路**不可能**闭合，
因为行为（在单位区间上）**不包含**索引 `n+1` 之后的系数。**

**=> 与第 964 轮的 `stacked_error_bound`（误差可预算）对照：
**正向的误差可以控制，反向的信息却是**真的缺失**。** -/
theorem gridWeights_not_extractable (n : ℕ) (hn : 0 < n) :
    ¬ ∃ extract : (Icc (0 : ℝ) 1 → ℝ) → (ℕ → Segment),
        ∀ g : ℕ → Segment, extract (fun x => gridEval g n x.1) = g :=
  not_injective_gives_no_extract _ (gridEval_unit_not_injective n hn)

end Lattice.Lib.Compiler.ReversibilityChain
