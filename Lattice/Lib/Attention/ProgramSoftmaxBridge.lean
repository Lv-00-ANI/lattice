import Mathlib
import Lattice.Lib.Attention.RealAttention
import Lattice.Lib.Attention.SoftmaxLipschitzBound
import Lattice.Runtime.ProgramAST

/-!
# `Lattice.Lib.Attention.ProgramSoftmaxBridge` — **AST 的 `softmax` 接到已证的 softmax 上**

## 两个定义，同一个公式

第 62 轮给 `Instr` 加了第一个真正非线性的构造子：

```lean
| .softmax => fun j => Real.exp (x j) / ∑ i, Real.exp (x i)
```

而 `Lattice.softmax`（`RealAttention.lean`，已有六条性质）是

```lean
def softmax (z : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (z i) / ∑ j, Real.exp (z j)
```

**逐字相同。** 所以本文件**不重新证明任何 softmax 性质**——它把已有的五条**搬到**
`applyInstr x .softmax` 上。每次搬运都是一次定义展开。

## 为什么桥放在 `Lib` 而不是 `Runtime`

层序：`Runtime` 是 rank 2，`Lib` 是 rank 3（`gov/gate.py` 的 `rank`）。
**`Runtime` 导入 `Lib` 是逆向依赖，会被 I4 拒绝。** 所以桥必须住在高的那一层：
`Lib/Attention/` 可以导入 `Runtime/ProgramAST`，反之不行。

**这不是风格问题**：softmax 的**性质**住在 `Lib`，AST 住在 `Runtime`，
**交点只能落在 `Lib`。**

## 为什么没有一条「两边相等」的定理

第一稿写了

```lean
theorem applyInstr_softmax_eq (x : Fin n → ℝ) :
    applyInstr x (.softmax : Instr n) = Lattice.softmax x := rfl
```

**删掉了**：它是一条 `:= rfl` 的等式复述，别名普查会（正确地）把它记成 `copy`。
**而且它不必要**——两边定义相同，所以下面每条性质**直接**成立，
**不需要先经过一条中介等式**。删掉它没有损失任何信息：
**若有人改了任一处的公式，下面的五条会一起失败。**

## `hn : 0 < n` 在这里第一次变成本质

第 62 轮说 `softmax` 的定义**不需要** `hn`：`Fin 0` 没有元素、空函数合法。**那是对的。**
但**性质需要它**——`∑ i, softmax x i = 1` 要求分母为正，分母为正要 `Fin n` 非空。
**所以 `hn` 在定义处是噪声，在性质处是前提。** 本文件用
`haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩` 把它变成类型类实例。
-/

namespace Lattice.Lib.Attention

variable {n : ℕ}

/-- `0 < n` 给出 `Fin n` 的 `Nonempty` 实例。

**这是把 `hn` 从假设变成类型类的那一步**：`Lattice.softmax_*` 的四条性质都要求
`[Nonempty ι]`，而对 `ι = Fin n` 它不自动可得。 -/
def finNonempty (hn : 0 < n) : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

/-! ## 性质：逐条搬运 -/

/-- **分母为正。** 来源：`SoftmaxLipschitzBound.sum_exp_pos`。 -/
theorem applyInstr_softmax_denom_pos (hn : 0 < n) (x : Fin n → ℝ) :
    0 < ∑ i, Real.exp (x i) := by
  haveI := finNonempty hn
  exact Lattice.Lib.Attention.sum_exp_pos x

/-- **非负。** 来源：`RealAttention.softmax_nonneg`。 -/
theorem applyInstr_softmax_nonneg (hn : 0 < n) (x : Fin n → ℝ) (j : Fin n) :
    0 ≤ Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.softmax : _) j := by
  haveI := finNonempty hn
  exact Lattice.softmax_nonneg x j

/-- **各行和为 1**（行随机）。来源：`RealAttention.softmax_sum_one`。 -/
theorem applyInstr_softmax_sum_one (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ j, Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.softmax : _) j = 1 := by
  haveI := finNonempty hn
  exact Lattice.softmax_sum_one x

/-- **严格正。** 来源：`SoftmaxLipschitzBound.softmax_pos`。 -/
theorem applyInstr_softmax_pos (hn : 0 < n) (x : Fin n → ℝ) (j : Fin n) :
    0 < Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.softmax : _) j := by
  haveI := finNonempty hn
  exact Lattice.Lib.Attention.softmax_pos x j

/-- ⭐⭐ **Lipschitz 界**：输入分量扰动不超过 `ε`，则输出分量扰动不超过 `2ε·exp(2ε)`。

来源：`SoftmaxLipschitzBound.softmax_lipschitz`（**无条件**，不要求分量有下界）。 -/
theorem applyInstr_softmax_lipschitz (hn : 0 < n) (x x' : Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ j, |x j - x' j| ≤ ε) (j : Fin n) :
    |Lattice.Lift.ProgramAST.applyInstr x (Lattice.Lift.ProgramAST.Instr.softmax : _) j
        - Lattice.Lift.ProgramAST.applyInstr x' (Lattice.Lift.ProgramAST.Instr.softmax : _) j|
      ≤ 2 * ε * Real.exp (2 * ε) := by
  haveI := finNonempty hn
  exact Lattice.Lib.Attention.softmax_lipschitz x x' ε hε h j

end Lattice.Lib.Attention
