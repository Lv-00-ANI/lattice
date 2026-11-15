import Mathlib
import Lattice.Lib.Compiler.ReluLemmas
import Lattice.Lib.Compiler.CarrierInstantiation
import Lattice.Lib.Compiler.Expressiveness

/-!
# 可逆性的**边界**：relu 载体不可逆（阶段 C，P6）

## 第 921 轮为什么失败，本轮为什么成了

**第 921 轮我把化简写在目标证明中间，卡在 `reluCompile 1 0 (-1) = 0`。**

**=> 根因：`relu` 有**两处**定义（`Core/Net.lean:73` 与 `Runtime/RealNonlinear.lean:35`），
`unfold relu` 在 `reluCompile` 的语境里展不开那一个。**

**本轮先写 `ReluLemmas.lean`，把化简收进 `reluCompile_of_nonpos` 一条引理并**单独编译通过**，
再回来用。于是本文件的证明全部是一到三行。**

**=> 这条经验是本轮唯一可复用的产出：**先把化简抽成独立引理并单独编译，再回目标。** -/

namespace Lattice.Lib.Compiler.ReversibilityLimit

/-- **⭐⭐ relu 载体**不可逆**。**

**=> 两个**不同**符号 `(1,0,0)` 与 `(1,0,-1)` 编译到同一输出 `0`（`reluCompile_collapses_ne`），
所以不存在从输出唯一还原符号的 `extract`。** -/
theorem relu_not_reversible :
    ¬ ∃ (extract : ℝ → ℝ × ℝ × ℝ),
        ∀ s : ℝ × ℝ × ℝ, extract (reluCompile s.1 s.2.1 s.2.2) = s := by
  rintro ⟨extract, hreext⟩
  obtain ⟨_, hne⟩ := Lattice.Lib.Compiler.ReluLemmas.reluCompile_collapses_ne
  have h0 := hreext (1, 0, 0)
  have h1 := hreext (1, 0, -1)
  rw [Lattice.Lib.Compiler.ReluLemmas.reluCompile_zero_zero] at h0
  rw [Lattice.Lib.Compiler.ReluLemmas.reluCompile_zero_neg] at h1
  -- h0 : extract 0 = (1,0,0),  h1 : extract 0 = (1,0,-1)
  rw [h0] at h1
  exact hne h1


end Lattice.Lib.Compiler.ReversibilityLimit
