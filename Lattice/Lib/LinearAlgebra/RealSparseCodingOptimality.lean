import Mathlib
import Lattice.Lib.LinearAlgebra.RealSparseCodingSoftThreshold
/-! # RealSparseCodingOptimality

拆分自 `RealSparseCoding.lean`（第 669–702 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealSparseCoding` 仍有效，
两个 importer（`RealCompressedSensing`、`RealSeamBridges2`）因此不受影响。

本模块重新声明了原文件的四项作用域设置（缺一不可）：
`noncomputable section`（原 :147）、`open scoped BigOperators`（原 :149）、
`namespace Lattice`（原 :151）、`variable {n : ℕ}`（原 :153）。

**边界经注释深度校验**：原文件中 `## ⚠ 登记在案的假命题之四`（:741）位于 :703 打开的
注释块**内部**，是散文而非分节标记；在 :741 切分会产生 `unterminated comment`。
本模块因此覆盖到 :1276，把该段散文与其所属块一并保留。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

variable {n : ℕ}

/-! ### 最优性的代数核心：二次函数的配方

`½(x−y)² + λx` 在 `x` 无约束时的唯一最小点是 `x = y − λ`；
`½(x−y)² − λx` 的唯一最小点是 `x = y + λ`。
这两条是全部三段论证的代数基础。 -/

/-- **配方引理（凸方向）**：`½(x−y)² + λ·x = ½(x − (y−λ))² + (λ·y − λ²/2)`。

即 `x = y − λ` 是唯一最小点，最小值为 `λ y − λ²/2`。 -/
theorem quadraticMinimizer_identity (y lam x : ℝ) :
    (1 / 2) * (x - y) ^ 2 + lam * x
      = (1 / 2) * (x - (y - lam)) ^ 2 + (lam * y - lam ^ 2 / 2) := by
  ring

/-- **配方引理（凹方向 / `x < 0` 支）**：`½(x−y)² − λ·x = ½(x − (y+λ))² + (−λ y − λ²/2)`。

即 `x = y + λ` 是唯一最小点，最小值为 `−λ y − λ²/2`。 -/
theorem quadraticMinimizer_identity_neg (y lam x : ℝ) :
    (1 / 2) * (x - y) ^ 2 - lam * x
      = (1 / 2) * (x - (y + lam)) ^ 2 + (-lam * y - lam ^ 2 / 2) := by
  ring

/-- **`½(x−y)² + λx ≥ λy − λ²/2` 的纯代数形式**（配方 + 平方非负）。 -/
theorem quadratic_value_ge (y lam x : ℝ) :
    (1 / 2) * (x - y) ^ 2 + lam * x ≥ lam * y - lam ^ 2 / 2 := by
  rw [quadraticMinimizer_identity y lam x]
  nlinarith [sq_nonneg (x - (y - lam))]

/-- **`½(x−y)² − λx ≥ −λy − λ²/2` 的纯代数形式**。 -/
theorem quadratic_value_ge_neg (y lam x : ℝ) :
    (1 / 2) * (x - y) ^ 2 - lam * x ≥ -lam * y - lam ^ 2 / 2 := by
  rw [quadraticMinimizer_identity_neg y lam x]
  nlinarith [sq_nonneg (x - (y + lam))]


end Lattice
