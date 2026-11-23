import Lattice.Lib.Compiler.Chain
import Lattice.Lib.Compiler.LowerBound

/-!
# **P2：能力选择规则——「选哪一族」不是自由裁量，而是被地板逼出来的**

## 规划要求什么

规划 §7 的 P2 要求「第二个目标族与按能力族的规模化迁移」，验收是
**「第二个族复用契约而非重写第一条路径」**。§1.6 的设计含义进一步说：

> **能力选择必须有规则：在给定目标与精度下，应当选可越过地板的族。该判据不是能力上限。**

**⇒ 本文件把这条规则写成两条定理：**
1. **`affine_target_cannot_meet`**：对 `x²` 目标，**仿射目标在 `ε < 1/8` 时不可能**；
2. **`grid_target_meets_of_budget`**：给定的 `ε > 0`，只要 `1/(4ε) ≤ n²`，**离散化目标可以达到**。

**⇒ 两条合起来就是选择规则：`ε < 1/8` 时**必须**用离散化族；不是偏好问题。**
**⇒ 而 `1/8` 这个数不是本文件给的，是 `LowerBound.target_not_attainable` 早就算出的。**

## 为什么这算「复用契约」

**本文件**没有**修改 `Target`（未加构造子）、`EvaluatedArtifact`（未加字段）、`evalAt`（未改定义）、
`writeBack`（未改）。新增的只有**关于已有构造子的判定定理**。
**⇒ 于是「第二族」不是一个平行实现，而是同一契约下的一格：`Target.affine` 与 `Target.squareApprox`
本来就在同一个 `Target` 里，本文件只是证明"在什么精度下该选哪一个"。**
-/

namespace Lattice.Lib.Compiler.Capability

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.Samples
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.Chain

/-- **⭐⭐ 仿射目标**不可能**满足 `x²` 在 `ε < 1/8` 下的整域要求。**

**⇒ 陈述在**产物**上（`evalAt`），不是抽象的 `a·x+b`：这只要求一次产物往返（`evalAt_ofSegments`），
其余直接落回既有的地板定理 `no_uniform_linear_approximation`。**

**⇒ 这条的内容是**排除**，而不是「做不到」这种含糊说法：
它说**不存在**任何仿射目标（对任意 `a`、`b`、任意布局与配方）能达到该精度。** -/
theorem affine_target_cannot_meet (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) (a b eps : ℝ) (heps : eps < 1 / 8) :
    ¬ (∀ x ∈ Set.Icc (0 : ℝ) 1,
        ∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
              (Target.family (.affine a b)) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ eps) := by
  intro hall
  apply Lattice.Lib.Compiler.LowerBound.no_uniform_linear_approximation eps heps
  refine ⟨a, b, fun x hx => ?_⟩
  obtain ⟨v, hv, hb⟩ := hall x hx
  -- **产物求值 = `a·x + b`（产物契约 + 常族求值），故 `v` 就是那个仿射值。**
  have hv' : (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
      (Target.family (.affine a b)) dom r).evalAt x = some (a * x + b) := by
    rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments]
    show some (gridEval (affineFamily a b) r.n x) = some (a * x + b)
    rw [gridEval_affineFamily]
  rw [hv'] at hv
  have hveq : v = a * x + b := (Option.some.inj hv).symm
  rwa [hveq] at hb

/-- **⭐⭐ 离散化目标在预算条件下达到要求。**

**⇒ 前提 `1/(4ε) ≤ n²` 就是 `budget_of_sq` 的可判定条件；`n` 由**配方**（产物自带）给出，
故本定理不要求调用者知道内部实现，只需要解一条不等式。**

**⇒ 与上一条合起来：`ε < 1/8` 时仿射被**排除**，而离散化族**可达**（对足够大的 `n`）——
这正是规划要的「选可越过地板的族」。** -/
theorem grid_target_meets_of_budget (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (eps : ℝ) (heps : 0 < eps) (hbudget : 1 / (4 * eps) ≤ (r.n : ℝ) ^ 2) :
    ∃ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family (.squareApprox r.n r.hn)) dom r).evalAt x = some v
        ∧ |x ^ 2 - v| ≤ eps := by
  obtain ⟨v, hv, hb⟩ := (square_path_bound r dom x hx).2
  exact ⟨v, hv, le_trans hb (budget_of_sq r.n r.hn eps heps hbudget)⟩

/-- **⭐⭐⭐ 能力选择规则：在 `x²` 目标上，`ε < 1/8` **排除**仿射族，而预算一旦满足就**存在**可行的离散化族。**

**⇒ 两个合取项分别是**上界的排除**与**下界的可达**；把它们放在一条陈述里，
是为了让「该选哪一族」成为一个**可引用的事实**，而不是文档里的建议。**

**⇒ 注意本定理**不提**「离散化族是唯一可行的」——那会是一个本文件没有证明、
也不该假定的断言（例如未来的非线性族可能更好）。** -/
theorem capability_rule (dom : Lattice.Lib.Compiler.SemDomain)
    (a b eps : ℝ) (heps_lt : eps < 1 / 8)
    (r : Lattice.Lib.Compiler.CompileRecipe) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (eps' : ℝ) (heps' : 0 < eps') (hbudget : 1 / (4 * eps') ≤ (r.n : ℝ) ^ 2) :
    (¬ (∀ x ∈ Set.Icc (0 : ℝ) 1,
          ∃ v : ℝ,
            (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
                (Target.family (.affine a b)) dom r).evalAt x = some v
              ∧ |x ^ 2 - v| ≤ eps))
      ∧ (∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
              (Target.family (.squareApprox r.n r.hn)) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ eps') :=
  ⟨affine_target_cannot_meet dom r a b eps heps_lt,
   grid_target_meets_of_budget dom r x hx eps' heps' hbudget⟩

end Lattice.Lib.Compiler.Capability