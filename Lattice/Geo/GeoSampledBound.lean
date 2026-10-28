/-
# 几何约束的采样验证定理

## 0. 本节做什么

`Lattice.Lift.GeoSampledBound` 给出了采样定理的**距离函数版**（任意 `d`，
只要求非负）。本节把 `d := rho n k` 代入，得到 `EqConstraint` 的采样定理。

## 1. 为什么放在 `Geo` 而不是 `Lift`

`Lift` 是通用阶梯层，不应知道「几何约束」是什么。`rho` 的度量性质、
`poly` 的各分支常数都在 `Geo`（它们依赖 `GeoExpr`、`sqDist` 这些具体概念）。
把实例化留在 `Geo` 保持了方向：`Geo` 建立在 `Lift` 之上，不是反过来。

## 2. 结论

若：
* `poly c` 在 `rho n k` 下是 `L`-Lipschitz（`L` 由 `PolyAssemble` 的分支常数给出）；
* 每个点列 `pts` 都有一个 `δ` 内的采样点 `s`，且 `poly c s = 0`；

则 `∀ pts, |poly c pts| ≤ L · δ`。

这是「验证回路」在几何侧的最终形式：**检查有限个点，公式给出没检查的点的误差界**。

## 3. 边界

- `hd` 的「每个点列都有 `δ`-近的零点」是**强前提**：它要求采样集在零点集上稠密。
  稀疏采样不满足它。本定理给的是「若稠密则界成立」，不是「任何采样都有界」。
- `L` 由调用方从 `PolyAssemble` 取对应分支的常数，本文件不重新计算。
- `δ` 是输入。收敛率不在本定理范围。
-/
import Mathlib
import Lattice.Geo.Lipschitz
import Lattice.Geo.RhoMetric
import Lattice.Geo.PolyAssemble
import Lattice.Runtime.GeoSampledBound

namespace Lattice.Geo

open Lattice.Lib.Linear.PenaltyVector

/-! ## 二、几何约束的采样定理 -/


open Lattice.Geo

/-- **几何约束的采样验证定理。**

若 `EqConstraint.poly c` 在 `rho n k` 下是 `L`-Lipschitz，且在每个采样点 `ρ = 0`
（即采样点上约束精确成立——可通过 `samePoint` 等分支验证），
则在 `δ`-稠密覆盖下全域 `|poly c pts| ≤ L·δ`。

这是「验证回路」在几何侧的最终形式：**检查有限个点，公式给出没检查的点的误差界**。

`hd_nonneg` 由 `rho_nonneg` 供给；`L` 与 `δ` 由调用方给出（`L` 可以是
`PolyAssemble` 里对应分支的常数）。 -/
theorem geo_sampled_bound {n k : ℕ} (c : EqConstraint n) {L δ : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ pts pts' : ℕ → Pt n,
      |EqConstraint.poly c pts - EqConstraint.poly c pts'| ≤ L * rho n k pts pts')
    (hd : ∀ pts : ℕ → Pt n, ∃ s : ℕ → Pt n,
      EqConstraint.poly c s = 0 ∧ rho n k pts s ≤ δ) :
    ∀ pts : ℕ → Pt n, |EqConstraint.poly c pts| ≤ L * δ := by
  have hmain := Lattice.Lift.residual_le_of_zero_on_dense_of_d
    (X := ℕ → Pt n)
    (d := fun a b => rho n k a b)
    (r := fun pts => EqConstraint.poly c pts)
    (Ω := Set.univ) (S := {s : ℕ → Pt n | EqConstraint.poly c s = 0})
    (fun a b => rho_nonneg n k a b)
    (fun x _ y _ => hlip x y) hL
    (fun x _ => by
      obtain ⟨s, hs0, hsd⟩ := hd x
      exact ⟨s, Set.mem_univ s, hs0, hsd⟩)
    (fun s hs => hs)
  intro pts
  exact hmain pts (Set.mem_univ pts)

end Lattice.Geo
