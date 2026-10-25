import Mathlib
import Lattice.Lib.Chain.RealModelChain
import Lattice.Lib.Chain.RealHreachClosed
import Lattice.Lib.LinearAlgebra.RealOperatorInvertibility
import Lattice.Lib.Attention.RealSoftmaxAttnNormBound
/-!
# `RealHreachWired` —— 把 `hreach` 从【前提】变成【导出】

## 一、缺口

`RealModelChain.lean:234` 的链定理把 `hreach` 作为**显式前提**传入：

```
(hreach : ∀ j ≤ m,
    c ≤ ‖ChainFwd F j x + SoftmaxAttnOp S V (ChainFwd F j x) + W (ChainFwd F j x)‖
  ∧ c ≤ ‖… 对 y 同理 …‖)
```

而**全库没有任何模块产生它**（`RealHreachClosed` 与 `RealHreachConditional` 的
importer 数均为 **0**）。依本项目判据（`B409.5-6`）：**「已编译」不等于「已接线」**。

本文件补上这一环：给出**同一结论**的变体，其中 `hreach` 由
`RealHreachClosed.residual_lower_bound_positive` **导出**。

## 二、关键设计：为什么需要【一致】间隙条件

`hreach` 要求一个**全局单一常数** `c`，对**每个访问点**都成立。
而 `residual_lower_bound_positive` 给出的下界是

```
c(h) := (1 - Lw) * ρ - M * ‖h‖
```

**它依赖 `h`**。故要得到全局常数，必须假定**一致**的间隙条件：

```
hgap : ∀ j ≤ m, M * ‖ChainFwd … j x‖ < (1 - Lw) * ρ
```

于是可取 `c := (1 - Lw) * ρ - M * B`（用 `hBc` 的上界 `‖·‖ ≤ B` 把 `M‖·‖` 放大到 `M*B`），
该 `c` **与 `j` 无关**，从而**逐点**满足 `hreach`。

⚠ 这正是本项目已承诺的「**可检验但非自动**」条件 —— 见 §四。

## 三、`PROCESS.md §2.2`：「这条定理比它的定义多说了什么？」

- `hreach_of_uniform_gap`：`hreach` 的**定义**只是一个下界陈述；
  本引理**多说**了「该下界可由 `M`、`Lw`、`B`、`ρ` 与**一致间隙条件**推出」——
  这是**蕴含**，不是定义展开。✅
- `model_chain_numeric_bound_wired`：`RealModelChain.model_chain_numeric_bound`
  **以 `hreach` 为前提**；本定理**去掉该前提**、换成一致间隙条件，并**产出同一结论**
  ⟹ **多**说了一个**消解（discharge）**。✅
- `model_chain_edit_locality_numeric_wired`：同上。✅

## 四、⚠⚠ 诚实边界（最重要的一段）

> ⭐ **最终定位**：`hreach` 可在一个【**可检验但非自动**】的条件下成立；
> 该条件**不再要求块是压缩映射**，但**仍不是真实模型的自动推论**。

**本文件【做到】的**：把 `hreach` 从**假设**换成**可检验的充分条件**
（`hV` + `hW` + `Lw ≤ 1` + 一致间隙 + 一致下界 `ρ`），从而**消解**链定理对 `hreach` 的依赖。

**本文件【没有做到】的**：

1. ⚠ **没有**证明真实 transformer 满足这些条件 —— 它们**可检查但非自动**。
   间隙要求 `M‖h‖ < (1 - Lw)ρ`；`M ≥ 1` 是常态，且 **`Lw ≥ 1` 时 `1 - Lw ≤ 0`
   使该条件直接不可能**（见 `RealHreachClosed.hreach_positivity_obstruction`）。
2. ⚠ 与旧的 `M + Lw < 1` **不等价**：`Lw` 大时更宽松（**不再要求整块是压缩映射**），
   但**多出 `M‖·‖` 这一开销**。障碍**转移**了，**没有消失**。
3. ⚠ `ρ ≤ ‖h‖` 是**逐点下界假设**，与 `hBc` 的**上界**是**两条独立**的信息，
   不能互相推出。
4. ⚠ **`c := (1 - Lw) * ρ - M * B` 可能为负**（当 `M*B ≥ (1-Lw)*ρ` 时）——
   此时 `hreach` 的前提虽然仍被**满足**（负常数当然是下界），但**无正性意义**。
   本文件**不**声称 `c > 0`；那是**用户**须自行检查的条件。

⛔ **本文件【不】声称真实 transformer 满足 `hreach`。**
命名上刻意**不**含任何暗示真实模型已被覆盖的词。
-/

open scoped BigOperators

namespace Lattice

variable {n k : ℕ} [NeZero k]

/-- ⭐ **消解引理**：由【一致】间隙条件产出一条轨迹上的 `hreach`。

取 `c := (1 - Lw) * ρ - M * B`，用 `hBc` 的上界 `‖h‖ ≤ B` 把逐点间隙
`M * ‖h‖ < (1 - Lw) * ρ` 强化为 `c ≤ (1 - Lw) * ρ - M * ‖h‖`，再套下界定理。

⚠ 本引理**只**产出 `hreach` 所需的下界形态；**不**断言 `c > 0`。 -/
theorem hreach_of_uniform_gap
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw B ρ : ℝ) (hM0 : 0 ≤ M) (hV : ∀ i, ‖V i‖ ≤ M) (hW : ‖W‖ ≤ Lw) (hLw1 : Lw ≤ 1)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hB : ∀ j ≤ m, ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B)
    (hnorm : ∀ j ≤ m, ρ ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖)
    (hgap : ∀ j ≤ m, M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ < (1 - Lw) * ρ) :
    ∀ j ≤ m,
      (1 - Lw) * ρ - M * B
        ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x
              + SoftmaxAttnOp S V (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)
              + W (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x)‖ := by
  intro j hj
  have hlow := (residual_lower_bound_positive S V W M Lw ρ hV hW hLw1
      (ChainFwd (fun _ : ℕ => ModelBlock S V W) j x) (hnorm j hj) (hgap j hj)).2
  -- 用 ‖h‖ ≤ B（配 0 ≤ M）把逐点下界 (1-Lw)*ρ - M*‖h‖ 降为与 j 无关的 (1-Lw)*ρ - M*B
  have hmono : M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ M * B :=
    mul_le_mul_of_nonneg_left (hB j hj) hM0
  linarith

/-- ⭐⭐ **端到端链定理（接线的版本）** —— 与
`RealModelChain.model_chain_numeric_bound` **同一结论**，
但**不含 `hreach` 前提**：它由 `hreach_of_uniform_gap` 对 `x`、`y` **两条轨迹分别导出**。

⚠ 换来的代价是**四条逐点假设**（`hBx`/`hnormx`/`hgapx` 与 `hBy`/`hnormy`/`hgapsy`），
外加 `hM0 : 0 ≤ M`、`hLw1 : Lw ≤ 1`。**这些是【可检验但非自动】的条件** —— 见文件头 §四。

⚠ **`hreach` 的常数取 `c := (1 - Lw) * ρ - M * B`**，**可能为负**；
本定理**不**断言它为正。 -/
theorem model_chain_numeric_bound_wired {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw B ρ : ℝ) (hM0 : 0 ≤ M) (hV : ∀ i, ‖V i‖ ≤ M) (hW : ‖W‖ ≤ Lw) (hLw1 : Lw ≤ 1)
    (m : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B
      ∧ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y‖ ≤ B)
    (hnormx : ∀ j ≤ m, ρ ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖)
    (hgapx : ∀ j ≤ m, M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ < (1 - Lw) * ρ)
    (hnormy : ∀ j ≤ m, ρ ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y‖)
    (hgapsy : ∀ j ≤ m, M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j y‖ < (1 - Lw) * ρ)
    -- ⚠⭐ 正性【必须显式假设】：`hgap*` 只给 `M*‖h‖ < (1-Lw)*ρ`，
    --    而常数 `c = (1-Lw)*ρ - M*B` 带的是 `M*B`，二者**不可比较**
    --    （`‖h‖ ≤ B` 只把 `M‖h‖` 向上放大）。故 `c > 0` 是一条**独立的**假设。
    (hcpos : 0 < (1 - Lw) * ρ - M * B) :
    ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) m x
      - ChainFwd (fun _ : ℕ => ModelBlock S V W) m y‖
      ≤ (modelBlockLb S W M B ((1 - Lw) * ρ - M * B)) ^ m * ‖x - y‖ := by
  -- 对两条轨迹分别消解 hreach，得到同一个与 j 无关的常数下界
  have hax := hreach_of_uniform_gap S V W M Lw B ρ hM0 hV hW hLw1 m x
    (fun j hj => (hBc j hj).1) hnormx hgapx
  have hay := hreach_of_uniform_gap S V W M Lw B ρ hM0 hV hW hLw1 m y
    (fun j hj => (hBc j hj).2) hnormy hgapsy
  exact model_chain_numeric_bound S V W M B ((1 - Lw) * ρ - M * B) hcpos hV m x y hBc
    (fun j hj => ⟨hax j hj, hay j hj⟩)

/-- ⭐⭐ **链编辑局部性（接线版）** —— 与
`RealModelChain.model_chain_edit_locality_numeric` 同一结论，但**不含 `hreach` 前提**。

⚠ 注意 `hreach` 原版在尾部只要求 `j ≤ m - kk`，而本版的一致假设写成 `j ≤ m`
（更强的假设，换来与 `hBc` 同一索引域，避免 `Nat.sub_le` 桥接）；
这是**有意的**取舍，且**对用户更保守**（要求更多，不是更少）。 -/
theorem model_chain_edit_locality_numeric_wired {n k : ℕ} [NeZero n] [NeZero k]
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin k → ℝ))
    (V : Fin k → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M Lw B ρ : ℝ) (hM0 : 0 ≤ M) (hV : ∀ i, ‖V i‖ ≤ M) (hW : ‖W‖ ≤ Lw) (hLw1 : Lw ≤ 1)
    (m kk : ℕ) (δ x : EuclideanSpace ℝ (Fin n))
    (hBc : ∀ j ≤ m,
      ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ)‖ ≤ B
      ∧ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ ≤ B)
    (hnormd : ∀ j ≤ m, ρ ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ)‖)
    (hgapd : ∀ j ≤ m, M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j (x + δ)‖ < (1 - Lw) * ρ)
    (hnormx : ∀ j ≤ m, ρ ≤ ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖)
    (hgapx : ∀ j ≤ m, M * ‖ChainFwd (fun _ : ℕ => ModelBlock S V W) j x‖ < (1 - Lw) * ρ)
    (hcpos : 0 < (1 - Lw) * ρ - M * B) :
    ‖ChainTail (fun _ : ℕ => ModelBlock S V W) kk m (x + δ)
      - ChainTail (fun _ : ℕ => ModelBlock S V W) kk m x‖
      ≤ (modelBlockLb S W M B ((1 - Lw) * ρ - M * B)) ^ (m - kk) * ‖δ‖ := by
  have had := hreach_of_uniform_gap S V W M Lw B ρ hM0 hV hW hLw1 m (x + δ)
    (fun j hj => (hBc j hj).1) hnormd hgapd
  have hax := hreach_of_uniform_gap S V W M Lw B ρ hM0 hV hW hLw1 m x
    (fun j hj => (hBc j hj).2) hnormx hgapx
  exact model_chain_edit_locality_numeric S V W M B ((1 - Lw) * ρ - M * B) hcpos hV m kk δ x hBc
    (fun j hj => ⟨had j (le_trans hj (Nat.sub_le m kk)), hax j (le_trans hj (Nat.sub_le m kk))⟩)

/-- ⭐⭐ **承重见证：`hcpos` 不能被去掉**（`PROCESS.md §3.3` ⑤ 固化反例）。

取 `Lw = 1`、`ρ = 1`、`M = 0`、`B = 0`，则 `(1 - Lw)*ρ - M*B = 0`，
**不是正数** —— 即 `hcpos` 的前提在此配置下**为假**。
故 `hcpos` **不是装饰**：没有它，`model_chain_numeric_bound` 的 `hc : 0 < c` 无法满足。

⚠ 这是**关于常数 `c` 的算术陈述**，**不是**关于算子的陈述 —— 如实标注，不夸大。 -/
theorem hcpos_not_free :
    ¬ (0 < (1 - (1 : ℝ)) * 1 - 0 * 0) := by
  norm_num

end Lattice
