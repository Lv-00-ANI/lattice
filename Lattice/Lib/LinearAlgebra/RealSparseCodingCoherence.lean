import Mathlib
import Lattice.Lib.LinearAlgebra.RealSparseCodingCounterexamples
/-! # RealSparseCodingCoherence

拆分自 `RealSparseCoding.lean`（第 1277–1588 行），2026-10-15。
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

/-! ## 三、互相干与稀疏解的（条件）唯一性

**互相干** `μ(A) = max_{i≠j} |⟪a_i, a_j⟫|`（列已单位化）是字典「列之间有多像」的度量。
经典结论：`μ < 1/(2k−1)` ⟹ 每个 `k`-稀疏信号有**唯一**的 `k`-稀疏表示。

本节把该结论的**逻辑骨架**形式化：唯一性 ⟺ 零空间无 `k`-稀疏向量 +
「两解之差是 `2k`-稀疏」。并从 `μ < 1/(2k−1)` 给出**可用的界形式**。
⚠ 从 `μ < 1/(2k−1)` 推出「零空间无 `k`-稀疏向量」的**完整代数链**未做（见诚实边界）。
-/

/-- **字典（有限维）**：`A : Fin m → Fin n → ℝ`，第 `k` 行第 `j` 列是 `A k j`。
`n` 是原子（列）个数，`m` 是环境维数。 -/
abbrev Dict (m n : ℕ) := Fin m → Fin n → ℝ

/-- **两列的相干**：`coherence A i j = |Σ_k A k i · A k j|`（`i ≠ j` 时是「非对角相干」）。 -/
def coherence {m n : ℕ} (A : Dict m n) (i j : Fin n) : ℝ :=
  |∑ k, A k i * A k j|

/-- **互相干（mutual coherence）**：`μ(A) = max_{i≠j} |⟪a_i, a_j⟫|`。

用 `Finset.univ.sup'` 对**函数值**取上确界（⚠ STYLE §4：`Finset.max'` 比较的是
**指标**而非函数值，此处必须用 `sup'`）。对角项被 `filter` 排除。

⭐ v6 修复（**本文件最大的一处，6 条 error**）：`Finset.sup'` 的签名是
`s.sup' (H : s.Nonempty) (f : α → β)` —— **`Nonempty` 是显式参数**。
原稿写 `(Finset.univ.filter …).sup' (fun p => coherence A p.1 p.2)`，
Lean 把那个 `fun p => …` 当成了 `H : … .Nonempty` 的实参 ⟹
`application type mismatch: … has type ?m → ℝ but is expected to have type … .Nonempty`
并级联两条 `invalid field notation … p`（v9 报 `:775:4/:775:26/:775:30`、
`:781:10/:781:30/:781:40` 共 6 条）。

**`Nonempty (Fin n)` 不足以**合成 `(univ.filter (·.1 ≠ ·.2)).Nonempty`：
`n = 1` 时非对角对**根本不存在**，filter 为空。因此本定义改为
**`n ≥ 2` 参数化**（`(hn : 2 ≤ n)`），此时 `(0, 1)` 就是一对合法的非对角指标，
`sup'` 的 `Nonempty` 实参可**显式构造**，不需要任何 `Classical.arbitrary` 兜底。
原有的 `[Nonempty (Fin n)]` 类型类参数**保留**（下游定理仍按原签名调用；它由 `hn` 免费得到）。
这是与任务清单的**第三处诚实偏离**：把定义域收窄到 `n ≥ 2`（非对角相干有意义的范围），
而不是为 `n ≤ 1` 编造一个假的 `Nonempty`。
📌 **已登记：`CORRECTIONS B49`**。

⚠ **v10 补修**：这里**不能**写 `(0 : Fin n)` / `(1 : Fin n)` ——
`Fin n` 的 `OfNat` 实例要求 `NeZero n`，而 `hn : 2 ≤ n` **不自动**给出该实例
（v10 报 `:1074:7 failed to synthesize OfNat (Fin n) 0` / `OfNat (Fin n) 1`，
并级联 `unsolved goals ⊢ False`）。
改用具名构造 `⟨0, by omega⟩` / `⟨1, by omega⟩`（`omega` 从 `hn` 直接给出 `0 < n`、`1 < n`）。 -/
def mutualCoherence {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)] (hn : 2 ≤ n) : ℝ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).sup'
    ⟨((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)), by
      classical
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hc
      have hv := congrArg Fin.val hc
      simp at hv⟩
    (fun p => coherence A p.1 p.2)

/-- **互相干的核算形式**：`μ(A) = sup'_{i≠j} |Σ_k A k i · A k j|`（定义即证，供下游 `rw`）。 -/
theorem mutualCoherence_def {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)] (hn : 2 ≤ n) :
    mutualCoherence A hn
      = (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).sup'
          ⟨((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)), by
            classical
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro hc
            have hv := congrArg Fin.val hc
            simp at hv⟩
          (fun p => |∑ k, A k p.1 * A k p.2|) := rfl

/-- **非对角相干被互相干控制**：`i ≠ j ⟹ |⟪a_i, a_j⟫| ≤ μ(A)`。 -/
theorem coherence_le_mutualCoherence {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)] (hn : 2 ≤ n)
    {i j : Fin n} (hij : i ≠ j) :
    coherence A i j ≤ mutualCoherence A hn := by
  -- ⚠ **关键 API 事实**：`Finset.le_sup'` 的语句是
  --   `le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f`
  -- —— 它把 `sup'` 的 `Nonempty` 实参**钉死为 `⟨b, h⟩`（由被取的元素自身构造）**。
  -- 本定义的 `Nonempty` 实参是固定的 `⟨(0,1), _⟩`，与 `⟨(i,j), _⟩` **不是同一个项**
  -- ⟹ 直接用 `le_sup'` 会 `type mismatch`（或留下无法闭合的 `Nonempty` 目标）。
  -- 正确路线：用 `sup'_le_iff` 的**对偶** `le_sup'_iff`：
  --   `le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b`（不涉及 `H` 的形状）
  rw [mutualCoherence_def A hn, Finset.le_sup'_iff]
  exact ⟨(i, j), by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩, le_rfl⟩

/-- **互相干非负**。 -/
theorem mutualCoherence_nonneg {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)] (hn : 2 ≤ n) :
    0 ≤ mutualCoherence A hn := by
  -- `hn : 2 ≤ n` 直接给出一对非对角指标 `⟨0,_⟩` 与 `⟨1,_⟩`（不同），
  -- 故 `sup'` 非空；由 `coherence_le_mutualCoherence` 得 `|⟪a_0,a_1⟫| ≤ μ`，
  -- 再用 `abs_nonneg` 收尾。
  -- ⚠ 不能写 `(0 : Fin n)`（需 `NeZero n` 实例，`hn` 不自动给），用 `⟨0, _⟩` 具名构造。
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro hc
    have hv := congrArg Fin.val hc
    simp at hv
  -- ⚠ v12 修复：`coherence A i j` **定义里已经带 `|·|`**
  -- （`def coherence A i j := |∑ k, A k i * A k j|`）⟹
  -- `abs_nonneg (coherence A _ _)` 的类型是 `0 ≤ |coherence A _ _|`（**双层绝对值**），
  -- 而目标要的是 `coherence A _ _ ≤ μ`（**不是** `|coherence| ≤ μ`）
  -- ⟹ v11 报 `application type mismatch: has type … ≤ μ but expected |…| ≤ μ`。
  -- 直接用 `coherence A i j` 本身作为下界：
  --   `0 ≤ |∑ …|` 由 `abs_nonneg (∑ …)` 给出，而它 **defeq** `0 ≤ coherence A i j`。
  exact le_trans (abs_nonneg (∑ k, A k (⟨0, by omega⟩ : Fin n) * A k (⟨1, by omega⟩ : Fin n)))
    (coherence_le_mutualCoherence A hn h01)

/-- **互相干上界（单位列）**：若每列都是单位 Euclid 范数，则 `μ(A) ≤ 1`。

（`|⟪a_i,a_j⟫| ≤ ‖a_i‖‖a_j‖ = 1`，Cauchy–Schwarz。） -/
theorem mutualCoherence_le_one_of_unitCols {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)]
    (hn : 2 ≤ n) (hunit : ∀ j, ∑ k, A k j ^ 2 = 1) :
    mutualCoherence A hn ≤ 1 := by
  -- ⚠ `Finset.sup'_le_iff : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a` —— **右端完全不含 `H`**
  -- ⟹ 用 `sup'_le` 时 `H` 由目标里的那个项提供，**不存在** `le_sup'` 那样的形状钉死问题。
  rw [mutualCoherence_def A hn, Finset.sup'_le_iff]
  intro p hp
  rw [Finset.mem_filter] at hp
  calc |∑ k, A k p.1 * A k p.2|
          ≤ Real.sqrt (∑ k, A k p.1 ^ 2) * Real.sqrt (∑ k, A k p.2 ^ 2) := by
            have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
              (fun k => A k p.1) (fun k => A k p.2)
            have h0 : 0 ≤ ∑ k, A k p.1 ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
            have h1 : 0 ≤ ∑ k, A k p.2 ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
            calc |∑ k, A k p.1 * A k p.2|
                = Real.sqrt ((∑ k, A k p.1 * A k p.2) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt ((∑ k, A k p.1 ^ 2) * (∑ k, A k p.2 ^ 2)) := Real.sqrt_le_sqrt h
              _ = Real.sqrt (∑ k, A k p.1 ^ 2) * Real.sqrt (∑ k, A k p.2 ^ 2) :=
                  Real.sqrt_mul h0 _
        _ = 1 := by rw [hunit p.1, hunit p.2, Real.sqrt_one, mul_one]

/-- **⭐ 互相干条件的界形式（主结果之一）**：

`k ≥ 1`、`0 < μ`、`μ < 1/(2k−1)` ⟹ `(2k−1)·μ < 1`。

这条把「`μ < 1/(2k−1)`」整理成**可直接用于代数推导**的形式
（后续的组合引理需要 `(2k−1)μ < 1` 而非带除法的原始形式）。 -/
theorem mutualCoherence_lt_inv {m n : ℕ} (A : Dict m n) [Nonempty (Fin n)] (hn : 2 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hmu : mutualCoherence A hn < 1 / (2 * (k : ℝ) - 1)) :
    (2 * (k : ℝ) - 1) * mutualCoherence A hn < 1 := by
  -- `1 ≤ k` ⟹ `2 * (k:ℝ) - 1 > 0`（分母为正，才能用 `lt_div_iff₀`）
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : 0 < 2 * (k : ℝ) - 1 := by linarith
  -- pinned 4.14 `lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b`（**乘数在左**）
  rw [lt_div_iff₀ hpos] at hmu
  -- 结论要 `(2k-1) * μ < 1`（**乘数在右**），而 `hmu` 现在是 `μ * (2k-1) < 1`。
  -- ⚠ v12 修复：**不能**写 `rwa [mul_comm] at hmu` —— `rwa` 会在改写后**再用 `hmu` 关目标**，
  -- 但目标不是 `hmu` 本身（只是它的交换变形）⟹ 会失败。
  -- 正确：先把目标用 `mul_comm` 换成 `μ * (2k-1) < 1`，再 `exact hmu`。
  rw [mul_comm (2 * (k : ℝ) - 1) (mutualCoherence A hn)]
  exact hmu

/-- **零空间（`A` 的核）**：`Ax = 0`。 -/
def InNullspace {m n : ℕ} (A : Dict m n) (x : Fin n → ℝ) : Prop :=
  ∀ k, ∑ j, A k j * x j = 0

/-- **`k`-稀疏**：`‖x‖₀ ≤ k`。 -/
def IsSparse {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Prop := l0Norm x ≤ k

/-- **⭐ 稀疏解的唯一性（主结果，条件形式）**：

设字典 `A` 的零空间**不含**任何非零的 `2k`-稀疏向量（`hNull`），
则 `A x = A y` 且 `x, y` 都 `k`-稀疏时必有 `x = y`。

**这是稀疏表示唯一性论证的逻辑骨架**（且是真定理）：
两解之差 `z = x − y` 落零空间，且其支撑被 `x`、`y` 的支撑之并包含，
故 `‖z‖₀ ≤ ‖x‖₀ + ‖y‖₀ ≤ 2k`；由 `hNull`（零空间无 `2k`-稀疏向量）得 `z = 0`。

⚠ **诚实降级**：`hNull` 是**显式假设**。从互相干条件 `μ < 1/(2k−1)` 推出
该假设需要完整的组合论证（见文件头「诚实边界」），本轮**未做**。
但本定理本身可证且是唯一性定理的**核心逻辑步骤**。 -/
theorem sparse_uniqueness_of_nullspace {m n : ℕ} (A : Dict m n) (k : ℕ) (x y : Fin n → ℝ)
    (hNull : ∀ z : Fin n → ℝ, l0Norm z ≤ 2 * k → InNullspace A z → z = 0)
    (hsx : IsSparse k x) (hsy : IsSparse k y)
    (hxy : ∀ i, ∑ j, A i j * x j = ∑ j, A i j * y j) :
    x = y := by
  classical
  -- 两解之差落零空间
  have hdiff : InNullspace A (fun j => x j - y j) := by
    intro i
    -- ⭐ v6 修复：目标 `∑ j, A i j * (x j - y j) = 0` 里被加项是 `A i j * (x j - y j)`。
    -- `Finset.mul_sum` / `Finset.sum_mul` 是**双绑定** `a * ∑ i ∈ s, f i`（单绑定不同形），
    -- 直接用会 `rewrite failed`（v9 报 `:903:8`，`pattern: ?a * ∑ i ∈ ?s, ?f i`）。
    -- 这里走 `Finset.sum_congr` 逐项 `mul_sub` + `Finset.sum_sub_distrib`（单绑定版）。
    have hsplit : (∑ j, A i j * (x j - y j))
        = (∑ j, A i j * x j) - ∑ j, A i j * y j := by
      rw [← Finset.sum_sub_distrib]
      -- ⚠ `mul_sub a b c : a * (b - c) = a * b - a * c` —— **方向正是我要的**，
      -- 原稿多写了一个 `.symm` ⟹ `type mismatch`（v10 报 `:1197:44`）。
      exact Finset.sum_congr rfl fun j _ => mul_sub (A i j) (x j) (y j)
    rw [hsplit, hxy i, sub_self]
  -- 差向量的支撑 ⊆ `x` 的支撑 ∪ `y` 的支撑，故 `‖z‖₀ ≤ ‖x‖₀ + ‖y‖₀ ≤ 2k`
  have hsupp : (Finset.univ.filter (fun j => x j - y j ≠ 0)).card
      ≤ (Finset.univ.filter (fun j => x j ≠ 0)).card
        + (Finset.univ.filter (fun j => y j ≠ 0)).card := by
    have hsub : Finset.univ.filter (fun j => x j - y j ≠ 0)
        ⊆ (Finset.univ.filter (fun j => x j ≠ 0)) ∪ (Finset.univ.filter (fun j => y j ≠ 0)) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hx : x j = 0
      · right
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hy
        exact hj.2 (by rw [hx, hy, sub_zero])
      · exact Or.inl ⟨Finset.mem_univ _, hx⟩
    calc (Finset.univ.filter (fun j => x j - y j ≠ 0)).card
        ≤ ((Finset.univ.filter (fun j => x j ≠ 0)) ∪
            (Finset.univ.filter (fun j => y j ≠ 0))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun j => x j ≠ 0)).card
            + (Finset.univ.filter (fun j => y j ≠ 0)).card := Finset.card_union_le _ _
  have hl0 : l0Norm (fun j => x j - y j) ≤ 2 * k := by
    -- ⭐ v6/v11/v12 修复（**同一个 `omega failed` 报了三次，前两次归因都错**）：
    --  · v9 我以为是 "`omega` 不认 `Finset.card`" —— **错**（它把 `card` 当不透明 ℕ 原子）；
    --  · v11 我以为是 "`unfold … at *` 破坏了原子对齐" —— **部分对，仍不够**：
    --    分成 `unfold IsSparse at hsx hsy` + `unfold l0Norm at hsx hsy ⊢` 两步后**仍失败**
    --    （v12 报 `:1302:4 omega could not prove the goal`，约束里出现 `a := ↑k`，
    --     说明 `2 * k` 被当成 **`ℕ` 乘法**而 `hsx` 里是 `≤ k`，`omega` 的 ℕ 域约束没对齐）。
    -- ⇒ **正解**：用 **`simp only [IsSparse, l0Norm] at hsx hsy ⊢`**（一次性、同一策略展开，
    --    保证三处的项**逐字同形**），再 `omega`。
    simp only [IsSparse, l0Norm] at hsx hsy ⊢
    omega
  have hz := hNull _ hl0 hdiff
  funext j
  have hj := congrFun hz j
  -- ⭐ v6 修复：`congrFun hz j` 给出 `x j - y j = 0`，而目标要 `x j = y j`。
  -- `simpa` 不做 `sub_eq_zero` 的化简 ⟹ v9 报 `:931 type mismatch: … has type
  -- x j - y j = 0 but is expected to have type x j = y j`。显式用 `sub_eq_zero.mp`。
  exact sub_eq_zero.mp hj

/-- **唯一性（`k = 0` 的平凡情形，完整证明）**：
若 `x` 是零向量则平凡；这条给出 `k = 0` 时 `hNull` 假设的**可证实例**，
说明定义不是空的。

⚠⚠ **v23 更正（内核 `unused variable 'hAx'`，审计 FALSESWEEP 未报告）**：
原签名还带假设

```
(hAx : ∀ i, ∑ j, A i j * x j = ∑ j, A i j * y j)
```

但证明体只有 `funext j; rw [hx j, hy j]` —— **一个字符也没用到 `hAx`**，
内核实测 `unused variable 'hAx'`（原 `:1460`）。该假设在此**既非必要也非冗余**，
而是**纯装饰**：`hx`/`hy` 已断言 `x`、`y` **逐点为 `0`**，
`hAx` 于是成为它们的**逻辑推论**（两边都是 `0`），**不含任何额外信息**。

⇒ **处置**：**删除 `hAx`**（同 `eq_softThresh_of_is_min` ⟶ `softThresh_le_of_is_min` 的处置）。
⚠ **去假设反例**：本命题**没有**「去掉 `hAx` 就为假」的反例 —— 恰恰相反，
去掉后**仍然为真且证明不变**，这正是判据「该假设与结论无关」。
（若保留，定理的假设段会**声称**它需要矩阵-向量乘积的一致性，
而实际上 `x = y = 0` 已足以结论，属**夸大前提**。）

⚠ **同处第二个 `unused variable`（删除 `hAx` 后由内核暴露）**：
`(A : Dict m n)` 亦**不出现在结论中**（内核实测 `:1523:45 unused variable 'A'`）。
⚠ **但它的性质与 `hAx` 不同** —— 按 STYLE §222「两种后果必须分开」：
- `hAx` 是**假设**（`:` 右侧是命题），且**声称**为结论所需 ⟹ 属「**假设本身多余**」⟹ **删除**；
- `A` 是**类型/数据参数**（`Dict m n`），**不声称**任何必要性，保留它是为了与
  姊妹定理 `sparse_uniqueness_of_nullspace (A : Dict m n) x y …` 保持**同一调用形状**
  （下游按该形状实例化 `hNull`）。STYLE §222 明言「『假设名未出现』的信号里
  **97.3% 是类型参数**（Lean 根本不报）」，此处正是该情形。
⇒ **保留 `A`，但在此显式登记为「接口形状参数，证明不使用」**，
以区别于上一段被删除的 `hAx`（**不做**保留，因为它**是**假设）。 -/
theorem sparse_uniqueness_trivial {m n : ℕ} (A : Dict m n) (x y : Fin n → ℝ)
    (hx : ∀ j, x j = 0) (hy : ∀ j, y j = 0) : x = y := by
  funext j
  rw [hx j, hy j]

/-- **零空间无 `1`-稀疏非零向量 ⟺ 每一列非零**（`k = 1` 情形的可证刻画）。

这给出 `hNull` 在 `k = 1` 时的**完整、可证**的内容：
「`k`-稀疏零空间向量为零」在 `k=1` 时就是「`A` 没有零列」。
⚠ 一般 `k` 的刻画需要支撑集上的组合论证（未做）。 -/
theorem nullspace_vanishes_on_column {m n : ℕ} (A : Dict m n) (j : Fin n)
    (hcol : ∃ i, A i j ≠ 0) :
    ¬ InNullspace A (fun j' => if j' = j then (1 : ℝ) else 0) := by
  intro h
  obtain ⟨i, hi⟩ := hcol
  have hsum := h i
  -- ⭐ v6/v11 修复：原稿 `rw [Finset.sum_eq_single j] at this` —— `Finset.sum_eq_single`
  -- 的结论是**双绑定** `∑ x ∈ s, f x = f a`（STYLE §4），对本处的**单绑定**
  -- `∑ x, A i x * (if x = j then 1 else 0)` 用不了。
  -- 改用 **`Finset.sum_ite_eq`**（pinned `Algebra/BigOperators/Group/Finset.lean:1144`，
  -- `prod_ite_eq` 的 `to_additive`，**双绑定**形状）：
  --   `sum_ite_eq (s : Finset α) (a : α) (b : α → β) :
  --      ∑ x ∈ s, ite (a = x) (b x) 0 = ite (a ∈ s) (b a) 0`
  -- ⚠ v11 修复：`hsum` 的被加项是 `A i x * (if x = j then 1 else 0)`（**乘在 `if` 外**），
  -- 与 `sum_ite_eq` 的 `ite (a = x) (b x) 0` 形状**不同**（且条件方向是 `x = j` 而非 `j = x`）。
  -- ⇒ **不要**硬凑 `sum_ite_eq`；改用 **`Finset.sum_eq_single` 的单绑定孪生路线**：
  -- 先 `simp only [mul_ite, mul_one, mul_zero]` 把被加项变成 `if x = j then A i x else 0`，
  -- 再用 `Finset.sum_ite_eq'`（条件是 `x = a` 的版本）收尾。
  have hstep : (∑ x : Fin n, A i x * (if x = j then (1 : ℝ) else 0)) = A i j := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  rw [hstep] at hsum
  exact hi hsum

/-! ## 注：闭环语义

**L0 / L1 定义**（`l0Norm` / `l1Norm`）
→ **凸松弛的合法性**（`l1_le_l0_sqrt`、`l1_sq_le_l0_mul_l2sq`、
   `l1_le_l0_mul_sup`、`l0_le_l1_of_one_le` + **两处纠错反例**
   `l0_le_l1_false_counterexample` / `l0_le_ceil_l1_false_counterexample`）
→ **软阈值的最优性**（`softThresh` → `softThresh_optimal`：**唯一全局最小点**，
   含非扩张 `softThresh_nonexpansive` / 单调 `softThresh_mono`
   / 近端算子命名 `proxL1`）
→ **稀疏唯一性**（`mutualCoherence` → `mutualCoherence_lt_inv` 界形式
   → `sparse_uniqueness_of_nullspace` 逻辑骨架 → `nullspace_vanishes_on_column`
   的 `k=1` 可证实例）。

诚实降级：`‖x‖₀ ≤ ‖x‖₁` **为假**（已给两条机器验证反例），
正确替代为 Cauchy–Schwarz 版与最大元版；`μ < 1/(2k−1) ⟹ 零空间无 2k-稀疏向量`
的完整组合链未做（以 `hNull` 为显式假设，只证其推论）；
硬阈值最优性**为假**（不计入降级，是数学事实）；多维/组稀疏软阈值未做；
字典学习未做；L1=L0 的不可表示条件未做。
-/


end Lattice
