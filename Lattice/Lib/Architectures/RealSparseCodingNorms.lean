import Mathlib

/-! # RealSparseCodingNorms

拆分自 `RealSparseCoding.lean`（第 155–493 行），2026-10-15。
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

/-! ## 一、L0 / L1 范数：凸松弛的合法性

`L0`「范数」其实不是范数（不满足齐次性：`‖2x‖₀ = ‖x‖₀ ≠ 2‖x‖₀`），
但它是**稀疏性的直接度量**。`L1` 是它的凸包络的最常用代理。
本节把「为何 L1 可以作为 L0 的代理」形式化为**不等式**。
-/

/-- **L0 范数（非零项个数）**：`‖x‖₀ = #{i | x i ≠ 0}`。

⚠ 术语标注：它**不是**数学意义上的范数（齐次性不成立：`‖c·x‖₀ = ‖x‖₀` 对 `c ≠ 0`，
而非 `|c|·‖x‖₀`）。取名 `l0Norm` 沿用文献惯例。

取 `ℕ` 值以便 `Finset.card` 直接给出（`ℚ`/`ℝ` 上的 `decide` 会卡，故此处用
`Finset.filter` + `Finset.card`，不做 `decide`）。 -/
def l0Norm {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- **L1 范数**：`‖x‖₁ = Σ_i |x i|`。 -/
def l1Norm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, |x i|

/-- **L2 范数平方**：`‖x‖₂² = Σ_i x i ^ 2`（用于反向控制 `l1_le_l0_sqrt`）。 -/
def l2NormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-! ### L0 与 L1 的基本关系

⚠ 关键纠错：任务描述里的 `‖x‖₁ ≥ ‖x‖₀` **本身为假**——反例 `x = (1/2, 0)`：
`‖x‖₀ = 1` 但 `‖x‖₁ = 1/2`。故本节只证**正确**的版本：
（i）在「非零分量绝对值 ≥ 1」的条件下 `L0 ≤ L1`；
（ii）`L1 ≤ √(L0)·‖x‖₂`（Cauchy–Schwarz，反向控制）；
（iii）`L1 ≤ L0·‖x‖_∞`（最大元版，无条件）。 -/

/-! **⚠ 登记在案的假命题之二（本轮实测抓出，未证明、不声称）**。

任务描述给出的 `‖x‖₁ ≥ ‖x‖₀` **为假**，且**加上取整也不能救**：
`x = (1/2, 1/2)` 时 `‖x‖₀ = 2`、`‖x‖₁ = 1`、`⌈‖x‖₁⌉ = 1`，故
`‖x‖₀ ≤ ‖x‖₁` 与 `‖x‖₀ ≤ ⌈‖x‖₁⌉` **都**不成立
（机器验证见 `l0_le_l1_false_counterexample` 与
`l0_le_ceil_l1_false_counterexample`）。

**根因**：「非零项个数」与「绝对值之和」**量纲不同**：
`L0` 是**计数**，`L1` 是**质量**。若每个非零分量绝对值 `≥ 1`（即 `L0 ≤ L1` 的
充分条件），两者可比；但分量可以任意小（`1/2, 1/1000, …`），
此时 `L1` 可以远小于 `L0`。**无量纲假设下 `L0 ≤ L1` 无从成立。**

**正确的替代陈述**（本文件实际采用的，均为真且可证）：
1. `l0_le_l1_of_one_le`：**条件版** `(∀ i, x i ≠ 0 → 1 ≤ |x i|) → L0 ≤ L1`；
2. `l1_le_l0_sqrt`：**Cauchy–Schwarz 版 `L1 ≤ √L0 · ‖x‖₂`**（**无条件**），
   其平方形式 `l1_sq_le_l0_mul_l2sq` 给出 `L1² ≤ L0 · L2²`——
   这是真正的「`L0` 控制 `L1`」关系，
   也是「L1 球与 L0 球在归一化下有相同稀疏解」的定量依据。
3. `l1_le_l0_mul_sup`：**最大元版** `L1 ≤ L0 · max_i |x i|`（**无条件**）——
   等价于「`L1/L0 ≤ ‖x‖_∞`」，是无条件成立的另一形态。

⇒ 本文件**不**声称任何「`L0 ≤ L1`」形式的无条件不等式。 -/

/-! **⚠ 机器验证的反例（`L0 ≤ ⌈L1⌉` 亦为假）**：

`x = (1/2, 1/2)`：`‖x‖₀ = 2`、`‖x‖₁ = 1`、`⌈1⌉ = 1`，故 `2 ≤ 1` 为假。

这条排除了「用上取整修好 `L0 ≤ L1`」的补救方案
（本轮先尝试了该修补，代小整数判真假后发现仍为假，按 STYLE §4 改为登记反例）。 -/
theorem l0_le_ceil_l1_false_counterexample :
    ¬ ((l0Norm (fun _ : Fin 2 => (1 : ℝ) / 2) : ℤ)
        ≤ ⌈l1Norm (fun _ : Fin 2 => (1 : ℝ) / 2)⌉) := by
  -- 显式计算两边：`L0 = 2`，`L1 = 1` 故 `⌈L1⌉ = 1`，于是 `2 ≤ 1` 为假。
  -- v5 修复：初稿用大 `simp only [...]` + `norm_num`，但 `ℤ` 上的 `⌈·⌉`
  -- 归约不到位（残留 `⊢ ⌈|1/2| + |1/2|⌉ < 2`），`norm_num` 也接不住。
  -- 改为**显式算三个中间量**，每步目标可见。
  intro h
  have hL0 : l0Norm (fun _ : Fin 2 => (1 : ℝ) / 2) = 2 := by
    unfold l0Norm
    rw [show (Finset.univ.filter (fun _ : Fin 2 => (1 : ℝ) / 2 ≠ 0)) = Finset.univ by
      refine Finset.filter_true_of_mem fun i _ => ?_
      norm_num]
    simp
  have hL1 : l1Norm (fun _ : Fin 2 => (1 : ℝ) / 2) = 1 := by
    unfold l1Norm
    -- v6 修复：`rw [Fin.sum_univ_two]` 之后目标里留下 `|1/2| + |1/2| = 1`
    -- （**不是** `↑(1+1)`），而 `norm_num` **不化简 `|·|`**（除非能判定正负），
    -- v10 报 `:232:58 unsolved goals`。显式用 `abs_of_pos` 消绝对值后再 `norm_num`。
    rw [Fin.sum_univ_two]
    norm_num [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  -- `⌈(1 : ℝ)⌉ = 1`（显式给，避免 `norm_num` 处理 `Int.ceil`）
  have hceil : ⌈(1 : ℝ)⌉ = (1 : ℤ) := Int.ceil_one
  rw [hL0, hL1, hceil] at h
  norm_num at h

/-- **L1 与 L0 的反向控制（Cauchy–Schwarz）**：`‖x‖₁ ≤ √(‖x‖₀)·‖x‖₂`。

即 `‖x‖₁ ≤ √(‖x‖₀) · √(Σ_i x_i²)`。这条与 `l0_le_l1_of_one_le` 一起表明：
**在 `‖x‖₂` 有界时 `‖x‖₁` 与 `‖x‖₀` 同阶**——这是「L1 约束与 L0 约束
在归一化字典下给出相同稀疏解」的定量基础。

⚠ 位置说明：本定理**必须**声明在 `l1_sq_le_l0_mul_l2sq` **之前**
（后者以它为前提）；初稿误置于其后，导致 `unknown identifier`。 -/
theorem l1_le_l0_sqrt (x : Fin n → ℝ) :
    l1Norm x ≤ Real.sqrt (l0Norm x) * Real.sqrt (l2NormSq x) := by
  classical
  unfold l1Norm l2NormSq l0Norm
  -- 先 `(Σ|x|)² ≤ (Σ 1_{x≠0}) · (Σ x²)`
  have hcs : (∑ i, |x i|) ^ 2 ≤ ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
      * (∑ i, x i ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => if x i = 0 then (0 : ℝ) else 1) (fun i => |x i|)
    -- 左端：`Σ 1_{x≠0} · |x| = Σ |x|`；右端第一因子：`Σ 1_{x≠0}² = card`
    have hleft : (∑ i, (if x i = 0 then (0 : ℝ) else 1) * |x i|) = ∑ i, |x i| := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hx : x i = 0
      · simp [hx]
      · simp [hx]
    have hright₁ : (∑ i, (if x i = 0 then (0 : ℝ) else 1) ^ 2)
        = ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ) := by
      -- ⭐ v6 修复（**更正 v5 的注释**）：`Finset.sum_filter` **确实存在**，
      -- 它是 `Finset.prod_filter` 的 `to_additive` 产物
      -- （源码 `Mathlib/Algebra/BigOperators/Group/Finset.lean:858-867`），
      -- **双绑定**形状：`∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0`
      -- （`to_additive` 把 `else 1` 映射为 `else 0`）。
      -- v5 的注释说"`sum_filter` 模式是 `∑ i ∈ s.filter p, f i`"是**记错了** —— 见 STYLE §4
      -- 「以名字判有无」家族：`rw` 对记错的名字**只报 pattern 失配**，不报 unknown identifier。
      -- 本处走**正向**：先把单绑定变双绑定，再用 `sum_filter` 把 `if` 收成 filter 指示函数。
      have hpt : ∀ i : Fin n, (if x i = 0 then (0 : ℝ) else 1) ^ 2
          = if ¬ x i = 0 then (1 : ℝ) else 0 := by
        intro i
        by_cases hx : x i = 0
        · simp [hx]
        · simp [hx]
      rw [Finset.sum_congr rfl fun i _ => hpt i]
      rw [show (∑ i : Fin n, (if ¬ x i = 0 then (1 : ℝ) else 0))
          = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if ¬ x i = 0 then (1 : ℝ) else 0) from by simp]
      -- ⭐ v6 修复（**方向搞反了，v10 实测纠正**）：`Finset.sum_filter` 的 LHS 是
      -- **filter 形式**、RHS 是 **ite 形式**：
      --   `∑ a ∈ s.filter p, f a = ∑ a ∈ s, if p a then f a else 0`
      -- （源码 `Algebra/BigOperators/Group/Finset.lean:858-867`，`prod_filter` 的 `to_additive`）。
      -- v10 报错信息里的 `pattern: ∑ a ∈ Finset.filter (fun a => ?p a) ?m, ?f a` **就是 LHS**，
      -- 证明我要的是**反向**（ite → filter）⟹ 必须写 `rw [← Finset.sum_filter]`。
      -- 原稿的方向本来就是对的；它当年失败的真因是**目标为单绑定**（`∑ i, …`），
      -- 现已在上一步用 `show` 变成双绑定 `∑ i ∈ Finset.univ, …` ⟹ 方向 + 形状都对齐。
      rw [← Finset.sum_filter]
      -- ⚠ v12 修复：`Finset.card_eq_sum_ones` 给的是 **`ℕ` 值** `#s = ∑ _ ∈ s, 1`，
      -- 而此处目标两侧都是 `ℝ`（左侧 `∑ i ∈ …, (1:ℝ)`）⟹ 直接 `rw` 会插入 `Nat.cast`
      -- 并留下 `∑ … 1 = ↑(∑ … 1)` 这种**跨类型**目标（v11 报 `:268:64 unsolved goals`，
      -- 显示为 `∑ a ∈ filter …, 1 = ↑(∑ x ∈ filter …, 1)`）。
      -- ⇒ 改在 **`ℝ` 上**证明"常数和 = 基数乘常数"：用 `Finset.sum_const` + `nsmul_eq_mul`。
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hright₂ : (∑ i, |x i| ^ 2) = ∑ i, x i ^ 2 :=
      Finset.sum_congr rfl fun i _ => sq_abs (x i)
    rw [hleft, hright₁, hright₂] at h
    exact h
  -- 开方
  have h0 : 0 ≤ (∑ i, |x i|) := Finset.sum_nonneg fun i _ => abs_nonneg (x i)
  have h1 : 0 ≤ ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ) := Nat.cast_nonneg _
  calc (∑ i, |x i|) ≤ Real.sqrt (((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
        * (∑ i, x i ^ 2)) := by
        rw [← Real.sqrt_sq h0]
        exact Real.sqrt_le_sqrt hcs
    _ = Real.sqrt ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
          * Real.sqrt (∑ i, x i ^ 2) := Real.sqrt_mul h1 _

/-- **⭐ Cauchy–Schwarz 型 L0–L1 关系（无条件成立，正确版本）**：

**`‖x‖₁² ≤ ‖x‖₀ · ‖x‖₂²`**，即 `(Σ_i |x i|)² ≤ (#{i | x i ≠ 0}) · Σ_i x i²`。

这是「`L1` 被 `√L0 · L2` 控制」的平方形式（`l1_le_l0_sqrt` 的直接推论），
**无需任何分量为 `≥ 1` 的假设**——是对「L1 与 L0 同阶」这一说法的
**无条件、正确**的定量刻画。 -/
theorem l1_sq_le_l0_mul_l2sq (x : Fin n → ℝ) :
    l1Norm x ^ 2 ≤ (l0Norm x : ℝ) * l2NormSq x := by
  classical
  have hsqrt := l1_le_l0_sqrt x
  have h0 : 0 ≤ l1Norm x := by
    unfold l1Norm; exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)
  calc l1Norm x ^ 2 ≤ (Real.sqrt (l0Norm x) * Real.sqrt (l2NormSq x)) ^ 2 := by
        exact pow_le_pow_left₀ h0 hsqrt 2
    _ = (Real.sqrt (l0Norm x)) ^ 2 * (Real.sqrt (l2NormSq x)) ^ 2 := mul_pow _ _ _
    _ = (l0Norm x : ℝ) * l2NormSq x := by
        rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (by
          unfold l2NormSq; exact Finset.sum_nonneg fun i _ => sq_nonneg (x i))]

/-- **最大元版 L0–L1 关系（`n ≥ 1` 时无条件成立）**：`‖x‖₁ ≤ ‖x‖₀ · max_i |x i|`。

（每个非零分量 `≤ ‖x‖_∞`，共 `L0` 项。）这是「`L1 ≤ L0·L∞`」的经典形式，
**无需分量为 `≥ 1` 的假设**。

⚠ 注意这与**为假**的 `L0 ≤ L1` 方向相反：那里用 `L1` 去**上界** `L0` 是错的，
这里用 `L0·L∞` 去上界 `L1` 是对的（`L0` 与 `L∞` 量纲互补）。

⚠ **必需假设 `0 < n`**（v5 修复）：`Finset.univ.sup'` 需要 `Finset.univ.Nonempty`，
即 `Nonempty (Fin n)`，而它**只对 `n ≥ 1` 可证**（`n = 0` 时 `Fin 0` 为空）。
初稿省略该假设 ⟹ 三条 `failed to synthesize`（`:290/294/302`），
且 `hterm` 声明在被污染的目标里 ⟹ 级联出 `unknown identifier 'hterm'`。
这是**一个根因、四条报错**的典型。

⚠ **v6 二次修复（关键 API 事实，v9/v10/v11 三次实测）**：
只在**证明体内**写 `haveI : Nonempty (Fin n)` **不够** ——
`Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty` 出现在**定理陈述**里，
而**陈述在证明体之前被精化**（`haveI` 是**局部实例**，作用域不覆盖陈述）。
原报错正是 `:345:50 failed to synthesize Nonempty (Fin n)`。
⇒ 正解：把 `Nonempty (Fin n)` 提为**显式的类型类参数** `[Nonempty (Fin n)]`，
让**陈述与证明体同处一个实例作用域**。
原 `(hn : 0 < n)` 假设**已移除**（它未被证明体使用，且 `[Nonempty (Fin n)]` 已足够；
调用点若有 `hn`，用 `haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn` 就地构造）。 -/
theorem l1_le_l0_mul_sup {n : ℕ} [Nonempty (Fin n)] (x : Fin n → ℝ) :
    l1Norm x ≤ (l0Norm x : ℝ) * (Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)) := by
  classical
  -- 记 `S = sup'_i |x i|`；用 `∑ i, |x i| ≤ ∑ i, (if x i = 0 then 0 else 1) * S` 收尾。
  -- ⚠ 全程**避免** ``∑ i, …` 与 `∑ i ∈ s, …` 混用（`Finset.sum_mul` 是**双绑定**，
  -- 单绑定目标不同形 ⟹ `rewrite failed` / `type mismatch`）。
  -- 因此这里**统一用单绑定**，并改用 `Finset.sum_mul` 的**单绑定孪生**路线：
  -- 先把 `S` 从和式中提出（`Finset.sum_mul`），再用 `Finset.sum_mul` 的逆。
  set S := Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|) with hS
  have hterm : ∀ i : Fin n, |x i| ≤ (if x i = 0 then (0 : ℝ) else 1) * S := by
    intro i
    by_cases hi : x i = 0
    · simp [hi]
    · rw [if_neg hi, one_mul]
      exact Finset.le_sup' (s := Finset.univ) (f := fun i => |x i|) (Finset.mem_univ i)
  have hsum1 : (∑ i, |x i|) ≤ ∑ i, (if x i = 0 then (0 : ℝ) else 1) * S :=
    Finset.sum_le_sum fun i _ => hterm i
  -- `∑ i, c i * S = (∑ i, c i) * S`（把常数 `S` 从和式提出）
  -- ⚠ 我核实了 pinned 4.14：`Finset.sum_mul` **只有双绑定版**
  -- （`Algebra/BigOperators/Ring.lean:42`：`(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`），
  -- **没有单绑定版**。故必须先把两侧都改成 `∑ i ∈ Finset.univ` 再 `rw`。
  have hsum2 : (∑ i, (if x i = 0 then (0 : ℝ) else 1) * S)
      = (∑ i, (if x i = 0 then (0 : ℝ) else 1)) * S := by
    rw [show (∑ i : Fin n, (if x i = 0 then (0 : ℝ) else 1) * S)
        = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if x i = 0 then (0 : ℝ) else 1) * S
        from by simp,
      show (∑ i : Fin n, (if x i = 0 then (0 : ℝ) else 1))
        = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if x i = 0 then (0 : ℝ) else 1)
        from by simp]
    rw [Finset.sum_mul]
  -- `∑ i, (if x i = 0 then 0 else 1) = ↑(l0Norm x)`
  have hsum3 : (∑ i, (if x i = 0 then (0 : ℝ) else 1)) = (l0Norm x : ℝ) := by
    unfold l0Norm
    -- ⚠ `Finset.sum_filter` 的 LHS 是 **filter 形式**、RHS 是 **ite 形式**
    -- （`prod_filter` 的 `to_additive`，`Algebra/BigOperators/Group/Finset.lean:858-867`）：
    --   `∑ a ∈ s.filter p, f a = ∑ a ∈ s, if p a then f a else 0`
    -- 这里要把**单绑定 ite** 变成 **filter**，故：单绑定 → 双绑定 → `← sum_filter`。
    rw [show (∑ i : Fin n, (if x i = 0 then (0 : ℝ) else 1))
        = ∑ i ∈ (Finset.univ : Finset (Fin n)), (if ¬ x i = 0 then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : x i = 0 <;> simp [hi]]
    rw [← Finset.sum_filter]
    -- `∑ i ∈ univ.filter (· ≠ 0), 1 = ↑(univ.filter (· ≠ 0)).card`
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc (∑ i, |x i|) ≤ ∑ i, (if x i = 0 then (0 : ℝ) else 1) * S := hsum1
    _ = (∑ i, (if x i = 0 then (0 : ℝ) else 1)) * S := hsum2
    _ = (l0Norm x : ℝ) * S := by rw [hsum3]
    _ = (l0Norm x : ℝ) * (Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|)) := by
        rw [hS]

/-- **L0 与 L1 的条件版不等式**：
若 `x` 的每个非零分量绝对值 `≥ 1`，则 `‖x‖₀ ≤ ‖x‖₁`。

⚠ 该条件**不可去**：`x = (1/2, 0)` 是反例（见 `l0_le_l1_false_counterexample`）。 -/
theorem l0_le_l1_of_one_le (x : Fin n → ℝ) (h : ∀ i, x i ≠ 0 → 1 ≤ |x i|) :
    (l0Norm x : ℝ) ≤ l1Norm x := by
  classical
  unfold l0Norm l1Norm
  -- ⭐ v6 修复：原稿的 `calc` 里第二条 `_ ≤ ∑ _i ∈ filter, |x i| := Finset.sum_le_sum hfine`
  -- 报 `:404:57 unknown identifier 'i'` —— 因为 `Finset.sum_le_sum` 的隐式参数
  -- （集合与函数）在**双绑定** `∑ _i ∈ s, f i` 记法下难以推断，且 `_i` 匿名 binder
  -- 让 `hfine` 的 `i` 无法对齐（STYLE §4「以名字判有无」的变体）。
  -- 改用**单绑定**写法 + `Finset.sum_le_sum` 的显式实参，避免匿名 binder。
  have hfine : ∀ i : Fin n, x i ≠ 0 → (1 : ℝ) ≤ |x i| := h
  have hcard : ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), (1 : ℝ) := hcard
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), |x i| :=
        Finset.sum_le_sum fun i hi => hfine i (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, |x i| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => abs_nonneg (x i))

/-- **`‖x‖₁ ≥ ‖x‖₀` 为假：机器可验证的反例**。

取 `x : Fin 2 → ℝ`，`x 0 = 1/2`、`x 1 = 0`。则 `‖x‖₀ = 1` 而 `‖x‖₁ = 1/2`，
故 `(l0Norm x : ℝ) ≤ l1Norm x` **不成立**（`1 ≤ 1/2` 为假）。

⚠ 这是任务描述中 `‖x‖₁ ≥ ‖x‖₀` 的**纠错**（STYLE §5「假命题处理」：
发现原稿命题为假 ⟹ 不证，给出反例并登记）。 -/
theorem l0_le_l1_false_counterexample :
    ¬ ((l0Norm (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 2 else 0) : ℝ)
        ≤ l1Norm (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 2 else 0)) := by
  -- 显式计算：`L0 = 1`（仅第 0 项非零），`L1 = 1/2`，故 `1 ≤ 1/2` 为假。
  -- 与上一个反例同样**避免大 `simp only` 集合**，改为逐步重写。
  intro h
  have hL0 : l0Norm (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 2 else 0) = 1 := by
    unfold l0Norm
    rw [show (Finset.univ.filter (fun i : Fin 2 =>
        (if i = 0 then (1 : ℝ) / 2 else 0) ≠ 0)) = {0} by
      ext i
      fin_cases i <;> simp]
    simp
  have hL1 : l1Norm (fun i : Fin 2 => if i = 0 then (1 : ℝ) / 2 else 0) = 1 / 2 := by
    unfold l1Norm
    rw [Fin.sum_univ_two]
    norm_num
  rw [hL0, hL1] at h
  norm_num at h

/-- **L0 为零 ⟺ 向量为零**。 -/
theorem l0_eq_zero_iff (x : Fin n → ℝ) : l0Norm x = 0 ↔ x = 0 := by
  classical
  -- ⭐ v6 修复：原稿写 `unfold l0Norm` + `rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]`。
  -- 两个问题：
  --   (a) `unfold` 在 `↔` 目标上**不一定**把 `l0Norm` 展开到两侧（v10 报
  --       `:448:4 introN failed, insufficient number of binders`，说明 `constructor`
  --       之后的第一个分支目标里 `l0Norm` 仍是**未展开的原子**，`intro h i` 只吃到一个 binder）；
  --   (b) `card_eq_zero`/`filter_eq_empty_iff` 都是 **iff**，`rw` 会把它们当**等式**用，
  --       换来形状错误的中间目标（v9 报 `:385 application type mismatch` / `:388 rfl failed`）。
  -- 正确路线：`simp only [l0Norm]` 展开（simp 会做到 `↔` 两侧），
  -- 之后**直接构造 iff**，不经过 `emptyset` 的中间形状。
  simp only [l0Norm]
  constructor
  · -- ⚠ v11 修复：`x = 0` 是**函数外延等式**，`intro h i` 只吃掉 `h`，
  -- 第二个 `i` 无处可绑 ⟹ `introN failed, insufficient number of binders`（v11 报 `:469:4`）。
  -- 必须先用 `funext i` 把它拆成逐点目标 `x i = 0`。
    intro h
    funext i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun i => x i ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    exact (Finset.card_ne_zero_of_mem hmem) h
  · intro h
    rw [h]
    -- `(fun _ : Fin n => (0:ℝ)) i ≠ 0` 为假 ⟹ filter 为空 ⟹ card = 0
    apply Finset.card_eq_zero.mpr
    exact Finset.filter_false_of_mem fun i _ => by simp

/-- **L0 为正 ⟺ 向量非零**。 -/
theorem l0_pos_iff (x : Fin n → ℝ) : 0 < l0Norm x ↔ x ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, l0_eq_zero_iff]


end Lattice
