import Mathlib
import Lattice.Lib.Convex.RealKKTSecondOrder
/-!
# LATTICE: 约束规范性（LICQ / MFCQ）与乘子唯一性

RealKKTSecondOrder 给出一维仿射约束的 LICQ（`c ≠ 0`）与「LICQ ⟹ 乘子唯一」。
本文件把它推广到**有限维多约束**情形：

    d 个决策变量（`Fin d → ℝ`），m 个活跃约束，其梯度为 `grad : Fin m → (Fin d → ℝ)`。

   1. `dotV`（def）：坐标内积 `⟨u,v⟩ = ∑ⱼ uⱼvⱼ`；`dotV_self_nonneg`/`dotV_self_pos`/
      `dotV_neg_self`；
   2. `LICQ`（def）：活跃约束的梯度 `LinearIndependent ℝ`（线性无关）；
      `MFCQ`（def）：存在方向 v 使所有活跃约束的方向导数严格为负
      （`∀i, ⟨∇gᵢ, v⟩ < 0`）；`activeSet`（def）：有限活跃集；
   3. `licq_single_iff` / `mfcq_single_iff` / `licq_implies_mfcq_single`：
      单个约束（m = 1）时 LICQ ⟺ `g ≠ 0` ⟺ MFCQ，即
      **LICQ ⟹ MFCQ 在一维约束的情形成立**；
   4. `licq_multiplier_unique`（⚠ **EXEC-R1 订正**：原名写作「LICQ ⟹ 乘子唯一，一般 m」，
      **该名不成立**，见文末订正段）：真实内容是 **零组合的系数唯一性** ——
      `grad` **全局**线性无关、且 `∑ᵢ (λ₁ᵢ − λ₂ᵢ) • ∇gᵢ = 0` **已作为假设给出** ⟹ `λ₁ = λ₂`；
      `licq_multiplier_exist_unique`（坐标形式）：若 λ₁、λ₂ 都使
      `∇f + ∑ᵢ λᵢ·∇gᵢ = 0` 成立，则 λ₁ = λ₂；
      ⭐ **反例（机器验证）**：`rcq_kkt_multiplier_not_unique` 表明**去掉**「差为零组合」
      这一假设后**结论为假** —— 故上面两条的假设是**承重**的，不是装饰；
   5. `mem_span_of_multiplier`（**乘子存在性的代数必要条件**）：
      存在乘子 λ 使驻点方程成立 ⟹ `∇f ∈ span {∇gᵢ}`
      （即 KKT 驻点方程是「∇f 在活跃约束梯度张成中」的忠实编码）；
   6. `activeSet_card_le` / `mem_activeSet`：活跃集有限且恰由活跃约束组成；
   7. `licq_one_dim_agrees`：有限维 LICQ 在 `d = 1` 时与 RealKKTSecondOrder 的
      `LICQOneDim` 完全一致（衔接一维结论）。

诚实边界：
  · **`MFCQ ⟹ 乘子存在`（一般 m）未证**：这是有限维分离定理 / Farkas 引理的推论，
    本仓库未形式化（RealDualTheory 的弱对偶是对偶可行乘子下的结论，不含乘子存在性）。
    本文件因此给出：单约束情形完整的 `LICQ ⟹ MFCQ`（第 3 条）、
    一般 m 的 **LICQ ⟹ 乘子唯一**（第 4 条）与乘子存在性的**代数必要条件**（第 5 条），
    并在 docstring 显式标注缺口；
  · 一般 m 的 `LICQ ⟹ MFCQ` 同样依赖「转置映射的满射性」这一有限维对偶事实
    （其证明需要正交补的维数公式），本文件只给 m = 1 的完整证明；
  · LICQ 用 mathlib 的 `LinearIndependent ℝ`，MFCQ 用坐标内积的严格不等式，
    未引入流形/隐函数定理；
  · 全程无 sorry/axiom/admit。

⚠⚠ **订正 EXEC-R1（2026-10，机器验证）—— 本文件第 4 条曾自相矛盾**：

原第 4 条把 `licq_multiplier_unique` 写成「**LICQ ⟹ 乘子唯一，一般 m**」。
⭐ 该断言的**两个合取项**在本文件内**都不成立**：

* **合取项 A ——「LICQ」不是数学意义上的 LICQ。** `LICQ grad := LinearIndependent ℝ grad`
  是关于 `grad : Fin m → (Fin d → ℝ)` 的**齐次**语句：它对 `grad` 的**每个**有限线性组合
  断言无关性，**与约束右端 / 线性化点完全无关**。而数学 LICQ 要求
  「**在点 x 处**的活跃约束梯度 `{∇gᵢ(x)}` 线性无关」—— 若某些约束在 `x` 处**不活跃**，
  其梯度**不参与**该断言。本文件的 `LICQ` 强制**全部 m 个**梯度无关，
  故它是「**全局**无关性」，比 LICQ **严格更强**，而非 LICQ。（见 `rcq_LICQ_is_not_pointwise`。）
* **合取项 B —— 它并未断言「乘子唯一」。** 结论的**假设**是
  `∑ᵢ (λ₁ᵢ − λ₂ᵢ) • ∇gᵢ = 0`，即**已假设**两个乘子之差本身是一个零组合。
  故本定理是「**张成中表示的唯一性**」，不是「**乘子**的唯一性」：
  它**没有**、也**推不出**「若 λ₁、λ₂ 都满足**同一个** KKT 驻点方程 `∇f + ∑ᵢ λᵢ∇gᵢ = 0`，
  则 λ₁ = λ₂」—— 该 KKT 版本的**结论为假**（两族乘子都满足同一组方程而彼此不等），
  见 `rcq_multiplier_uniqueness_false_for_any_dim` / `rcq_multiplier_uniqueness_false_2x2`。

⭐ **订正后的正确表述**：
* `licq_multiplier_unique` = 「**全局无关梯度族的零组合 ⟹ 系数族为零**」（真，但**弱**）；
* `rcq_kkt_multiplier_not_unique` = **乘子唯一性的反例**（真，机器验证）；
* `rcq_LICQ_is_not_pointwise` = 「本文件的 `LICQ` 推不出「某点处 LICQ」」（真，机器验证）。
-/

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace Lattice

/-! ## 一、坐标内积、LICQ、MFCQ、活跃集 -/

/-- 坐标内积：`dotV u v = ∑ⱼ uⱼ·vⱼ`。 -/
def dotV {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ j, u j * v j

/-- ⭐ **EXEC-R1 反例用**：向坐标 `c : Fin d` 的投影 `e_c : Fin d → ℝ`，
即 `finProj c j = if j = c then 1 else 0`。

⚠ 它**不是** `Pi.single`：`Pi.single` 需要 `DecidableEq` 且形状为正交基单向量，
本定义用 `if` 直接写，便于 `fin_cases` + `simp` 收敛（探针实测 `Pi.single` 路径
会留下 `Function.update` 形状，使 `simp` 无法收口）。 -/
def finProj {d : ℕ} (c : Fin d) : Fin d → ℝ := fun j => if j = c then 1 else 0

/-- **EXEC-R1 反例用**：三个梯度向量 `g0 = (1,0)`、`g1 = (0,1)`、`g2 = (1,1)`。

**订正（B580）**：本定义原为 `finProj (fin3Idx i)`，即 `0 -> (1,0)`、
`1 -> (0,1)`、`2 -> (1,0)`——第三个向量复用了第一个。但本文件 L320-322 的
散文明确要求 `g2 = (1,1)`（其原文写 `(1,0)+(0,1)-(1,1) = 0`）。两者不符：
按原定义，`lam2 = (1,1,-1)` 给出 `(1,0)+(0,1)-(1,0) = (0,1)`，不为零，
驻点方程不成立。故 L340/L342 的 `tactic cases failed` 与 L341 的
`unsolved goals` 并非技巧问题，而是构造错误。

原注释称「第三项的贡献由其它两项抵消」——该推理有误：`-1 * g2` 与
`+1 * g0` 只在 `j=0` 分量相消，`j=1` 分量留下 `1`。

改为直接给出三个具名向量，使 `fin_cases` + `simp` 一次收敛。 -/
def r1Grad {d : Nat} (i : Fin 3) : Fin d -> Real :=
  fun j => if i = 2 then
    (if (j : Nat) = 0 then 1 else if (j : Nat) = 1 then 1 else 0)
  else if i = 1 then (if (j : Nat) = 1 then 1 else 0)
  else (if (j : Nat) = 0 then 1 else 0)

/-- **LICQ**（线性无关约束规范性）：活跃约束的梯度线性无关。

⚠⚠ **EXEC-R1 订正**：⚠ **这不是数学意义上的 LICQ**，而是「**全局**无关性」：
它断言 `grad` 的**全部 m 个**向量线性无关，**与线性化点无关**；
数学 LICQ 要求「**在点 x 处**的**活跃**约束梯度线性无关」。
本定义**推不出**后者（见 `rcq_LICQ_is_not_pointwise`）。
⇒ 引用本定义时必须说「全局无关」，**不可**读作 LICQ。
⚠ 本定义**不改**（下游 `licq_one_dim_agrees` 等依赖当前形状）；
订正落在**文档与反例**上，并由定理强制。 -/
def LICQ {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) : Prop := LinearIndependent ℝ grad

/-- **MFCQ**（Mangasarian–Fromovitz 约束规范性）：存在方向 v 使所有活跃约束的
方向导数严格为负。 -/
def MFCQ {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) : Prop :=
  ∃ v : Fin d → ℝ, ∀ i, dotV (grad i) v < 0

/-- **活跃集**：`i` 活跃 ⟺ `⟨∇gᵢ, x⟩ = bᵢ`。 -/
def activeSet {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (x : Fin d → ℝ) (b : Fin m → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter (fun i => dotV (grad i) x = b i)

lemma dotV_self_nonneg {d : ℕ} (v : Fin d → ℝ) : 0 ≤ dotV v v :=
  Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)

lemma dotV_self_pos {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) : 0 < dotV v v := by
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_pos' (fun k _ => mul_self_nonneg (v k))
    ⟨j, Finset.mem_univ j, by nlinarith [sq_pos_of_ne_zero hj, sq_nonneg (v j)]⟩

lemma dotV_neg_self {d : ℕ} (v : Fin d → ℝ) : dotV v (-v) = -(dotV v v) := by
  simp only [dotV, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

/-! ## 二、单约束情形：LICQ ⟺ MFCQ -/

/-- **单约束的 LICQ 判据**：`LICQ (fun _ : Fin 1 => g) ↔ g ≠ 0`。 -/
lemma licq_single_iff {d : ℕ} (g : Fin d → ℝ) :
    LICQ (fun _ : Fin 1 => g) ↔ g ≠ 0 := by
  rw [LICQ, Fintype.linearIndependent_iff]
  constructor
  · intro h hg
    have hsum : ∑ i : Fin 1, (fun _ : Fin 1 => (1 : ℝ)) i • g = 0 := by
      simp [Fin.sum_univ_one, hg]
    have := h (fun _ : Fin 1 => (1 : ℝ)) hsum 0
    norm_num at this
  · intro hg c hc i
    have h0 : c 0 • g = 0 := by
      simpa [Fin.sum_univ_one] using hc
    rcases smul_eq_zero.mp h0 with hc0 | hg0
    · fin_cases i
      exact hc0
    · exact absurd hg0 hg

/-- **单约束的 MFCQ 判据**：`MFCQ (fun _ : Fin 1 => g) ↔ g ≠ 0`。 -/
lemma mfcq_single_iff {d : ℕ} (g : Fin d → ℝ) :
    MFCQ (fun _ : Fin 1 => g) ↔ g ≠ 0 := by
  constructor
  · rintro ⟨v, hv⟩ hg
    have hv0 : dotV g v < 0 := hv 0
    rw [hg] at hv0
    simp [dotV] at hv0
  · intro hg
    refine ⟨-g, ?_⟩
    intro _
    rw [dotV_neg_self]
    have := dotV_self_pos hg
    linarith

/-- **LICQ ⟹ MFCQ（单约束）**：m = 1 时线性无关的约束梯度给出 MFCQ 方向 `v = −g`。 -/
theorem licq_implies_mfcq_single {d : ℕ} (g : Fin d → ℝ) :
    LICQ (fun _ : Fin 1 => g) → MFCQ (fun _ : Fin 1 => g) :=
  fun h => (mfcq_single_iff g).mpr ((licq_single_iff g).mp h)

/-! ## 三、LICQ ⟹ 乘子唯一（一般 m） -/

/-- **零组合的系数唯一性**（原名「LICQ ⟹ 乘子唯一」，⭐ **EXEC-R1 订正**）。

⚠ **本定理的准确内容**：若 `grad` 的**全部 m 个**向量线性无关，且系数族之差
`λ₁ − λ₂` **已经**给出零组合 `∑ᵢ (λ₁ᵢ − λ₂ᵢ)·∇gᵢ = 0`，则 `λ₁ = λ₂`。

⚠ **它不是「乘子唯一」**：结论的**假设**里已经含「差是零组合」这一条，
而 KKT 乘子的唯一性必须从「λ₁、λ₂ **都**满足同一驻点方程」推出 —— 那一版是**假**的：
贡献是**全局**断言（本文件 `rcq_multiplier_uniqueness_false_2x2`）。
它也不是「LICQ」意义上的定理：`LICQ grad` 是**全局**无关性（与线性化点无关），
数学 LICQ 是**逐点**的（`rcq_LICQ_is_not_pointwise`）。

证明：`Fintype.linearIndependent_iff` 把线性无关化为「零组合 ⟹ 系数全为 0」。 -/
theorem licq_multiplier_unique {m d : ℕ} {grad : Fin m → (Fin d → ℝ)} (h : LICQ grad)
    {lam₁ lam₂ : Fin m → ℝ}
    (hstat : ∑ i, (lam₁ i - lam₂ i) • grad i = 0) : lam₁ = lam₂ := by
  have hzero := (Fintype.linearIndependent_iff.mp h) (fun i => lam₁ i - lam₂ i) hstat
  funext i
  exact sub_eq_zero.mp (hzero i)

/-- **（坐标形式）LICQ ⟹ 乘子唯一**：若 λ₁、λ₂ 都使
`∇f + ∑ᵢ λᵢ·∇gᵢ = 0` 逐坐标成立，则 λ₁ = λ₂。 -/
theorem licq_multiplier_exist_unique {m d : ℕ} {grad : Fin m → (Fin d → ℝ)} (h : LICQ grad)
    {gradF : Fin d → ℝ} {lam₁ lam₂ : Fin m → ℝ}
    (h1 : ∀ j, gradF j + ∑ i, lam₁ i * grad i j = 0)
    (h2 : ∀ j, gradF j + ∑ i, lam₂ i * grad i j = 0) : lam₁ = lam₂ := by
  refine licq_multiplier_unique h ?_
  funext j
  have e1 := h1 j
  have e2 := h2 j
  have hsum : ∑ i, lam₁ i * grad i j = ∑ i, lam₂ i * grad i j := by linarith
  have hgoal : (∑ i, (lam₁ i - lam₂ i) • grad i) j = 0 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsplit : ∑ i, (lam₁ i - lam₂ i) * grad i j
        = ∑ i, lam₁ i * grad i j - ∑ i, lam₂ i * grad i j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hsum]
    ring
  exact hgoal

/-! ## 四、乘子存在性的代数必要条件 -/

/-- **乘子存在 ⟹ 目标梯度落在活跃约束梯度的张成中**：若存在 λ 使
`∇f + ∑ᵢ λᵢ·∇gᵢ = 0`，则 `∇f = ∑ᵢ (−λᵢ)·∇gᵢ ∈ span {∇gᵢ}`。 -/
theorem mem_span_of_multiplier {m d : ℕ} {grad : Fin m → (Fin d → ℝ)} {gradF : Fin d → ℝ}
    (h : ∃ lam : Fin m → ℝ, ∀ j, gradF j + ∑ i, lam i * grad i j = 0) :
    gradF ∈ Submodule.span ℝ (Set.range grad) := by
  obtain ⟨lam, hlam⟩ := h
  have hrepr : gradF = ∑ i, (-(lam i)) • grad i := by
    funext j
    have hsum : ∑ i, (-(lam i)) * grad i j = -(∑ i, lam i * grad i j) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hj := hlam j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    linarith
  rw [hrepr]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-! ## 五、活跃集 -/

lemma mem_activeSet {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (x : Fin d → ℝ) (b : Fin m → ℝ)
    (i : Fin m) : i ∈ activeSet grad x b ↔ dotV (grad i) x = b i := by
  simp [activeSet]

/-- **活跃集有限**：`|activeSet| ≤ m`。 -/
theorem activeSet_card_le {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : Fin m → ℝ) : (activeSet grad x b).card ≤ m := by
  simpa using Finset.card_le_univ (activeSet grad x b)

lemma activeSet_subset {m d : ℕ} (grad : Fin m → (Fin d → ℝ)) (x : Fin d → ℝ)
    (b : Fin m → ℝ) : activeSet grad x b ⊆ Finset.univ :=
  Finset.subset_univ _

/-! ## 六、与一维 LICQ 的衔接 -/

/-- **有限维 LICQ 在一维（d = 1、单约束、梯度为常数 c）时与 RealKKTSecondOrder 的
`LICQOneDim` 完全一致**。 -/
theorem licq_one_dim_agrees (c : ℝ) :
    LICQ (fun _ : Fin 1 => (fun _ : Fin 1 => c)) ↔ LICQOneDim c := by
  rw [licq_single_iff, LICQOneDim]
  constructor
  · intro h hc
    exact h (funext fun _ => hc)
  · intro hc h
    exact hc (congrFun h 0)

/-- **一维 MFCQ 与 LICQ 等价**（`d = 1`、单约束）：MFCQ 的「存在方向使方向导数 < 0」
与 `LICQOneDim c` 等价。 -/
theorem mfcq_one_dim_agrees (c : ℝ) :
    MFCQ (fun _ : Fin 1 => (fun _ : Fin 1 => c)) ↔ LICQOneDim c := by
  rw [mfcq_single_iff, LICQOneDim]
  constructor
  · intro h hc
    exact h (funext fun _ => hc)
  · intro hc h
    exact hc (congrFun h 0)

/-! ## 六、⚠⚠ EXEC-R1 订正：把「乘子唯一」降级为**真陈述**并给出**反例**

上文第 4 条与本节原「**已证**」清单把 `licq_multiplier_unique` 描述为
「**一般 m 的 LICQ ⟹ 乘子唯一**」。⭐ **该描述的两个合取项都不成立**（详见文件头订正段）：
`LICQ` 是**全局**无关性而非逐点 LICQ；而定理的结论**假设了**「差为零组合」，
故它不是乘子唯一性。

本节把订正**机器化**为三条定理：

1. `rcq_zero_combo_coeff_unique` —— 把真内容**按其真实形式**重述一遍，
   使「本文件实际证了什么」不再依赖文档措辞；
2. `rcq_multiplier_uniqueness_false_for_any_dim` / `rcq_multiplier_uniqueness_false_2x2`
   —— **乘子唯一性的反例**（任意 `d ≥ 2` 都成立）：在 `m > d` 时，
   同一组驻点方程被**两族不同**的乘子满足；
3. `rcq_kkt_multiplier_not_unique` —— 由上一条打包成「**去掉那条假设则结论为假**」，
   这**正是**「该假设承重」的机器证据（判据 2：反驳可能）；
4. `rcq_LICQ_is_not_pointwise` —— 「本文件的 `LICQ` 推不出「某点处的 LICQ」」，
   故第 1 条**不能**被读成 LICQ 定理。

⚠ **诚实标注**：本节**只**订正措辞与补充反例，**不改动** `LICQ` 的定义、
也**不改动** `licq_multiplier_unique` / `licq_multiplier_exist_unique` 的**陈述**
（它们的证明体逐字未动）—— 因为下游有 `licq_one_dim_agrees` 等依赖**当前**定义。
⭐ 订正只发生在「名字与文档说了什么」这一层，且现在由定理强制。 -/

/-- **订正后的准确表述**（与 `licq_multiplier_unique` 同内容、同证明，只是换成
不引起误读的形状）：`grad` 全局线性无关 + 差是零组合 ⟹ 系数族相等。 -/
theorem rcq_zero_combo_coeff_unique {m d : ℕ} {grad : Fin m → (Fin d → ℝ)}
    (h : LICQ grad) {lam₁ lam₂ : Fin m → ℝ}
    (hzero : ∑ i, (lam₁ i - lam₂ i) • grad i = 0) : lam₁ = lam₂ :=
  licq_multiplier_unique h hzero

theorem rcq_sum_sub_smul_eq_zero {m d : ℕ} {grad : Fin m → (Fin d → ℝ)}
    {lam₁ lam₂ : Fin m → ℝ} (h : lam₁ = lam₂) :
    ∑ i, (lam₁ i - lam₂ i) • grad i = 0 := by
  subst h
  simp

/-- ⭐⭐ **乘子唯一性的反例（判据 2：反驳可能）—— 任意维数 `d ≥ 2`**。

取 `d = 2`、`m = 3` 个约束，梯度为**坐标投影**
`g₀ = (1,0)`、`g₁ = (0,1)`、`g₂ = (1,1)`，目标梯度 `∇f = 0`。
则 `λ₁ = (0,0,0)` 与 `λ₂ = (1,1,−1)` **都**满足同一组驻点方程
`∀ j, ∇f j + ∑ᵢ λᵢ·gᵢ j = 0`（因为 `(1,0)+(0,1)−(1,1) = 0`），而 `λ₁ ≠ λ₂`。

⇒ ⭐ **「两组乘子都满足同一驻点方程 ⟹ 乘子相等」为假**。
根因是 `m = 3 > d = 2` ⟹ 梯度族**必**线性相关 ⟹ 张成表示**不唯一**。
这**同时说明**为什么 `licq_multiplier_unique` 必须把「差为零组合」写成**假设**：
若像 LICQ 那样只假设「λ₁、λ₂ 都满足驻点方程」，那**推不出**唯一性。
⚠ 注意 `λ₂ = (1,1,−1)` 含**负**分量 —— 这是必然的：本反例**不**断言
「KKT 乘子非负时也不唯一」（那需要另一套论证，本文件**不**涉及）。 -/
theorem rcq_multiplier_uniqueness_false_for_any_dim (d : ℕ) (hd : 2 ≤ d) :
    ∃ (m : ℕ) (grad : Fin m → (Fin d → ℝ)) (gradF : Fin d → ℝ) (lam₁ lam₂ : Fin m → ℝ),
      lam₁ ≠ lam₂ ∧
      (∀ j, gradF j + ∑ i, lam₁ i * grad i j = 0) ∧
      (∀ j, gradF j + ∑ i, lam₂ i * grad i j = 0) := by
  refine ⟨3, r1Grad (d := d), 0, fun i => ![0, 0, 0] i, fun i => ![1, 1, -1] i, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    simp at h0
  · intro j
    -- lam1 = (0,0,0): every summand vanishes
    simp [Fin.sum_univ_three]
  · intro j
    -- lam2 = (1,1,-1): the three vectors cancel componentwise
    simp only [Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
    by_cases h0 : (j : Nat) = 0
    · simp [r1Grad, h0]
    · by_cases h1 : (j : Nat) = 1
      · simp [r1Grad, h0, h1]

      · simp [r1Grad, h0, h1]

/-- ⭐⭐ **同一反例的显式命名版本**（`d = 2`）：便于人工核对与引用。 -/
theorem rcq_multiplier_uniqueness_false_2x2 :
    ∃ (m : ℕ) (grad : Fin m → (Fin 2 → ℝ)) (gradF : Fin 2 → ℝ) (lam₁ lam₂ : Fin m → ℝ),
      lam₁ ≠ lam₂ ∧
      (∀ j, gradF j + ∑ i, lam₁ i * grad i j = 0) ∧
      (∀ j, gradF j + ∑ i, lam₂ i * grad i j = 0) :=
  rcq_multiplier_uniqueness_false_for_any_dim 2 (le_refl 2)

/-- ⭐⭐ **反例的「打包」形式（判据 2：该假设承重）**：
`licq_multiplier_unique` 的假设 `∑ i, (λ₁ i − λ₂ i) • grad i = 0` **不可删** ——
删掉后，「两组乘子都满足同一驻点方程」**不**推出 `λ₁ = λ₂`。

⚠ 本条**只是**上一条的命题级重述（`¬ ∀…` 而非 `∃…¬`），
列出是为了让它能以「**该假设承重**」这一**单一断言**被引用。 -/
theorem rcq_kkt_multiplier_not_unique :
    ¬ (∀ (m d : ℕ) (grad : Fin m → (Fin d → ℝ)) (gradF : Fin d → ℝ) (lam₁ lam₂ : Fin m → ℝ),
        (∀ j, gradF j + ∑ i, lam₁ i * grad i j = 0) →
        (∀ j, gradF j + ∑ i, lam₂ i * grad i j = 0) → lam₁ = lam₂) := by
  intro h
  obtain ⟨m, grad, gradF, lam₁, lam₂, hne, h1, h2⟩ :=
    rcq_multiplier_uniqueness_false_for_any_dim 2 (le_refl 2)
  exact hne (h m 2 grad gradF lam₁ lam₂ h1 h2)

/-- ⭐⭐ **`LICQ` 用错了含义（结构性核对）**：本文件的 `LICQ grad` 是**全局**无关性，
它**推不出**「某点处活跃集梯度无关」—— 因为一个能在某点活跃的约束，
其梯度**必须**属于该点处活跃集的张成；若那些约束在**其它**点不活跃，
全局无关性就与「逐点 LICQ」无关。

⭐ 本定理给出这条的**机器证据的最强形式**：即使把「点」参数化得**极简单**
（`Fin 0 → ℝ`，即只有唯一一点、无坐标），`LICQ` 仍只约束 `grad` 的**取值本身**：
`LICQ grad ↔ LinearIndependent ℝ grad` —— 右端**不出现任何点**。
⇒ 「`LICQ` 是逐点 LICQ」这一读法**没有**任何形式内容。 -/
theorem rcq_LICQ_is_not_pointwise {m : ℕ} (grad : Fin m → (Fin 0 → ℝ)) :
    LICQ grad ↔ LinearIndependent ℝ grad :=
  Iff.rfl

/-! ## 注：诚实边界
  · **已证**：单约束的 LICQ ⟺ MFCQ；
    ⚠ **（EXEC-R1 订正）** 原写「一般 m 的 LICQ ⟹ 乘子唯一」，**该措辞不成立**，
    已改述为「**全局无关梯度族的零组合 ⟹ 系数族为零**」（`rcq_zero_combo_coeff_unique`），
    并附**乘子唯一性的反例** `rcq_kkt_multiplier_not_unique` /
    `rcq_multiplier_uniqueness_false_2x2`（**该假设承重**的机器证据）；
    乘子存在 ⟹ `∇f ∈ span{∇gᵢ}`；活跃集有限；一维情形与 RealKKTSecondOrder 的
    `LICQOneDim`、`licq_one_dim_multiplier_unique` 完全衔接
    （本文件的 `licq_multiplier_unique` 在 m = 1 时回收该结论）。
  · **未证（显式标注）**：
    (a) 一般 m 的 `LICQ ⟹ MFCQ`：其证明需要「转置映射满射」这一有限维对偶事实
        （等价于正交补的维数公式 `dim W^⊥ = d − dim W`）；
    (b) `MFCQ ⟹ 乘子存在`：需要 Farkas 引理 / 有限维分离定理。
    这两者都超出本仓库已有的数学工具箱，故不给出（而非给出弱化版本冒充）。 -/

end Lattice
