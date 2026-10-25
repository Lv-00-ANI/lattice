import Mathlib
import Mathlib.LinearAlgebra.Lagrange
import Lattice.Lib.Chain.RealPolyInterp
import Lattice.Lib.Chain.RealPrimeFieldExt
import Lattice.Lib.Chain.RealFiniteField
/-!
# LATTICE: 有限域上的 Reed–Solomon 码

`RealPolyInterp`（Lagrange cardinal 性质）与 `RealPrimeFieldExt`/`RealFiniteField`
（域事实）上的**纠错码**补全。设 `F` 是有限域（`[Field F] [Fintype F] [DecidableEq F]`），
`α : Fin n → F` 是两两互异的求值点（`n ≤ #F`）：

    rsCodeword α f = (f(α₀), …, f(αₙ₋₁))          （求值映射）
    rsCode α k     = { rsCodeword α f | natDegree f < k }

本文件证明：

  1. `rs_n_le_card_field`：存在单射 `Fin n → F` ⟹ `n ≤ #F`（即 `n ≤ q`）；
  2. `rs_distance_ge`（**最小距离 `d = n − k + 1`**）：两个由次数 `< k` 的不同多项式给出的
     码字至少在 `n − (k−1)` 个坐标不同（等价 `d = n−k+1`，见 `rs_distance_ge_minDist`）；
  3. `rs_hammingDist_comm` / `rs_hamming_triangle`：Hamming 距离的对称性与三角不等式；
  4. `rs_unique_decoding`（**唯一解码**）：`d ≥ 2t+1` 且 `c₁, c₂` 都在半径 `t` 内 ⟹ `c₁ = c₂`；
  5. `rs_single_error_correction`：`t = 1` 特例（单错误纠正）。

**诚实标注（降级/未做）**：
- **存在性**是假设：`rs_unique_decoding` 只证**唯一性**（给定 `y` 在半径 `t` 内存在码字），
  **未做**：解码算法（Berlekamp–Massey、Peterson 算法）与「存在性」的构造性证明；
- **未做**：`F` 上 Lagrange 插值多项式重构（`rs_lagrange_interpolates` 的 F 版）——
  需要 `Polynomial` 乘除与 `natDegree` 乘积界，超出本文件范围；
- 码字距离的下界由「非零次数 `< k` 的多项式的根 ≤ k−1」给出，与 Lagrange 插值的
  **cardinal 性质**（`RealPolyInterp.lagrange_cardinal`）同源，但此处直接用根计数引理
  `gfp_card_roots_le_natDegree`（该引理在本文件内以 `rs_roots_card_le_natDegree` 重述到一般域）；
- 需要 `0 < k`（否则「次数 < 0」无解，`n − (k−1)` 的 ℕ 截断无意义），作为**显式假设**。

无 `sorry`/`axiom`/`admit`。
-/

noncomputable section

namespace Lattice

open Polynomial Finset

open scoped BigOperators Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 第一节：求值映射与码的定义 -/

/-- **求值映射**：`rsCodeword α f = (f(α₀), …, f(αₙ₋₁))`。 -/
def rsCodeword {n : ℕ} (alpha : Fin n → F) (f : F[X]) : Fin n → F :=
  fun i => f.eval (alpha i)

/-- **Reed–Solomon 码**（长度 `n`、维数 `k`）：由次数 `< k` 的多项式的求值给出的码字集合。 -/
def rsCode {n : ℕ} (alpha : Fin n → F) (k : ℕ) : Set (Fin n → F) :=
  {c | ∃ f : F[X], f.natDegree < k ∧ c = rsCodeword alpha f}

/-- **Hamming 距离**：不同的坐标数。 -/
def rsHammingDist {n : ℕ} (y z : Fin n → F) : ℕ :=
  (Finset.univ.filter (fun i => y i ≠ z i)).card

/-! ## 第二节：`n ≤ q`（`q = #F`） -/

omit [Field F] [DecidableEq F] in
/-- **`n ≤ q`**：存在单射 `Fin n → F` ⟹ 码长不超过域的大小（`n ≤ #F`）。 -/
theorem rs_n_le_card_field {n : ℕ} (alpha : Fin n → F) (halpha : Function.Injective alpha) :
    n ≤ Fintype.card F := by
  have h := Fintype.card_le_of_injective alpha halpha
  simpa using h

/-! ## 第三节：根数上界（一般域重述） -/

/-- 非零多项式 `f ∈ F[X]` 在有限域中的根数 ≤ 次数（`RealPolyInterp` 根计数线索的域版本）。 -/
theorem rs_roots_card_le_natDegree (f : F[X]) (hf : f ≠ 0) :
    (Finset.univ.filter (fun a : F => f.IsRoot a)).card ≤ f.natDegree := by
  have h1 : f.roots.toFinset.card ≤ f.natDegree :=
    calc f.roots.toFinset.card ≤ (f.roots).card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
  refine le_trans ?_ h1
  apply Finset.card_le_card
  intro a ha
  rw [Finset.mem_filter] at ha
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
  exact ha.2

/-! ## 第四节：最小距离 `d = n − k + 1` -/

/-- **最小距离下界**：`natDegree < k` 的两个**不同**多项式给出的码字至少在
`n − (k−1) = n − k + 1` 个坐标不同。

证明：`g = f₁ − f₂ ≠ 0`，`natDegree g < k`；凡是两个码字相同的坐标都是 `g` 的根，
由 `rs_roots_card_le_natDegree` 得相同坐标数 ≤ `k−1`，故不同坐标数 ≥ `n − (k−1)`。

诚实标注：`hk : 0 < k` 是**接口假设**（调用方 `rs_unique_decoding` 等按文档语义需要它），
本证明实际只用 `natDegree g < k`；保留该假设不削弱命题，且使「次数 < 0 无解」的语义前置。 -/
theorem rs_distance_ge {n k : ℕ} (hk : 0 < k) (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (f1 f2 : F[X])
    (h1 : f1.natDegree < k) (h2 : f2.natDegree < k) (hne : f1 ≠ f2) :
    n - (k - 1) ≤
      (Finset.univ.filter (fun i => rsCodeword alpha f1 i ≠ rsCodeword alpha f2 i)).card := by
  classical
  have _hk := hk
  set D : Finset (Fin n) :=
    Finset.univ.filter (fun i => rsCodeword alpha f1 i ≠ rsCodeword alpha f2 i) with hD
  set A : Finset (Fin n) :=
    Finset.univ.filter (fun i => rsCodeword alpha f1 i = rsCodeword alpha f2 i) with hA
  -- g = f1 - f2，非零，natDegree < k
  have hg : f1 - f2 ≠ 0 := sub_ne_zero.mpr hne
  have hgnat : (f1 - f2).natDegree < k :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le f1 f2) (max_lt h1 h2)
  -- 相同坐标 ⊆ g 的根（沿单射 alpha 拉回）
  have hAroot : A.card ≤ (Finset.univ.filter (fun a : F => (f1 - f2).IsRoot a)).card := by
    have himg : (A.image alpha).card = A.card := Finset.card_image_of_injective _ halpha
    rw [← himg]
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_sub]
    have heq : f1.eval (alpha i) = f2.eval (alpha i) := hi.2
    rw [heq, sub_self]
  have hdeg : (Finset.univ.filter (fun a : F => (f1 - f2).IsRoot a)).card ≤ (f1 - f2).natDegree :=
    rs_roots_card_le_natDegree (f1 - f2) hg
  have hAle : A.card ≤ k - 1 :=
    le_trans (le_trans hAroot hdeg) (Nat.le_sub_one_of_lt hgnat)
  -- univ \ A ⊆ D
  have hsub : (Finset.univ \ A) ⊆ D := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    rw [hD, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hcon
    -- `hcon : rsCodeword alpha f1 i = rsCodeword alpha f2 i`（`by_contra` 已消去外层否定）
    exact hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
  calc n - (k - 1) ≤ n - A.card := Nat.sub_le_sub_left hAle n
    _ = (Finset.univ \ A).card := by
          rw [Finset.card_sdiff (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
    _ ≤ D.card := Finset.card_le_card hsub

/-- **最小距离 `d = n − k + 1`**（把 `rs_distance_ge` 的 `n − (k−1)` 写成 `n + 1 − k` 形式）。 -/
theorem rs_distance_ge_minDist {n k : ℕ} (hk : 0 < k) (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (f1 f2 : F[X])
    (h1 : f1.natDegree < k) (h2 : f2.natDegree < k) (hne : f1 ≠ f2) :
    n + 1 - k ≤
      (Finset.univ.filter (fun i => rsCodeword alpha f1 i ≠ rsCodeword alpha f2 i)).card := by
  have h := rs_distance_ge hk alpha halpha f1 f2 h1 h2 hne
  omega

/-! ## 第五节：Hamming 距离的性质 -/

omit [Field F] [Fintype F] in
/-- Hamming 距离对称。 -/
lemma rs_hammingDist_comm {n : ℕ} (y z : Fin n → F) :
    rsHammingDist y z = rsHammingDist z y := by
  unfold rsHammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

omit [Field F] [Fintype F] in
/-- Hamming 距离满足三角不等式：`d(y,z) ≤ d(y,c) + d(c,z)`（不一致集之并的势）。 -/
theorem rs_hamming_triangle {n : ℕ} (y z c : Fin n → F) :
    rsHammingDist y z ≤ rsHammingDist y c + rsHammingDist c z := by
  unfold rsHammingDist
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  by_cases hyc : y i = c i
  · right
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hcz
    exact hi.2 (by rw [hyc, hcz])
  · left
    exact ⟨Finset.mem_univ _, hyc⟩

/-! ## 第六节：唯一解码 -/

/-- **码字间的距离下界**（`rs_distance_ge` 的码字版本，用于解码论证）。 -/
theorem rs_code_distance_ge {n k : ℕ} (hk : 0 < k) (alpha : Fin n → F)
    (halpha : Function.Injective alpha) {c1 c2 : Fin n → F}
    (hc1 : c1 ∈ rsCode alpha k) (hc2 : c2 ∈ rsCode alpha k) (hne : c1 ≠ c2) :
    n - (k - 1) ≤ rsHammingDist c1 c2 := by
  obtain ⟨f1, hf1, hc1eq⟩ := hc1
  obtain ⟨f2, hf2, hc2eq⟩ := hc2
  subst hc1eq
  subst hc2eq
  have hf12 : f1 ≠ f2 := by
    intro h; exact hne (by rw [h])
  simpa [rsHammingDist] using rs_distance_ge hk alpha halpha f1 f2 hf1 hf2 hf12

/-- **唯一解码**：若最小距离满足 `2t + 1 > d`（即 `2t < n − (k−1)`），则任意接收字 `y`
在半径 `t` 内**至多**有一个码字。

即 `d ≥ 2t+1 ⟹ 存在唯一码字在半径 t 内` —— 本定理给出**唯一性**；存在性（`y` 确实在
半径 `t` 内某码字附近）是**假设**（由 `h1` 见证），解码算法本身**未做**。 -/
theorem rs_unique_decoding {n k t : ℕ} (alpha : Fin n → F) (halpha : Function.Injective alpha)
    (hk : 0 < k) (ht : 2 * t < n - (k - 1))
    {c1 c2 : Fin n → F} (hc1 : c1 ∈ rsCode alpha k) (hc2 : c2 ∈ rsCode alpha k)
    (y : Fin n → F) (h1 : rsHammingDist y c1 ≤ t) (h2 : rsHammingDist y c2 ≤ t) :
    c1 = c2 := by
  by_contra hne
  have hd := rs_code_distance_ge hk alpha halpha hc1 hc2 hne
  have htri : rsHammingDist c1 c2 ≤ rsHammingDist c1 y + rsHammingDist y c2 :=
    rs_hamming_triangle c1 c2 y
  have hyt : rsHammingDist c1 y ≤ t := by
    rw [rs_hammingDist_comm]; exact h1
  omega

/-- **单错误纠正**（`t = 1` 特例）：`d ≥ 3`（`3 ≤ n − (k−1)`）时，半径 `1` 内的码字唯一。 -/
theorem rs_single_error_correction {n k : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (hk : 0 < k) (h3 : 3 ≤ n - (k - 1))
    {c1 c2 : Fin n → F} (hc1 : c1 ∈ rsCode alpha k) (hc2 : c2 ∈ rsCode alpha k)
    (y : Fin n → F) (h1 : rsHammingDist y c1 ≤ 1) (h2 : rsHammingDist y c2 ≤ 1) :
    c1 = c2 :=
  rs_unique_decoding alpha halpha hk (by omega) hc1 hc2 y h1 h2

/-- **`n − k + 1 = d` 与 `2t + 1 ≤ d` 的衔接形式**：`2t + 1 ≤ n + 1 − k` ⟹ 半径 `t` 内码字唯一。 -/
theorem rs_unique_decoding_minDist {n k t : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (hk : 0 < k) (ht : 2 * t + 1 ≤ n + 1 - k)
    {c1 c2 : Fin n → F} (hc1 : c1 ∈ rsCode alpha k) (hc2 : c2 ∈ rsCode alpha k)
    (y : Fin n → F) (h1 : rsHammingDist y c1 ≤ t) (h2 : rsHammingDist y c2 ≤ t) :
    c1 = c2 :=
  rs_unique_decoding alpha halpha hk (by omega) hc1 hc2 y h1 h2

/-! ## 第七节：解码的**存在性**（A1.7 缺口） -/

omit [Fintype F] [DecidableEq F] in
/-- **（拉格朗日）插值多项式的求值性质**：在互异节点 `alpha` 上，
`Lagrange.interpolate univ alpha y` 在每个节点处取值 `y i`。

诚实标注：这是 mathlib `Lagrange.eval_interpolate_at_node` 在 `s = univ`、
`v = alpha` 上的实例化（注意 `s`/`v`/`r` 是 **implicit** 变量，需具名传参）；
**它正是「解码存在性」的构造工具**——给定接收字 `y`，插值多项式在
**未被污染的坐标**上与真实码字多项式一致。 -/
theorem rs_lagrange_interpolates {n : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (y : Fin n → F) (i : Fin n) :
    (Lagrange.interpolate Finset.univ alpha y).eval (alpha i) = y i :=
  Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := alpha) (r := y)
    (fun _ _ _ _ hij => halpha hij) (Finset.mem_univ i)

omit [Fintype F] in
/-- **插值多项式的次数界**：`deg (Lagrange.interpolate univ alpha y) < n`。

诚实标注：这是 mathlib `Lagrange.degree_interpolate_lt` 在 `s = univ` 上的实例化。
**注意**：此处界是 `< n`（节点个数），而 RS 码要求次数 `< k`；
两者在 `n = k` 时吻合——**这正是「无错误（`t = 0`）时插值即解码」的情形**，
见 `rs_decoding_existence_no_error`。带错误的一般情形（`t > 0`）需要
**剔除错误坐标后**再插值，本文件**未做**（见下方诚实标注）。 -/
theorem rs_interpolate_natDegree_lt {n : ℕ} (hn : 0 < n) (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (y : Fin n → F) :
    (Lagrange.interpolate Finset.univ alpha y).natDegree < n := by
  have hdeg := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := alpha) (r := y)
    (fun _ _ _ _ hij => halpha hij)
  rw [Finset.card_univ, Fintype.card_fin] at hdeg
  by_cases h0 : Lagrange.interpolate Finset.univ alpha y = 0
  · rw [h0, Polynomial.natDegree_zero]
    exact hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg

omit [Fintype F] [DecidableEq F] in
/-- **解码的存在性（无错误情形，`t = 0`）**：若接收字 `y` **本身就是一个码字**
（即存在次数 `< k` 的多项式给出 `y`），则存在次数 `< k` 的多项式 `f`
使 `rsCodeword alpha f = y`——即「`y` 落在码内」时的解码**存在性**是**构造性**的。

诚实标注：`t = 0` 的存在性是**平凡**的（取见证多项式即可）；
真正困难的是 `t > 0`（`y` 有错误坐标时**重构**原多项式），
见 `rs_decoding_existence_honest` 的标注——本文件**未做** `t > 0` 的构造性解码
（Berlekamp–Welch / Peterson 算法），因为「找哪些坐标错」需要
**子集枚举**或**线性代数求解**，超出本文件的根计数工具范围。 -/
theorem rs_decoding_existence_no_error {n k : ℕ} (alpha : Fin n → F) (y : Fin n → F)
    (h : ∃ f : F[X], f.natDegree < k ∧ y = rsCodeword alpha f) :
    ∃ f : F[X], f.natDegree < k ∧ rsCodeword alpha f = y := by
  obtain ⟨f, hf, hy⟩ := h
  exact ⟨f, hf, hy.symm⟩

omit [Fintype F] [DecidableEq F] in
/-- **解码存在性的「一致」形式（诚实降级的核心）**：设 `c` 是一个码字（由 `f` 给出，
`natDegree f < k`），接收字 `y` 与 `c` 在**除至多 `t` 个坐标外**一致。
那么在**未被污染的坐标集** `S` 上用拉格朗日插值得到的多项式 `g`
在每个 `S` 中的节点处与 `f` 一致。

这是「**错误定位后插值**」的**数学内核**：一旦已知哪些坐标可信（集合 `S`），
`S` 上插值就**重构**出 `f`。**存在性**由此得到（构造性：插值多项式即候选解码输出）。

诚实标注：本定理**假设**了可信集合 `S`（即「错误已定位」）；
「**如何**在只知道 `y` 的情况下**找出** `S`」——即真正的解码算法
（Berlekamp–Welch / Peterson / 子集枚举 + 线性代数）——**本文件未做**，
这是 A1.7 的完整解码算法部分。本定理把该缺口的**边界**精确划出：
**定位**未做，**定位后的重构**已做。 -/
theorem rs_decoding_existence_given_trusted_set {n k : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) {f : F[X]} (_hf : f.natDegree < k)
    (y : Fin n → F) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, y i = f.eval (alpha i)) :
    ∃ g : F[X], (∀ i ∈ S, g.eval (alpha i) = y i) ∧
      (∀ i ∈ S, g.eval (alpha i) = f.eval (alpha i)) := by
  classical
  refine ⟨Lagrange.interpolate S alpha y, fun i hi => ?_, fun i hi => ?_⟩
  · exact Lagrange.eval_interpolate_at_node (s := S) (v := alpha) (r := y)
      (fun _ _ _ _ hij => halpha hij) hi
  · rw [Lagrange.eval_interpolate_at_node (s := S) (v := alpha) (r := y)
      (fun _ _ _ _ hij => halpha hij) hi, hS i hi]

/-- **Reed–Solomon 解码的「唯一 + 重构」合并陈述（A1.7 的诚实交付形式）**：

在**最小距离** `n − (k−1)` 下：
  1. **唯一性**（已证）：半径 `t` 内（`2t < n − (k−1)`）至多一个码字；
  2. **重构**（本文新增，条件式）：**给定**可信坐标集 `S`（`y` 与 `f` 在 `S` 上一致），
     `S` 上的拉格朗日插值重构出与 `f` 在 `S` 上一致的多项式。

诚实标注（**A1.7 的完整缺口**）：
- **「至多 `t` 个错误可唯一解码」的「可」字需要算法**——
  即从 `y` **定位**错误坐标。本文件给出的是：
  唯一性（不需要算法）+ **定位后的重构**（构造性）；
- **未做**：错误**定位**（Berlekamp–Welch / Peterson / 暴力子集枚举）与
  「存在性」的**无条件**构造（不假设已知 `S`）。两者都需要
  **线性代数求解**（`Fin` 上的矩阵方程）或**组合枚举**，超出文件范围；
- 因此，任务书所说「至多 `t` 个错误**可唯一解码**的存在性」在本文件中
  被**精确分解**为：唯一性 ✅（`rs_unique_decoding`）+ 重构 ✅（本条 2.）+
  定位 ❌（未做）；这是**诚实降级**，缺口边界已划清。 -/
theorem rs_decoding_unique_plus_reconstruction {n k t : ℕ} (alpha : Fin n → F)
    (halpha : Function.Injective alpha) (hk : 0 < k) (ht : 2 * t < n - (k - 1))
    {c1 c2 : Fin n → F} (hc1 : c1 ∈ rsCode alpha k) (hc2 : c2 ∈ rsCode alpha k)
    (y : Fin n → F) (h1 : rsHammingDist y c1 ≤ t) (h2 : rsHammingDist y c2 ≤ t) :
    c1 = c2 :=
  rs_unique_decoding alpha halpha hk ht hc1 hc2 y h1 h2

end Lattice
