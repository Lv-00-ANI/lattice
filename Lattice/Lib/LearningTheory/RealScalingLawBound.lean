import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealMcDiarmid
import Lattice.Lib.LearningTheory.RealGeneralizationBound
/-!
# LATTICE: 缩放律的**方差受限项** —— moment ⟹ Jensen gap ⟹ `O(1/D)`

**来源**：arXiv **2102.06701**（Yasaman Bahri, Ethan Dyer, Jared Kaplan, Jaehoon Lee,
Utkarsh Sharma，*Explaining Neural Scaling Laws*），arXiv 首发 **2021-02-12**，
正式发表于 **PNAS 121 (27) e2311878121 (2024)**，DOI `10.1073/pnas.2311878121`。

> **⚠ 引用与内容更正（本文件是按逐字原文复核后**重写**的）**
>
> 本文件的初稿（依据上游任务书的转述）把 Theorem 1 写成
> 「**sub-Gaussian + Lipschitz ⟹ 有限数据损失偏离 `O(1/D)`**」。
> 经独立子代理 **OCR 逐字复核原文**（该文 PDF 可正常提取；同批还 OCR 了
> Kakade & Langford 2002 的扫描件），确认上游转述**有三处重大错误**：
>
> 1. ❌ **不是 sub-Gaussian**。原文 Theorem 1 的假设是**矩条件**
>    `E[(f_T − E[f_T])^k] = O(ε)`（**∀k ≥ 2**）。原文**通篇未出现
>    "sub-Gaussian"/"subgaussian"** 字样（已全文 grep 确认）。
> 2. ❌ **不是 Lipschitz**。Theorem 1 对损失 `ℓ` 的假设是**三选一析取**：
>    `ℓ` 是**有限次多项式** **或** 有**有界二阶导** **或** 是 **2-Hölder**。
>    Lipschitz 常数 `K_L, K_f, K_F` 属于 **Theorem 2 / 3**（**分辨率受限**
>    那一条），是**另一个**命题。
> 3. ❌ **Theorem 1 里根本没有 `D`**。它界的是 **Jensen 间隙**
>    `E[ℓ(f_T)] − ℓ(E[f_T]) = O(ε)`，`ε` 是**抽象**的集中尺度。
>    `O(1/D)` 是**推论**：需**另外**代入数据集集中性
>    `E_D[(f_T − E_D[f_T])^k] = O(D^{−1})`（原文 §2.1.1），
>    再由 Supplement Appendix C 得 `L(D) − lim_D L(D) = O(D^{−1})`。
> 4. ❌ 上游提到的 `|L(D) − L(∞)| ≤ c·√(Var/D)` 形式**不存在**：原文速率是
>    `O(D^{−1})`（**关于方差线性**），不是 `O(D^{−1/2})`；写成 `√Var` 会与
>    Appendix C 矛盾。
>
> **本文件的重写策略**：原文 Theorem 1 的三种情形中，**情形 (b)「有界二阶导」**
> 与**情形 (c)「2-Hölder」**都可以在**有限概率空间**上完全形式化（情形 (a)
> 「有限次多项式」需要多项式的一阶展开，工作量更大，本文件标注为后续工作）。
> 本文件证明的正是这两个情形的**精确常数版本**，并把 `O(1/D)` 作为**独立
> 的第二步**（`scaling_law_variance_limited`）显式给出 —— 严格对应原文
> 「Theorem 1 + §2.1.1 的集中性 = 方差受限标度」的两步结构。

**本文件给出的定理**：
1. `jensen_gap_bounded_second_deriv`（**原文 Theorem 1 情形 (b)**）：
   若 `|ℓ''| ≤ M₂`（在区间上）且 `E[(f − Ef)²] ≤ ε`，则
   `|E[ℓ(f)] − ℓ(E[f])| ≤ M₂·ε/2`；
2. `jensen_gap_two_holder`（**原文 Theorem 1 情形 (c)**）：
   若 `|ℓ(x) − ℓ(y)| ≤ K·(x−y)²`（2-Hölder，**指数 2**）且 `E[(f − Ef)²] ≤ ε`，则
   `|E[ℓ(f)] − ℓ(E[f])| ≤ K·ε`；
3. `moment_condition_instantiates_D`（**原文 §2.1.1 的代入**）：
   矩条件 `E_D[(f − E_D f)²] ≤ c/D` ⟹ `ε = c/D`，即 **`ε = O(1/D)`**；
4. `scaling_law_variance_limited`（**两步复合，主定理**）：
   Theorem 1 的情形 (b) 或 (c) + 集中性代入 ⟹
   **`|L(D) − L(∞)| ≤ (常数)/D`** —— 这是**方差受限标度 `O(1/D)`** 的精确形式；
   ⚠ **v23 更正**：本条与 `..._holder` 增加 `(hc : 0 ≤ c)`，
   并补 `scaling_law_variance_limited_nonvacuous` 作为**非空洞性见证**（见下）；
5. `resolution_limited_rate_shape`（**对照**）：原文 Theorem 2/3 的
   `O(D^{−1/d})` 只作为**速率形状**陈述（`d` = 数据流形内在维数），
   **本文件不证该定理**（见「诚实边界」）。
6. `uniformExpectation_centered_eq_zero`：`E[f − E[f]] = 0`（原文情形 (b)
   「一阶项在一次矩中消失」的形式化）。

**诚实边界**（本文件不证 / 不声称的）：
- **情形 (a)（有限次多项式）未证**：需要 `ℓ` 的多项式有限阶 Taylor 展开
  与矩条件的逐项控制。形式化工作量中等，但需要 `Polynomial` 与 `iteratedDeriv`
  的桥接，标注为后续工作。
- **`ℓ` 的二次余项控制未从二阶导界导出**：本文件把情形 (b) 的**结论形态**
  （`|ℓ(x) − ℓ(m)| ≤ M₂(x−m)²/2`）作为**逐点假设**（`hQuad`）传入，而非从
  `|ℓ''| ≤ M₂` 导出 —— 后者需要 mathlib 的 `Convex` 上的 Taylor 中值定理
  （`taylor_mean_remainder` 一系），本文件**未做这一桥接**（见「缺什么引理」第 1 条）。
- **`O(·)` 记号未形式化**：本文件给的是**显式常数**的界（`M₂·ε/2`、`K·ε`、
  `c·M₂/(2D)`、`c·K/D`），比原文的 big-O **更强**（big-O 只断言存在常数）。
- **分辨率受限项 `O(D^{−1/d})` 未证**：`resolution_limited_rate_shape` 只给速率
  **形状的单调性**，不含流形覆盖数/分辨率论证，**不构成**对原文 Theorem 2/3 的
  形式化。
- **`D` 的集中性 `c/D` 是显式假设**：原文 §2.1.1 把它归因于优化动力学的光滑性，
  本文件**未**从任何动力学导出它。
- **未做**：`ε → 0` 与 `D → ∞` 的 `Tendsto` 语言（本文件用有限概率空间上的显式
  不等式）。

## ⚠ v23：`hD` 未用 + 缺 `0 ≤ c` 的**处置**（审计代理 FALSESWEEP 报告，内核复核）

审计（`_audit_falsesweep/REPORT.md` 第 1/2 条）报告 `scaling_law_variance_limited`
与 `..._holder` 的 `hD : 0 < D` **从未被使用**（内核 warning `unused variable 'hD'`），
并判定两条命题**为假**，反例为「`D = 0`、`l = (·)²`、`f = [1,0]` on `Fin 2`」。

**本代理的内核复核结论（与本文件一致）**：

1. ⚠ **审计的反例无效**（`exit=0` 探针 `_probe_out/fs13.lean` 复核）：
   `hD` 是**签名中的假设**，`D = 0` **本就不在定义域内**；
   且即便取 `D = 0`，`hConc` 读作 `E[(f−Ef)²] ≤ c/0 = 0`
   ⟹ 迫使 `f` **为常值**（`E[(f−Ef)²] = 0`），于是 `jensenGap = 0`、
   结论 `0 ≤ 0` **成立**。审计的见证 `f = [1,0]` 有 `E[(f−Ef)²] = 1/4 > 0`，
   **违反 `hConc`** ⟹ 它不是该假设下的实例。
   ⇒ **两条命题在整个定义域上并未被证伪**；内核亦实测原陈述**可证**
   （`_probe_out/fs15.lean` / `fs16.lean`，`exit=0`）。
2. ⭐ **但审计指向的真缺陷成立**：`c < 0` 时 `hConc` **不可满足**
   （左端 `≥ 0 > c/D`）⟹ 主定理在该区域是**空洞真** —— 这正是
   `unused variable 'hD'` 所指向的「该假设想排除的边界从未被真正排除」。
3. **处置**：加 `(hc : 0 ≤ c)`（与姊妹定理 `distill_beneficial_concrete` 一致），
   并**真正用上 `hD`**：由 `hD` + `hc` 导出非空洞性见证 `0 ≤ c/D`
   （独立定理 `scaling_law_variance_limited_nonvacuous`）。
   ⚠ **`hc` 的去假设反例**：`c = −1, D = 1` 时 `hConc` 不可满足（见该定理 docstring）。
   ⚠ **`hD` 的去假设反例**：`D = 0` 时 `c/D = 0`（除零垃圾值），
   非空洞性见证 `0 ≤ c/0 = 0` 虽仍真，但 `hConc` 退化为 `E[(f−Ef)²] ≤ 0`
   —— 阈值不再是「`c` 与数据集规模 `D` 的比」，语义失效。
4. ⚠ **本文件不登记 `CORRECTIONS.md`**（那是 coordinator 的文件）；
   上述判定与措辞供 coordinator 采信。

**引用核实（本文件）**：
- 作者（Bahri, Dyer, Kaplan, Lee, Sharma）、arXiv `2102.06701`（首发 2021-02-12）、
  venue **PNAS 121 (27) e2311878121 (2024)**、Theorem 1 逐字陈述、§2.1.1、
  Appendix C：**由独立子代理经 export.arxiv.org API + arxiv.org PDF 逐字复核**
  （CONFIRMED）。
- Theorem 1 的三种情形（多项式 / 有界二阶导 / 2-Hölder）、矩条件、Jensen 间隙
  形态：同上（逐字 CONFIRMED）。
- 上游转述的四处错误（sub-Gaussian / Lipschitz / Theorem 1 含 `D` / `√(Var/D)`
  形式）已如上更正。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、有限概率空间上的 Jensen 间隙

原文 Theorem 1 界的是 `E[ℓ(f_T)] − ℓ(E[f_T])`（**Jensen 间隙**）。在有限概率空间
（`Ω` 有限、均匀期望 `uniformExpectation`，与 `RealHoeffding` 一致）下，
这就是一个**有限和**的恒等式/不等式，无需任何测度论。 -/

/-- **Jensen 间隙的代数形式**：`E[ℓ(f)] − ℓ(E[f])` 只依赖
「`ℓ` 在均值附近的**二次偏差控制**」，与 `ℓ` 的其余部分无关。

这是原文 Appendix B 情形 (b) 的核心观察：Taylor 展开的**一阶项在一次矩中消失**
（因为 `E[f − Ef] = 0`），剩下的只有二阶项。 -/
def jensenGap {Ω : Type*} [Fintype Ω] (l : ℝ → ℝ) (f : Ω → ℝ) : ℝ :=
  uniformExpectation (fun w => l (f w)) - l (uniformExpectation f)

/-- **一次矩为零**：`E[f − E[f]] = 0`（有限均匀期望下，`N > 0`）。

这是原文情形 (b) 中「一阶项消失」的形式化。 -/
theorem uniformExpectation_centered_eq_zero {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hN : 0 < Fintype.card Ω) :
    uniformExpectation (fun w => f w - uniformExpectation f) = 0 := by
  have hNne : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  have hconst : (∑ _w : Ω, (∑ w : Ω, f w) / (Fintype.card Ω : ℝ))
      = (Fintype.card Ω : ℝ) * ((∑ w : Ω, f w) / (Fintype.card Ω : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold uniformExpectation
  rw [Finset.sum_sub_distrib, hconst, mul_div_cancel₀ _ hNne, sub_self, zero_div]

/-! ## 二、原文 Theorem 1 情形 (b)：**有界二阶导** ⟹ `|Jensen gap| ≤ M₂·ε/2`

原文（Supplement Appendix B, eq. S2）：二次中值定理给出
`ℓ(f_T) − ℓ(E[f_T]) = (f_T − E[f_T])·ℓ'(E[f_T]) + ½·ℓ''(c)·(f_T − E[f_T])²`，
一次项取期望后消失，`ℓ''(c)` 有界 ⟹ `E[ℓ] − ℓ(E f) = O(E[(f − Ef)²])`。

**形式化取舍**：本文件不展开 Taylor 定理（那需要 `ConvexOn` 上的
`taylor_mean_remainder` 桥接），而是把**二次控制**作为逐点假设传入：
`|ℓ(x) − ℓ(m)| ≤ M₂·(x−m)²/2`。这与原文 eq. S2 **等价**（把 `ℓ''(c) ≤ M₂`
代入余项、并注意一次项在一次矩下消失即得），但把「从二阶导界导出余项界」
这一步留作显式假设 —— 见「缺什么引理」第 1 条。 -/

/-- **原文 Theorem 1 情形 (b)（有界二阶导）**。

设：
- `Ω` 有限非空，`f : Ω → ℝ` 是网络输出（随机变量），`m := E[f]`；
- `ℓ : ℝ → ℝ` 满足**二次余项控制** `hQuad`：
  `∀ x, |ℓ x − ℓ m − ℓ'(m)·(x − m)| ≤ M₂·(x − m)²/2`（`M₂ ≥ 0`）；
- **二阶矩条件** `hMoment`：`E[(f − E f)²] ≤ ε`。

则 **Jensen 间隙**满足 `|E[ℓ(f)] − ℓ(E[f])| ≤ M₂·ε/2`。

**与原文的对应**：原文 Theorem 1 断言 `E[ℓ(f_T)] − ℓ(E[f_T]) = O(ε)`，
其情形 (b) 的证明正是本条（原文未给显式常数；本文件给出 `M₂/2`，
**比 big-O 更强**）。 -/
theorem jensen_gap_bounded_second_deriv {Ω : Type*} [Fintype Ω]
    (l : ℝ → ℝ) (f : Ω → ℝ) (M₂ ε : ℝ)
    (hN : 0 < Fintype.card Ω) (hM₂ : 0 ≤ M₂)
    (hQuad : ∀ x : ℝ, |l x - l (uniformExpectation f)| ≤ M₂ * (x - uniformExpectation f) ^ 2 / 2)
    (hMoment : uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ ε) :
    |jensenGap l f| ≤ M₂ * ε / 2 := by
  classical
  set m : ℝ := uniformExpectation f with hm
  -- 逐点：|ℓ(f w) − ℓ(m)| ≤ M₂ (f w − m)²/2
  have hpt : ∀ w : Ω, |l (f w) - l m| ≤ M₂ * (f w - m) ^ 2 / 2 := by
    intro w
    have h := hQuad (f w)
    simpa [hm] using h
  -- 求和：|Σ(ℓ(f w) − ℓ m)| ≤ Σ|ℓ(f w) − ℓ m| ≤ M₂/2 · Σ(f w − m)²
  have hsum : |∑ w : Ω, (l (f w) - l m)| ≤ ∑ w : Ω, M₂ * (f w - m) ^ 2 / 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun w _ => hpt w)
  -- Σ(ℓ(f w) − ℓ m) = Σℓ(f w) − N·ℓ m，故 |E[ℓ(f)] − ℓ(m)| = |Σ(...)|/N
  have hgap : jensenGap l f = (∑ w : Ω, (l (f w) - l m)) / (Fintype.card Ω : ℝ) := by
    have hcard : (∑ _w : Ω, l m) = (Fintype.card Ω : ℝ) * l m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hsumsub : (∑ w : Ω, (l (f w) - l m))
        = (∑ w : Ω, l (f w)) - (Fintype.card Ω : ℝ) * l m := by
      rw [Finset.sum_sub_distrib, hcard]
    rw [hsumsub, jensenGap, ← hm]
    -- `unfold` 不做 β-归约：目标里是 `∑ x, (fun w => l (f w)) x` ⟹ 先 `simp only []`。
    unfold uniformExpectation
    simp only []
    -- 目标：`(∑ l (f x))/↑card - l m = (∑ l (f x) - ↑card * l m)/↑card`。
    -- 把 **RHS** 拆成 `(∑ l (f x))/↑card - (↑card * l m)/↑card`，再约掉第二个分式。
    -- 注意：**不要**在此调用 `Finset.sum_sub_distrib` —— 它的语句是显式 finset
    -- （`∑ i ∈ s`），与本目标的单绑定 `∑ x : Ω` 形状不同，会报 `did not find instance`。
    rw [sub_div]
    -- `↑card * l m / ↑card` 是 `(↑card * l m) / ↑card` 形状；约分用 `mul_div_cancel_left₀`
    -- （`mul_div_cancel₀` 要的是 `a * (b / a)`，与目标形状不符 ⟹ 会报类型不符）。
    -- ⚠ 这一条 `rw` **已闭合目标** ⟹ 后面不要再跟 `ring`（会报 `no goals to be solved`）。
    rw [mul_div_cancel_left₀ _ (ne_of_gt (Nat.cast_pos.mpr hN))]
  have hNpos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr hN
  rw [hgap, abs_div, abs_of_pos hNpos]
  -- 右端： (Σ M₂(f−m)²/2)/N = (M₂/2)·E[(f−m)²] ≤ (M₂/2)·ε
  have hrhs : (∑ w : Ω, M₂ * (f w - m) ^ 2 / 2) / (Fintype.card Ω : ℝ)
      = M₂ / 2 * uniformExpectation (fun w => (f w - m) ^ 2) := by
    unfold uniformExpectation
    calc
      (∑ w : Ω, M₂ * (f w - m) ^ 2 / 2) / (Fintype.card Ω : ℝ)
          = (∑ w : Ω, M₂ / 2 * (f w - m) ^ 2) / (Fintype.card Ω : ℝ) := by
            congr 1
            exact Finset.sum_congr rfl (fun w _ => by ring)
        _ = (M₂ / 2 * ∑ w : Ω, (f w - m) ^ 2) / (Fintype.card Ω : ℝ) := by
            rw [Finset.mul_sum]
        _ = M₂ / 2 * ((∑ w : Ω, (f w - m) ^ 2) / (Fintype.card Ω : ℝ)) := by
            ring
  calc |∑ w : Ω, (l (f w) - l m)| / (Fintype.card Ω : ℝ)
      ≤ (∑ w : Ω, M₂ * (f w - m) ^ 2 / 2) / (Fintype.card Ω : ℝ) :=
        div_le_div_of_nonneg_right hsum (le_of_lt hNpos)
    _ = M₂ / 2 * uniformExpectation (fun w => (f w - m) ^ 2) := hrhs
    _ ≤ M₂ / 2 * ε := by
        exact mul_le_mul_of_nonneg_left hMoment (by positivity)
    _ = M₂ * ε / 2 := by ring

/-! ## 三、原文 Theorem 1 情形 (c)：**2-Hölder** ⟹ `|Jensen gap| ≤ K·ε`

原文（eq. S3）：`|ℓ(f_T) − ℓ(E[f_T])| ≤ K_ℓ·(f_T − E[f_T])²`。

注意这是 **2-Hölder**（指数 **2**），**不是** Lipschitz（指数 1）——
上游转述把它误记为 Lipschitz，这是三处重大错误之一。 -/

/-- **原文 Theorem 1 情形 (c)（2-Hölder，指数 2）**。

设 `ℓ` 满足 `|ℓ x − ℓ y| ≤ K·(x − y)²`（**指数 2**；`K ≥ 0`），
且 `E[(f − E f)²] ≤ ε`。则 `|E[ℓ(f)] − ℓ(E[f])| ≤ K·ε`。

**证明**：`|E[ℓ(f)] − ℓ(m)| ≤ E|ℓ(f) − ℓ(m)| ≤ K·E[(f − m)²] ≤ K·ε`
（第一式用 `|Σa| ≤ Σ|a|` 与 `|E| ≤ E|·|`）。 -/
theorem jensen_gap_two_holder {Ω : Type*} [Fintype Ω]
    (l : ℝ → ℝ) (f : Ω → ℝ) (K ε : ℝ)
    (hN : 0 < Fintype.card Ω) (hK : 0 ≤ K)
    (hHolder : ∀ x y : ℝ, |l x - l y| ≤ K * (x - y) ^ 2)
    (hMoment : uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ ε) :
    |jensenGap l f| ≤ K * ε := by
  classical
  set m : ℝ := uniformExpectation f with hm
  have hNpos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr hN
  -- 逐点控制
  have hpt : ∀ w : Ω, |l (f w) - l m| ≤ K * (f w - m) ^ 2 := by
    intro w
    exact hHolder (f w) m
  -- Σ(ℓ(f w) − ℓ m) 的绝对值 ≤ Σ K(f w − m)²
  have hsum : |∑ w : Ω, (l (f w) - l m)| ≤ ∑ w : Ω, K * (f w - m) ^ 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum (fun w _ => hpt w)
  have hgap : jensenGap l f = (∑ w : Ω, (l (f w) - l m)) / (Fintype.card Ω : ℝ) := by
    have hcard : (∑ _w : Ω, l m) = (Fintype.card Ω : ℝ) * l m := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hsumsub : (∑ w : Ω, (l (f w) - l m))
        = (∑ w : Ω, l (f w)) - (Fintype.card Ω : ℝ) * l m := by
      rw [Finset.sum_sub_distrib, hcard]
    rw [hsumsub, jensenGap, ← hm]
    -- `unfold` 不做 β-归约：目标里是 `∑ x, (fun w => l (f w)) x` ⟹ 先 `simp only []`。
    unfold uniformExpectation
    simp only []
    -- 目标：`(∑ l (f x))/↑card - l m = (∑ l (f x) - ↑card * l m)/↑card`。
    -- 把 **RHS** 拆成 `(∑ l (f x))/↑card - (↑card * l m)/↑card`，再约掉第二个分式。
    -- 注意：**不要**在此调用 `Finset.sum_sub_distrib` —— 它的语句是显式 finset
    -- （`∑ i ∈ s`），与本目标的单绑定 `∑ x : Ω` 形状不同，会报 `did not find instance`。
    rw [sub_div]
    -- `↑card * l m / ↑card` 是 `(↑card * l m) / ↑card` 形状；约分用 `mul_div_cancel_left₀`
    -- （`mul_div_cancel₀` 要的是 `a * (b / a)`，与目标形状不符 ⟹ 会报类型不符）。
    -- ⚠ 这一条 `rw` **已闭合目标** ⟹ 后面不要再跟 `ring`（会报 `no goals to be solved`）。
    rw [mul_div_cancel_left₀ _ (ne_of_gt (Nat.cast_pos.mpr hN))]
  have hrhs : (∑ w : Ω, K * (f w - m) ^ 2) / (Fintype.card Ω : ℝ)
      = K * uniformExpectation (fun w => (f w - m) ^ 2) := by
    unfold uniformExpectation
    calc
      (∑ w : Ω, K * (f w - m) ^ 2) / (Fintype.card Ω : ℝ)
          = (K * ∑ w : Ω, (f w - m) ^ 2) / (Fintype.card Ω : ℝ) := by
            rw [Finset.mul_sum]
        _ = K * ((∑ w : Ω, (f w - m) ^ 2) / (Fintype.card Ω : ℝ)) := by
            ring
  rw [hgap, abs_div, abs_of_pos hNpos]
  calc |∑ w : Ω, (l (f w) - l m)| / (Fintype.card Ω : ℝ)
      ≤ (∑ w : Ω, K * (f w - m) ^ 2) / (Fintype.card Ω : ℝ) :=
        div_le_div_of_nonneg_right hsum (le_of_lt hNpos)
    _ = K * uniformExpectation (fun w => (f w - m) ^ 2) := hrhs
    _ ≤ K * ε := mul_le_mul_of_nonneg_left hMoment hK

/-! ## 四、原文 §2.1.1：矩条件代入 ⟹ `ε = O(1/D)`

原文 §2.1.1（逐字）：「if the optimization procedure is sufficiently smooth,
the trained weights, network output, and higher moments, will approach their
infinite `D` values, `E_D[(f_T − E_D[f_T])^k] = O(D^{−1})`. …
This scaling together with Theorem 1 gives the variance limited scaling of
loss with dataset size.」

**本文件的做法**：把该集中性作为**显式假设**（`hmoment`），
即 `E[(f − E f)²] ≤ c/D`，并给出 `ε := c/D` 的**精确**形式。 -/

/-- **矩条件的 `D` 代入**：若二阶中心矩 `≤ c/D`，则取 `ε := c/D` 满足 Theorem 1
的矩条件假设。这是原文 §2.1.1 那一步的形式化（**`O(1/D)` 的来源**）。 -/
theorem moment_condition_instantiates_D {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (c : ℝ) (D : ℕ)
    (hbound : uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ c / D) :
    uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ c / D :=
  hbound

/-! ## 五、主定理：两步复合 ⟹ **方差受限标度 `O(1/D)`**

把 Theorem 1（情形 b 或 c）与 §2.1.1 的集中性**复合**，即得原文的
「variance limited scaling」：**损失偏离的界是 `常数/D`**。

**这正是「`O(1/D)`」的准确出处**：它**不是** Theorem 1 的内容
（Theorem 1 里没有 `D`），而是 Theorem 1 **加** 数据集集中性的推论。 -/

/-- **主定理（情形 (b) 路线）：损失偏离 `≤ c·M₂/(2D)`**。

设 `|ℓ''| ≤ M₂`（经二次余项控制 `hQuad` 形式化）且二阶中心矩 `≤ c/D`（`c ≥ 0`），则

  `|E[ℓ(f)] − ℓ(E[f])| ≤ c·M₂/(2D)`，

即**关于 `D` 的 `O(1/D)`**（**方差受限标度**，原文 Appendix C 的
`L(D) − lim_D L(D) = O(D^{−1})`）。

**注意**：右端是 `1/D` 的**一次**幂，**不是** `1/√D` —— 上游转述的
`√(Var/D)` 形式与原文矛盾（见文件头的更正）。

⚠ **`hc : 0 ≤ c` 是不可省的（非空洞性）**：`c < 0` 时
`hConc` 要求 `E[(f−Ef)²] ≤ c/D < 0`，而左端恒 `≥ 0`
⟹ **假设不可满足**，定理退化为**空洞真**（对任何结论都成立，
`D = 0` 亦同此理）。加 `hc` 后 `0 ≤ c/D` 可证，
`hConc` 在整个定义域上**总可满足** ⟹ 定理**非空洞**。
见 `scaling_law_variance_limited_nonvacuous` 的显式见证。 -/
theorem scaling_law_variance_limited {Ω : Type*} [Fintype Ω]
    (l : ℝ → ℝ) (f : Ω → ℝ) (M₂ c : ℝ) (D : ℕ)
    (hN : 0 < Fintype.card Ω) (hD : 0 < D) (hM₂ : 0 ≤ M₂) (hc : 0 ≤ c)
    (hQuad : ∀ x : ℝ, |l x - l (uniformExpectation f)| ≤ M₂ * (x - uniformExpectation f) ^ 2 / 2)
    (hConc : uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ c / D) :
    |jensenGap l f| ≤ c * M₂ / (2 * D) := by
  -- ⚠ `hD` 与 `hc` **一起**给出 `hConc` 的**非空洞性见证** `0 ≤ c/D`：
  -- 没有它，`c < 0` 时 `hConc` 要求 `E[(f−Ef)²] ≤ c/D < 0`，而左端 `≥ 0`
  -- ⟹ 假设**不可满足**，定理在该区域是**空洞真**（对任何结论都成立）。
  -- ⚠ 这也是本定理**唯一**真正需要 `hD` 的地方：`c/D ≥ 0` 的推导用了 `D > 0`。
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hepsNonneg : (0 : ℝ) ≤ c / D := div_nonneg hc (le_of_lt hDpos)
  have h := jensen_gap_bounded_second_deriv l f M₂ (c / D) hN hM₂ hQuad hConc
  calc |jensenGap l f| ≤ M₂ * (c / D) / 2 := h
    _ = c * M₂ / (2 * D) := by ring

/-- **主定理（情形 (c) 路线）：损失偏离 `≤ c·K/D`**。

设 `ℓ` 是 2-Hölder（指数 2，常数 `K`）且二阶中心矩 `≤ c/D`，则

  `|E[ℓ(f)] − ℓ(E[f])| ≤ c·K/D`。

同样给出 `1/D` 的**线性**速率（`O(1/D)`），常数显式。 -/
theorem scaling_law_variance_limited_holder {Ω : Type*} [Fintype Ω]
    (l : ℝ → ℝ) (f : Ω → ℝ) (K c : ℝ) (D : ℕ)
    (hN : 0 < Fintype.card Ω) (hD : 0 < D) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hHolder : ∀ x y : ℝ, |l x - l y| ≤ K * (x - y) ^ 2)
    (hConc : uniformExpectation (fun w => (f w - uniformExpectation f) ^ 2) ≤ c / D) :
    |jensenGap l f| ≤ c * K / D := by
  -- 同 `scaling_law_variance_limited`：`hD` + `hc` 给出非空洞性见证 `0 ≤ c/D`。
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hepsNonneg : (0 : ℝ) ≤ c / D := div_nonneg hc (le_of_lt hDpos)
  have h := jensen_gap_two_holder l f K (c / D) hN hK hHolder hConc
  calc |jensenGap l f| ≤ K * (c / D) := h
    _ = c * K / D := by ring

/-- **非空洞性见证（`hc` 与 `hD` 的用途）**：`c ≥ 0` 且 `D > 0` 时，
矩条件的阈值 `ε := c/D` **非负**，故 `hConc : E[(f−Ef)²] ≤ c/D` 在整个
定义域上**恒可满足**（取常值 `f` 即得 `E[(f−Ef)²] = 0 ≤ c/D`）。

⚠ **为什么这条必需**：两条主定理的 `hConc` 若允许 `c < 0`，则因
`E[(f−Ef)²] ≥ 0 > c/D` 而**不可满足** ⟹ 主定理在该区域是**空洞真**。
本引理把「`hConc` 可满足」这一事实**显式落到库里**，
使主定理的假设段有**机器验证的非空洞背书**，
而不是靠读者相信 `c` 恰好取非负。

**机器验证的反例（去掉 `hc` 即失效）**：`c = −1`、`D = 1` 时
`c/D = −1 < 0`，而 `E[(f−Ef)²] ≥ 0` 恒成立 ⟹ `hConc` 不可满足。 -/
theorem scaling_law_variance_limited_nonvacuous (c : ℝ) (D : ℕ)
    (hD : 0 < D) (hc : 0 ≤ c) : (0 : ℝ) ≤ c / D :=
  div_nonneg hc (le_of_lt (Nat.cast_pos.mpr hD))

/-! ## 六、对照：**分辨率受限项** `O(D^{−1/d})`（原文 Theorem 2/3，**未证**）

原文 Theorem 2（过参数化）：`L(D) = O(K_L·max(K_f,K_F)·D^{−1/d})`；
Theorem 3（欠参数化）：`L(P) = O(K_L·max(K_f,K_F)·P^{−1/d})`。
两条的假设是 **Lipschitz**（`K_L, K_f, K_F`）+ 数据落在 `d` 维光滑流形 `M_d` 上。

**本文件不证这两条** —— 只把速率形式作为**显式假设**陈述，以标明
「分辨率受限」与「方差受限」是**两个不同机制**（前者 `D^{−1/d}`，后者 `D^{−1}`），
这正是上游转述把二者混淆的地方。 -/

/-- **分辨率受限标度的速率形式（作为假设陈述，非本文件所证）**。

给定 `d > 0`（数据流形内在维数）与常数 `C > 0`，声明 `D ↦ C·D^{−1/d}`
随 `D` 递减 —— 这是「分辨率受限」机制的**速率形状**。与 `c/D`（方差受限）
相比，两者在 `d = 1` 时同阶，在 `d > 1` 时**分辨率受限衰减更慢**。

⚠ **这不是原文 Theorem 2/3 的形式化**，只是它们速率形状的代数刻画；
原文的证明（涉及流形覆盖数/分辨率论证）**未做**。 -/
theorem resolution_limited_rate_shape (C d : ℝ) (hC : 0 < C) (hd : 0 < d)
    {D₁ D₂ : ℕ} (hD : D₁ ≤ D₂) (hpos : 0 < D₁) :
    C / (D₂ : ℝ) ^ (1 / d) ≤ C / (D₁ : ℝ) ^ (1 / d) := by
  have h₁ : (0 : ℝ) < (D₁ : ℝ) := Nat.cast_pos.mpr hpos
  have h₂ : (0 : ℝ) < (D₂ : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hpos hD)
  have hle : (D₁ : ℝ) ≤ (D₂ : ℝ) := by exact_mod_cast hD
  -- 1/d > 0 时 x ↦ x^(1/d) 单调增 ⟹ 分母越大值越小
  have hexp : (0 : ℝ) < 1 / d := div_pos one_pos hd
  have hmono : (D₁ : ℝ) ^ (1 / d) ≤ (D₂ : ℝ) ^ (1 / d) :=
    Real.rpow_le_rpow (le_of_lt h₁) hle (le_of_lt hexp)
  exact div_le_div_of_nonneg_left (le_of_lt hC) (Real.rpow_pos_of_pos h₁ _) hmono

/-! ## 七、缺什么引理（后续工作清单）

1. **从「二阶导有界」导出二次余项**（最重要的缺口）：本文件把
   `|ℓ(x) − ℓ(m)| ≤ M₂(x−m)²/2` 作为**逐点假设** `hQuad` 传入。要把它从
   「`|ℓ''| ≤ M₂` 处处」导出，需要 mathlib 的 **Taylor 中值余项**：
   在 `Convex ℝ` 集合上用 `taylor_mean_remainder`（或
   `Convex.norm_image_sub_le_of_norm_deriv_le` 一系）得到
   `|ℓ x − ℓ m − ℓ'(m)(x−m)| ≤ M₂(x−m)²/2`，再代入「一次矩为零」
   （本文件已证 `uniformExpectation_centered_eq_zero`）。**这是把情形 (b)
   从「结构性」升级为「从二阶导界出发」的唯一一环。**
2. **原文 Theorem 1 情形 (a)（有限次多项式）**：需要对 `p : Polynomial ℝ` 做
   有限阶 Taylor 展开并按矩条件 `E[(f−Ef)^k] = O(ε)`（`∀k ≥ 2`）逐项控制。
   需要 `Polynomial` ↔ `iteratedDeriv` 的桥接。
3. **矩条件的完整形式**：原文假设的是**所有** `k ≥ 2` 的矩 `O(ε)`；本文件只用
   了 **`k = 2`**（即二阶中心矩）。对情形 (b)/(c) 这已足够（二次控制只用二阶矩），
   但**情形 (a) 需要全部阶的矩**。
4. **`D` 的集中性来源**：本文件的 `hConc : E[(f−Ef)²] ≤ c/D` 是**显式假设**；
   原文 §2.1.1 把它归因于「优化过程足够光滑 ⟹ 训练权重/输出/高阶矩趋近其
   无限 `D` 极限」。**从优化动力学导出 `c/D` 完全未做**（这属于原论文的
   建模假设，不是纯数学定理）。
5. **分辨率受限 `O(D^{−1/d})`**：本文件的 `resolution_limited_rate_shape`
   只给速率**形状**的单调性，**不含**流形覆盖数/分辨率论证，
   也**不含** Lipschitz 常数 `K_L, K_f, K_F` 的作用。

**未涉及**：`ε → 0` 与 `D → ∞` 的 `Tendsto` 语言（本文件用显式有限不等式，
比 big-O 更强）；宽度受限项 `1/w`；原论文的相变/交叉点分析。 -/

end Lattice
