import Mathlib
import Lattice.Lib.Attention.RealAttention
/-!
# LATTICE: 注意力的单调性与温度极限（架构方向，W8-1）

## 建立什么

softmax 作为注意力权重行的、**超出定义本身**的定量事实（任意 `Fin k` 分数、
任意温度 `T > 0`）：

1. `sm_softmax_mono_pair`：**两点单调性**——只把第 `i` 个分数抬高（其余不变），
   则第 `i` 个权重**不降**（分母也变大，故非恒等重述）；
2. `sm_temp_upper`（核心）：`softmax(s/T)_i ≤ exp(-(s_m - s_i)/T)`，`s_m = max_j s_j`；
3. `sm_temp_sharp`：`R ≤ s_m - s_i` ⟹ `softmax(s/T)_i ≤ exp(-R/T)`（可代入的常数界）；
4. `sm_argmax_lower`：`s_i = s_m` ⟹ `softmax(s/T)_i ≥ 1/k`（**与 `T` 无关**的下界）；
5. `sm_temp_mono`：`0 < T ≤ T'`、`s_i = s_m` ⟹ `softmax(s/T')_i ≤ softmax(s/T)_i`。

## 依赖什么

`Mathlib` + `RealAttention`（`Lattice.softmax`、`softmax_denom_pos`）。
**不** import 任何正在被其他代理改动的模块。

## 不做什么（诚实边界）

- 不给 `Filter.Tendsto` 形式；本文件给**逐 `T` 的显式界**（蕴含退化语义，更强）；
- 不涉及硬注意力算子（`RealHardAttention`）与 `T → ∞` 均匀化（`RealSoftmaxTemp`）；
- 对多头 / 因果掩码**不做**任何断言：陈述只针对**单个 softmax 行**；
- ⚠ **不**声称「**同时**抬高所有分数 ⟹ 权重不降」。该命题**需要额外假设**：
  抬高所有分数时分子与分母同时增长，二者的相对速率不可由逐点支配决定。
  本文件因此只证**两点**形态（`sm_softmax_mono_pair`），它是**可证且非平凡**的。

## ⚠ 边界取等检查（结论为何必须带「分数亏损」）

`T → 0` 的退化**只在非最大位置发生**。若 `s_i = s_m`，则 `softmax(s/T)_i ≥ 1/k > 0`
对每个 `T > 0` 恒成立，**不趋于 0**。
- **假命题**：「`∀ i, softmax(s/T)_i → 0`（`T → 0`）」——
  反例 `k = 2`、`s = (0,0)`：两位置皆为 max，权重恒为 `1/2`。
- **真命题**（本文件形态）：结论由**亏损** `s_m - s_i` 控制；亏损为 `0` 时
  界退化为 `≤ 1`（平凡但**正确**），亏损为正时才非平凡。
-/

noncomputable section

namespace Lattice

variable {k : ℕ}

/-- **`i : Fin k` 见证 `k > 0`**。 -/
private lemma fin_card_pos (i : Fin k) : (0 : ℝ) < k := by
  exact_mod_cast i.pos

/-- **温度 softmax 的分母为正**（任意 `T`、任意 `s`）。
`softmax_denom_pos` 的复合形式：分数被线性缩放后分母仍为正。 -/
lemma sm_denom_pos (s : Fin k → ℝ) (T : ℝ) (i : Fin k) :
    0 < ∑ j : Fin k, Real.exp (s j / T) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩

/-- 无温度版（`T = 1`）的分母正性，`sm_softmax_mono_pair` 用。 -/
private lemma sm_denom_pos_one (s : Fin k → ℝ) (i : Fin k) :
    0 < ∑ j : Fin k, Real.exp (s j) := by
  simpa using sm_denom_pos s 1 i

/-- **两点单调性**：只把第 `i` 个分数从 `a` 抬到 `b`（`a ≤ b`，其余坐标不动），
则第 `i` 个权重**不降**。

**它比定义多说了什么**：这是「分子变大而分母同时变大」这一**竞争**的**可解情形**。
设抬高前的分数为 `sa`、抬高后为 `sb`（二者只在 `i` 处不同），则

  `softmax sb i - softmax sa i = (e^b - e^a)·(Σ_{j≠i} e^{s_j}) / (D_b · D_a) ≥ 0`，

其中两个分母都为正、`Σ_{j≠i} e^{s_j} ≥ 0`、`e^b ≥ e^a`。
**关键**：分子中的 `(e^b - e^a)` 与**其余项之和**配对，正是「分母变大的量与分子变大的
量同阶」的定量形式——故结论**非平凡**（不是把定义换句话重说）。

**证明**：通分后左右交叉相乘，化为 `e^a·(e^b + R) ≤ e^b·(e^a + R)`
（`R := Σ_{j≠i} e^{s_j} ≥ 0`），即 `e^a·R ≤ e^b·R`，由 `e^a ≤ e^b`、`R ≥ 0` 得。

⚠ **`k = 1` 的退化**：此时 `R = 0`，差为 `0`（结论仍真但平凡）——
本定理**不**需要 `k ≥ 2` 的显式假设，因为 `R ≥ 0` 已足够。 -/
theorem sm_softmax_mono_pair (s : Fin k → ℝ) (i : Fin k) (a b : ℝ) (hab : a ≤ b) :
    softmax (fun j => if j = i then a else s j) i
      ≤ softmax (fun j => if j = i then b else s j) i := by
  haveI : Nonempty (Fin k) := ⟨i⟩
  set sa : Fin k → ℝ := fun j => if j = i then a else s j with hsa
  set sb : Fin k → ℝ := fun j => if j = i then b else s j with hsb
  have hsa_i : sa i = a := by simp [hsa]
  have hsb_i : sb i = b := by simp [hsb]
  have hDa : 0 < ∑ j : Fin k, Real.exp (sa j) := sm_denom_pos_one sa i
  have hsplit_a : ∑ j : Fin k, Real.exp (sa j)
      = Real.exp a + ∑ j ∈ Finset.univ.erase i, Real.exp (sa j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hsa_i, add_comm]
  have hsplit_b : ∑ j : Fin k, Real.exp (sb j)
      = Real.exp b + ∑ j ∈ Finset.univ.erase i, Real.exp (sb j) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hsb_i, add_comm]
  have hsame : ∑ j ∈ Finset.univ.erase i, Real.exp (sa j)
      = ∑ j ∈ Finset.univ.erase i, Real.exp (sb j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [hsa, hsb, hji]
  set R : ℝ := ∑ j ∈ Finset.univ.erase i, Real.exp (sa j) with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => le_of_lt (Real.exp_pos _)
  have hDa' : ∑ j : Fin k, Real.exp (sa j) = Real.exp a + R := hsplit_a
  have hDb' : ∑ j : Fin k, Real.exp (sb j) = Real.exp b + R := by rw [hsplit_b, hsame]
  have hDa_pos : 0 < Real.exp a + R := hDa' ▸ hDa
  have hDb_pos : 0 < Real.exp b + R := by
    have : 0 < ∑ j : Fin k, Real.exp (sb j) := sm_denom_pos_one sb i
    rwa [hDb'] at this
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  rw [softmax, softmax]
  simp only [hsa_i, hsb_i, hDa', hDb']
  rw [div_le_div_iff₀ hDa_pos hDb_pos]
  nlinarith [hexp, hR0, Real.exp_pos a, Real.exp_pos b]

/-! ## 二、温度上界（核心）：非最大位置被指数压掉 -/

/-- **温度上界（核心定理）**：`sm := max_j s_j`，则对任意 `T > 0`、任意 `i`，

  `softmax(s/T)_i ≤ exp(-(sm - s_i)/T)`。

**它比定义多说了什么**：定义只给出「分子除以分母」；本定理把比值**从上方**
化成一个**只依赖 `i` 自身亏损**的指数式，**与其余坐标的分数无关**
（分母被最大项从下方界住，其余项非负）。
由此立即得到 `T → 0` 的退化语义：亏损 `> 0` 时右端随 `T ↓ 0` 指数消失。

⚠ **边界取等**：`s_i = sm` 时右端 `= exp 0 = 1`，界**取等且平凡**——
这是**正确**的（权重至多 `1`），而非「趋于 0」。 -/
theorem sm_temp_upper (s : Fin k → ℝ) (i : Fin k) (T : ℝ) (hT : 0 < T) :
    softmax (fun j => s j / T) i
      ≤ Real.exp (-((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) - s i) / T) := by
  obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) ⟨i, Finset.mem_univ i⟩ s
  haveI : Nonempty (Fin k) := ⟨i⟩
  have hsingle : Real.exp ((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) / T)
      ≤ ∑ j : Fin k, Real.exp (s j / T) := by
    have h := Finset.single_le_sum (f := fun j : Fin k => Real.exp (s j / T))
      (fun _ _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ j0)
    simp only at h
    have h2 : Real.exp (s j0 / T)
        = Real.exp ((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) / T) := by rw [hj0]
    exact h2 ▸ h
  have hden : 0 < Real.exp ((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) / T) := Real.exp_pos _
  calc softmax (fun j => s j / T) i
      = Real.exp (s i / T) / ∑ j : Fin k, Real.exp (s j / T) := rfl
    _ ≤ Real.exp (s i / T) / Real.exp ((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) / T) :=
        div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hden hsingle
    _ = Real.exp (-((Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) - s i) / T) := by
        rw [← Real.exp_sub]
        congr 1
        ring

/-- **温度上界的 sharp 常数形态**：`R ≤ sm - s_i` ⟹ `softmax(s/T)_i ≤ exp(-R/T)`。

**它比定义多说了什么**：把上一条的**实际亏损**换成**任意给定下界** `R`，
使定理可按「已知的最小分差」直接代入。

⚠ **`hgain` 不可省**：去掉后取 `k = 2`、`s = (0,0)`、`R = 1`、`T = 1/10`：
左端 `= 1/2`，右端 `= exp(-10) ≈ 4.5e-5 < 1/2`，**命题为假**。
⚠ `s_i = sm`（亏损 `0`）时 `hgain` 迫使 `R ≤ 0`，右端 `≥ 1`，界平凡但正确。 -/
theorem sm_temp_sharp (s : Fin k → ℝ) (i : Fin k) (T R : ℝ) (hT : 0 < T)
    (hgain : R ≤ (Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) - s i) :
    softmax (fun j => s j / T) i ≤ Real.exp (-R / T) := by
  refine le_trans (sm_temp_upper s i T hT) (Real.exp_le_exp.mpr ?_)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right hgain (le_of_lt hT)

/-! ## 三、反向对照：最大位置的下界与温度单调 -/

/-- **最大位置的权重下界**：`s_i = sm` ⟹ `softmax(s/T)_i ≥ 1/k`（**与 `T` 无关**）。

**它比定义多说了什么**：给出**一致**下界。分母是 `k` 项之和，每项
`≤ exp(s_i/T)`（因 `s_i` 是最大值）⟹ 分母 `≤ k·exp(s_i/T)`，分子 `= exp(s_i/T)`，
故商 `≥ 1/k`。⚠ `k > 0` 由签名的 `i : Fin k` 强制。 -/
theorem sm_argmax_lower (s : Fin k → ℝ) (i : Fin k) (T : ℝ) (hT : 0 < T)
    (hi : s i = Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) :
    1 / (k : ℝ) ≤ softmax (fun j => s j / T) i := by
  haveI : Nonempty (Fin k) := ⟨i⟩
  have hD : 0 < ∑ j : Fin k, Real.exp (s j / T) := sm_denom_pos s T i
  have hnum : 0 < Real.exp (s i / T) := Real.exp_pos _
  have hterm : ∀ j : Fin k, Real.exp (s j / T) ≤ Real.exp (s i / T) := by
    intro j
    have hj : s j ≤ s i := by
      rw [hi]; exact Finset.le_sup' s (Finset.mem_univ j)
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hj (le_of_lt hT))
  have hden : ∑ j : Fin k, Real.exp (s j / T) ≤ (k : ℝ) * Real.exp (s i / T) := by
    calc ∑ j : Fin k, Real.exp (s j / T) ≤ ∑ _j : Fin k, Real.exp (s i / T) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (k : ℝ) * Real.exp (s i / T) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkpos : (0 : ℝ) < k := fin_card_pos i
  rw [softmax, div_le_div_iff₀ (by positivity) hD]
  nlinarith [hden, hnum, hkpos]

/-- **温度单调（降温使最大位置权重不降）**：`0 < T ≤ T'`、`s_i = sm` ⟹
`softmax(s/T')_i ≤ softmax(s/T)_i`。

**它比定义多说了什么**：把「低温 ⟹ 更尖锐」落到**同一坐标的单调比较**上。

**证明路线（⚠ 本文件写作中实测更正过一次）**：初稿走的是
`softmax(s/T')_i ≤ 1/k ≤ softmax(s/T)_i`（把 `≤ 1/k` 当作中间引理）。
⚠ **该中间引理 `softmax(s/T')_i ≤ 1/k` 为假**：`i` 是 argmax 时
`Σ_j exp(s_j/T) ≤ k·exp(s_i/T)` 给出的是**下界** `softmax_i ≥ 1/k`，
方向与上界相反（反例：`k = 3`、`s = (1,0,0)`、`T = 1` 时 `softmax_0 = 0.576 > 1/3`）。
⇒ 该路线**不可能**闭合，已弃用。

**现路线**（只用到 `i` 是最大值）：用移位恒等式
`exp(s_j/U) = exp(s_i/U)·exp((s_j - s_i)/U)` 把两侧的商**同时**化为
`1 / Σ_j exp((s_j - s_i)/U)`——此时 `exp(s_i/U)` 因子精确约掉，
只剩「`T` 越小 ⟹ `(s_j - s_i)/T` 越小（更负）⟹ 求和越小 ⟹ 倒数越大」。
即由 `s_j - s_i ≤ 0` 与 `T ≤ T'` 得 `(s_j - s_i)/T ≤ (s_j - s_i)/T'`，
逐项取 `exp` 后求和，再用 `one_div_le_one_div_of_le`（**注意其结论方向**：
`1/b ≤ 1/a`）收口。

⚠ **`0 < T` 不可省**：`T = 0` 时 `s j / T` 是除零垃圾值。
⚠ **`hi` 不可省**：`i` 不是最大位置时 `s_j ≤ s_i` 失败，逐项比较垮掉。 -/
theorem sm_temp_mono (s : Fin k → ℝ) (i : Fin k) (T T' : ℝ) (hT : 0 < T)
    (hTT' : T ≤ T') (hi : s i = Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ s) :
    softmax (fun j => s j / T') i ≤ softmax (fun j => s j / T) i := by
  haveI : Nonempty (Fin k) := ⟨i⟩
  have hT'pos : 0 < T' := lt_of_lt_of_le hT hTT'
  have hle : ∀ j : Fin k, s j ≤ s i := by
    intro j
    rw [hi]; exact Finset.le_sup' s (Finset.mem_univ j)
  have hshift : ∀ (U : ℝ) (j : Fin k),
      Real.exp (s j / U) = Real.exp (s i / U) * Real.exp ((s j - s i) / U) := by
    intro U j
    rw [← Real.exp_add]
    congr 1
    ring
  have hfac : ∀ U : ℝ, (∑ j : Fin k, Real.exp (s j / U))
      = Real.exp (s i / U) * ∑ j : Fin k, Real.exp ((s j - s i) / U) := by
    intro U
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hshift U j
  have hterm : ∀ j : Fin k, Real.exp ((s j - s i) / T) ≤ Real.exp ((s j - s i) / T') := by
    intro j
    apply Real.exp_le_exp.mpr
    have hnum : s j - s i ≤ 0 := by linarith [hle j]
    rw [div_le_div_iff₀ hT hT'pos]
    nlinarith [hnum, hTT']
  have hden : ∑ j : Fin k, Real.exp ((s j - s i) / T)
      ≤ ∑ j : Fin k, Real.exp ((s j - s i) / T') :=
    Finset.sum_le_sum fun j _ => hterm j
  have hpos : 0 < ∑ j : Fin k, Real.exp ((s j - s i) / T) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  have hkey : (1 : ℝ) / (∑ j : Fin k, Real.exp ((s j - s i) / T'))
      ≤ 1 / (∑ j : Fin k, Real.exp ((s j - s i) / T)) :=
    one_div_le_one_div_of_le hpos hden
  have hA : softmax (fun j => s j / T') i
      = 1 / (∑ j : Fin k, Real.exp ((s j - s i) / T')) := by
    rw [softmax, hfac T']
    field_simp
  have hB : softmax (fun j => s j / T) i
      = 1 / (∑ j : Fin k, Real.exp ((s j - s i) / T)) := by
    rw [softmax, hfac T]
    field_simp
  rw [hA, hB]
  exact hkey

end Lattice
