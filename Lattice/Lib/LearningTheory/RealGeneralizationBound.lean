import Mathlib
import Lattice.Lib.Concentration.RealHoeffding
import Lattice.Lib.Concentration.RealUnionBound
import Lattice.Lib.LearningTheory.RealPACBayes
/-!
# LATTICE: 统一泛化界接口 —— Rademacher / PAC-Bayes / 并集界三条路线的汇总

方向（§5 验证行「泛化界」）：`RealHoeffding` 给出单个假设的经验风险到真实风险的
指数集中（**集中不等式**），`RealUnionBound` 把「单假设的坏事件」放大为
「有限假设类中至少一个假设坏」的并集界（容量代价 `log |F|`），
`RealPACBayes` 用变测度法给出数据相关的容量代价 `KL(Q‖P)`。
`RealRademacher` 则用对称化把同样的集中不等式接到 Rademacher 复杂度上。
本文件把这些**统一**成一个「泛化界接口」：

  **给定容量度量 `cap` + 一个集中不等式（坏事件概率 ≤ δ） ⟹ 泛化界 `pop ≤ emp + bound`**。

核心定义 `generalizesWith emp pop bound δ` 把「以概率 ≥ 1 − δ 有 `pop ≤ emp + bound`」
写成坏事件的概率界 `P(bound < pop − emp) ≤ δ`；
结构 `GeneralizationBound emp pop` 把容量、置信度、界与**已证明的** soundness
打包成一个「证明携带」的接口。随后给出三个实例：

1. `genBound_single`：**单假设**（集中不等式本身，Hoeffding 双边界）。
2. `genBound_finiteClass` / `genBound_erm`：**有限假设类的一致收敛**
   （并集界 + Hoeffding；`genBound_erm` 对任意数据相关的选择器 `sel` 成立，
   即「ERM 型」泛化界）。
3. `genBound_pacBayes`：**PAC-Bayes**（变测度法，容量 = `KL(Q‖P)`）。

最后 `genBound_capacity_mono` / `genBound_subsample_mono` / `genBound_tradeoff`
给出接口级的**容量-风险权衡**单调性（容量越大界越松、样本越多界越紧），
与 `RealRidge` 的岭正则化（用 `β‖w‖²` 控制有效容量）在 docstring 层面衔接。

**诚实标注**：本文件的 Rademacher 实例以**有限假设类的并集界**为容量
（`cap = log |F|`，实际常数 `|F|·2e^{−nt²/8}`）；`RealRademacher` 的
对称化路线把容量细化到 `Rad_n(F)`，但本文件**未**把那条界直接嵌入接口
（接口需要 `Rad` 的显式数值，属后续工作）。统一接口本身是定义 + 三个真实实例，
不含任何未证假设。`Real.log` 是全函数。不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、泛化界接口 -/

/-- **泛化界语义**：坏事件 `bound < pop ω − emp ω` 的概率 ≤ `δ`，
即「`pop ≤ emp + bound` 以概率 ≥ 1 − δ 成立」。 -/
def generalizesWith {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (emp pop : Ω → ℝ) (bound δ : ℝ) :
    Prop :=
  uniformProb (Finset.univ.filter (fun ω => bound < pop ω - emp ω)) ≤ δ

/-- **泛化界接口（证明携带结构）**：给定经验风险 `emp`、真实风险 `pop`，
一个泛化界由容量度量 `cap`、置信参数 `δ`、界值 `bound` 与**已验证的**
soundness 命题 `sound : generalizesWith emp pop bound δ` 组成。

「容量 + 集中不等式 ⟹ 泛化界」这一范式在 Lean 里就是：把 soundness 的证明
作为结构字段传入。`cap` 不参与 soundness 的证明，它只记录**代价来源**
（`log |F|` 或 `KL(Q‖P)`），由后续的权衡引理使用。 -/
structure GeneralizationBound {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (emp pop : Ω → ℝ) where
  /-- 容量度量：`log |F|`（有限类）或 `KL(Q‖P)`（PAC-Bayes）。 -/
  cap : ℝ
  /-- 置信参数 δ。 -/
  delta : ℝ
  /-- 泛化界值：`pop ≤ emp + bound` 以概率 ≥ 1 − δ 成立。 -/
  bound : ℝ
  /-- δ > 0。 -/
  hdelta : 0 < delta
  /-- 已证明的 soundness。 -/
  sound : generalizesWith emp pop bound delta

/-- 接口的 soundness 展开（供下游直接使用）。 -/
theorem GeneralizationBound.sound' {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {emp pop : Ω → ℝ}
    (B : GeneralizationBound emp pop) : generalizesWith emp pop B.bound B.delta :=
  B.sound

/-! ## 二、实例 1：单假设（集中不等式本身） -/

/-- **单假设泛化界**：`|f| ≤ 1`、`n` 个坐标的均匀（组合式）平均、真实风险 `μ = E f`，
则 `μ > Êf + t` 的概率 ≤ `2·e^{−nt²/8}`（`RealHoeffding.hoeffding_two_sided`）。
样本空间是 `Fin n → α` 上由 `uniformProb` 给出的均匀（组合式）概率，
参数中不含任何独立性假设（`hn : 0 < n`、`hN : 0 < Fintype.card α` 仅保证基数非零）。
这是接口的最基本实例：容量为 1（单个假设），集中不等式直接给出界。 -/
theorem genBound_single {α : Type*} [Fintype α] [DecidableEq α] {f : α → ℝ}
    (mu : ℝ) (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hmean : uniformExpectation f = mu) (hb : ∀ x : α, |f x| ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    generalizesWith (Ω := Fin n → α)
      (fun w => (∑ i : Fin n, f (w i)) / (n : ℝ)) (fun _ => mu) t
      (2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)) := by
  unfold generalizesWith
  have hsub : Finset.univ.filter (fun w : Fin n → α =>
        t < mu - (∑ i : Fin n, f (w i)) / (n : ℝ)) ⊆
      Finset.univ.filter (fun w : Fin n → α =>
        t ≤ |(∑ i : Fin n, f (w i)) / (n : ℝ) - mu|) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have h1 : t ≤ |mu - (∑ i : Fin n, f (w i)) / (n : ℝ)| :=
      le_trans (le_of_lt hw) (le_abs_self _)
    rwa [abs_sub_comm] at h1
  refine le_trans ?_ (hoeffding_two_sided mu n hn hN hmean hb ht)
  unfold uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (Nat.cast_nonneg _)

/-- 单假设泛化界的**接口打包**（`cap = 1`）。 -/
def genBound_single_bundle {α : Type*} [Fintype α] [DecidableEq α] {f : α → ℝ}
    (mu : ℝ) (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α)
    (hmean : uniformExpectation f = mu) (hb : ∀ x : α, |f x| ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    GeneralizationBound (Ω := Fin n → α)
      (fun w => (∑ i : Fin n, f (w i)) / (n : ℝ)) (fun _ => mu) where
  cap := 1
  delta := 2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)
  bound := t
  hdelta := by positivity
  sound := genBound_single mu n hn hN hmean hb ht

/-! ## 三、实例 2：有限假设类的一致收敛（并集界 + Hoeffding） -/

/-- **有限假设类的一致收敛**：假设类以有限指标集 `ι` 参数化
（`Fintype ι`、容量 `log |ι|`），每个假设 `fs i` 满足 `|fs i x| ≤ 1`。
则「**存在**某个假设 `i` 使经验均值偏离真实风险 ≥ t」的概率
≤ `|ι| · 2·e^{−nt²/8}` —— 并集界把 `|ι|` 个单假设坏事件的概率相加
（`RealUnionBound.union_bound_finite`）。
本定理陈述中**没有**任何容量项：结论是绝对概率界 `|ι| · 2e^{−nt²/8}`，
既无 `cap` 字段也无 `log |ι|`；「容量代价从 `log 1` 升到 `log |ι|`」只是
容量度量的叙述（见 `GeneralizationBound.cap` 的类型说明），并不出现在本定理陈述内。
另需注意该界仅在 `t < 1` 时非平凡：当 `t ≥ 1` 时右端 `≥ 2|ι|`，
已不再是概率意义上的有效界（严格情形 `t ≥ 2` 恒为真）。 -/
theorem genBound_finiteClass {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    [DecidableEq ι] (fs : ι → (α → ℝ)) (hfs : ∀ i x, |fs i x| ≤ 1)
    (n : ℕ) (hn : 0 < n) (hN : 0 < Fintype.card α) {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        ∃ i : ι, t ≤ |(∑ j : Fin n, fs i (w j)) / (n : ℝ) - uniformExpectation (fs i)|)) ≤
      (Fintype.card ι : ℝ) * (2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)) := by
  have hset : Finset.univ.filter (fun w : Fin n → α =>
        ∃ i : ι, t ≤ |(∑ j : Fin n, fs i (w j)) / (n : ℝ) - uniformExpectation (fs i)|)
      = (Finset.univ : Finset ι).biUnion (fun i => Finset.univ.filter (fun w : Fin n → α =>
          t ≤ |(∑ j : Fin n, fs i (w j)) / (n : ℝ) - uniformExpectation (fs i)|)) := by
    ext w
    simp [Finset.mem_biUnion]
  rw [hset]
  have h := union_bound_finite (Finset.univ : Finset ι)
    (fun i => Finset.univ.filter (fun w : Fin n → α =>
      t ≤ |(∑ j : Fin n, fs i (w j)) / (n : ℝ) - uniformExpectation (fs i)|))
    (fun i _ => hoeffding_two_sided (uniformExpectation (fs i)) n hn hN rfl (hfs i) ht)
  simpa [Finset.card_univ] using h

/-- **ERM 型泛化界**：对**任意数据相关**的选择器 `sel : (Fin n → α) → ι`
（例如经验风险最小化器），「所选假设的真实风险超过经验风险 + t」的概率
同样 ≤ `|ι|·2e^{−nt²/8}`：坏事件 ⊆ 一致收敛的坏事件
（因为 `sel w` 也是某个假设）。 -/
theorem genBound_erm {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    [DecidableEq ι] (fs : ι → (α → ℝ)) (hfs : ∀ i x, |fs i x| ≤ 1)
    (n : ℕ) (hn : 0 < n) (sel : (Fin n → α) → ι) (hN : 0 < Fintype.card α)
    {t : ℝ} (ht : 0 < t) :
    uniformProb (Finset.univ.filter (fun w : Fin n → α =>
        t < uniformExpectation (fs (sel w)) -
          (∑ j : Fin n, fs (sel w) (w j)) / (n : ℝ))) ≤
      (Fintype.card ι : ℝ) * (2 * Real.exp (-(n : ℝ) * t ^ 2 / 8)) := by
  refine le_trans ?_ (genBound_finiteClass fs hfs n hn hN ht)
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    refine ⟨sel w, ?_⟩
    have h1 : t ≤ |uniformExpectation (fs (sel w)) -
        (∑ j : Fin n, fs (sel w) (w j)) / (n : ℝ)| :=
      le_trans (le_of_lt hw) (le_abs_self _)
    rwa [abs_sub_comm] at h1)

/-! ## 四、实例 3：PAC-Bayes（变测度法） -/

/-- **PAC-Bayes 泛化界（接口版）**：有限先验 `P`、后验 `Q`（均严格正、各和为 1），
损失取值 `[0,1]`，则后验风险 `E_Q R` 与后验经验风险 `E_Q R̂` 之差
以概率 ≥ 1 − δ 被 `(KL(Q‖P) + log(1/δ) + λ²/(2n))/λ` 控制
（对任意 `λ > 0`）。直接来自 `RealPACBayes.pacBayes_bound`，
容量度量为 `KL(Q‖P)`（`RealKL.kl`），**数据相关**且不需要 `log |F|`。 -/
theorem genBound_pacBayes {Z : Type*} [Fintype Z] [DecidableEq Z] (k n : ℕ)
    (hk : 0 < k) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ)
    (hP : ∀ h, 0 < P h) (hPsum : ∑ h, P h = 1)
    (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1)
    (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    generalizesWith (Ω := Fin n → Z)
      (fun w => pacBayesPosteriorEmpRisk loss Q w)
      (fun _ => pacBayesPosteriorRisk loss Q)
      ((kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam) δ := by
  unfold generalizesWith
  refine le_trans ?_ (pacBayes_bound k n hk hN hn P Q loss hP hPsum hQ hQsum h01 hδ hlam)
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (fun w hw => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    linarith)

/-- PAC-Bayes 泛化界的**接口打包**（容量 = `KL(Q‖P)`）。 -/
def genBound_pacBayes_bundle {Z : Type*} [Fintype Z] [DecidableEq Z] (k n : ℕ)
    (hk : 0 < k) (hN : 0 < Fintype.card Z) (hn : 0 < n)
    (P Q : Fin k → ℝ) (loss : Fin k → Z → ℝ)
    (hP : ∀ h, 0 < P h) (hPsum : ∑ h, P h = 1)
    (hQ : ∀ h, 0 < Q h) (hQsum : ∑ h, Q h = 1)
    (h01 : ∀ h z, 0 ≤ loss h z ∧ loss h z ≤ 1)
    {δ lam : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) :
    GeneralizationBound (Ω := Fin n → Z)
      (fun w => pacBayesPosteriorEmpRisk loss Q w)
      (fun _ => pacBayesPosteriorRisk loss Q) where
  cap := kl Q P
  delta := δ
  bound := (kl Q P + Real.log (1 / δ) + lam ^ 2 / (2 * (n : ℝ))) / lam
  hdelta := hδ
  sound := genBound_pacBayes k n hk hN hn P Q loss hP hPsum hQ hQsum h01 hδ hlam

/-! ## 五、容量-风险权衡的接口级单调性 -/

/-- **容量越大，界越松**：固定 `λ > 0` 与其它项 `L`，
`(cap + L)/λ` 关于 `cap` 单调不减。这对应 PAC-Bayes 界的容量项：
`KL(Q‖P)` 增大（后验偏离先验更远）则界变松。 -/
theorem genBound_capacity_mono {cap cap' L lam : ℝ} (hcap : cap ≤ cap') (hlam : 0 < lam) :
    (cap + L) / lam ≤ (cap' + L) / lam :=
  div_le_div_of_nonneg_right (by linarith) (le_of_lt hlam)

/-- **样本越多，界越紧**：`λ²/(2n)` 关于 `n` 单调不增（`n > 0`），
故界关于样本数 `n` 单调不增。 -/
theorem genBound_subsample_mono {cap L lam : ℝ} (hlam : 0 < lam) {n n' : ℕ}
    (hn : 0 < n) (hnn : n ≤ n') :
    (cap + L + lam ^ 2 / (2 * (n' : ℝ))) / lam ≤
      (cap + L + lam ^ 2 / (2 * (n : ℝ))) / lam := by
  have hbase : lam ^ 2 / (2 * (n' : ℝ)) ≤ lam ^ 2 / (2 * (n : ℝ)) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hcast : (n : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hnn
    exact div_le_div_of_nonneg_left (sq_nonneg lam) (by linarith)
      (by linarith)
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hlam)

/-- **容量-风险权衡**：把「经验风险 + 容量项」作为总界时，
非负容量项只会让界变松：`L/λ ≤ (cap + L)/λ`（`cap ≥ 0`、`λ > 0`）。
这对应 `RealRidge` 的岭正则化：正则强度 `β`（等价于容量预算）越大，
训练误差项可被压小，但泛化界的容量项变大——权衡由该单调性刻画。 -/
theorem genBound_tradeoff {cap L lam : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    L / lam ≤ (cap + L) / lam :=
  div_le_div_of_nonneg_right (by linarith) (le_of_lt hlam)

/-! ## 六、注：三条路线的汇总与后续工作

· **单假设 → 有限类**：`genBound_single`（容量 1，集中不等式）
  经 `RealUnionBound.union_bound_finite` 放大为 `genBound_finiteClass`
  （容量 `log |ι|`），再经「选择器坏事件 ⊆ 一致坏事件」得到 `genBound_erm`。
· **有限类 → PAC-Bayes**：`genBound_pacBayes` 用 `RealPACBayes.pacBayes_change_of_measure`
  （Gibbs 变分式）把容量从 `log |ι|` 换成数据相关的 `KL(Q‖P)`；
  `genBound_capacity_mono` / `genBound_subsample_mono` 给出界对容量、样本数的单调性。
· **Rademacher（`RealRademacher`）**：同一集中不等式经对称化给出
  `E sup_f (Ef − Êf) ≤ 2 Rad_n(F)`，把容量细化为 Rademacher 复杂度；
  本文件的有限类实例是它的「并集界」对应物。**未做（诚实标注）**：
  把 `Rad_n(F)` 的显式数值直接填入 `GeneralizationBound.cap` 字段
  （需要为具体函数类计算 `Rad`）。
· **与 `RealRidge` 的衔接**：岭正则化 `β‖w‖²` 通过限制权重范数控制有效容量，
  对应本文件 `genBound_tradeoff` 的「容量项单调」；把 `β` 精确翻译为
  `KL(Q‖P)` 的具体数值**未做**。
-/

end Lattice
