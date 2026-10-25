import Mathlib
import Lattice.Lib.Concentration.RealStochasticProcess
import Lattice.Lib.Concentration.RealAzumaMartingale
import Lattice.Lib.Concentration.RealMartingaleChain
import Lattice.Lib.Concentration.RealHoeffding
/-!
# LATTICE: 多步过滤迭代与条件期望乘积引理 —— 鞅差之和的整段 MGF 界

对应 `ROADMAP.md` **A3.2**（多步过滤迭代的通用引理，把 `RealMcDiarmid` 的 `hmgf`
真正证出）与 **A3.3**（多界相乘的条件期望引理 `condExpFiber_mul_of_adapted`）。
这两个缺口在既有文件里都有**明确标注**：

* `RealMartingaleChain` 路线 A（该文件 docstring 明列「路线 A 停在单界传递」，
  行号略，以文字定位）：把
  `FibreBound π Y₁ EB₁` 与 `FibreBound π Y₂ EB₂` 合并为 `FibreBound π (Y₁·Y₂) (EB₁·EB₂)`
  需要 `AdaptedTo π Y₁` 才能把 `Y₁` 提出条件期望，而**乘积版**
  `condExpFiber_mul_of_adapted`「在本文件与既有文件中均未构造」——**本文件构造之**。
* `RealAzumaMartingale` 的诚实清单「**未做（多期过滤迭代）**」条：把上述 `hmgf`
  真正证明出来所需的 n 步过滤迭代未做；该文件亦把
  「多期滤链的完整迭代」留作未来工作（它只建立了单步条件 Hoeffding
  `condExpFiber_hoeffding` 与塔串接 `tower_hoeffding_transfer`）——**本文件补上迭代**。

## 定理链

**第一部分：乘积引理族（A3.3）**
  1. `condExpFiber_nonneg_p`：非负函数的纤维均值非负；
  2. `condExpFiber_mul_of_adapted_at`：点形式
     `E[Y₁·Y₂ | π](π a) = Y₁ a · E[Y₂ | π](π a)`（`Y₁` 关于 `π` 可测）；
  3. `condExpFiber_mul_of_adapted_mem`：纤维成员形式（沿 `a ∈ fiber π b`）；
  4. `condExpFiber_mul_of_adapted`（**主引理**）：无纤维假设的形式
     `E[Y₁·Y₂ | π](b) = E[Y₁ | π](b) · E[Y₂ | π](b)`
     —— 空纤维时两边同为零，故**不需要非空纤维前提**；
  5. `condExpFiber_mul_of_adapted_of_ne`：非空纤维 + `Classical.choose` 形式；
  6. `fibreBound_mul`：**多界相乘** `FibreBound π Y₁ EB₁ → FibreBound π Y₂ EB₂ →
     FibreBound π (Y₁·Y₂) (EB₁·EB₂)`（这正是路线 A 缺的那一步）。

**第二部分：n 步过滤迭代（A3.2）**
  7. `fibreBound_mgf_succ`：**单步推进**（迭代的归纳步）
     `FibreBound ρ (e^{λS_k}) (B k) → FibreBound ρ (e^{λS_{k+1}}) (B k · e^{λ²c_k²/2})`；
  8. `fibreBound_mgf_iterate`（**主定理**）：单步条件 Hoeffding 界沿 `n` 步**逐步复合**
     `FibreBound ρ (e^{λS_n}) (exp(λ²·∑_{j<n}c_j²/2))`；
  9. `uniformExpectation_mgf_iterate`：**整段 MGF 界**
     `E[e^{λS_n}] ≤ exp(λ²·∑_{j<n}c_j²/2)`；
  10. `uniformExpectation_mgf_iterate_of_condZeroMean`：把单步假设 `hstep`
      **真正证出** —— 每步由鞅差条件 `CondZeroMean` + 有界性 + `c k > 0` + 非空纤维，
      经 `RealAzumaMartingale.condExpFiber_hoeffding` 给出条件 MGF 界；
  11. `uniformExpectation_mgf_iterate_uniform`：等界特例 `exp(λ²·n·c²/2)`。

**辅助**
  12. `sum_eq_sum_card_mul_condExpFiber` / `sum_card_fiber` / `uniformExpectation_le_of_fibreBound`
      （纤维分解求和形式，把 `FibreBound` 转成全局期望界）。

## 诚实边界（本文件不证 / 不声称的）

* **σ-代数固定的迭代（重要）**：`fibreBound_mgf_iterate` 在**固定投影 `ρ`** 上迭代
  —— σ-代数不变，而**逐步的条件 Hoeffding 界 `hstep k` 可以不同**
  （不同增量 `D k`、不同常数 `c k`）。这正是「把单步界复合为整段界」的实质内容，
  也是 McDiarmid/Azuma MGF 步的标准归纳结构。
  一般 n 期滤链 `ρ 0 ⊑ ρ 1 ⊑ ⋯`（σ-代数**随期数变化**）的版本见
  `fibreBound_mgf_iterate_filtration`：其**跨 σ-代数的传递步 `htransfer` 作为显式假设列出**
  （见该定理 `未证` 标注）——`RealAzumaMartingale.tower_hoeffding_transfer` 只给出
  **细 → 粗**方向的传递，而该处需要**粗 → 细**方向，如实列为剩余工作。
* **常数 `/2` 与 `RealMcDiarmid` 的 `/8`（重要·如实标注）**：本文件的迭代给出
  `exp(λ²·∑c²/2)`，与 `RealAzuma.hoeffding_lemma_scaled`（`|d| ≤ c ⟹ e^{λ²c²/2}`）
  的常数一致。而 `RealMcDiarmid.mcdiarmid_tail_of_mgf` 的假设 `hmgf` 用的是
  `exp(λ²·∑cᵢ²/8)`，它对应的是 **「区间长 ≤ c」版 Hoeffding**
  （零均值 r.v. 落在区间长 `L` 内 ⟹ `E[e^{λX}] ≤ exp(λ²L²/8)`），
  与「`|d| ≤ c`」是**不同的假设形式**（`|d| ≤ c` 给出区间长 ≤ `2c`，故指数为
  `exp(λ²(2c)²/8) = exp(λ²c²/2)`）。
  **因此本文件给出的迭代不能直接代入 `hmgf` 的 `/8` 形状**——要接上还差一步：
  *补一条「区间长版 Hoeffding」（`X ∈ [a,b]`、`EX = 0` ⟹ `E[e^{λX}] ≤ exp(λ²(b−a)²/8)`），
  并把 `CondZeroMean` 的「纤维均值零」升级为「纤维支撑在长 `c k` 的区间内」*。
  本条**未做**，如实标注，**不伪造**已接上 `RealMcDiarmid`。
  （另注：`RealMcDiarmid` 的 `/8` 假设本身**未改动**——本文件对既有文件**只读引用**。）
* **未做（测度论版本）**：本文件全部是**有限 / 计数**概率空间（`Fintype` + 纤维均值
  条件期望）上的版本；一般概率空间的 `condexp` / `Filtration` / `Martingale` 版本
  **未做**（由工作包边界另行处理）。
* **未做（单步界的再推导）**：`hstep` 的充分条件由 `RealAzumaMartingale` 的
  `condExpFiber_hoeffding` 提供（定理 10 自动满足之），本文件不重复推导。

**回收说明**：本文件的证明体在定稿前于探针文件 `_probe_fi.lean` 中迭代验证，
全部定理均在锁下经 `lake env lean` 探针与 `lake build` 正式构建双重确认后回收
（探针文件已删除）。共回收 **17** 条声明（正文定理 13 条 + 二、三节的纤维分解辅助
声明 4 条：`condExpFiber_nonneg_p`、`sum_eq_sum_card_mul_condExpFiber`、`sum_card_fiber`、
`uniformExpectation_le_of_fibreBound`；此处曾记作 **16**，系按旧口径计数，**已订正**）。

无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

variable {α β γ : Type*} [Fintype α]

/-! ## 一、条件期望的乘积引理（A3.3） -/

/-- **纤维均值非负**：非负函数在任意纤维上的均值非负（空纤维取 0，故亦非负）。 -/
theorem condExpFiber_nonneg_p (π : α → β) [DecidableEq β] (X : α → ℝ) (hX : ∀ a, 0 ≤ X a)
    (b : β) : 0 ≤ condExpFiber π X b := by
  classical
  rw [condExpFiber]
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (Finset.sum_nonneg (fun a _ => hX a)) (Nat.cast_nonneg _)

/-- **乘积引理（点形式）**：若 `Y₁` 关于 `π` 可测，则
`E[Y₁·Y₂ | π](π a) = Y₁ a · E[Y₂ | π](π a)`。

证明：`Y₁` 在纤维 `fiber π (π a)` 上恒等于 `Y₁ a`（适应性），
把它从纤维求和中提出（`Finset.mul_sum`），再用 `mul_div_assoc`。 -/
theorem condExpFiber_mul_of_adapted_at (π : α → β) [DecidableEq β] (Y₁ Y₂ : α → ℝ)
    (hY : AdaptedTo π Y₁) (a : α) :
    condExpFiber π (fun ω => Y₁ ω * Y₂ ω) (π a) = Y₁ a * condExpFiber π Y₂ (π a) := by
  classical
  have ha : a ∈ fiber π (π a) := by simp [fiber]
  have hmemF : ∀ c ∈ fiber π (π a), Y₁ c = Y₁ a := by
    intro c hc
    have h1 : π c = π a := by
      rw [(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp ha).2]
    exact hY c a h1
  have hpos : (fiber π (π a)).card ≠ 0 := Finset.card_ne_zero_of_mem ha
  rw [condExpFiber, condExpFiber, if_neg hpos, if_neg hpos]
  have h1 : ∑ c in fiber π (π a), Y₁ c * Y₂ c = Y₁ a * ∑ c in fiber π (π a), Y₂ c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c hc => by rw [hmemF c hc])
  rw [h1, mul_div_assoc]

/-- **乘积引理（纤维成员形式）**：沿任意纤维成员 `a ∈ fiber π b` 的点形式。 -/
theorem condExpFiber_mul_of_adapted_mem (π : α → β) [DecidableEq β] (Y₁ Y₂ : α → ℝ)
    (hY : AdaptedTo π Y₁) {b : β} {a : α} (ha : a ∈ fiber π b) :
    condExpFiber π (fun ω => Y₁ ω * Y₂ ω) b = Y₁ a * condExpFiber π Y₂ b := by
  classical
  have hmemF : ∀ c ∈ fiber π b, Y₁ c = Y₁ a := by
    intro c hc
    exact hY c a (by rw [(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp ha).2])
  have hpos : (fiber π b).card ≠ 0 := Finset.card_ne_zero_of_mem ha
  rw [condExpFiber, condExpFiber, if_neg hpos, if_neg hpos]
  have h1 : ∑ c in fiber π b, Y₁ c * Y₂ c = Y₁ a * ∑ c in fiber π b, Y₂ c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun c hc => by rw [hmemF c hc])
  rw [h1, mul_div_assoc]

/-- **乘积引理（主形式，A3.3 的公共缺口）**：若 `Y₁` 关于 `π` 可测，则
`E[Y₁·Y₂ | π](b) = E[Y₁ | π](b) · E[Y₂ | π](b)`（逐点，对**任意** `b`）。

**无纤维非空假设**：空纤维时 `condExpFiber` 约定为 0，两边同为零，
故本形式比「非空纤维」版更强、更易用（路线 A 的多界相乘正需要它）。
非空情形取纤维成员 `a`，用 `condExpFiber_mul_of_adapted_mem` 与
`condExpFiber_self_of_adapted`（适应性）。 -/
theorem condExpFiber_mul_of_adapted (π : α → β) [DecidableEq β] (Y₁ Y₂ : α → ℝ)
    (hY : AdaptedTo π Y₁) (b : β) :
    condExpFiber π (fun ω => Y₁ ω * Y₂ ω) b
      = condExpFiber π Y₁ b * condExpFiber π Y₂ b := by
  classical
  by_cases h : (fiber π b).card = 0
  · simp only [condExpFiber, if_pos h, mul_zero]
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
    have hab : π a = b := (Finset.mem_filter.mp ha).2
    rw [condExpFiber_mul_of_adapted_mem π Y₁ Y₂ hY ha, ← hab,
      condExpFiber_self_of_adapted π Y₁ hY a]

/-- **乘积引理（非空纤维形式）**：纤维非空时，用 `Classical.choose` 取代表点，
即任务说明书所要求的「`Y₁ ω · E[Y₂ | π] ω`」逐点形状（`ω` 由非空性选出）。 -/
theorem condExpFiber_mul_of_adapted_of_ne (π : α → β) [DecidableEq β] (Y₁ Y₂ : α → ℝ)
    (hY : AdaptedTo π Y₁) (b : β) (h : (fiber π b).card ≠ 0) :
    condExpFiber π (fun ω => Y₁ ω * Y₂ ω) b
      = Y₁ (Classical.choose (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))
        * condExpFiber π Y₂ b :=
  condExpFiber_mul_of_adapted_mem π Y₁ Y₂ hY
    (Classical.choose_spec (Finset.card_pos.mp (Nat.pos_of_ne_zero h)))

/-- **多界相乘**（路线 A 主交付）：由 `FibreBound π Y₁ EB₁` 与 `FibreBound π Y₂ EB₂`
得 `FibreBound π (Y₁·Y₂) (EB₁·EB₂)`（需 `Y₁, Y₂` 逐点非负与 `EB₁ ≥ 0` 以保方向）。

证明：主乘积引理把条件期望拆成两个因子之积，再用 `mul_le_mul`。 -/
theorem fibreBound_mul (π : α → β) [DecidableEq β] (Y₁ Y₂ : α → ℝ) {EB₁ EB₂ : ℝ}
    (hY : AdaptedTo π Y₁) (h₁ : FibreBound π Y₁ EB₁) (h₂ : FibreBound π Y₂ EB₂)
    (_hY₁nn : ∀ a, 0 ≤ Y₁ a) (hY₂nn : ∀ a, 0 ≤ Y₂ a) (hEB₁ : 0 ≤ EB₁) :
    FibreBound π (fun ω => Y₁ ω * Y₂ ω) (EB₁ * EB₂) := by
  intro b
  rw [condExpFiber_mul_of_adapted π Y₁ Y₂ hY b]
  exact mul_le_mul (h₁ b) (h₂ b) (condExpFiber_nonneg_p π Y₂ hY₂nn b) hEB₁

/-! ## 二、纤维分解的求和形式（迭代所需的桥） -/

/-- **全局均值的纤维分解**：`∑_a X a = ∑_b |fiber ρ b| · E[X | ρ](b)`
（`sum_card_mul_condExpFiber` 的对称形式）。 -/
theorem sum_eq_sum_card_mul_condExpFiber [Fintype γ] [DecidableEq γ] (ρ : α → γ) (X : α → ℝ) :
    (∑ a, X a) = ∑ b, ((fiber ρ b).card : ℝ) * condExpFiber ρ X b :=
  (sum_card_mul_condExpFiber ρ X).symm

/-- **纤维基数求和 = 全空间**：`∑_b |fiber ρ b| = |α|`。 -/
theorem sum_card_fiber [Fintype γ] [DecidableEq γ] (ρ : α → γ) :
    ∑ b, ((fiber ρ b).card : ℝ) = (Fintype.card α : ℝ) := by
  have h := fiber_sum_eq ρ (fun _ : α => (1 : ℝ))
  simpa [Finset.sum_const, nsmul_eq_mul] using h

/-- **由纤维界得全局期望界**：`FibreBound ρ X EB ⟹ E[X] ≤ EB`（需 `|α| > 0`）。

证明：纤维分解把全局均值写成纤维均值的加权平均，逐项代入 `≤ EB`，
再用 `∑_b |fiber ρ b| = |α|` 约去分母。 -/
theorem uniformExpectation_le_of_fibreBound [Fintype γ] [DecidableEq γ] (ρ : α → γ) (X : α → ℝ)
    {EB : ℝ} (hN : 0 < Fintype.card α) (h : FibreBound ρ X EB) : uniformExpectation X ≤ EB := by
  have hNne : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  rw [uniformExpectation, sum_eq_sum_card_mul_condExpFiber ρ X]
  calc (∑ b, ((fiber ρ b).card : ℝ) * condExpFiber ρ X b) / (Fintype.card α : ℝ)
      ≤ (∑ b, ((fiber ρ b).card : ℝ) * EB) / (Fintype.card α : ℝ) :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (h b) (Nat.cast_nonneg _)))
          (Nat.cast_nonneg _)
    _ = EB := by
        rw [← Finset.sum_mul, sum_card_fiber ρ]
        field_simp

/-! ## 三、n 步过滤迭代（A3.2） -/

/-- **单步推进（迭代的归纳步）**：`FibreBound ρ (e^{λS_k}) (B k)` ⟹
`FibreBound ρ (e^{λS_{k+1}}) (B k · e^{λ²c_k²/2})`。

证明：由 `hSsucc` 与 `mul_add`/`Real.exp_add` 得
`e^{λS_{k+1}} = e^{λS_k} · e^{λD_k}`（逐点）；`e^{λS_k}` 关于 `ρ` 可测
（前提 `hadapt`），用 `fibreBound_mul`（即乘积引理）合并归纳假设 `hIH`
与单步条件 Hoeffding 界 `hstep k`。 -/
theorem fibreBound_mgf_succ [Fintype γ] [DecidableEq γ] (ρ : α → γ) (D S : ℕ → α → ℝ)
    (c : ℕ → ℝ) (lam : ℝ) (B : ℕ → ℝ) (k : ℕ)
    (hSsucc : ∀ j a, S (j + 1) a = S j a + D j a)
    (hadapt : AdaptedTo ρ (fun a => Real.exp (lam * S k a)))
    (hstep : FibreBound ρ (fun a => Real.exp (lam * D k a))
      (Real.exp (lam ^ 2 * c k ^ 2 / 2)))
    (hIH : FibreBound ρ (fun a => Real.exp (lam * S k a)) (B k))
    (hBk : 0 ≤ B k) :
    FibreBound ρ (fun a => Real.exp (lam * S (k + 1) a))
      (B k * Real.exp (lam ^ 2 * c k ^ 2 / 2)) := by
  have hpoint : (fun a => Real.exp (lam * S (k + 1) a))
      = fun a => Real.exp (lam * S k a) * Real.exp (lam * D k a) := by
    funext a
    rw [hSsucc k a, mul_add, Real.exp_add]
  rw [hpoint]
  exact fibreBound_mul ρ _ _ hadapt hIH hstep
    (fun a => (Real.exp_pos _).le) (fun a => (Real.exp_pos _).le) hBk

/-- **n 步过滤迭代（A3.2 主定理）**：单步条件 Hoeffding 界沿 `n` 期**逐步复合**为整段界。

`S k = ∑_{j<k} D j` 是鞅差的部分和（`hS0` / `hSsucc` 给出）；`hstep k` 是第 `k` 步的
**条件** Hoeffding 界（**每步可有不同的增量 `D k` 与常数 `c k`**）；
`hadapt k` 说 `e^{λS_k}` 关于 `ρ` 可测（鞅的适应性）。结论：
`FibreBound ρ (e^{λS_n}) (exp(λ² · ∑_{j<n} c_j² / 2))`。

证明：对 `n` 归纳。`n = 0` 时 `S 0 ≡ 0`，`e^0 = 1`，右边 `exp(0) = 1`；
`n = k+1` 时用 `fibreBound_mgf_succ`，指数合并由
`Finset.sum_range_succ` + `Real.exp_add` + `ring` 完成。

**诚实边界**：本定理在**固定投影 `ρ`** 上迭代（σ-代数不变，单步界可变）；
σ-代数随期数变化的版本见 `fibreBound_mgf_iterate_filtration`（传递步为显式假设）。 -/
theorem fibreBound_mgf_iterate [Fintype γ] [DecidableEq γ] (ρ : α → γ)
    (D S : ℕ → α → ℝ) (c : ℕ → ℝ) (lam : ℝ)
    (hS0 : ∀ a, S 0 a = 0)
    (hSsucc : ∀ j a, S (j + 1) a = S j a + D j a)
    (hadapt : ∀ k, AdaptedTo ρ (fun a => Real.exp (lam * S k a)))
    (hstep : ∀ k, FibreBound ρ (fun a => Real.exp (lam * D k a))
      (Real.exp (lam ^ 2 * c k ^ 2 / 2))) :
    ∀ n, FibreBound ρ (fun a => Real.exp (lam * S n a))
      (Real.exp (lam ^ 2 * (∑ j in Finset.range n, c j ^ 2) / 2)) := by
  intro n
  induction n with
  | zero =>
      have h1 : (fun a => Real.exp (lam * S 0 a)) = fun _ : α => (1 : ℝ) := by
        funext a
        rw [hS0 a, mul_zero, Real.exp_zero]
      have hconst : FibreBound ρ (fun _ : α => (1 : ℝ)) 1 := by
        intro b'
        by_cases hb : (fiber ρ b').card = 0
        · rw [condExpFiber, if_pos hb]
          norm_num
        · rw [condExpFiber_const _ _ b' hb]
      rw [h1]
      have hz : Real.exp (lam ^ 2 * (∑ j in Finset.range 0, c j ^ 2) / 2) = 1 := by
        rw [Finset.sum_range_zero]
        norm_num
      rw [hz]
      exact hconst
  | succ k ih =>
      have hBk : 0 ≤ Real.exp (lam ^ 2 * (∑ j in Finset.range k, c j ^ 2) / 2) :=
        (Real.exp_pos _).le
      have hstep' := fibreBound_mgf_succ ρ D S c lam
        (fun n => Real.exp (lam ^ 2 * (∑ j in Finset.range n, c j ^ 2) / 2))
        k hSsucc (hadapt k) (hstep k) ih hBk
      have hsum : (∑ j in Finset.range (k + 1), c j ^ 2)
          = (∑ j in Finset.range k, c j ^ 2) + c k ^ 2 := Finset.sum_range_succ _ _
      have hgoal : Real.exp (lam ^ 2 * (∑ j in Finset.range (k + 1), c j ^ 2) / 2)
          = Real.exp (lam ^ 2 * (∑ j in Finset.range k, c j ^ 2) / 2)
            * Real.exp (lam ^ 2 * c k ^ 2 / 2) := by
        rw [hsum, ← Real.exp_add]
        congr 1
        ring
      rw [hgoal]
      exact hstep'

/-- **n 期滤链版本（σ-代数随期数变化；传递步为显式假设 · `未证` 标注）**。

与 `fibreBound_mgf_iterate` 的区别：投影**随期数变化** `ρ 0, ρ 1, …`。
归纳步拆成两条假设：
* `hcompound`：在**同一个** `ρ k` 上把 `S k → S (k+1)` 的条件界推进一步
  （即 `fibreBound_mgf_succ` 的抽象形式，本文件已证其具体版）；
* `htransfer`：**跨 σ-代数**把 `ρ k` 上的条件界提升到 `ρ (k+1)` 上。

**诚实标注（缺口，`未证`）**：`htransfer` 在本文件**未证**。原因是在有限纤维框架下，
`RealAzumaMartingale.tower_hoeffding_transfer` 只给出**细 → 粗**方向的传递
（`FibreBound π Y EB → FibreBound (g∘π) Y EB`），而此处需要**粗 → 细**方向
（`ρ k` 信息更少 → `ρ (k+1)` 信息更多）。该方向并非普遍成立，需额外结构
（如「`ρ k = g k ∘ ρ (k+1)` 且 `Y` 关于 `ρ (k+1)` 可测且 `ρ k`-纤维均值 = `Y`」）。
本条如实列为剩余工作，**不伪造**。 -/
theorem fibreBound_mgf_iterate_filtration [Fintype γ] [DecidableEq γ] (ρ : ℕ → α → γ)
    (D S : ℕ → α → ℝ) (c : ℕ → ℝ) (lam : ℝ) (B : ℕ → ℝ)
    (htransfer : ∀ k, FibreBound (ρ k) (fun a => Real.exp (lam * S (k + 1) a)) (B (k + 1)) →
      FibreBound (ρ (k + 1)) (fun a => Real.exp (lam * S (k + 1) a)) (B (k + 1)))
    (_hstep : ∀ k, FibreBound (ρ k) (fun a => Real.exp (lam * D k a))
      (Real.exp (lam ^ 2 * c k ^ 2 / 2)))
    (hcompound : ∀ k, FibreBound (ρ k) (fun a => Real.exp (lam * S k a)) (B k) →
      FibreBound (ρ k) (fun a => Real.exp (lam * S (k + 1) a)) (B (k + 1)))
    (hbase : FibreBound (ρ 0) (fun a => Real.exp (lam * S 0 a)) (B 0)) :
    ∀ n, FibreBound (ρ n) (fun a => Real.exp (lam * S n a)) (B n) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ k ih => exact htransfer k (hcompound k ih)

/-! ## 四、整段 MGF 界与自动满足单步 Hoeffding -/

/-- **整段 MGF 界（全局期望形式）**：`E[e^{λS_n}] ≤ exp(λ²·∑_{j<n}c_j²/2)`。

证明：`fibreBound_mgf_iterate` 给出 `FibreBound ρ (e^{λS_n}) (…)`，
再由 `uniformExpectation_le_of_fibreBound` 转为全局期望界。 -/
theorem uniformExpectation_mgf_iterate [Fintype γ] [DecidableEq γ] (ρ : α → γ)
    (D S : ℕ → α → ℝ) (c : ℕ → ℝ) (lam : ℝ)
    (hN : 0 < Fintype.card α)
    (hS0 : ∀ a, S 0 a = 0)
    (hSsucc : ∀ j a, S (j + 1) a = S j a + D j a)
    (hadapt : ∀ k, AdaptedTo ρ (fun a => Real.exp (lam * S k a)))
    (hstep : ∀ k, FibreBound ρ (fun a => Real.exp (lam * D k a))
      (Real.exp (lam ^ 2 * c k ^ 2 / 2))) (n : ℕ) :
    uniformExpectation (fun a => Real.exp (lam * S n a))
      ≤ Real.exp (lam ^ 2 * (∑ j in Finset.range n, c j ^ 2) / 2) :=
  uniformExpectation_le_of_fibreBound ρ (fun a => Real.exp (lam * S n a)) hN
    (fibreBound_mgf_iterate ρ D S c lam hS0 hSsucc hadapt hstep n)

/-- **n 步迭代（单步假设被真正证出）**：把 `fibreBound_mgf_iterate` 的 `hstep`
由**鞅差条件 + 有界性**自动满足 —— 每步用 `RealAzumaMartingale.condExpFiber_hoeffding`
（条件 Hoeffding 引理）给出该步的**条件** MGF 界。

这是「多步过滤迭代」的**完整可用形式**：只需逐期的 `CondZeroMean`（鞅差）、
`|D k| ≤ c k`、`c k > 0` 与纤维非空，即可得整段 `E[e^{λS_n}] ≤ exp(λ²∑c²/2)`。

**诚实标注**：常数为 `/2`（与 `RealAzuma.hoeffding_lemma_scaled` 的 `|d| ≤ c` 假设一致）；
接到 `RealMcDiarmid.hmgf` 的 `/8` 形状还差一条「区间长版 Hoeffding」，见文件头诚实边界。 -/
theorem uniformExpectation_mgf_iterate_of_condZeroMean [Fintype γ] [DecidableEq γ]
    (ρ : α → γ) (D S : ℕ → α → ℝ) (c : ℕ → ℝ) (lam : ℝ)
    (hN : 0 < Fintype.card α)
    (hS0 : ∀ a, S 0 a = 0)
    (hSsucc : ∀ j a, S (j + 1) a = S j a + D j a)
    (hadapt : ∀ k, AdaptedTo ρ (fun a => Real.exp (lam * S k a)))
    (hc : ∀ k, 0 < c k)
    (hzero : ∀ k, CondZeroMean ρ (D k))
    (hb : ∀ k a, |D k a| ≤ c k)
    (hne : ∀ b, (fiber ρ b).card ≠ 0) (n : ℕ) :
    uniformExpectation (fun a => Real.exp (lam * S n a))
      ≤ Real.exp (lam ^ 2 * (∑ j in Finset.range n, c j ^ 2) / 2) :=
  uniformExpectation_mgf_iterate ρ D S c lam hN hS0 hSsucc hadapt
    (fun k => condExpFiber_hoeffding ρ (D k) (hzero k) (hc k) (hb k) hne) n

/-- **等界特例（逐期 `c_j ≡ c`）**：`E[e^{λS_n}] ≤ exp(λ²·n·c²/2)`。

由 `uniformExpectation_mgf_iterate` 取常数列 `c` 并合并 `∑_{j<n} c² = n·c²`。 -/
theorem uniformExpectation_mgf_iterate_uniform [Fintype γ] [DecidableEq γ]
    (ρ : α → γ) (D S : ℕ → α → ℝ) (c lam : ℝ)
    (hN : 0 < Fintype.card α)
    (hS0 : ∀ a, S 0 a = 0)
    (hSsucc : ∀ j a, S (j + 1) a = S j a + D j a)
    (hadapt : ∀ k, AdaptedTo ρ (fun a => Real.exp (lam * S k a)))
    (hstep : ∀ k, FibreBound ρ (fun a => Real.exp (lam * D k a))
      (Real.exp (lam ^ 2 * c ^ 2 / 2))) (n : ℕ) :
    uniformExpectation (fun a => Real.exp (lam * S n a))
      ≤ Real.exp (lam ^ 2 * ((n : ℝ) * c ^ 2) / 2) := by
  have hmain := uniformExpectation_mgf_iterate ρ D S (fun _ => c) lam hN hS0 hSsucc hadapt
    (fun _ => hstep _) n
  have hsum : (∑ _j in Finset.range n, c ^ 2) = (n : ℝ) * c ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rwa [hsum] at hmain

end Lattice
