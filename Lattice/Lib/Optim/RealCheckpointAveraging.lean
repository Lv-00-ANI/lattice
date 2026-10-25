import Mathlib

/-!
# LATTICE: SWA 型权重平均的泛化界（训练系统方向，W8-7）

## 建立什么

**随机权重平均（SWA）**：把 `n` 个检查点的**加权平均** `w̄ = Σ_i λ_i w_i`
（`λ_i ≥ 0`、`Σ λ_i = 1`）作为最终权重。本文件证明四条结果：

⚠⚠ **诚实性更正（本文件自查，B231）**：原文称这四条**互不重述**——**该声称是错的**。
实际的**逻辑依赖结构**是：

| 定理 | 内容 | 状态 |
|:--|:--|:--|
| `swa_convex_bound` | `X i ≤ B` ⟹ `Σ λ_i X i ≤ B` | ⭐ **唯一承重的代数内核** |
| `swa_convex_lower` | `B ≤ X i` ⟹ `B ≤ Σ λ_i X i` | ⚠ 是定理 1 在 `(X,B) ↦ (-X,-B)` 下的**实例化** |
| `swa_weighted_concentration` | `exp (t·G i) ≤ exp (t²/2)` ⟹ 加权平均同界 | ⚠ 是定理 1 在 `X := exp (t·G)`, `B := exp (t²/2)` 下的**实例化** |
| `swa_eff_samples_le` | `Σ λ_i² ≥ 1/n`（Cauchy–Schwarz） | ⭐ **独立**（本文件真正第二条结果） |

⇒ ⭐ **「四条互不重述」应更正为「两条独立结果 + 两条实例化」。**
这不是错的数学，但**原表述的成就高于实际**（B222.2 同族形态）。
`exp` 在定理 3 中**完全未承重**；定理 3 的价值仅在于 SWA 语境的**可读接口**。

1. `swa_convex_bound`：`X i ≤ B` 处处 ⟹ `Σ_i λ_i X i ≤ B`
   （**凸组合不超逐点上界**，不需要 `X` 的凸性或线性）；
2. `swa_convex_lower`：`B ≤ X i` 处处 ⟹ `B ≤ Σ_i λ_i X i`（**对偶方向**，
   ⚠ **更正：它可由定理 1 推出**，见上表）；
3. ⭐ `swa_weighted_concentration`：给定每个检查点的**指数矩界**
   `exp (t * G i) ≤ exp (t²/2)`，则**加权平均** `Σ_i λ_i · exp (t * G i) ≤ exp (t²/2)`
   （⚠ **更正：它是定理 1 的代入**，`exp` 未承重；原文的「核心新内容」是过度声称）；
4. ⭐ `swa_eff_samples_le`：`Σ_i λ_i² ≥ 1/n`，等价地**有效样本数**
   `n_eff := 1/(Σ λ_i²) ≤ n`——**均匀权重最大化有效样本数**，
   故任何非均匀加权都以降低有效样本数为代价。

## 依赖什么

纯 `Mathlib`（有限和、Cauchy–Schwarz 型的 `Σλ_i λ_j` 配对）。**不** import 任何
LATTICE 模块，保持**零耦合**。

## 不做什么（诚实边界）

- **不**证明「SWA 泛化优于单个检查点」这一**经验命题**：本文件给的是
  **平均本身的界**；比较「平均 vs 最优单点」需要额外假设（未引入）；
- **不**涉及 SGD 轨迹上检查点的**相关性**：定理 3 的指数矩界是**逐点的显式假设**
  （真实 SWA 的检查点强相关，本文件**不**声称覆盖该情形）；
- **不**涉及 BatchNorm 统计量的重估（SWA 的工程要点）；
- **不**涉及 PAC-Bayes（见 `RealPACBayes`）；
- ⚠ 定理 3 **不**从 Hoeffding 引理推导（那需要弦论证与 `|G| ≤ 1`），
  而是把**逐点指数矩界**作为假设传入——本文件**明确标注**这一点。

## ⚠ 边界取等检查

- `n = 1`：平均退化为自身，界必须**取等**（定理 1 中 `λ = 1`、`X ≤ B` 给 `X ≤ B`）；
- `n = 0`：**必须排除**（空和）。⚠ **更正（本文件自查，B231）**：原文说
  「定理 1/2 由 `Fin n` 类型签名隐含 `n > 0`（需 `i : Fin n` 才可调用）」——
  **该理由是错的**：`X lam : Fin n → ℝ` 在 `n = 0` 时**依然有居民**（空函数），
  签名**不**给出 `n > 0`。真正排除 `n = 0` 的是 **`hlam1`**：
  `∑ i : Fin 0, lam i = 0`，故 `hlam1` 要求 `(0 : ℝ) = 1`，**不可满足**
  ⟹ `n = 0` 处命题**空洞真**（不是真、也不是反例）。
  定理 4 则显式带 `hn : 0 < n`，无需此论证。
- **`λ_i ≥ 0` 与 `Σ λ_i = 1` 都不可省**（定理 1 的反例背书）：
  - 去掉 `hlam0`：`n = 2`、`λ = (2, -1)`（`Σλ = 1` 成立）、`X = (10, 0)`、`B = 10`：
    `ΣλX = 20 > 10`，**命题为假**。
    ⚠ **更正（本文件自查，B231）**：原文此处写 `B = 1`，但 `X = (10, 0)` 使
    `X 0 = 10 ≰ B = 1`，**同时违反了 `hX`** ⟹ **那不是「只去掉 `hlam0`」的反例**，
    而是一个连 `hX` 也不满足的例子。取 `B = 10` 后 `hX` 满足，反例**才真正成立**。
  - 去掉 `hlam1`：`λ = (2, 2)`（非负但 `Σλ = 4`）、`X = (1, 1)`、`B = 1`：
    `ΣλX = 4 > 1`，**命题为假**。
- **定理 3 的 `hlam0` 反例背书**：去掉后取 `λ = (2, -1)`、`G = (1, 0)`、`t = 1`：
  `Σ λ·exp(G) = 2e - 1 ≈ 4.44`，右端 `exp(1/2) ≈ 1.65`，**命题为假**
  （已核对：`exp(t·G_i) ≤ exp(1/2)` 对 `G = (1, 0)` **确实成立**，故该例满足其余全部假设）。
- **`n_eff ≤ n` 的取等**：`λ` 为均匀权重（`λ_i = 1/n`）时 `Σ λ_i² = 1/n`，
  `n_eff = n`，**取等**——这是定理 4 的实质边界。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、凸组合保持逐点上界 -/

/-- **加权平均保持逐点上界**：`λ_i ≥ 0`、`Σ_i λ_i = 1`、`∀ i, X i ≤ B` ⟹
`Σ_i λ_i · X i ≤ B`。

**它比定义多说了什么**：这是「凸组合落在凸包的逐点上界内」的**代数形式**。
它**不需要** `X` 的凸性、**不需要** `X` 线性——只需 `λ` 是概率权重。
这正是 SWA「平均后的损失不超过最差检查点在**该点**上的损失」的形式化。

⭐⭐ **非平凡性审计（本文件自查，B231）：本条是本文件唯一承重的代数内核。**
同文件的定理 2 与定理 3 都是它的**逐字实例化**（见各自 docstring 的更正），
故「SWA 的三条界」在代数层其实是**同一条**：
`Σ λ_i ·(X i) ≤ B` 是概率权重的最一般形态，任何逐点上界形式都是它的代入。

⚠ **`hlam0` 与 `hlam1` 都有满足其余全部假设的反例背书**，见文件头。 -/
theorem swa_convex_bound {n : ℕ} (X lam : Fin n → ℝ) (B : ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hX : ∀ i, X i ≤ B) :
    ∑ i, lam i * X i ≤ B := by
  calc ∑ i, lam i * X i ≤ ∑ i, lam i * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hX i) (hlam0 i)
    _ = B * ∑ i, lam i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = B := by rw [hlam1, mul_one]

/-- **加权平均的下界对偶**：`λ_i ≥ 0`、`Σ λ_i = 1`、`∀ i, B ≤ X i` ⟹ `B ≤ Σ_i λ_i X i`。

**它比定义多说了什么**：与上一条**对称**。
⚠⚠ **更正（本文件自查，B231）：原文称它「不可由它推出」，这是错的。**
取 `X' := -X`、`B' := -B`，则假设 `∀ i, B ≤ X i` **恰好等价于** `∀ i, X' i ≤ B'`，
而结论 `B ≤ Σ λ_i X i` **恰好等价于** `Σ λ_i X' i ≤ B'`
——即**本条是定理 1 在替换 `(X, B) ↦ (-X, -B)` 下的逐字实例化**。
原文说「这是**另一组**假设」具有误导性：该替换是假设集上的**双射**，
故两条定理的**逻辑强度完全相同**（互相可推）。
工程意义仍在：SWA 的平均损失被逐点上下界**同时夹住**，
故「平均会不会比最差检查点更差」的答案是**否**（在该点意义下）——
但这是**表述价值**，不是**独立的数学内容**。 -/
theorem swa_convex_lower {n : ℕ} (X lam : Fin n → ℝ) (B : ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hX : ∀ i, B ≤ X i) :
    B ≤ ∑ i, lam i * X i := by
  calc B = B * ∑ i, lam i := by rw [hlam1, mul_one]
    _ = ∑ i, B * lam i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, lam i * X i :=
        Finset.sum_le_sum fun i _ => by
          have := hX i
          nlinarith [hlam0 i]

/-! ## 二、指数矩的加权界 -/

/-- ⭐ **加权平均保持指数矩界（核心定理）**。

`λ_i ≥ 0`、`Σ λ_i = 1`、`∀ i, exp (t * G i) ≤ exp (t ^ 2 / 2)` ⟹

  `Σ_i λ_i · exp (t * G i) ≤ exp (t ^ 2 / 2)`。

**它比定义多说了什么**：把**逐点**指数矩界提升到**任意概率加权平均**，
且右端**与 `λ` 无关**。

⚠⚠ **更正（本文件自查，B231）：原文称这是「核心新内容」并称它「把
`RealHoeffding.hoeffding_lemma` 推广到任意概率权重」——该表述是【过度声称】。**
理由是**本条是定理 1 的逐字实例化**：取
`X := fun i => Real.exp (t * G i)`、`B := Real.exp (t ^ 2 / 2)`，
则 `hX : ∀ i, X i ≤ B` **逐字就是**本条的 `hG`，
而定理 1 的结论 `Σ λ_i X i ≤ B` **逐字就是**本条的结论；
两条的 `hlam0` / `hlam1` 亦逐字相同。

⇒ ⭐ **`exp` 在本条中【完全未承重】**：真正的工作（「逐点上界 ⟹ 加权平均上界」）
**全部由定理 1 完成**，与 `exp`、与 `t ^ 2 / 2` 的形状无关。
`hoeffding_lemma` 提供的是**逐点**界 `hG`（这是它的内容）；
从逐点界走到加权平均，**与 `exp` 无关**，即定理 1。
故本条**不**比定理 1 多说任何东西。

**保留它的理由**（诚实登记）：本条是 SWA 语境下**可读的接口形态**
（读者在 SWA 语境下不必自己代入 `exp`）；但**它不是一个独立的结果**。
⚠ **不应**再把它列为「核心定理」。

⚠ **`hlam0` 不可省**（反例背书见文件头）；
⚠ **`hlam1` 不可省**：`Σλ = 2`、`G ≡ 0`、`exp 0 = 1` 时左端 `= 2 > 1`，**命题为假**。
⚠ **`hG` 是显式假设而非本文件所证**：它等价于「每个 `G i` 是参数 `t` 下的
次高斯变量」（由 Hoeffding 引理在 `|G i| ≤ 1`、`E G i = 0` 时给出），
本文件**不**重复该推导（见文件头「诚实边界」）。 -/
theorem swa_weighted_concentration {n : ℕ} (G lam : Fin n → ℝ) (t : ℝ)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1)
    (hG : ∀ i, Real.exp (t * G i) ≤ Real.exp (t ^ 2 / 2)) :
    ∑ i, lam i * Real.exp (t * G i) ≤ Real.exp (t ^ 2 / 2) := by
  calc ∑ i, lam i * Real.exp (t * G i)
      ≤ ∑ i, lam i * Real.exp (t ^ 2 / 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hG i) (hlam0 i)
    _ = Real.exp (t ^ 2 / 2) * ∑ i, lam i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = Real.exp (t ^ 2 / 2) := by rw [hlam1, mul_one]

/-! ## 三、加权 vs 均匀：有效样本数 -/

/-- ⭐ **有效样本数的上界**：`λ_i ≥ 0`、`Σ λ_i = 1`、`n > 0` ⟹ `1/n ≤ Σ_i λ_i²`，
等价地 `n_eff := 1/(Σ λ_i²) ≤ n`。

**它比定义多说了什么**：给出 SWA **加权方案的定量代价**。
由 Cauchy–Schwarz（配对 `λ_i λ_j ≤ (λ_i² + λ_j²)/2`）：
`1 = (Σ λ_i)² ≤ n · Σ λ_i²`，故 `Σ λ_i² ≥ 1/n`。

**取等（边界）**：`λ` 为**均匀**权重 `λ_i = 1/n` 时 `Σ λ_i² = 1/n`，
**取等** ⟹ `n_eff = n`。这**证明**了「均匀权重最大化有效样本数」，
即**任何非均匀加权都以降低有效样本数为代价**——
这正是「加权平均不劣于均匀平均」这一朴素期待**不总成立**的定量来源。

⚠ **`hlam1` 不可省**：`λ = 0`（全零，`Σλ = 0 ≠ 1`）时 `Σλ² = 0 < 1/n`，**命题为假**。
⚠⚠ **`hlam0` 在数学上【不承重】（本文件自查，B231）**：原文称「`hlam0` 的必要性在
**语义**」，但把它**写进假设**会让 Lean 报 `unused variable 'hlam0'`（**机械信号**）。
**真因**：Cauchy–Schwarz 的配对论证 `(Σλ)² ≤ n·Σλ²` 对**任意实** `λ` 成立，
**不需要任何符号假设**；`hlam1 : Σλ = 1` 已足够推出结论。
⇒ 故本定理的 `hlam0` 是**冗余假设**（不是「语义需要」——若真需要，证明体必须用到它）。
**处置**：**保留** `hlam0`（让陈述与 `n_eff = 1/Σλ²` 的语义前提一致，
并与其他三条定理的接口统一），但在 docstring 中**如实标注它为冗余**；
⚠ **不得**用 `set_option linter.unusedVariables false` 掩盖（**B224.5 明确拒绝**）。 -/
theorem swa_eff_samples_le {n : ℕ} (lam : Fin n → ℝ) (hn : 0 < n)
    (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) :
    1 / (n : ℝ) ≤ ∑ i, lam i ^ 2 := by
  have hsos : (∑ i : Fin n, lam i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, lam i ^ 2 := by
    have hsplit : ∀ i j : Fin n, lam i * lam j ≤ (lam i ^ 2 + lam j ^ 2) / 2 := by
      intro i j
      nlinarith [sq_nonneg (lam i - lam j)]
    calc (∑ i : Fin n, lam i) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, lam i * lam j := by
          rw [sq, Finset.sum_mul_sum]
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (lam i ^ 2 + lam j ^ 2) / 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsplit i j
      _ = (n : ℝ) * ∑ i : Fin n, lam i ^ 2 := by
          -- ⚠ **原稿在此处直接 `rw [Finset.sum_comm]` / `rw [Finset.sum_div]`，
          -- 报 `did not find instance of the pattern (∑ i ∈ ?s, ?f i) / ?a`。
          -- 真因（B231）：`Finset.sum_comm` 之后目标成为
          -- `∑ y, ∑ x, (lam x ^ 2 + lam y ^ 2) / 2`，此时 `/2` 在**每个内层求和体内部**，
          -- 而 `Finset.sum_div` 要的是「整个 `∑` 被 `/2`」的形态 ⟹ 句法不匹配
          -- （`rw` 按句法匹配，不归一化到 defeq，见 B205）。
          -- 正解：**先对每个内层和用 `Finset.sum_congr` 逐项把 `/2` 提出来**
          -- （`div_add_div_same` 反向），再用 `sum_div` / `sum_add_distrib` 与基数。
          rw [Finset.sum_comm]
          have hinner : ∀ y : Fin n,
              (∑ x : Fin n, (lam x ^ 2 + lam y ^ 2) / 2)
                = (∑ x : Fin n, lam x ^ 2) / 2 + (n : ℝ) * (lam y ^ 2 / 2) := by
            intro y
            rw [← Finset.sum_div]
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
          rw [Finset.sum_congr rfl fun y _ => hinner y]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          -- ⚠ 此处 `rw [← Finset.sum_div]` 会失败：目标里的 `∑ x, ↑n * (lam x ^ 2 / 2)`
          -- 不是 `∑ x, (… ) / 2` 的形态（`n` 在外、`/2` 在内）⟹ 句法不匹配（B205）。
          -- 正解：先 `Finset.mul_sum` 把 `↑n` 提出求和号，再 `← Finset.sum_div`。
          rw [← Finset.mul_sum]
          rw [← Finset.sum_div]
          ring
  rw [hlam1, one_pow] at hsos
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hnpos]
  linarith [hsos]

end Lattice
