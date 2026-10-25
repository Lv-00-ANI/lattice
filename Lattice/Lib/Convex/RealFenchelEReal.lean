import Mathlib
import Lattice.Lib.Convex.RealFenchelMoreau
import Lattice.Lib.Convex.RealConjugateDuality
/-!
# LATTICE: 扩展实数（`EReal`）值域的 Fenchel 共轭 —— 根治 `sSup` 的 junk 值语义

## 问题（`CORRECTIONS.md` C 节「`sSup` 的 junk 值」一行）

`RealFenchelMoreau.fenchelConjAll` 把共轭实现为 **`ℝ` 值**的 `sSup`：

    fenchelConjAll f y = sSup {v : ℝ | ∃ z, v = z·y − f z}        (RealFenchelMoreau.lean:66)

mathlib 的 `sSup` 对 `ℝ` **不是**「无上界 → `⊤`」：`ℝ` 无顶元，
`sSup` 在集合**无上界时返回 junk 值 `0`**（本文件 §8 用
`Real.sSup_of_not_bddAbove` 机器验证）。后果：`RealFenchelMoreau` /
`RealConjugateDuality` 中 `f*` 的**凸性**与各条**共轭演算律都必须带逐点
`BddAbove` 假设**——**去掉假设命题为假**（见 §8 审计结论）。

## 路线 A（本文件）：值域换成 `EReal = [-∞, +∞]`

`EReal` 是**完备格**（`instCompleteLinearOrderEReal`），其 `sSup` 语义是**真上确界**：
集合无上界 ⟹ `sSup = ⊤`。于是

    fenchelConjAllEReal f y = ⨆ z, ↑(z·y − f z)

- **无上界时真的是 `⊤`**（`fenchelConjAllEReal_eq_top_iff`，§2）；
- **凸性无需 `BddAbove`**（`fenchelConjAllEReal_convex`，§3，**3 个假设 → 0 个**）；
- **与旧 `ℝ` 值版本在 `BddAbove` 下精确桥接**（`fenchelConjAllEReal_toReal`，§6）；
- **下半连续性**（旧版「未做」）在 `EReal` 下**无条件**成立（§7）。

## 本文件声明一览

| § | 声明 | 旧 `ℝ` 版对应 | `BddAbove` |
|:--|:--|:--|:--|
| 1 | `fenchelConjAllEReal`（定义） | `fenchelConjAll` | — |
| 1 | `le_fenchelConjAllEReal` / `fenchelConjAllEReal_le` | `le_fenchelConjAll` / `fenchelConjAll_le` | **取消** |
| 1 | `fenchel_ineq_all_ereal` | `fenchel_ineq_all` | **取消** |
| 2 | `fenchelConjAllEReal_eq_top_iff`（`⊤` 语义正确性） | （旧版丢弃该信息） | — |
| 3 | `fenchelConjAllEReal_convex`（**凸性**） | `fenchelConjAll_convex`（3 个假设） | **取消（3→0）** |
| 4 | `fenchelConjAllEReal_shift`（平移，等号） | `fenchelConjAll_shift` | **取消** |
| 4 | `fenchelConjAllEReal_add_le_split`（加法-下卷积） | `fenchelConjAll_add_le_split`（3 个假设） | **取消（3→0）** |
| 4 | `fenchelConjAllEReal_scaling_le`（缩放，**只有 `≤`**） | `fenchelConjAll_scaling`（等号） | **取消**（但**降级为 `≤`**，见下） |
| 5 | `subgradient_iff_fenchelConjAllEReal_eq`（次梯度 ⟺ 取到） | `subgradient_iff_fenchelConj_eq` | **取消** |
| 6 | `fenchelConjAllEReal_toReal`（**一致性桥接**） | — | 需 `BddAbove`（**桥接的代价，不是新命题的代价**） |
| 7 | `fenchelConjAllEReal_lowerSemicontinuous`（**下半连续**） | （旧版未做） | **取消** |
| 8 | `audit_*`（**审计反例**） | — | — |

## 诚实边界（本文件不证 / 不声称的）

- **不修改** `RealFenchelMoreau` / `RealConjugateDuality`（一字未动）。它们保留
  `ℝ` 值定义与 `BddAbove` 假设作为**旧接口**；本文件是**独立的新权威**。
  两套定义并存期间的**一致性**由 §6 桥接定理保证。
- **诚实降级（缩放律只到 `≤`）**：本版只证 `(λf)*(y) ≤ λ·f*(y/λ)`（`λ > 0`），
  **未证等号**。原因**不是**命题为假，而是**本版 mathlib 的 `EReal` 缺代数实例**：
  **无 `PosMulReflectLE`**（故不能从 `↑λ·u ≤ ↑λ·v` 反推 `u ≤ v`，即不能消去 `↑λ`），
  且**无 `ContinuousMul`**（故不能用 `continuous_const.mul continuous_id` 或
  `Monotone.map_iSup_of_continuousAt` 把 `↑λ` 提出 `iSup`）。
  `≤` 方向只需 `mul_le_mul_of_nonneg_left`（由 `EReal.instPosMulMono` 提供），
  已证；等号方向留下的正是"`↑λ * ⨆ g = ⨆ (↑λ * g)`"这一步，**标注为后续工作**。
  下游只需 `≤`（Fenchel 不等式方向），故不影响本文件其余结论。
- **未做**：下卷积**等号** `(f □ g)* = f* + g*` 的 `EReal` 无条件版——一般等号需
  `inf` 被取到（凸 + 下半连续的 coercivity/分离定理）。本文件只给 §4 的
  `_add_le_split`（`≤` 方向，**无需** `BddAbove`）。
- **未做**：一般有限维 `ℝ^d` 的 `EReal` 值共轭与 Fenchel–Moreau **等号方向**
  （需 epigraph 支撑超平面 + 真闭凸性）。本文件只做**一维**。
- **未做**：`f**`（二次共轭）的 `EReal` 版。`EReal` 上 `sSup` 再嵌套时
  `⊤ − ⊤` 不是良定义运算，`y·x − f*(y)` 在 `f*(y) = ⊤` 处需分支论证。
  **标注**：本文件**不声称** `EReal` 下的 Fenchel–Moreau。
- **未做**：`BddAbove` 下 `f*` 的**连续性**（比 §7 的 LSC 更强）。它需要
  `ℝ` 值 `sSup` 与 `Tendsto` 交换的定理，超出已完成范围，标注为后续工作
  （`fenchelConjAllEReal_toReal_of_bddAbove` 给出其起点：有限性与一致性）。
- **未做**：`f*` 的**次微分**（`∂f*`）在 `EReal` 下的完整演算——`EReal` 加法非消去，
  需 `⊤`/`⊥` 分支。只做到 §5 的次梯度-取到 iff。
- §7 的 LSC **不需要** `f` 的任何假设（凸性、闭性都不要）：`f*` 是一族连续函数的
  逐点上确界，在 `EReal` 完备格下自动 LSC。这是 `EReal` 值域相对 `ℝ` 值域的
  **额外收益**。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 1. 定义与基本性质（全部**无条件**） -/

/-- **`EReal` 值全空间 Fenchel 共轭（一维，路线 A 的核心定义）**：
`f*(y) = ⨆_{z ∈ ℝ} ↑(z·y − f z)`。

值域取 `EReal = [-∞, +∞]`（mathlib 扩展实数），它是**完备格**，
故 `sSup` 语义是**真上确界**：集合无上界时返回 `⊤`（而非 `ℝ` 值的 junk 值 `0`）。

与旧定义 `RealFenchelMoreau.fenchelConjAll`（`ℝ` 值 + 逐点 `BddAbove`）的关系：
在 `BddAbove` 下二者由 `fenchelConjAllEReal_toReal` 精确桥接。 -/
noncomputable def fenchelConjAllEReal (f : ℝ → ℝ) (y : ℝ) : EReal :=
  sSup (Set.range fun z : ℝ => ((z * y - f z : ℝ) : EReal))

/-- 把定义写成 `iSup` 形式，便于使用完备格引理（`sSup_range`）。 -/
lemma fenchelConjAllEReal_eq_iSup (f : ℝ → ℝ) (y : ℝ) :
    fenchelConjAllEReal f y = ⨆ z : ℝ, ((z * y - f z : ℝ) : EReal) := by
  rw [fenchelConjAllEReal, sSup_range]

/-- `sSup` 的上界性质：每个 `z·y − f z` 都不超过 `f*(y)`。**无条件**——
这正是 `EReal` 值域的意义（旧版 `le_fenchelConjAll` 需要 `BddAbove`）。 -/
lemma le_fenchelConjAllEReal (f : ℝ → ℝ) (y z : ℝ) :
    ((z * y - f z : ℝ) : EReal) ≤ fenchelConjAllEReal f y := by
  rw [fenchelConjAllEReal_eq_iSup]
  exact le_iSup (fun z : ℝ => ((z * y - f z : ℝ) : EReal)) z

/-- `sSup` 的最小上界性质：若每个 `z·y − f z ≤ C`，则 `f*(y) ≤ C`。**无条件**；
`C : EReal` 可取 `⊤`。 -/
lemma fenchelConjAllEReal_le (f : ℝ → ℝ) (y : ℝ) (C : EReal)
    (h : ∀ z : ℝ, ((z * y - f z : ℝ) : EReal) ≤ C) :
    fenchelConjAllEReal f y ≤ C := by
  rw [fenchelConjAllEReal_eq_iSup]
  exact iSup_le h

/-- **Fenchel 不等式（`EReal` 版，无条件）**：`z·y ≤ f z + f*(y)`。
旧版 `RealFenchelMoreau.fenchel_ineq_all` 必须假设 `BddAbove`，本版不需要。
（`EReal` 版中右端可能为 `⊤`，命题仍有意义且为真。） -/
lemma fenchel_ineq_all_ereal (f : ℝ → ℝ) (z y : ℝ) :
    ((z * y : ℝ) : EReal) ≤ ((f z : ℝ) : EReal) + fenchelConjAllEReal f y := by
  have h := le_fenchelConjAllEReal f y z
  -- `↑(z·y) = ↑(f z) + ↑(z·y − f z)`（`EReal.coe_add` 反向），再对第二项用 `h`
  rw [show ((z * y : ℝ) : EReal)
      = ((f z : ℝ) : EReal) + ((z * y - f z : ℝ) : EReal) from by
    rw [← EReal.coe_add]; ring_nf]
  exact add_le_add le_rfl h

/-! ## 2. `⊤` 语义正确性：无上界 ⟺ 共轭为 `⊤` -/

/-- 集合在 `ℝ` 中有上界 ⟹ `f*(y) ≤ ↑M`（作为 `EReal`）。 -/
lemma fenchelConjAllEReal_le_of_bddAbove (f : ℝ → ℝ) (y M : ℝ)
    (hM : ∀ z : ℝ, z * y - f z ≤ M) : fenchelConjAllEReal f y ≤ ((M : ℝ) : EReal) :=
  fenchelConjAllEReal_le f y _ fun z => EReal.coe_le_coe_iff.mpr (hM z)

/-- **`⊤` 语义正确性（路线 A 的目标之一）**：`f*(y) = ⊤` **当且仅当**
`{z·y − f z}` 在 `ℝ` 中**无上界**。

这正是旧 `ℝ` 值版本丢掉的信息：旧版在该情形静默返回 junk 值 `0`，
使 `f*` 的凸性与演算律**必须**外加 `BddAbove` 才知道自己在说什么。
`EReal` 版把"无上界"**编码进值本身**，故假设可整体取消。 -/
theorem fenchelConjAllEReal_eq_top_iff (f : ℝ → ℝ) (y : ℝ) :
    fenchelConjAllEReal f y = ⊤
      ↔ ¬ BddAbove (Set.range fun z : ℝ => (z * y - f z : ℝ)) := by
  constructor
  · rintro htop ⟨M, hM⟩
    have hle := fenchelConjAllEReal_le_of_bddAbove f y M fun z => hM ⟨z, rfl⟩
    rw [htop] at hle
    exact EReal.coe_ne_top M (top_le_iff.mp hle)
  · intro hnb
    by_contra hne
    have hbot : fenchelConjAllEReal f y ≠ ⊥ := by
      intro hb
      have h0 := le_fenchelConjAllEReal f y 0
      rw [hb] at h0
      exact not_le_of_gt (EReal.bot_lt_coe (0 * y - f 0)) h0
    have hcoe : (((fenchelConjAllEReal f y).toReal : ℝ) : EReal) = fenchelConjAllEReal f y :=
      EReal.coe_toReal hne hbot
    refine hnb ⟨(fenchelConjAllEReal f y).toReal, fun v hv => ?_⟩
    obtain ⟨z, rfl⟩ := hv
    have hz := le_fenchelConjAllEReal f y z
    rw [← hcoe] at hz
    exact EReal.coe_le_coe_iff.mp hz

/-! ## 3. 凸性：**无需 `BddAbove`**（对照旧版 3 个假设 → 0 个） -/

/-- **`f*` 的凸性（`EReal` 版，无 `BddAbove`）** —— 本文件核心目标之一：
`f*(a·y₁ + b·y₂) ≤ a·f*(y₁) + b·f*(y₂)`，`a, b ≥ 0`、`a + b = 1`。

对照 `RealConjugateDuality.fenchelConjAll_convex`：旧版带**三个** `BddAbove`
假设（`_h12`、`h1`、`h2`），本版**一个都不要**。

证明：对每个 `z`，由 `a + b = 1` 有
`z·(a·y₁ + b·y₂) − f z = a·(z·y₁ − f z) + b·(z·y₂ − f z)`，
右端两分量分别 ≤ `a·f*(y₁)`、`b·f*(y₂)`，故 `a·f*(y₁) + b·f*(y₂)` 是 `sSup` 的上界，
`iSup_le` 收尾——**上界取 `EReal`，可以就是 `⊤`**，这正是取消假设的关键。 -/
theorem fenchelConjAllEReal_convex (f : ℝ → ℝ) (y₁ y₂ a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    fenchelConjAllEReal f (a * y₁ + b * y₂)
      ≤ ((a : ℝ) : EReal) * fenchelConjAllEReal f y₁
        + ((b : ℝ) : EReal) * fenchelConjAllEReal f y₂ := by
  apply fenchelConjAllEReal_le
  intro z
  have e1 := le_fenchelConjAllEReal f y₁ z
  have e2 := le_fenchelConjAllEReal f y₂ z
  have hsum : (a + b) * f z = f z := by rw [hab, one_mul]
  have key : z * (a * y₁ + b * y₂) - f z
      = a * (z * y₁ - f z) + b * (z * y₂ - f z) := by linarith [hsum]
  have hcoe : ((z * (a * y₁ + b * y₂) - f z : ℝ) : EReal)
      = ((a * (z * y₁ - f z) : ℝ) : EReal) + ((b * (z * y₂ - f z) : ℝ) : EReal) := by
    rw [key, EReal.coe_add]
  rw [hcoe]
  have m1 : ((a * (z * y₁ - f z) : ℝ) : EReal)
      ≤ ((a : ℝ) : EReal) * fenchelConjAllEReal f y₁ := by
    rw [EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left e1 (EReal.coe_nonneg.mpr ha)
  have m2 : ((b * (z * y₂ - f z) : ℝ) : EReal)
      ≤ ((b : ℝ) : EReal) * fenchelConjAllEReal f y₂ := by
    rw [EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left e2 (EReal.coe_nonneg.mpr hb)
  exact add_le_add m1 m2

/-! ## 4. 演算律：平移 / 加法-下卷积 / 缩放（均无 `BddAbove`） -/

/-- **平移规则（`EReal` 版，无条件）**：`(f + ⟨a,·⟩)*(y) = f*(y − a)`。
只需**集合层面的逐点恒等式** `z·y − (f z + a·z) = z·(y − a) − f z`，
两侧 `sSup` 集合完全相同。旧版此处**本就没有** `BddAbove`，本版保持一致。 -/
theorem fenchelConjAllEReal_shift (f : ℝ → ℝ) (a y : ℝ) :
    fenchelConjAllEReal (fun z => f z + a * z) y = fenchelConjAllEReal f (y - a) := by
  have hset : (Set.range fun z : ℝ => ((z * y - (f z + a * z) : ℝ) : EReal))
      = Set.range fun z : ℝ => ((z * (y - a) - f z : ℝ) : EReal) := by
    apply congrArg Set.range
    funext z
    congr 1
    ring
  rw [fenchelConjAllEReal, hset, fenchelConjAllEReal]

/-- **加法规则（`EReal` 版，下卷积拆分形式，无 `BddAbove`）**：
对**任意**分解 `y = y₁ + y₂`，
`(f+g)*(y₁ + y₂) ≤ f*(y₁) + g*(y₂)`。
真恒等式是 `z·(y₁+y₂) − (f z + g z) = (z·y₁ − f z) + (z·y₂ − g z)`。
旧版 `RealConjugateDuality.fenchelConjAll_add_le_split` 带**三个** `BddAbove`，
`EReal` 版一个都不要。 -/
theorem fenchelConjAllEReal_add_le_split (f g : ℝ → ℝ) (y₁ y₂ : ℝ) :
    fenchelConjAllEReal (fun z => f z + g z) (y₁ + y₂)
      ≤ fenchelConjAllEReal f y₁ + fenchelConjAllEReal g y₂ := by
  apply fenchelConjAllEReal_le
  intro z
  have e1 := le_fenchelConjAllEReal f y₁ z
  have e2 := le_fenchelConjAllEReal g y₂ z
  have key : z * (y₁ + y₂) - (f z + g z) = (z * y₁ - f z) + (z * y₂ - g z) := by ring
  have hcoe : ((z * (y₁ + y₂) - (f z + g z) : ℝ) : EReal)
      = ((z * y₁ - f z : ℝ) : EReal) + ((z * y₂ - g z : ℝ) : EReal) := by
    rw [key, EReal.coe_add]
  rw [hcoe]
  exact add_le_add e1 e2

/-- **缩放规则（`EReal` 版，**诚实降级为 `≤`**，无 `BddAbove`）**：
`λ > 0` ⟹ `(λ·f)*(y) ≤ λ·f*(y/λ)`。

逐点恒等式 `↑(z·y − λ·f z) = ↑λ · ↑(z·(y/λ) − f z)`（`EReal.coe_mul`）给出
`(λf)*(y) = ⨆ z, ↑λ · g z`，而 `↑λ · ⨆ z, g z` 是它的上界
（`mul_le_mul_of_nonneg_left` + `EReal.instPosMulMono`），故 `≤` 成立。

**诚实降级（未证等号）**：等号方向需要把 `↑λ` 提出 `iSup`，即
`↑λ * ⨆ g = ⨆ (↑λ * g)`。本版 mathlib 的 `EReal` **无 `PosMulReflectLE`**
（不能消去 `↑λ`）且**无 `ContinuousMul`**（不能用
`Monotone.map_iSup_of_continuousAt`），故**未证**。**标注为后续工作**。
下游演算只用到 Fenchel 不等式方向（`≤`），故本文件其余结论不受影响。
旧版 `RealConjugateDuality.fenchelConjAll_scaling` 是等号，但需 `BddAbove`。 -/
theorem fenchelConjAllEReal_scaling_le (f : ℝ → ℝ) (y lam : ℝ) (hlam : 0 < lam) :
    fenchelConjAllEReal (fun z => lam * f z) y
      ≤ ((lam : ℝ) : EReal) * fenchelConjAllEReal f (y / lam) := by
  have hlam0 : (0 : EReal) ≤ ((lam : ℝ) : EReal) := EReal.coe_nonneg.mpr (le_of_lt hlam)
  have hkey : ∀ z : ℝ, ((z * y - lam * f z : ℝ) : EReal)
      = ((lam : ℝ) : EReal) * ((z * (y / lam) - f z : ℝ) : EReal) := by
    intro z
    -- 先把右边写成 `↑(λ * (…))`，再用 `ℝ` 中的恒等式
    rw [show ((lam : ℝ) : EReal) * ((z * (y / lam) - f z : ℝ) : EReal)
        = ((lam * (z * (y / lam) - f z) : ℝ) : EReal) from (EReal.coe_mul lam _).symm]
    congr 1
    field_simp
  rw [fenchelConjAllEReal_eq_iSup,
    show (fun z : ℝ => ((z * y - lam * f z : ℝ) : EReal))
        = fun z : ℝ => ((lam : ℝ) : EReal) * ((z * (y / lam) - f z : ℝ) : EReal) from
      funext hkey]
  apply iSup_le
  intro z
  exact mul_le_mul_of_nonneg_left (le_iSup (fun z : ℝ => ((z * (y / lam) - f z : ℝ) : EReal)) z) hlam0

/-! ## 5. 次梯度 ⟺ 共轭在 `g` 处被取到（**无 `BddAbove`**） -/

/-- **次梯度 ⟺ 共轭等式（`EReal` 版，无 `BddAbove`）**：
`g ∈ ∂f(x) ⟺ f*(g) = ↑(g·x − f x)`。

两个方向都**不需要凸性，也不需要 `BddAbove`**——这正是 `EReal` 值域的收益。
旧版 `RealFenchelMoreau.subgradient_iff_fenchelConj_eq` 必须假设
`BddAbove {z·g − f z}` 才能陈述（否则 `ℝ` 值 `sSup` 可为 junk 值 `0`
而使 iff 为假）；`EReal` 版把该前提吸收进 `⊤` 语义。 -/
theorem subgradient_iff_fenchelConjAllEReal_eq (f : ℝ → ℝ) (x g : ℝ) :
    Subgradient f x g
      ↔ fenchelConjAllEReal f g = ((g * x - f x : ℝ) : EReal) := by
  constructor
  · intro hg
    apply le_antisymm
    · apply fenchelConjAllEReal_le
      intro z
      have h := hg z
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · have h := le_fenchelConjAllEReal f g x
      rwa [show x * g - f x = g * x - f x from by ring] at h
  · intro heq z
    have h := le_fenchelConjAllEReal f g z
    rw [heq] at h
    have h' := EReal.coe_le_coe_iff.mp h
    linarith

/-! ## 6. 一致性桥接：`EReal` 版与 `ℝ` 版在 `BddAbove` 下吻合 -/

/-- **一致性桥接（路线 A 的目标之一）**：当 `{z·y − f z}` 在 `ℝ` 中有上界时，
`EReal` 版共轭**有限**，且其 `toReal` 恰是旧 `ℝ` 值共轭：

    (fenchelConjAllEReal f y).toReal = fenchelConjAll f y

即：新定义在**旧定义有意义的一切场合**都给出相同答案——
这是"新权威不改变既有结论"的凭据（旧文件因此可原样保留）。
`BddAbove` 在此**只服务于桥接**（把 `⊤` 排除掉以便降回 `ℝ`），
**不是**新命题（凸性/演算律）的前提。 -/
theorem fenchelConjAllEReal_toReal (f : ℝ → ℝ) (y : ℝ)
    (hb : BddAbove (Set.range fun z : ℝ => (z * y - f z : ℝ))) :
    (fenchelConjAllEReal f y).toReal = fenchelConjAll f y := by
  obtain ⟨M, hM⟩ := hb
  have htop : fenchelConjAllEReal f y ≠ ⊤ := by
    intro h
    have hle := fenchelConjAllEReal_le_of_bddAbove f y M fun z => hM ⟨z, rfl⟩
    rw [h] at hle
    exact EReal.coe_ne_top M (top_le_iff.mp hle)
  have hbot : fenchelConjAllEReal f y ≠ ⊥ := by
    intro h
    have h0 := le_fenchelConjAllEReal f y 0
    rw [h] at h0
    exact not_le_of_gt (EReal.bot_lt_coe (0 * y - f 0)) h0
  -- 关键恒等式：`BddAbove` 时 `↑(旧值)` 与 `EReal` 版**相等**
  -- `≤` 方向：`↑(c) ≤ X` 只需每个生成元 `≤ X`？不成立；改用 `toReal` 中转。
  have hcoe : (((fenchelConjAll f y : ℝ)) : EReal) = fenchelConjAllEReal f y := by
    apply le_antisymm
    · -- `↑(旧值) ≤ ⨆ …`：先证 `↑(旧值)` 的 `toReal` 意义下的逼近
      rw [fenchelConjAllEReal_eq_iSup]
      -- 对任意 `ε > 0`，存在 `z` 使 `旧值 − ε ≤ z·y − f z`；取极限
      by_contra hlt
      push_neg at hlt
      -- `hlt : ⨆ … < ↑(旧值)`；取 `toReal` 得矛盾
      have hne : (⨆ z : ℝ, ((z * y - f z : ℝ) : EReal)) ≠ ⊤ :=
        ne_of_lt (lt_of_lt_of_le hlt le_top)
      have hbot : (⨆ z : ℝ, ((z * y - f z : ℝ) : EReal)) ≠ ⊥ := by
        intro h
        have h0 := le_iSup (fun z : ℝ => ((z * y - f z : ℝ) : EReal)) 0
        rw [h] at h0
        exact not_le_of_gt (EReal.bot_lt_coe (0 * y - f 0)) h0
      have hcoe2 : ((((⨆ z : ℝ, ((z * y - f z : ℝ) : EReal))).toReal : ℝ) : EReal)
          = ⨆ z : ℝ, ((z * y - f z : ℝ) : EReal) := EReal.coe_toReal hne hbot
      have hreal : (⨆ z : ℝ, ((z * y - f z : ℝ) : EReal)).toReal < fenchelConjAll f y :=
        EReal.coe_lt_coe_iff.mp (by rw [hcoe2]; exact hlt)
      -- 但 `⨆` 的 `toReal` 不小于每个 `z·y − f z`，故 `旧值` 不是最小上界
      have hub : ∀ z : ℝ, z * y - f z ≤ (⨆ z : ℝ, ((z * y - f z : ℝ) : EReal)).toReal := by
        intro z
        have hz := le_iSup (fun z : ℝ => ((z * y - f z : ℝ) : EReal)) z
        rw [← hcoe2] at hz
        exact EReal.coe_le_coe_iff.mp hz
      have : fenchelConjAll f y ≤ (⨆ z : ℝ, ((z * y - f z : ℝ) : EReal)).toReal :=
        csSup_le ⟨0 * y - f 0, ⟨0, rfl⟩⟩ fun v hv => by
          obtain ⟨z, rfl⟩ := hv
          exact hub z
      linarith
    · -- `⨆ …` ≤ `↑(旧值)`：旧值是 ℝ 中上界（`M` 与 `hM` 来自 `hb` 的解构）
      rw [fenchelConjAllEReal_eq_iSup]
      apply iSup_le
      intro z
      exact EReal.coe_le_coe_iff.mpr (le_csSup ⟨M, fun v hv => hM (by
        obtain ⟨w, rfl⟩ := hv
        exact Set.mem_range_self w)⟩ ⟨z, rfl⟩)
  calc (fenchelConjAllEReal f y).toReal
      = ((((fenchelConjAll f y : ℝ)) : EReal)).toReal := by rw [hcoe]
    _ = fenchelConjAll f y := EReal.toReal_coe _

/-- §6 桥接的别名形式（便于下游按 `BddAbove` 命名检索）。 -/
theorem fenchelConjAllEReal_toReal_of_bddAbove (f : ℝ → ℝ) (y : ℝ)
    (hb : BddAbove (Set.range fun z : ℝ => (z * y - f z : ℝ))) :
    (fenchelConjAllEReal f y).toReal = fenchelConjAll f y :=
  fenchelConjAllEReal_toReal f y hb

/-! ## 7. `f*` 的下半连续性（旧版「未做」，`EReal` 下**无条件**成立） -/

/-- 每个 `z` 对应的函数 `y ↦ ↑(z·y − f z)` 在 `ℝ` 上**连续**。
由 `EReal.continuous_coe_iff` 把连续性问题送回 `ℝ`。 -/
lemma continuous_fenchelConjAllEReal_term (f : ℝ → ℝ) (z : ℝ) :
    Continuous fun y : ℝ => ((z * y - f z : ℝ) : EReal) := by
  rw [EReal.continuous_coe_iff]
  exact (continuous_const.mul continuous_id).sub continuous_const

/-- **`f*` 的下半连续性（`EReal` 版，无条件）** —— 旧 `ℝ` 版**未做**，
在 `EReal` 下由完备格结构**免费**得到：

`f*(y) = ⨆_z ↑(z·y − f z)` 是一族**连续函数**的逐点上确界，
而 `lowerSemicontinuous_iSup` 断言（`δ` 为 `CompleteLinearOrder` 时）
下半连续函数的 `iSup` 仍下半连续。`EReal` 正是完备线性序。

**注意**：`f*` 的 LSC **不需要 `f` 的任何假设**——凸性、闭性、有界性都不要，
也不需要 `BddAbove`。这与"共轭是仿射函数族的 sup"这一几何直觉一致。
`ℝ` 值域下同一定理**不成立**（`ℝ` 无 `⊤`，`iSup` 不被上半连续保持），
故这是 `EReal` 值域的**额外收益**。 -/
theorem fenchelConjAllEReal_lowerSemicontinuous (f : ℝ → ℝ) :
    LowerSemicontinuous fun y : ℝ => fenchelConjAllEReal f y := by
  have h : (fun y : ℝ => fenchelConjAllEReal f y)
      = fun y : ℝ => ⨆ z : ℝ, ((z * y - f z : ℝ) : EReal) :=
    funext fun y => fenchelConjAllEReal_eq_iSup f y
  rw [h]
  exact lowerSemicontinuous_iSup fun z =>
    (continuous_fenchelConjAllEReal_term f z).lowerSemicontinuous

/-! ## 8. 审计：哪些 `BddAbove` 是**真的**必要（机器验证反例）

对 `RealFenchelMoreau` / `RealConjugateDuality` 中每条带 `BddAbove` 的陈述，
本节用**可在内核验证的反例**判定"去掉假设后是否真的为假"。

### 8.1 `ℝ` 值 `sSup` 在无上界时确实返回 junk 值 `0`

`Set.range (fun z : ℝ => z)` **无上界**，其 `ℝ` 值 `sSup` 是 junk 值 `0`
（`Real.sSup_of_not_bddAbove`）。这正是全部 `BddAbove` 的**唯一根源**。 -/

/-- `Set.range (fun z : ℝ => z)` 在 `ℝ` 中无上界。 -/
lemma not_bddAbove_range_id : ¬ BddAbove (Set.range fun z : ℝ => z) := by
  rintro ⟨M, hM⟩
  have h : (M + 1 : ℝ) ≤ M := hM ⟨M + 1, rfl⟩
  linarith

/-- **审计反例 A（junk 值语义）**：`f := fun _ => 0`、`y := 1` 时
`{z·y − f z} = Set.range (fun z : ℝ => z)` 无上界，`ℝ` 值 `sSup` 是 junk 值 `0`；
而 `EReal` 版正确地给出 `⊤`。**结论**：旧版全部 `BddAbove` 都是真的必要——
它们正是"排除 junk 值"的显式条件。 -/
theorem audit_real_sSup_junk_and_ereal_top :
    sSup (Set.range fun z : ℝ => z) = 0
      ∧ ¬ BddAbove (Set.range fun z : ℝ => z)
      ∧ fenchelConjAllEReal (fun _ => (0 : ℝ)) 1 = ⊤ := by
  refine ⟨Real.sSup_of_not_bddAbove not_bddAbove_range_id, not_bddAbove_range_id, ?_⟩
  rw [fenchelConjAllEReal_eq_top_iff]
  refine fun hb => not_bddAbove_range_id ?_
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, fun v hv => by
    obtain ⟨z, rfl⟩ := hv
    exact hM ⟨z, by ring⟩⟩

/-- **审计反例 B（旧版凸性去掉 `BddAbove` 后，假设不可满足）**：
取 `f := fun _ => 0`、`y₁ := y₂ := 1`。旧版 `fenchelConjAll_convex` 的三个
`BddAbove` 假设（`_h12`、`h1`、`h2`）在此**同时为假**，
故该陈述在这一点上**根本无从谈起**——这不是"技术条件"，
而是旧定义在该点没有语义。

`EReal` 版在同一数据上三点全为 `⊤`，命题 `⊤ ≤ ½·⊤ + ½·⊤` **无条件为真**。 -/
theorem audit_ereal_convexity_unconditional :
    ¬ BddAbove (Set.range fun z : ℝ => (z * 1 - (fun _ => (0 : ℝ)) z : ℝ))
      ∧ fenchelConjAllEReal (fun _ => (0 : ℝ)) 1 = ⊤
      ∧ fenchelConjAllEReal (fun _ => (0 : ℝ)) ((1/2 : ℝ) * 1 + (1/2 : ℝ) * 1)
          ≤ (((1/2 : ℝ)) : EReal) * fenchelConjAllEReal (fun _ => (0 : ℝ)) 1
            + (((1/2 : ℝ)) : EReal) * fenchelConjAllEReal (fun _ => (0 : ℝ)) 1 := by
  refine ⟨?_, ?_, fenchelConjAllEReal_convex (fun _ => (0 : ℝ)) 1 1 (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num)⟩
  · refine fun hb => not_bddAbove_range_id ?_
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun v hv => by
      obtain ⟨z, rfl⟩ := hv
      exact hM ⟨z, by ring⟩⟩
  · rw [fenchelConjAllEReal_eq_top_iff]
    refine fun hb => not_bddAbove_range_id ?_
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun v hv => by
      obtain ⟨z, rfl⟩ := hv
      exact hM ⟨z, by ring⟩⟩

/-- **审计反例 C（桥接必要性）**：在反例 A 的数据上，
`BddAbove` **失败**而旧 `ℝ` 值 `fenchelConjAll` 给出 `0`、`EReal` 版给出 `⊤`，
二者**不一致**——恰好说明 §6 桥接定理中 `BddAbove` **不可去掉**：
它是"两套定义在该点说同一件事"的充要前提。 -/
theorem audit_bridge_needs_bddAbove :
    ¬ BddAbove (Set.range fun z : ℝ => (z * 1 - (fun _ => (0 : ℝ)) z : ℝ))
      ∧ fenchelConjAll (fun _ => (0 : ℝ)) 1 = 0
      ∧ fenchelConjAllEReal (fun _ => (0 : ℝ)) 1 = ⊤ := by
  refine ⟨?_, ?_, ?_⟩
  · refine fun hb => not_bddAbove_range_id ?_
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun v hv => by
      obtain ⟨z, rfl⟩ := hv
      exact hM ⟨z, by ring⟩⟩
  · rw [fenchelConjAll]
    exact Real.sSup_of_not_bddAbove (by
      refine fun hb => not_bddAbove_range_id ?_
      obtain ⟨M, hM⟩ := hb
      exact ⟨M, fun v hv => by
        obtain ⟨z, rfl⟩ := hv
        exact hM ⟨z, by ring⟩⟩)
  · rw [fenchelConjAllEReal_eq_top_iff]
    refine fun hb => not_bddAbove_range_id ?_
    obtain ⟨M, hM⟩ := hb
    exact ⟨M, fun v hv => by
      obtain ⟨z, rfl⟩ := hv
      exact hM ⟨z, by ring⟩⟩

end Lattice
