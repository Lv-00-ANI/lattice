import Mathlib
import Lattice.Lib.LearningTheory.RealCausalInference
/-!
# LATTICE: SCM 因果效应的可识别性——不可识别反例与后门充分条件

方向（因果推断基础）：本文件回答「**仅凭观测分布能否识别 do-分布**」。

## 头号交付：不可识别性的机器可验证反例（`ℚ` 版）

构造两个**分布层面**的模型，它们**观测分布完全相同**，但干预分布不同：

* **模型 C（无混杂）**：`X` 是公平硬币（`UX`），`Y := X`（确定性）。
  观测 `P(X=x, Y=y) = 1/2·[x=y]`；干预 `do(X=x)` 时 `Y := x`，
  故 `P(Y=y|do(X=x)) = [y=x]`（`doC`）。
* **模型 D（隐混杂 U）**：隐变量 `U ~ Bern(1/2)`，`X := U`，`Y := U`。
  于是 `X` 与 `Y` **通过隐变量 U 相关**（Y 不是被 X 决定的，二者都是 U 的
  确定性函数）。观测 `P(X=x, Y=y) = 1/2·[x=y]`，与模型 C 相同；
  但干预 `do(X=x)` 只截断 `X = U` 这条方程，`U` 仍然随机，`Y = U`，
  故 `P(Y=y|do(X=x)) = 1/2`（`doD`），与 `x` **无关**。

模型 D 的 `obsD` / `doD` 用**隐变量求和**显式写出（而不是查表），
所以「同一观测、不同干预」不是定义上的巧合，而是两个**结构不同**的
数据生成过程的真实后果。

这不是结构方程建模层面的图模型，而是**分布层面的等价类反例**：
它验证的结论是——**同一观测分布对应两个不同的干预分布，故仅凭观测
分布不能识别 do-分布（因果效应不可识别）**。

主要定理：

* `obs_C_eq_obs_D : obsC = obsD`（两模型观测分布相同，`ℚ` 上可计算验证）；
* `do_C_ne_do_D : doC ≠ doD`（给出具体见证 `doC (false,false) = 1 ≠ 1/2 = doD (false,false)`）；
* `causal_effect_unidentifiable : obsC = obsD ∧ doC ≠ doD`；
* `no_function_recovers_do`（**最锋利的不可识别性陈述**）：不存在任何
  从观测分布到干预分布的泛函 `F`（无论多复杂）能同时在这两个模型上
  都正确恢复 do-分布——因为 `obsC = obsD ⟹ F obsC = F obsD`，与
  `doC ≠ doD` 矛盾。

## 第二交付：可识别性的充分条件（无混杂 + 正性）

* `id_adjust`：后门**调整泛函**，只依赖观测表 `O x y z = P(X=x,Y=y,Z=z)`；
* `doY_eq_id_adjust`：在正性假设下，`doY M = id_adjust (obs M)`
  （即 `RealCausalInference.backdoor_adjustment` 写成的泛函形式）；
* `backdoor_identifiable`：若两个 `BinSCM` 观测分布相同且正性成立，
  则干预分布相同——**无混杂（`BinSCM` 的因子化外生分布）+ 正性 ⟹ 可识别**。

## 诚实标注（降级 / 未做 / 未证）

* **正性（positivity / overlap）**：`doY_eq_id_adjust` 与
  `backdoor_identifiable` 都带显式正性假设；这是标准的前提，不是 gap。
* **忠实性（faithfulness）在本版本中未证、也未使用**：本文件证的可识别性
  只需「无混杂 + 正性」。忠实性（以及它为条件独立 ⟹ 图结构所需的假设）
  属于**结构学习**方向，本文件**未做**——请勿把本结果读作「忠实性已被证明」。
* **未做**：不可识别性反例的连续变量 / 测度论版本（只做了 `ℚ` 二值版，
  以保证机器可验证）；任意 DAG 的后门准则一般形式；
  「可识别的必要充分条件」刻画。
* **标注**：`ℚ` 上不用 `by decide` 做整体函数相等判定（mathlib 4.14 中
  `Rat.normalize` 可能卡），改用显式求值与见证点。

无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 不可识别反例：两个观测等价但干预不同的模型 -/

/-- **模型 C（无混杂）** 的观测联合分布：`X` 是公平硬币，`Y := X`。
`obsC (x,y) = 1/2·[x=y]`。 -/
def obsC (p : Bool × Bool) : ℚ := if p.1 = p.2 then 1 / 2 else 0

/-- **模型 C** 的干预分布：`do(X=x)` 时 `Y := x`（确定性），
`doC (x,y) = [y=x]`。 -/
def doC (p : Bool × Bool) : ℚ := if p.2 = p.1 then 1 else 0

/-- **模型 D（隐混杂 U）** 的观测联合分布：隐变量 `U ~ Bern(1/2)` 同时决定
`X := U` 与 `Y := U`，故 `obsD (x,y) = Σ_u 1/2·[u=x]·[u=y] = 1/2·[x=y]`。
用隐变量求和显式写出，体现结构与模型 C 的**结构差异**。 -/
def obsD (p : Bool × Bool) : ℚ :=
  ∑ u : Bool, (1 / 2 : ℚ) * (if u = p.1 then (1 : ℚ) else 0)
    * (if u = p.2 then (1 : ℚ) else 0)

/-- **模型 D** 的干预分布：`do(X=x)` 只截断 `X := U`，`U` 仍为 `Bern(1/2)`，
`Y := U` 不变，故 `doD (x,y) = Σ_u 1/2·[u=y] = 1/2`，与 `x` 无关。 -/
def doD (p : Bool × Bool) : ℚ :=
  ∑ u : Bool, (1 / 2 : ℚ) * (if u = p.2 then (1 : ℚ) else 0)

/-! ## 反例的机器验证 -/

/-- **观测分布相同**：`obsC = obsD`（两个结构不同的模型给出同一观测律）。
逐点对 `Bool` 的四种取值显式计算。 -/
theorem obs_C_eq_obs_D : obsC = obsD := by
  funext p
  obtain ⟨x, y⟩ := p
  cases x <;> cases y <;> simp [obsC, obsD, Fintype.sum_bool]

/-- **干预分布不同**：`doC ≠ doD`，见证点 `(false, false)`——
`doC (false,false) = 1` 而 `doD (false,false) = 1/2`。 -/
theorem do_C_ne_do_D : doC ≠ doD := by
  intro h
  have h1 : doC (false, false) = doD (false, false) := congrFun h (false, false)
  norm_num [doC, doD, Fintype.sum_bool] at h1

/-- **因果效应不可识别（主结论）**：存在观测分布相同、干预分布不同的两个模型。
即「仅凭观测分布不能识别 do-分布」——在 `ℚ` 上完全可计算验证。 -/
theorem causal_effect_unidentifiable : obsC = obsD ∧ doC ≠ doD :=
  ⟨obs_C_eq_obs_D, do_C_ne_do_D⟩

/-- **不存在从观测分布恢复干预分布的泛函**（最锋利的不可识别性陈述）：
对任意（可任意复杂的、甚至不可计算的）映射
`F : (Bool × Bool → ℚ) → (Bool × Bool → ℚ)`，若它在模型 C 上正确
（`F obsC = doC`）且在模型 D 上正确（`F obsD = doD`），
则由 `obsC = obsD` 得 `F obsC = F obsD`，即 `doC = doD`，与
`do_C_ne_do_D` 矛盾。故这样的 `F` **不存在**。 -/
theorem no_function_recovers_do :
    ¬ ∃ F : (Bool × Bool → ℚ) → (Bool × Bool → ℚ),
        F obsC = doC ∧ F obsD = doD := by
  rintro ⟨F, h1, h2⟩
  rw [obs_C_eq_obs_D] at h1
  exact do_C_ne_do_D (h1.symm.trans h2)

/-! ## 反例的自检：确实是概率分布 -/

/-- 模型 C 的观测分布是概率分布（`Σ_{x,y} obsC = 1`）。 -/
lemma obsC_sum_one : (∑ p : Bool × Bool, obsC p) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  norm_num [obsC]

/-- 模型 C 的干预分布对 `y` 归一：对每个 `x`，`Σ_y doC (x,y) = 1`。 -/
lemma doC_normalized (x : Bool) : (∑ y : Bool, doC (x, y)) = 1 := by
  cases x <;> simp only [Fintype.sum_bool] <;> norm_num [doC]

/-- 模型 D 的干预分布对 `y` 归一（隐变量求和显式计算）。 -/
lemma doD_normalized (x : Bool) : (∑ y : Bool, doD (x, y)) = 1 := by
  simp only [doD, Fintype.sum_bool]
  norm_num

/-! ## 可识别性的充分条件：后门调整泛函 -/

/-- **后门调整泛函**：只依赖观测表 `O x y z = P(X=x, Y=y, Z=z)`，
`id_adjust O x y = Σ_z P(Z=z) · P(Y=y | X=x, Z=z)`，其中
`P(Z=z) = Σ_x Σ_y O x y z`，`P(Y=y|X=x,Z=z) = O x y z / Σ_y' O x y' z`。
这是 `RealCausalInference.backdoor_adjustment` 右端的纯观测重写。 -/
def id_adjust (O : Bool → Bool → Bool → ℝ) (x y : Bool) : ℝ :=
  ∑ z : Bool, (∑ x' : Bool, ∑ y' : Bool, O x' y' z)
    * (O x y z / (∑ y' : Bool, O x y' z))

/-- **调整公式 = 观测泛函**：在正性假设下 `doY M = id_adjust (obs M)`，
即干预分布是观测分布的（显式给出的）函数。 -/
theorem doY_eq_id_adjust (M : BinSCM) (hpos : ∀ x z, 0 < obsXZ M x z) (x y : Bool) :
    doY M x y = id_adjust (obs M) x y := by
  rw [backdoor_adjustment M x y hpos]
  simp only [id_adjust, condYZ, obsXZ]
  apply Finset.sum_congr rfl
  intro z _
  rw [pZobs_eq_sum_sum_obs M z]

/-- **可识别性的充分条件（无混杂 + 正性）**：若两个 `BinSCM`
（无未观测混杂，外生噪声因子化）的观测分布完全相同，
且正性 `∀ x z, 0 < P(X=x, Z=z)` 成立，则它们的干预分布完全相同。

证明：`doY = id_adjust ∘ obs`（`doY_eq_id_adjust`），
故观测相等 ⟹ 调整公式取值相等 ⟹ 干预相等。
**不需要忠实性**（见文件头标注）。 -/
theorem backdoor_identifiable (M M' : BinSCM)
    (hpos : ∀ x z, 0 < obsXZ M x z)
    (h : ∀ x y z, obs M x y z = obs M' x y z) :
    ∀ x y, doY M x y = doY M' x y := by
  have hpos' : ∀ x z, 0 < obsXZ M' x z := by
    intro x z
    have hxz : obsXZ M' x z = obsXZ M x z := by
      simp only [obsXZ, h]
    rw [hxz]
    exact hpos x z
  intro x y
  rw [doY_eq_id_adjust M hpos x y, doY_eq_id_adjust M' hpos' x y]
  simp only [id_adjust, h]

end Lattice
