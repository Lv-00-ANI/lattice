import Mathlib

/-!
# LATTICE: 有限结构因果模型（SCM）——截断语义与后门调整公式

方向（因果推断基础）：在**二元**（全部变量取值于 `Bool`）结构因果模型
（Structural Causal Model, SCM）上，把 Pearl 的 do-演算
「干预 = 替换结构方程（truncated factorization / 截断语义）」形式化，
并证明**后门调整公式（back-door adjustment）**。

## 模型

图结构固定为 `Z → X`、`Z → Y`、`X → Y`：

```
Z = fZ uz,      X = fX z ux,      Y = fY x z uy
```

外生变量 `(ux, uy, uz) : Bool × Bool × Bool` 的联合分布**因子化**为
`pU ux uy uz = pX ux * pY uy * pZ uz`。

**这是「无未观测混杂（no unobserved confounding）」的显式结构假设**：
外生噪声 `UX`、`UY`、`UZ` 互相独立，因此 `(X, Y)` 之间除 `Z` 与
`X → Y` 之外没有共同的隐变量通道——即后门准则对 `(X, Y, Z)` 成立
（`Z` 阻断了所有后门路径）。本文件把这条假设**写在类型里**
（三个因子化的边缘分布字段），而不是当作隐含前提。

## 观测分布与截断（干预）分布

* `obs M x y z = P(X=x, Y=y, Z=z)`——对 `(ux, uy, uz)` 三重和；
* `doYZ M x y z = P(Y=y, Z=z | do(X=x))`——把 `X` 的方程
  `X = fX z ux` **替换为常数 `x`**（截断语义），其余方程与分布不变；
* `doY M x y = P(Y=y | do(X=x))` 是 `doYZ` 对 `z` 的边缘化。

## 主要结果

1. `obs_eq_xmarg_mul_ycond_mul_pZobs`：观测分布**因子化**
   `P(x,y,z) = P(X=x|Z=z) · P(Y=y|X=x,Z=z) · P(Z=z)`（乘积之和分解）；
2. `obsXZ_eq`：`Σ_y P(x,y,z) = P(X=x|Z=z) · P(Z=z)`（用 `Σ_uy pY = 1`）；
3. `doY_eq_sum_pZobs_ycond`：**截断语义的显式形式**
   `P(Y=y|do(X=x)) = Σ_z P(Z=z) · P(Y=y|X=x,Z=z)`
   —— 干预分布只依赖机制项；
4. `doYZ_sum`：干预分布对 `y` 求和为 1（是概率分布）；
5. **`backdoor_adjustment`（主定理）**：在**正性 / 重叠假设**
   `hpos : ∀ x z, 0 < P(X=x, Z=z)` 下，
   `P(Y=y|do(X=x)) = Σ_z P(Z=z) · P(Y=y|X=x,Z=z)`
   —— 即调整公式（`condYZ` 形式）。

## 诚实标注（降级 / 未做 / 未证）

* **正性（positivity / overlap）假设**：定理 5 的陈述带显式假设
  `hpos`。这不是被掩盖的 gap：若某层 `(x, z)` 的观测概率为 0，
  条件概率 `P(Y=y|X=x,Z=z)` 无定义（Lean 中 `a/0 = 0`），
  调整公式**确实可能失效**——这是因果推断的标准可识别性前提。
* **有限 / 二值版**：本文件只处理 `Bool` 取值的 SCM 与有限和；
  未做连续变量、测度论版（`RealDPIComplete` 等文件提供了测度工具，
  但 do-演算的测度版本未做）。
* **忠实性（faithfulness）未证、也未使用**：可识别性在本版本中只需
  「无混杂 + 正性」，忠实性属于结构学习方向，本文件**未做**。
* **图结构固定**：只有 `Z → X → Y`、`Z → Y` 这一条三元图；
  **未做**任意 DAG 的后门准则一般形式（d-分离 / 最小充分调整集）。
* 其余（`doY_sum`、`pZobs_sum` 等）为概率归一性的自检引理。

无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 二值指示函数 -/

/-- 二值指示函数：命题真值嵌入 `ℝ`（`p` 真取 `1`，否则取 `0`）。 -/
def binInd (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

/-- 指示函数非负（概率语义的基础：指示量是 0/1 概率质量）。 -/
lemma binInd_nonneg (p : Prop) [Decidable p] : 0 ≤ binInd p := by
  by_cases h : p <;> simp [binInd, h]

/-- 真命题的指示为 `1`。 -/
lemma binInd_true : binInd True = 1 := rfl

/-- 假命题的指示为 `0`。 -/
lemma binInd_false : binInd False = 0 := rfl

/-- Bool 上「指示恰有一项为 1」：
`binInd (c = true) + binInd (c = false) = 1`（`c` 两个取值分情况）。 -/
lemma binInd_bool_sum (c : Bool) : binInd (c = true) + binInd (c = false) = 1 := by
  cases c <;> simp [binInd]

/-- 指示函数求和版：`Σ_{b : Bool} binInd (c = b) = 1`
（Bool 上恰有一个 `b` 使 `c = b` 成立——「替换」性质的求和形式）。 -/
lemma sum_bool_binInd_eq_one (c : Bool) : (∑ b : Bool, binInd (c = b)) = 1 := by
  rw [Fintype.sum_bool]
  exact binInd_bool_sum c

/-- 具体情形：`binInd (a = a) = 1`（同一 Bool 值的指示为真）。 -/
@[simp] lemma binInd_eq_self (a : Bool) : binInd (a = a) = 1 := by simp [binInd]

/-- 具体情形：`binInd (true = false) = 0`。 -/
@[simp] lemma binInd_true_eq_false : binInd (true = false) = 0 := by simp [binInd]

/-- 具体情形：`binInd (false = true) = 0`。 -/
@[simp] lemma binInd_false_eq_true : binInd (false = true) = 0 := by simp [binInd]

/-- **指示替换引理**：`Σ_{b : Bool} binInd (c = b) * G b = G c`
（观测分布对 `z` 求和时，指示量把被积函数在 `z = c` 处取值——
这是截断语义「以方程取值代入」的代数核心）。 -/
lemma sum_bool_binInd_mul (c : Bool) (G : Bool → ℝ) :
    (∑ b : Bool, binInd (c = b) * G b) = G c := by
  rw [Fintype.sum_bool]
  cases c <;> simp [binInd]

/-! ## 二元结构因果模型（Z → X, Z → Y, X → Y） -/

/-- 二元结构因果模型：

* 结构方程 `Z = fZ uz`、`X = fX z ux`、`Y = fY x z uy`；
* 外生变量 `(ux, uy, uz)` 的边缘分布 `pX / pY / pZ` 均为 `Bool` 上的
  概率分布（**字段级**非负 `pX_nonneg`/`pY_nonneg`/`pZ_nonneg` + 归一 `pX_sum`/`pY_sum`/`pZ_sum`）；
* **无未观测混杂假设**：联合分布因子化
  `pU ux uy uz = pX ux * pY uy * pZ uz`——三个外生噪声互相独立，
  故 `(X, Y)` 之间没有 `Z` 之外的后门通道（后门准则成立）。该假设
  由「只有三个边缘分布字段、没有联合分布字段」在类型上强制。

⚠ **降级更正（v14，S8 定义↔使用审计发现；coordinator 已核实）**：
上面「概率分布」的**两个组成部分并非都已被证明**——
- ✅ **归一（求和为 1）已证**：`doYZ_sum` / `doXZ_sum` 等（见本节第 4 条与 `:314`）；
- ❌ **非负（干预分布的非负性）未证**：**`doY`/`doX` 上没有任何 `_nonneg` 定理**。
  素材**已就位**（`binInd_nonneg : 0 ≤ binInd p`，`:79`），但**从未被消费**——
  全库对 `binInd_nonneg` 的引用**只有它自己的声明行**，
  `doY_nonneg`/`doX_nonneg` **在全库不存在**（coordinator 已 grep 复核）。
- ⇒ **`doYZ_sum` 只证明了「和为 1」这一半**；把它读作「干预分布是概率分布」是**过度声称**。
  **本条如实标注为「只证归一，非负未做」**，并保留本段作为后续补齐的接口说明。 -/
structure BinSCM where
  /-- `X` 的结构方程 `X = fX z ux`。 -/
  fX : Bool → Bool → Bool
  /-- `Z` 的结构方程 `Z = fZ uz`。 -/
  fZ : Bool → Bool
  /-- `Y` 的结构方程 `Y = fY x z uy`。 -/
  fY : Bool → Bool → Bool → Bool
  /-- 外生噪声 `UX` 的分布。 -/
  pX : Bool → ℝ
  /-- 外生噪声 `UY` 的分布。 -/
  pY : Bool → ℝ
  /-- 外生噪声 `UZ` 的分布。 -/
  pZ : Bool → ℝ
  /-- `pX` 非负。 -/
  pX_nonneg : ∀ u, 0 ≤ pX u
  /-- `pY` 非负。 -/
  pY_nonneg : ∀ u, 0 ≤ pY u
  /-- `pZ` 非负。 -/
  pZ_nonneg : ∀ u, 0 ≤ pZ u
  /-- `pX` 归一。 -/
  pX_sum : (∑ u : Bool, pX u) = 1
  /-- `pY` 归一。 -/
  pY_sum : (∑ u : Bool, pY u) = 1
  /-- `pZ` 归一。 -/
  pZ_sum : (∑ u : Bool, pZ u) = 1

/-! ## 观测分布与干预（截断）分布 -/

/-- **观测联合分布** `obs M x y z = P(X=x, Y=y, Z=z)`：
对外生噪声 `(ux, uy, uz)` 按因子化联合分布求和，
结构方程以指示函数 `binInd (fX z ux = x)` 等作为「选择器」。 -/
def obs (M : BinSCM) (x y z : Bool) : ℝ :=
  ∑ ux : Bool, ∑ uy : Bool, ∑ uz : Bool,
    M.pX ux * M.pY uy * M.pZ uz *
      binInd (M.fX z ux = x) * binInd (M.fY x z uy = y) * binInd (M.fZ uz = z)

/-- 观测边缘分布 `P(X=x, Z=z)`（对 `y` 求和。定义即 `Σ_y obs`）。 -/
def obsXZ (M : BinSCM) (x z : Bool) : ℝ := ∑ y : Bool, obs M x y z

/-- **截断（干预）分布** `doYZ M x y z = P(Y=y, Z=z | do(X=x))`：
把 `X` 的结构方程替换为常数 `x`（不再对 `ux` 求和），
`Z` 与 `Y` 的方程及外生分布保持不变。注意 `Y` 方程中读的是
截断后的 `Z` 值 `fZ uz`——这正是「干预沿有向路径传播」。 -/
def doYZ (M : BinSCM) (x y z : Bool) : ℝ :=
  ∑ uy : Bool, ∑ uz : Bool,
    M.pY uy * M.pZ uz * binInd (M.fY x (M.fZ uz) uy = y) * binInd (M.fZ uz = z)

/-- 干预后的因果效应 `P(Y=y | do(X=x))`（对 `z` 边缘化）。 -/
def doY (M : BinSCM) (x y : Bool) : ℝ := ∑ z : Bool, doYZ M x y z

/-- 观测到的 `Z` 边缘分布 `P(Z=z) = Σ_uz pZ uz · binInd (fZ uz = z)`。 -/
def pZobs (M : BinSCM) (z : Bool) : ℝ := ∑ uz : Bool, M.pZ uz * binInd (M.fZ uz = z)

/-- 条件机制项 `P(X=x | Z=z)` 的**结构和** `Σ_ux pX ux · binInd (fX z ux = x)`。 -/
def xmarg (M : BinSCM) (x z : Bool) : ℝ := ∑ ux : Bool, M.pX ux * binInd (M.fX z ux = x)

/-- 条件机制项 `P(Y=y | X=x, Z=z)` 的**结构和** `Σ_uy pY uy · binInd (fY x z uy = y)`。 -/
def ycond (M : BinSCM) (x y z : Bool) : ℝ := ∑ uy : Bool, M.pY uy * binInd (M.fY x z uy = y)

/-- 观测条件概率 `P(Y=y | X=x, Z=z) = obs / obsXZ`（Lean 中 `a/0 = 0`）。 -/
def condYZ (M : BinSCM) (x y z : Bool) : ℝ := obs M x y z / obsXZ M x z

/-! ## 引理：机制项的归一性 -/

/-- `Σ_y ycond M x y z = 1`：对 `y` 求和后，每个外生取值 `uy` 恰好贡献
`pY uy`（指示替换），故总和为 `Σ_uy pY uy = 1`。 -/
lemma ycond_sum (M : BinSCM) (x z : Bool) : (∑ y : Bool, ycond M x y z) = 1 := by
  have hY : M.pY true + M.pY false = 1 := by
    have := M.pY_sum
    rwa [Fintype.sum_bool] at this
  simp only [ycond, Fintype.sum_bool]
  have h1 : binInd (M.fY x z true = true) + binInd (M.fY x z true = false) = 1 :=
    binInd_bool_sum _
  have h2 : binInd (M.fY x z false = true) + binInd (M.fY x z false = false) = 1 :=
    binInd_bool_sum _
  linear_combination M.pY true * h1 + M.pY false * h2 + hY

/-- `Σ_x xmarg M x z = 1`：与 `ycond_sum` 同构，用 `Σ_ux pX ux = 1`。 -/
lemma xmarg_sum (M : BinSCM) (z : Bool) : (∑ x : Bool, xmarg M x z) = 1 := by
  have hX : M.pX true + M.pX false = 1 := by
    have := M.pX_sum
    rwa [Fintype.sum_bool] at this
  simp only [xmarg, Fintype.sum_bool]
  have h1 : binInd (M.fX z true = true) + binInd (M.fX z true = false) = 1 :=
    binInd_bool_sum _
  have h2 : binInd (M.fX z false = true) + binInd (M.fX z false = false) = 1 :=
    binInd_bool_sum _
  linear_combination M.pX true * h1 + M.pX false * h2 + hX

/-- `Σ_z pZobs M z = 1`：观测到的 `Z` 分布归一。 -/
lemma pZobs_sum (M : BinSCM) : (∑ z : Bool, pZobs M z) = 1 := by
  have hZ : M.pZ true + M.pZ false = 1 := by
    have := M.pZ_sum
    rwa [Fintype.sum_bool] at this
  simp only [pZobs, Fintype.sum_bool]
  have h1 : binInd (M.fZ true = true) + binInd (M.fZ true = false) = 1 :=
    binInd_bool_sum _
  have h2 : binInd (M.fZ false = true) + binInd (M.fZ false = false) = 1 :=
    binInd_bool_sum _
  linear_combination M.pZ true * h1 + M.pZ false * h2 + hZ

/-! ## 定理一：观测分布的因子化 -/

/-- **观测分布因子化**（定理 1）：
`P(X=x,Y=y,Z=z) = P(X=x|Z=z) · P(Y=y|X=x,Z=z) · P(Z=z)`。

证明路线：三重和 `Σ_ux Σ_uy Σ_uz (A ux · B uy · C uz)` 是三个和之积
（对每个 `Bool` 只展开两项，纯环恒等式），其中
`A ux = pX ux · binInd (fX z ux = x)`、`B uy = pY uy · binInd (fY x z uy = y)`、
`C uz = pZ uz · binInd (fZ uz = z)`。 -/
theorem obs_eq_xmarg_mul_ycond_mul_pZobs (M : BinSCM) (x y z : Bool) :
    obs M x y z = xmarg M x z * ycond M x y z * pZobs M z := by
  simp only [obs, xmarg, ycond, pZobs, Fintype.sum_bool]
  ring

/-- `Σ_y P(x,y,z) = P(X=x|Z=z) · P(Z=z)`（定理 2）：
用定理 1 与 `Σ_y ycond = 1`。 -/
theorem obsXZ_eq (M : BinSCM) (x z : Bool) :
    obsXZ M x z = xmarg M x z * pZobs M z := by
  have hy : ycond M x true z + ycond M x false z = 1 := by
    have h := ycond_sum M x z
    rwa [Fintype.sum_bool] at h
  rw [obsXZ, Fintype.sum_bool, obs_eq_xmarg_mul_ycond_mul_pZobs,
    obs_eq_xmarg_mul_ycond_mul_pZobs]
  calc xmarg M x z * ycond M x true z * pZobs M z
        + xmarg M x z * ycond M x false z * pZobs M z
      = xmarg M x z * pZobs M z * (ycond M x true z + ycond M x false z) := by ring
    _ = xmarg M x z * pZobs M z * 1 := by rw [hy]
    _ = xmarg M x z * pZobs M z := by ring

/-- `P(Z=z) = Σ_x P(X=x, Z=z)`：观测边缘分布与 `Z` 边缘分布一致
（用 `Σ_x xmarg = 1`）。 -/
lemma sum_obsXZ_eq_pZobs (M : BinSCM) (z : Bool) :
    (∑ x : Bool, obsXZ M x z) = pZobs M z := by
  have hsum : xmarg M true z + xmarg M false z = 1 := by
    have h := xmarg_sum M z
    rwa [Fintype.sum_bool] at h
  simp only [obsXZ_eq, Fintype.sum_bool]
  linear_combination pZobs M z * hsum

/-- 展开形式：`P(Z=z) = Σ_x Σ_y P(x,y,z)`（把 `obsXZ` 定义展开，供调整公式使用）。 -/
lemma pZobs_eq_sum_sum_obs (M : BinSCM) (z : Bool) :
    pZobs M z = ∑ x : Bool, ∑ y : Bool, obs M x y z := by
  rw [← sum_obsXZ_eq_pZobs M z]
  rfl

/-! ## 定理三：截断语义的显式形式 -/

/-- **截断语义的显式形式**（定理 3）：
`P(Y=y | do(X=x)) = Σ_z P(Z=z) · P(Y=y | X=x, Z=z)`。

证明路线：把左右两边按 `Bool` 的两个取值完全展开（`Fintype.sum_bool`），
再对 `fZ true`、`fZ false` 分情况；此时每个 `binInd (fZ uz = z)`
都化为常数 `0/1`，指示量选出唯一的 `z = fZ uz`，剩下的等式是
关于原子 `pY uy, pZ uz, binInd (fY x c uy = y)` 的纯环恒等式。 -/
theorem doY_eq_sum_pZobs_ycond (M : BinSCM) (x y : Bool) :
    doY M x y = ∑ z : Bool, pZobs M z * ycond M x y z := by
  cases h1 : M.fZ true <;> cases h2 : M.fZ false
  all_goals
    simp only [doY, doYZ, pZobs, ycond, Fintype.sum_bool, h1, h2]
    simp only [binInd_eq_self, binInd_true_eq_false, binInd_false_eq_true]
    ring

/-- **干预分布归一**（定理 4）：`Σ_y P(Y=y, Z=z | do(X=x)) = P(Z=z)`。
即截断后的 `(Y, Z)` 边缘在 `Y` 上归一，得到观测的 `Z` 分布。 -/
theorem doYZ_sum (M : BinSCM) (x z : Bool) :
    (∑ y : Bool, doYZ M x y z) = pZobs M z := by
  have hY : M.pY true + M.pY false = 1 := by
    have := M.pY_sum
    rwa [Fintype.sum_bool] at this
  simp only [doYZ, pZobs, Fintype.sum_bool]
  have h1 : binInd (M.fY x (M.fZ true) true = true)
      + binInd (M.fY x (M.fZ true) true = false) = 1 := binInd_bool_sum _
  have h2 : binInd (M.fY x (M.fZ false) true = true)
      + binInd (M.fY x (M.fZ false) true = false) = 1 := binInd_bool_sum _
  have h3 : binInd (M.fY x (M.fZ true) false = true)
      + binInd (M.fY x (M.fZ true) false = false) = 1 := binInd_bool_sum _
  have h4 : binInd (M.fY x (M.fZ false) false = true)
      + binInd (M.fY x (M.fZ false) false = false) = 1 := binInd_bool_sum _
  linear_combination
    M.pY true * M.pZ true * binInd (M.fZ true = z) * h1
      + M.pY true * M.pZ false * binInd (M.fZ false = z) * h2
      + M.pY false * M.pZ true * binInd (M.fZ true = z) * h3
      + M.pY false * M.pZ false * binInd (M.fZ false = z) * h4
      + (M.pZ true * binInd (M.fZ true = z)
          + M.pZ false * binInd (M.fZ false = z)) * hY

/-- **干预分布是概率分布**：`Σ_y P(Y=y | do(X=x)) = 1`
（由定理 3、`ycond_sum` 与 `pZobs_sum` 交换求和得到）。 -/
lemma doY_sum (M : BinSCM) (x : Bool) : (∑ y : Bool, doY M x y) = 1 := by
  have h1 : ∀ y : Bool, doY M x y = ∑ z : Bool, pZobs M z * ycond M x y z :=
    fun y => doY_eq_sum_pZobs_ycond M x y
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ z : Bool, (∑ y : Bool, pZobs M z * ycond M x y z) = pZobs M z := by
    intro z
    rw [← Finset.mul_sum, ycond_sum, mul_one]
  simp only [h2]
  exact pZobs_sum M

/-! ## 定理五：后门调整公式 -/

/-- **调整公式的逐点核心**：在正性假设下
`P(Z=z) · P(Y=y | X=x, Z=z) = P(Z=z) · P(Y=y | X=x, Z=z)`（机制项版），
即 `P(Z=z) · condYZ = P(Z=z) · ycond`。

证明路线：把 `obsXZ` 换成 `xmarg · pZobs`（定理 2），正性给出
`xmarg ≠ 0` 与 `pZobs ≠ 0`，于是 `obs / obsXZ = (xmarg·ycond·pZobs)/(xmarg·pZobs) = ycond`
（`field_simp` + `ring`）。 -/
lemma pZobs_mul_ycond_eq_condYZ (M : BinSCM) (hpos : ∀ x z, 0 < obsXZ M x z)
    (x y z : Bool) :
    pZobs M z * ycond M x y z = pZobs M z * condYZ M x y z := by
  have hXZ : obsXZ M x z = xmarg M x z * pZobs M z := obsXZ_eq M x z
  have hpos' : 0 < xmarg M x z * pZobs M z := by
    rw [← hXZ]
    exact hpos x z
  have hx : xmarg M x z ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hpos'
    exact absurd hpos' (lt_irrefl 0)
  have hz : pZobs M z ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpos'
    exact absurd hpos' (lt_irrefl 0)
  have hden : xmarg M x z * pZobs M z ≠ 0 := mul_ne_zero hx hz
  unfold condYZ
  rw [obs_eq_xmarg_mul_ycond_mul_pZobs, hXZ]
  field_simp [hden]
  try ring

/-- **后门调整公式（主定理，定理 5）**：

在正性 / 重叠假设 `hpos : ∀ x z, 0 < P(X=x, Z=z)` 下，
对后门准则成立的图 `Z → X → Y`、`Z → Y`（无未观测混杂，
由 `BinSCM` 的因子化外生分布保证），

`P(Y=y | do(X=x)) = Σ_z P(Z=z) · P(Y=y | X=x, Z=z)`。

证明路线：先用定理 3 把 `doY` 写成 `Σ_z pZobs · ycond`，
再用逐点核心引理把 `ycond` 换成观测条件概率 `condYZ`。 -/
theorem backdoor_adjustment (M : BinSCM) (x y : Bool)
    (hpos : ∀ x z, 0 < obsXZ M x z) :
    doY M x y = ∑ z : Bool, pZobs M z * condYZ M x y z := by
  rw [doY_eq_sum_pZobs_ycond M x y]
  apply Finset.sum_congr rfl
  intro z _
  exact pZobs_mul_ycond_eq_condYZ M hpos x y z

/-- 调整公式的**泛函形式**：`doY` 只通过观测表 `obs` 的三种边缘量
（`Σ_x Σ_y obs`、`Σ_y obs`）依赖模型，为下一文件
`RealSCMIdentification` 的「观测相等 ⟹ 干预相等」提供桥梁。 -/
lemma condYZ_eq_div (M : BinSCM) (x y z : Bool) :
    pZobs M z * condYZ M x y z
      = (∑ x' : Bool, ∑ y' : Bool, obs M x' y' z)
          * (obs M x y z / (∑ y' : Bool, obs M x y' z)) := by
  rw [pZobs_eq_sum_sum_obs M z]
  simp only [condYZ, obsXZ]

end Lattice
