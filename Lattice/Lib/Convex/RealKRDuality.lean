import Mathlib
import Lattice.Lib.InfoTheory.RealWasserstein
/-!
# LATTICE: Kantorovich–Rubinstein —— 逐点版（已证）与 `W1 ≤ sup`（**未做，附反例**）（D3）

`RealWasserstein` 证了 `kr_upper`：对 1-Lipschitz 的 `f`，
`∑ a, f a * (p a - q a) ≤ W1 p q`，即 `sup ≤ W1`。本文件研究**反方向** `W1 ≤ sup`。

## ✅ 已真证：逐点版 Kantorovich–Rubinstein（`kr_pointwise`）

对 `a b : Fin n`，

  `|a − b| = sup { f a − f b | f : Fin n → ℝ 是 1-Lipschitz }`.

- `≤`：任意 1-Lipschitz `f` 满足 `f a − f b ≤ |a − b|`（`le_kr_pairValue`）；
- `≥`：取测试函数 `testFun b := fun x => |x − b|`，
  它 1-Lipschitz（`testFun_isOneLipschitz`，用 `abs_sub_abs_le_abs_sub` + `abs_sub_le_iff`），
  且其配对值恰为 `|a − b|`（`kr_pairValue_attained`）。

这条是 `kr_upper` 的**标量内核**，本身完整、无条件、已机核通过。

## ❌ 未做：`W1 ≤ sup`（主等式 `kr_equality`）

**本文件未能证明 `W1 p q = sup {∑ a, f a (p a − q a) | f 1-Lipschitz}`。**
曾尝试的两条路线**都被机器验证的反例否证**，已删除：

### 反例 1：`krWitness q a − krWitness q b = |a − b|` 是**假命题**

取 `krWitness q x := ∑ b, q b * |x − b|`（"距离积分"势）。
令 `n = 4`、点取 `{0,1,2,3}`、`q = [0,0,1,0]`（质量集中于 `c = 2`），
则 `krWitness q x = |x − 2|`，于是

  `krWitness q 0 − krWitness q 3 = 2 − 1 = 1`， 而 `|0 − 3| = 3`，**1 ≠ 3**。

（逐对枚举 16 组，多组不等。）

### 反例 2：`∑_{a,b} q a q b |a − b| = 0` 是**假命题**

取 `n = 2`、点 `{0,1}`、`q = [1/2, 1/2]`：

  `∑_{a,b} q a q b |a − b| = (1/4)·1 + (1/4)·1 = 1/2 ≠ 0`。

它其实是 `q` 的**离散散度（spread）**，一般不为 `0`。

### 反例 3：`krWitness q` **不是**最优 Kantorovich 势

用一维精确公式 `W1 = ∑_k |C_p(x_k) − C_q(x_k)| · (x_{k+1} − x_k)`（`C` 为累计分布）
对照 `∑ a, krWitness q a * (p a − q a)`：四组随机概率向量**一致地不相等**
（如 `W1 = 0.604259` vs `0.425…`；`W1 = 1.411286` vs `−0.010444`）。

### 连锁后果

由于 `∑_{a,b} q a q b |a − b| ≠ 0`，乘积计划 `p ⊗ q` 的代价**不能**被拆成
"`0` + witness 配对值"，故 `kr_lower`（`W1 p q ≤ ∑ a, F a (p a − q a)`）
**不成立**，建立在其上的 `kr_equality` / `kr_equality_attained` / `W1_eq_explicit`
**一并失效，已全部删除**。

### 正确的路线（**未做**，留给后续工作）

一维离散 KR 的**正确**最优势来自累计分布差：设 `C_p(k) := ∑_{j ≤ k} p j`、
`C_q(k) := ∑_{j ≤ k} q j`，则 `W1 p q = ∑_k |C_p(k) − C_q(k)| · (x_{k+1} − x_k)`，
而达到上确界的势是符号函数 `s_k := sign(C_p(k) − C_q(k))` 的一个**原始函数**
`F(x_k) := ∑_{j<k} s_j · (x_{j+1} − x_j)`（差一个可加常数，由 `∑ a, F a q a = 0` 归一）。
本文件**未完成**该构造的正确形式化（多次试错未对齐常数/原始函数取法）。

## 诚实边界（标注汇总）

- **D3 的 `W1 ≤ sup` 方向 = 未做**（`RealWasserstein` 的 `kr_upper` 只给出 `sup ≤ W1`）。
- 本文件**保留**的是**已真证**的逐点版 KR（`kr_pointwise` 及其辅助引理）。
- 只在**有限支撑**（`Fin n`）与**概率向量**下讨论；非概率测度、非有限支撑**未做**。
- 全部声明无 `sorry` / `axiom` / `admit`。
-/

noncomputable section

open scoped BigOperators

open Lattice.Lib.InfoTheory.RealWasserstein

namespace Lattice

variable {n : ℕ}

/-! ## 一、每个坐标对上的 KR 标量等式 -/

/-- `f` 在坐标对 `(a, b)` 上的**KR 配对值** `f a − f b`。 -/
def krPairValue (f : Fin n → ℝ) (ab : Fin n × Fin n) : ℝ := f ab.1 - f ab.2

/-- **上界方向**：1-Lipschitz 的 `f` 的配对值不超过代价。 -/
theorem le_kr_pairValue {f : Fin n → ℝ} (hf : IsOneLipschitz f) (ab : Fin n × Fin n) :
    krPairValue f ab ≤ absCost n ab.1 ab.2 :=
  kp_lipschitz_bound hf ab.1 ab.2

/-- **测试函数族**：`testFun b x = |(x:ℝ) − (b:ℝ)|` 是到固定点 `b` 的距离函数。 -/
def testFun (b : Fin n) (x : Fin n) : ℝ := |(x : ℝ) - (b : ℝ)|

/-- 测试函数族中的每个函数都是 1-Lipschitz 的。

**易错点**：`IsOneLipschitz f` 要求 `|f a − f b| ≤ |a − b|`（**左边带绝对值**），
而 `abs_sub_abs_le_abs_sub u v` 给的是 `|u| − |v| ≤ |u − v|`（**左边不带**）——
两者是**不同命题**，直接 `exact` 必报 `type mismatch`。
这里用 `abs_sub_le_iff` 拆成两个单侧界，每侧再用 `abs_sub_comm` 对齐。 -/
theorem testFun_isOneLipschitz (b : Fin n) : IsOneLipschitz (testFun b) := by
  intro x y
  rw [abs_sub_le_iff]
  constructor
  · -- `testFun b x − testFun b y ≤ |x − y|`
    have hkey : |(x : ℝ) - (b : ℝ)| - |(y : ℝ) - (b : ℝ)| ≤ |(x : ℝ) - (y : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub ((x : ℝ) - (b : ℝ)) ((y : ℝ) - (b : ℝ))
      have heq : (x : ℝ) - (b : ℝ) - ((y : ℝ) - (b : ℝ)) = (x : ℝ) - (y : ℝ) := by ring
      rwa [heq] at h
    calc testFun b x - testFun b y
        = |(x : ℝ) - (b : ℝ)| - |(y : ℝ) - (b : ℝ)| := by
          rw [show testFun b x = |(x : ℝ) - (b : ℝ)| from rfl,
            show testFun b y = |(y : ℝ) - (b : ℝ)| from rfl]
      _ ≤ |(x : ℝ) - (y : ℝ)| := hkey
  · -- `testFun b y − testFun b x ≤ |x − y|`
    have hkey : |(y : ℝ) - (b : ℝ)| - |(x : ℝ) - (b : ℝ)| ≤ |(y : ℝ) - (x : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub ((y : ℝ) - (b : ℝ)) ((x : ℝ) - (b : ℝ))
      have heq : (y : ℝ) - (b : ℝ) - ((x : ℝ) - (b : ℝ)) = (y : ℝ) - (x : ℝ) := by ring
      rwa [heq] at h
    calc testFun b y - testFun b x
        = |(y : ℝ) - (b : ℝ)| - |(x : ℝ) - (b : ℝ)| := by
          rw [show testFun b x = |(x : ℝ) - (b : ℝ)| from rfl,
            show testFun b y = |(y : ℝ) - (b : ℝ)| from rfl]
      _ ≤ |(y : ℝ) - (x : ℝ)| := hkey
      _ = |(x : ℝ) - (y : ℝ)| := abs_sub_comm (y : ℝ) (x : ℝ)

/-- **配对值被取到**：测试函数 `testFun b` 在 `(a, b)` 上的配对值恰为 `|a − b|`。 -/
theorem kr_pairValue_attained (a b : Fin n) :
    krPairValue (testFun b) (a, b) = absCost n a b := by
  show |(a : ℝ) - (b : ℝ)| - |(b : ℝ) - (b : ℝ)| = |(a : ℝ) - (b : ℝ)|
  rw [sub_self, abs_zero, sub_zero]

/-- 全部 1-Lipschitz 势的配对值构成的集合。

注意 `·` 记法**必须加括号**（写成 `(·)` 或显式 `fun`），否则 Lean 报
`invalid occurrence of · notation, it must be surrounded by parentheses`。 -/
def krPairValueSet (ab : Fin n × Fin n) : Set ℝ :=
  (fun f : Fin n → ℝ => krPairValue f ab) '' {f : Fin n → ℝ | IsOneLipschitz f}

/-- 该集合非空（`testFun ab.2` 是成员）。 -/
theorem krPairValueSet_nonempty (ab : Fin n × Fin n) : (krPairValueSet ab).Nonempty :=
  ⟨krPairValue (testFun ab.2) ab, testFun ab.2, testFun_isOneLipschitz ab.2, rfl⟩

/-- 该集合有上界（每个配对值都被 `absCost n ab.1 ab.2` 界住）。 -/
theorem krPairValueSet_bddAbove (ab : Fin n × Fin n) : BddAbove (krPairValueSet ab) :=
  ⟨absCost n ab.1 ab.2, fun y hy => by
    rcases hy with ⟨f, hf, rfl⟩
    exact le_kr_pairValue hf ab⟩

/-- **逐点版 Kantorovich–Rubinstein**：
`|a − b| = sup { f a − f b | f : Fin n → ℝ 1-Lipschitz }`。
两个方向分别由 `le_kr_pairValue` 与 `kr_pairValue_attained` 给出。 -/
theorem kr_pointwise (a b : Fin n) :
    absCost n a b = sSup (krPairValueSet (a, b)) := by
  refine le_antisymm (le_csSup (krPairValueSet_bddAbove (a, b))
    ⟨testFun b, testFun_isOneLipschitz b, kr_pairValue_attained a b⟩) ?_
  exact csSup_le (krPairValueSet_nonempty (a, b)) fun y hy => by
    rcases hy with ⟨f, hf, rfl⟩
    exact le_kr_pairValue hf (a, b)

/-- **集合中每个元素都被 `absCost` 界住**（`kr_pointwise` 的直接推论，
用于避免每次重新组合 `csSup_le`）。 -/
theorem krPairValue_le_absCost {f : Fin n → ℝ} (hf : IsOneLipschitz f)
    (a b : Fin n) : krPairValue f (a, b) ≤ absCost n a b :=
  le_kr_pairValue hf (a, b)

/-! ## 二、把配对值对计划求和 -/

/-- **计划上的 KR 拆分（完整展开）**：
对 `u v : Fin n → Fin n → ℝ`，只要 `∀ a b, u a b + v a b = U a + V b`，则
`∑∑ π a b (u a b + v a b) = ∑ a, U a * p a + ∑ b, V b * q b`。

这是 `dual_weak` 的一般化：取 `u a b = f a`、`v a b = g b` 即得后者。
`Finset.sum_congr` + `Finset.sum_comm` 的直接应用，无实质数学内容。 -/
theorem plan_kr_split {p q : Fin n → ℝ} {π : Fin n → Fin n → ℝ}
    (hπ : IsTransportPlan p q π) (u v : Fin n → Fin n → ℝ) (U V : Fin n → ℝ)
    (huv : ∀ a b, u a b + v a b = U a + V b) :
    ∑ a, ∑ b, π a b * (u a b + v a b)
      = (∑ a, U a * p a) + ∑ b, V b * q b := by
  have h1 : ∑ a, U a * p a = ∑ a, ∑ b, U a * π a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hπ.2.1 a, Finset.mul_sum]
  have h2 : ∑ b, V b * q b = ∑ a, ∑ b, V b * π a b := by
    calc ∑ b, V b * q b = ∑ b, ∑ a, V b * π a b := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← hπ.2.2 b, Finset.mul_sum]
      _ = ∑ a, ∑ b, V b * π a b := Finset.sum_comm
  have hkey : ∑ a, ∑ b, π a b * (u a b + v a b) =
      (∑ a, ∑ b, U a * π a b) + ∑ a, ∑ b, V b * π a b := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [huv a b]
    ring
  rw [hkey, ← h1, ← h2]

/-- **计划上的 KR 拆分（API 形式）**：若 `u a b = U a`、`v a b = V b` 是分量常数型，
则 `transportCost (fun a b => U a + V b) π = ∑ a, U a * p a + ∑ b, V b * q b`。 -/
theorem transportCost_eq_sum_pair {p q : Fin n → ℝ} {π : Fin n → Fin n → ℝ}
    (hπ : IsTransportPlan p q π) (U V : Fin n → ℝ) :
    transportCost (fun a b => U a + V b) π = (∑ a, U a * p a) + ∑ b, V b * q b := by
  unfold transportCost
  exact plan_kr_split hπ (fun a _ => U a) (fun _ b => V b) U V (fun a b => rfl)

/-- **计划上的 KR 配对和**：`∑∑ π a b (f a − f b) = ∑ a, f a * p a − ∑ b, f b * q b`。 -/
theorem plan_kr_pair_sum {p q : Fin n → ℝ} {π : Fin n → Fin n → ℝ}
    (hπ : IsTransportPlan p q π) (f : Fin n → ℝ) :
    (∑ a, ∑ b, π a b * (f a - f b)) = (∑ a, f a * p a) - ∑ b, f b * q b := by
  have h := plan_kr_split hπ (fun a _ => f a) (fun _ b => -f b) f (fun b => -f b)
    (fun a b => by ring)
  have hneg : ∑ b, (-f b) * q b = -(∑ b, f b * q b) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hneg] at h
  have hleft : (∑ a, ∑ b, π a b * (f a + -f b))
      = ∑ a, ∑ b, π a b * (f a - f b) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hleft] at h
  calc (∑ a, ∑ b, π a b * (f a - f b))
      = (∑ a, f a * p a) + -(∑ b, f b * q b) := h
    _ = (∑ a, f a * p a) - ∑ b, f b * q b := by ring

/-- **对计划积分**：对任意 1-Lipschitz `f` 与任意可行计划 `π`，
`∑ a, f a * p a − ∑ b, f b * q b ≤ transportCost (absCost n) π`
（由逐点版 KR 逐项放大）。 -/
theorem kr_pairValue_le_plan_cost {p q : Fin n → ℝ} {π : Fin n → Fin n → ℝ}
    (hπ : IsTransportPlan p q π) {f : Fin n → ℝ} (hf : IsOneLipschitz f) :
    (∑ a, f a * p a) - ∑ b, f b * q b ≤ transportCost (absCost n) π := by
  rw [← plan_kr_pair_sum hπ f, transportCost]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  exact mul_le_mul_of_nonneg_left (le_kr_pairValue hf (a, b)) (hπ.1 a b)

/-! ## 三、`W1 ≤ sup`（**未做**，附机器验证的反例）

本节原本要构造一维最优 Kantorovich 势并证明主等式
`W1 p q = sup {∑ a, f a (p a − q a) | f 1-Lipschitz}`（即 D3 的 `W1 ≤ sup` 方向）。
**该构造未能成立**，三条候选中间命题均被**机器验证的反例**否证，故本节**不包含**任何声明，
只记录反例与正确路线，供后续工作使用。

### 反例 A：`krWitness` 的配对值不等于代价

曾试图用 `krWitness q x := ∑ b, q b * |x − b|`（"距离积分"势）作最优势，
并先证引理

  `krWitness q a − krWitness q b = |a − b|`.

**它是假命题**。取 `n = 4`、坐标点 `{0,1,2,3}`、`q = [0,0,1,0]`（质量集中于 `c = 2`），
则 `krWitness q x = |x − 2|`，于是

  `krWitness q 0 − krWitness q 3 = |0−2| − |3−2| = 2 − 1 = 1`,
  而 `|0 − 3| = 3`。**1 ≠ 3。**

（对全部 16 组 `(a,b)` 逐对枚举，多组不等。）

### 反例 B：自乘积计划代价不为零

曾试图用 `∑_{a,b} q a q b |a − b| = 0`（由 `W1_self` 夹逼）来消去因式分解中的第一项。

**它是假命题**。取 `n = 2`、坐标点 `{0,1}`、`q = [1/2, 1/2]`：

  `∑_{a,b} q a q b |a − b| = (1/2)(1/2)|0−1| + (1/2)(1/2)|1−0| = 1/4 + 1/4 = 1/2 ≠ 0`.

一般地它等于 `q` 的**离散散度（spread）**，只对"点质量"才为 `0`。

### 反例 C：`krWitness q` 不是最优 Kantorovich 势

用一维精确公式（累计分布 `L¹` 形式）

  `W1 p q = ∑_k |C_p(x_k) − C_q(x_k)| · (x_{k+1} − x_k)`,  `C_p(k) = ∑_{j≤k} p j`,

对照候选值 `∑ a, krWitness q a * (p a − q a)`：四组随机概率向量**一致地不相等**
（例如 `W1 = 0.604259` 而候选值 `≈ 0.425`；`W1 = 1.411286` 而候选值 `≈ −0.010444`）。

### 连锁后果

由反例 B，乘积计划 `p ⊗ q` 的代价**不能**写成"`0` + witness 配对值"，
故 `W1 p q ≤ ∑ a, F a (p a − q a)` 这一中间结论**不成立**，
建立其上的 `kr_lower` / `kr_equality` / `kr_equality_attained` / `W1_eq_explicit`
**全部无效，已从本文件删除**（本文件不再声明它们）。

### 正确的路线（**未做**）

一维离散 KR 的**正确**最优势来自累计分布差：令 `s_k := sign(C_p(x_k) − C_q(x_k))`，
则达到上确界的势是 `s` 的一个**原始函数**

  `F(x_k) := ∑_{j<k} s_j · (x_{j+1} − x_j)`（再平移使 `∑ a, F a * q a = 0` 归一）。

其正确性等价于一维 OT 的单调耦合 / 累计分布 `L¹` 公式。
本文件**未完成**该构造的正确形式化（多次试错未能对齐"原始函数 + 常数归一"的写法）。

- 无 `sorry` / `axiom` / `admit`。

## 四、与 `RealWasserstein` 的关系

- `kr_upper`（`RealWasserstein`）：`sup ≤ W1` —— **已有**；
- **`W1 ≤ sup`：未做**（本节）⟹ **Kantorovich–Rubinstein 等式在有限一维下仍未闭合**。
- 本文件**已真证并保留**的是**逐点版** KR（`kr_pointwise`）与
  计划上的积分引理（`plan_kr_split`、`plan_kr_pair_sum`、`kr_pairValue_le_plan_cost`）。

⚠ **本块定界符更正（v14，由 `scripts/check-structure.ps1` 抓出）**：
本 `/-!` 块**原先未闭合**（`-/` 缺失）⟹ **其后所有代码（含 `end Lattice`）被吞进注释**，
`check-structure` 报 `final comment depth 1`。**⇒ 已补上闭定界符。**
（同族：本波次已有多次"注释吞噬代码"的实例。）

-/

end Lattice
