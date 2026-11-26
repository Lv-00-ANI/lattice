import Mathlib
import Lattice.Core.VariableNet
import Lattice.Core.VariableActLayer
import Lattice.Core.AnalysisHelper
import Lattice.Core.RepairModule.VariableDerivativeQuadratic

/-!
# `VariableDerivativeDegree`

**3/4：参数次数的正确载体 `MvPolynomial`。**

**⇒ 自 2,663–4,196 行。**
-/

namespace Lattice.Core


/-! ## ⭐⭐⭐ 参数次数的正确载体：`MvPolynomial`

## 为什么第 5 轮把问题推到这里

**`LowDeg` 阶梯在第 5 轮可证明地终止了：归纳步需要 `t` 的【平移不变性】，
而 `LowDeg` 不是平移不变的。**

**⇒ 正确的载体是把输出看成参数向量 `g : Fin N → ℝ` 的【多变量多项式】，
次数取 `totalDegree`。**

**⚠ `totalDegree` 对参数平移【显然**不变（多项式本身不变），
**所以第 5 轮的障碍在这个载体上根本不会出现。`totalDegree_mul` 已核实存在。**

## 本节给出形状

**对宽 1 的单层，显式写出那个多项式并证其次数 ≤ 1。**

**⚠ 一般深度的归纳仍未做——但载体现在是对的。** -/

/-- **宽 1、单层的输出作为参数 `g : Fin N → ℝ` 的多项式**：
**`X 0 · x₀ + X 1`**（`X 0` 是权重槽位，`X 1` 是偏置槽位）。 -/
noncomputable def oneLayerParamPoly (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ) :
    MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X ⟨0, h0⟩ * MvPolynomial.C x0 + MvPolynomial.X ⟨1, h1⟩

/-- ⭐⭐ **单层多项式求值等于该层的计算**——**载体与网络一致。** -/
theorem oneLayerParamPoly_eval (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ)
    (g : Fin N → ℝ) :
    (oneLayerParamPoly N h0 h1 x0).eval g = g ⟨0, h0⟩ * x0 + g ⟨1, h1⟩ := by
  simp only [oneLayerParamPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- ⭐⭐ **单层多项式的次数 ≤ 1**——**「深度 1 ⟹ 参数次数 ≤ 1」的载体形式。** -/
theorem oneLayerParamPoly_degree_le (N : ℕ) (h0 : 0 < N) (h1 : 1 < N) (x0 : ℝ) :
    (oneLayerParamPoly N h0 h1 x0).totalDegree ≤ 1 := by
  have hm : (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
      : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ (MvPolynomial.X (⟨0, h0⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
        + (MvPolynomial.C x0 : MvPolynomial (Fin N) ℝ).totalDegree :=
    MvPolynomial.totalDegree_mul _ _
  have hx : (MvPolynomial.X (⟨0, h0⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  have hc : (MvPolynomial.C x0 : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C x0
  have hy : (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [oneLayerParamPoly]
  calc (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ max (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
            : MvPolynomial (Fin N) ℝ).totalDegree
          (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 1 := by
        rw [max_le_iff]
        constructor
        · omega
        · omega


/-- **宽 1、两层的输出作为参数的多项式**：
**`X 2 · (X 0 · x₀ + X 1) + X 3`**
（第 1 层用槽位 `0`/`1`，第 2 层用 `2`/`3`）。 -/
noncomputable def twoLayerParamPoly (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) : MvPolynomial (Fin N) ℝ :=
  MvPolynomial.X ⟨2, h2⟩
    * (MvPolynomial.X ⟨0, h0⟩ * MvPolynomial.C x0 + MvPolynomial.X ⟨1, h1⟩)
    + MvPolynomial.X ⟨3, h3⟩

/-- ⭐⭐ **两层多项式求值等于该链的计算**——**与第 188 轮的显式形式一致。** -/
theorem twoLayerParamPoly_eval (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) (g : Fin N → ℝ) :
    (twoLayerParamPoly N h0 h1 h2 h3 x0).eval g
      = g ⟨2, h2⟩ * (g ⟨0, h0⟩ * x0 + g ⟨1, h1⟩) + g ⟨3, h3⟩ := by
  simp only [twoLayerParamPoly, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, MvPolynomial.eval_C]

/-- ⭐⭐ **一次式乘常数仍是一次**——**归纳步的基础。** -/
theorem totalDegree_X_mul_C_le (N : ℕ) (s : Fin N) (c : ℝ) :
    (MvPolynomial.X s * MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
  have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X s : MvPolynomial (Fin N) ℝ)
    (MvPolynomial.C c : MvPolynomial (Fin N) ℝ)
  have hx : (MvPolynomial.X s : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  have hc : (MvPolynomial.C c : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C c
  omega

/-- ⭐⭐⭐ **两层多项式的次数 ≤ 2**——**「深度 2 ⟹ 参数次数 ≤ 2」的载体形式。** -/
theorem twoLayerParamPoly_degree_le (N : ℕ) (h0 : 0 < N) (h1 : 1 < N)
    (h2 : 2 < N) (h3 : 3 < N) (x0 : ℝ) :
    (twoLayerParamPoly N h0 h1 h2 h3 x0).totalDegree ≤ 2 := by
  -- 内层：X 0 · x₀ + X 1 的次数 ≤ 1
  have hinner : (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 1 := by
    calc (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
        ≤ max (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
              : MvPolynomial (Fin N) ℝ).totalDegree
            (MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
          rw [max_le_iff]
          exact ⟨totalDegree_X_mul_C_le N _ x0, by simp⟩
  -- 外层：X 2 · 内层 的次数 ≤ 2
  have hprod : (MvPolynomial.X (⟨2, h2⟩ : Fin N)
        * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N)) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 2 := by
    have hm := MvPolynomial.totalDegree_mul (MvPolynomial.X (⟨2, h2⟩ : Fin N)
      : MvPolynomial (Fin N) ℝ)
      (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
        + MvPolynomial.X (⟨1, h1⟩ : Fin N) : MvPolynomial (Fin N) ℝ)
    have hx : (MvPolynomial.X (⟨2, h2⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X _
    omega
  rw [twoLayerParamPoly]
  calc (MvPolynomial.X (⟨2, h2⟩ : Fin N)
        * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
          + MvPolynomial.X (⟨1, h1⟩ : Fin N))
        + MvPolynomial.X (⟨3, h3⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
      ≤ max (MvPolynomial.X (⟨2, h2⟩ : Fin N)
            * (MvPolynomial.X (⟨0, h0⟩ : Fin N) * MvPolynomial.C x0
              + MvPolynomial.X (⟨1, h1⟩ : Fin N)) : MvPolynomial (Fin N) ℝ).totalDegree
          (MvPolynomial.X (⟨3, h3⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
        rw [max_le_iff]
        exact ⟨hprod, by simp⟩


/-! ## ⚠⚠ 第 8 轮：链层递归的障碍记录（未完成）

## 目标

**把第 7 轮的 `twoLayerParamPoly` 推广成对 `Chain` 的递归：
`chainPoly ch off h x` 给出整条宽 1 链的输出多项式，并证 `totalDegree ≤ chainDepth ch`。**

## 数学上它是对的，而且很简单

**宽 1 时不需要多项式【代入】**：**每一层只是「乘一个变量、加一个变量」，输入 `x` 是标量常数。**
**⇒ 递归是纯乘加：**

    chainPoly (.idf _)     off x = C x
    chainPoly (.cons l ch) off x = X off · chainPoly ch (off+2) x + X (off+1)

**核对**：**`Φ_1 = X 0 · C x + X 1`，`Φ_2 = X 2 · Φ_1 + X 3`——展开正是第 188 轮的形式。✓**

**⇒ 次数归纳只需 `totalDegree_mul`（相加）与 `totalDegree_add`（取 max），两者都已核实存在。**

## 实际卡住的地方（Lean 工程问题，不是数学问题）

**1. 递归的度量**：`off` 每层加 2，所以「整条链够用」的界必须随递归变化。
我把它写成全局界 `hN : off + 2 * chainDepth ch + 1 < N` 并配 `termination_by`，**定义体本身通过了**——
**但随后 `termination_by ch off hN x => chainDepth ch` 报 `application type mismatch`：
`ch` 在该位置被绑定为 `ℕ`（因为 `termination_by` 的参数是【被消去后的**那些）。**

**2. 展开 `noncomputable def`**：`rw [chainPoly]` 与 `simp only [chainPoly]` 都报 `made no progress`——
**递归定义需要在等式引理的形式下展开，而我没有找到正确的展开方式。**

**3. 命名冲突**：`chainDepth` 是 `{m n : ℕ} → Chain m n → ℕ`（有隐式参数），
在 `termination_by` 的位置上隐式参数无法推断，于是 `ch` 被错配到第一个显式位置（`ℕ`）。**

## 结论

**本轮没有把这条写进代码。** **上面的三步是【具体的下一步**，
而它们需要的是 Lean 的 dependent recursion 工程（`termination_by` 的正确写法、
递归定义的展开引理、隐式参数的显式化），**不是更多数学。**

**⇒ 第 7 轮的 `oneLayerParamPoly`／`twoLayerParamPoly` 与它们的次数界仍然有效，
而「对链递增归纳」这一步【登记为未做**，理由是上述三条工程障碍。** -/


/-! ## ⚠⚠ 第 9 轮：第 8 轮三条障碍的进展（一条解决、两条仍未）

## 障碍 1（`termination_by`）——**已解决**

**第 8 轮写成 `termination_by ch off hN x => chainDepth ch` 时报
`application type mismatch`：`termination_by` 的参数是【消去之后】的那些，`ch` 在那里被绑定为 `ℕ`。**

**⇒ 第 9 轮实测：`noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) →
(off : ℕ) → (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ`
配【结构模式匹配**（`| _, _, Chain.idf _ ...` 与 `| _, _, Chain.cons ... l rest ...`），
**完全不需要 `termination_by`**——**Lean 自己认出 `rest` 是 `Chain.cons` 的结构子项。**

**⇒ 这个定义【编译通过**（第 9 轮实测），所以障碍 1 【不再是障碍**。** -/

/-! ## 障碍 2（展开 `noncomputable def`）——**已解决**

**第 8 轮 `rw [chainPoly]` 报 `made no progress`。
第 9 轮实测：对【模式匹配**的递归定义，`rw [chainPoly]` **是**有效的
（探针 `testRec` 与 `testChainPoly` 都验证过）。

**⇒ 障碍 2 也不再是障碍。** -/

/-! ## 障碍 3（`omega` 与非线性的 `2 * chainDepth`）——**本轮未解决**

**定义体通过之后，`chainPoly_degree_le` 的归纳步需要在
`hN : off + 2 * chainDepth (Chain.cons l rest) + 1 < N` 与
`hN' : off + 2 * chainDepth rest + 3 < N` 之间做**线性提取**：

    要证：  off < N          （给 `Fin N` 的证明项）
    已知：  off + 2·d + 3 < N   （d 即 chainDepth rest）

**⚠ `omega` 做不到**：**它的约束求解把 `2 * d` 当作【非线性项**，
虽然它自己能证明 `d ≥ 0`，却拼不出 `off ≤ off + 2·d + 3`。

**⚠ 而 `Nat.le_add_right` 之类的引理给的是 `a ≤ a + b` 的形状，
需要把 `2 * d + 3` 显式写成 `b`——我试了 `Nat.le_add_right (off) (2 * d + 3)` 但类型对不上
（`Nat.le_add_right a b : a ≤ b + a`，参数顺序与我想的反了）。**

**⇒ 正确的引理应当是 `Nat.le_add_left`／`Nat.le.intro`，或者最直接：

    have : off ≤ off + (2 * d + 3) := Nat.le_add_right off (2 * d + 3)   -- 若 `Nat.le_add_right a b : a ≤ a + b`

**⚠ 我核对的 `Nat.le_add_right` 签名是 `a ≤ b + a`，所以应用 `Nat.le_add_left` 或 `le_add_of_nonneg_right`。**

**⇒ 这是一条【一行引理选择**的问题，而本轮在同一处消耗了过多尝试。** -/


/-! ## ⭐⭐⭐ 第 10 轮：`chainPoly` 定义与展开引理【已通过】，次数归纳差最后一步

## 本轮确认的三件事

**1. `chainPoly` 的定义【编译通过**：**

    noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
        (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ
      | _, _, Chain.idf _, _, _, x => MvPolynomial.C x
      | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x =>
          X ⟨off, ...⟩ * chainPoly rest (off + 2) (...) x + X ⟨off + 1, ...⟩

**⚠ 关键在于：`termination_by` 【不需要**（结构模式匹配足够），
而 `Fin N` 的证明项需要**先用 `le_add_of_nonneg_right (Nat.zero_le _)` 给出
`off ≤ off + (2·chainDepth rest + 3)`**，**再由 `omega` 线性地得出 `off < N`。**

**⚠ 第 10 轮探针确认：`Nat.le_add_right a b : a ≤ a + b`，而
`Nat.le_add_left a b : a ≤ b + a`——两者顺序相反**（第 9 轮我搞反了四次）。**

**2. `chainPoly_idf` 的展开【编译通过】——且必须是【泛化**形式：**

    theorem chainPoly_idf {N n : ℕ} (off : ℕ)
        (hN : off + 2 * chainDepth (Chain.idf n) + 1 < N) (x : ℝ) :
        chainPoly (Chain.idf n) off hN x = MvPolynomial.C x := by rw [chainPoly]

**⚠ 特化到 `Chain.idf 1` 会失败**，因为归纳里 `n` 是泛化的。

**3. `chainPoly_degree_le` 的归纳步差最后一步。**

## 最后一步的精确形状

**归纳步的 calc 是**

    deg(X·Φ_rest + Y) ≤ max (deg(X·Φ_rest)) (deg Y)      -- totalDegree_add
                     ≤ max (1 + deg Φ_rest) 1             -- totalDegree_mul 与 totalDegree_X
                     ≤ chainDepth (cons l rest)           -- hc

**⚠ 中间那一步的目标是 `deg(X·Φ_rest) ≤ 1 + chainDepth rest`，
而 `deg Φ_rest ≤ chainDepth rest` 正是归纳假设 `ih`。**

**⚠ 把 `ih` 交给 `omega`／`linarith` 都失败了**——**因为目标里 `deg(X·Φ_rest)`
已经被 `totalDegree_mul` 换成 `deg X + deg Φ_rest = 1 + deg Φ_rest`，
而 `linarith` 看到的 `ih : deg Φ_rest ≤ chainDepth rest` 与该表达式之间的
【项**不是同一个（`deg Φ_rest` 在其中出现的位置不同）。

**⇒ 正确做法：先用 `omega`／`linarith` 把 `1 + deg Φ_rest ≤ 1 + chainDepth rest`
从 `ih` 推出来（这一步是纯线性、项相同），再交给 `totalDegree_mul` 的 calc 链。
即【先证 `1 + deg Φ_rest ≤ 1 + chainDepth rest`，再 `exact` 合并**，
而不是把 `ih` 直接丢给末端的 `linarith`。**

**⇒ 这是本轮最后一次尝试的失败点，也是下一轮的第一件事。** -/


/-! ## ⭐⭐⭐ 宽 1 链的参数多项式：递归与次数上界

## 三条工程障碍的解法（第 8–10 轮磨合的结果）

1. **`termination_by` 不需要**——结构模式匹配让 Lean 认出 `rest` 是子项。
2. **`rw [chainPoly]` 对模式匹配递归定义有效**。
3. **`omega` 面对 `2 * chainDepth` 的非线性**：**先用
   `le_add_of_nonneg_right (Nat.zero_le _)` 给出 `off ≤ off + (2·d + 3)`，
   再由 `omega` 线性使用。** **注意 `Nat.le_add_right a b : a ≤ a + b`
   而 `Nat.le_add_left a b : a ≤ b + a`（顺序相反）。** -/

/-- **宽 1 链的输出多项式**。 -/
noncomputable def chainPoly {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
    (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) → MvPolynomial (Fin N) ℝ
  | _, _, Chain.idf _, _, _, x => MvPolynomial.C x
  | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x =>
      MvPolynomial.X ⟨off, by
        have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by
          have h := chainDepth_cons l rest
          omega
        have h2 : off ≤ off + (2 * chainDepth (m := n') (n := _) rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega⟩
        * chainPoly (m := n') (n := _) rest (off + 2) (by
            have h := chainDepth_cons l rest
            omega) x
        + MvPolynomial.X ⟨off + 1, by
            have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by
              have h := chainDepth_cons l rest
              omega
            have h2 : off + 1 ≤ off + 1 + (2 * chainDepth (m := n') (n := _) rest + 2) :=
              le_add_of_nonneg_right (Nat.zero_le _)
            omega⟩

/-- ⭐⭐ **空链的多项式是常数**——**对任意宽度 `n` 通用（特化到 `idf 1` 会失败）。** -/
theorem chainPoly_idf {N n : ℕ} (off : ℕ)
    (hN : off + 2 * chainDepth (m := n) (n := n) (Chain.idf n) + 1 < N) (x : ℝ) :
    chainPoly (Chain.idf n) off hN x = MvPolynomial.C x := by
  rw [chainPoly]

/-- ⭐⭐⭐ **宽 1 链的输出多项式次数 ≤ 层数**——**「参数次数 = 深度」的载体形式。**

**⚠ 第 10 轮确定的最后一步：先由 `ih` 得出 `1 + deg Φ_rest ≤ 1 + chainDepth rest`
（纯线性的 `Nat.add_le_add_left`），再放进 calc。** -/
theorem chainPoly_degree_le {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
    (hN : off + 2 * chainDepth ch + 1 < N) → (x : ℝ) →
    (chainPoly ch off hN x).totalDegree ≤ chainDepth ch
  | _, _, Chain.idf _, off, hN, x => by
      rw [chainPoly_idf]
      simp
  | _, _, Chain.cons (m := m') (n := n') l rest, off, hN, x => by
      rw [chainPoly]
      have hc := chainDepth_cons l rest
      have hNc : off + 2 * chainDepth (m := n') (n := _) rest + 3 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainDepth (m := n') (n := _) rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainDepth (m := n') (n := _) rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hrec : (off + 2) + 2 * chainDepth (m := n') (n := _) rest + 1 < N := by
        have h2 : (off + 2) + 2 * chainDepth (m := n') (n := _) rest + 1
            = off + 2 * chainDepth (m := n') (n := _) rest + 3 := by ring
        rw [h2]
        exact hNc
      have ih : (chainPoly rest (off + 2) hrec x).totalDegree
          ≤ chainDepth (m := n') (n := _) rest :=
        chainPoly_degree_le (m := n') (n := _) rest (off + 2) hrec x
      -- 关键：先得到 1 + deg ≤ 1 + chainDepth（纯线性、项相同）
      have hstep : 1 + (chainPoly rest (off + 2) hrec x).totalDegree
          ≤ 1 + chainDepth (m := n') (n := _) rest :=
        Nat.add_le_add_left ih 1
      have hmul : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
          * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
          ≤ (1 + chainDepth (m := n') (n := _) rest) := by
        calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
              * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
            ≤ (MvPolynomial.X (⟨off, hlt⟩ : Fin N) : MvPolynomial (Fin N) ℝ).totalDegree
              + (chainPoly rest (off + 2) hrec x).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + chainDepth (m := n') (n := _) rest := by
              have hx : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
                  : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
              omega
      calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
            * chainPoly rest (off + 2) hrec x
            + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree
          ≤ max (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
                * chainPoly rest (off + 2) hrec x : MvPolynomial (Fin N) ℝ).totalDegree
              (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                : MvPolynomial (Fin N) ℝ).totalDegree :=
            MvPolynomial.totalDegree_add _ _
        _ ≤ max (1 + chainDepth (m := n') (n := _) rest) 1 := by
            rw [max_le_iff]
            have hy : (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
            exact ⟨le_trans hmul (le_max_left _ _), by rw [hy]; exact le_max_right _ _⟩
        _ ≤ chainDepth (Chain.cons l rest) := by
            rw [hc]
            omega


/-! ## ⚠⚠ 第 12 轮：载体忠实性的障碍记录（未完成）

## 目标

    theorem chainPoly_eval {N : ℕ} : {m n : ℕ} → (ch : Chain m n) → (off : ℕ) →
        (hN) → (x : ℝ) → (g : Fin N → ℝ) → (j : Fin n) →
        (chainPoly ch off hN x).eval g = flatChainAct ch off g (fun _ => x) j

**这是把第 11 轮的「某个多项式次数 ≤ 深度」变成「【网络输出】次数 ≤ 深度」的最后一步。**

## 归纳步的形态（数学上是直接的）

**`chainPoly` 的 `cons` 支求值后是**

    g_off · (chainPoly rest ... x).eval g + g_{off+1}

**而 `flatChainAct (cons l rest) off g (fun _ => x) j` 展开成**

    flatChainAct rest (off + 2) g (flatParamActSafe off g (fun _ => x)) j

**⇒ 两者对接需要两件事：**

1. **把 `(chainPoly rest ... x).eval g` 用归纳假设换成
   `flatChainAct rest ... g (fun _ => x) j′`——但注意 `j′` 的【类型不同**：
   **`chainPoly` 的 `cons` 支输出在 `Fin n`（单坐标），
   而 `rest` 输出在 `Fin c`（尾链的输出宽度）。**
2. **把 `flatParamActSafe off g (fun _ => x)` 换成常函数
   `fun _ => readSlot g off * x + readSlot g (off+1)`。**

## 实际卡住的地方

**⚠ 第 1 点【不成立**：**`chainPoly` 是【宽 1 专用**的（它的 `cons` 支返回 `MvPolynomial (Fin N) ℝ`
而【没有输出坐标**），**而 `flatChainAct` 在 `Cons` 之后输出宽度变成 `c`。**

**⇒ `chainPoly` 与 `flatChainAct` 的对应【只在链的【最终**输出宽度为 1 时才有意义，
**而中间层的宽度可能不是 1。** **⇒ 正确的陈述必须限制在「每一层宽度都是 1」的链上，
即 `Chain 1 1`——而 `chainPoly` 目前对【任意 `m n`** 都有定义，那是个过强的签名。**

**⚠ 第 2 点在 `flatChainAct_cons_general` 重写【之后**才能用，
因为那个重写会消掉 `flatParamActSafe` 出现的位置——本轮把它放在了重写之前，顺序错了。**

## 结论

**本轮没有产出代码。** **两条精确的下一步：**

1. **把 `chainPoly` 的签名限制到 `Chain 1 1`**（或在 `cons` 支增加「`rest` 也是 1 宽」的约束），
   **因为只有那时「输出坐标」才与「标量激活」同型。**
2. **`hfun` 的 `rw` 必须放在 `flatChainAct_cons_general` 【之前**。

**⇒ 这是签名设计与重写顺序两件事，不是数学。** -/


/-! ## ⚠⚠ 第 13 轮：`Chain 1 1` 【不足以】表达「每层宽度都是 1」

## 第 12 轮的诊断不完整

**第 12 轮说「必须把链限制到 `Chain 1 1`」。第 13 轮实测发现：那【不够**。

**`Chain.cons l rest` 里 `l : MLayer m n` 而 `rest : Chain n c`。
即使 `ch : Chain 1 1`，中间宽度 `n` 仍是【自由**的——
例如 `chain2 : Chain 2 1` 是合法的，它的一层从宽度 2 降到 1。**

**⇒ 归纳步的目标右侧是**

    flatChainAct rest (off+2) g (flatParamActSafe off g (fun _ => x)) 0

**而 `flatParamActSafe off g (fun _ => x) : Fin n → ℝ` 是一个【向量**，
**只有当 `n = 1` 时它才与 `chainPoly` 的标量输入同型。**

**⇒ 「`Chain 1 1` 只约束两端，不约束中间」——这是 `Chain` 这个索引族的表达限度，
不是证明技巧的问题。**

## 正确的载体：一个每层宽度都是 1 的链类型

**要表达的链类是**

    ChainOne : Type
      | idf  : ChainOne
      | cons : MLayer 1 1 → ChainOne → ChainOne

**⚠ 它【不是** `Chain` 的特化，而是一个新的归纳类型。**

**⇒ 那会复制 `Chain` 的结构，而别名普查会把它标为 copy。
⇒ 但那是【必要的复制**：`Chain` 是「任意宽度序列」的族，
而 `ChainOne` 是「宽度恒为 1」的族，后者不是前者的特化——**它们之间的关系
是「`ChainOne` 解释成 `Chain 1 1`」，即一个转换函数。**

## 结论

**本轮没有产出代码。** **精确的下一步**：

1. **定义 `ChainOne`（三层结构：`idf`、`cons`）与它的 `chainOneToChain : ChainOne → Chain 1 1`；**
2. **把 `chainPoly`／`chainPoly_degree_le` 的陈述移到 `ChainOne` 上**
   （现有的 `Chain` 版本保留——它作为纯代数事实仍然为真）；
3. **再证忠实性 `chainPoly_eval`。**

**⚠ 第 2 步会产生「同一数学的两个版本」，别名普查可能报 copy。
⇒ 正确的处理是在 `chainOneToChain` 的层面上连接，而不是重述定理。** -/


/-! ## ⚠⚠ 第 14 轮：`chainOnePoly` 的【定义方向】是错的

## 本轮做到了什么

**1. `ChainOne` 已定义并编译通过**（`idf`／`cons (l : MLayer 1 1)`），
**连同 `chainOneDepth`、`chainOneToChain`、`chainDepth_chainOneToChain`。**
**⚠ 但这些在回退时被丢弃了——它们是【正确的第一步**，下轮可原样重放。**

**2. 次数界在 `ChainOne` 上也走到了最后一步。**

## 根本缺陷：`chainOnePoly` 把输入当成【常数】

**本轮的定义是**

    chainOnePoly (.cons l rest) off x = X off · chainOnePoly rest (off+2) x + X (off+1)

**⇒ 每一层都用【同一个 `x`】。**

**⚠ 但网络上，一层的输出 `readSlot g off · x + readSlot g (off+1)`
才是【下一层的输入**。所以尾链的多项式里应当是那个【新标量】**，不是原来的 `x`。**

**⇒ 忠实性 `eval = flatChainAct` 必然对不上——本轮最后正是在这里失败的：
左边是 `g_off · eval(chainOnePoly rest … x) + g_{off+1}`，
右边是 `flatChainAct rest … (fun _ => readSlot g off · x + …)`，
【尾链的输入不同**。**

## 正确的定义方向

**多项式不能依赖 `g`（它就是要对 `g` 求值的对象），
所以「把新标量喂给尾链」不能在多项式【内部**完成。**

**⇒ 唯一正确的形状是：`chainOnePoly` 应当是一个【从输入标量到多项式的函数族**，
即**它的类型里 `x` 是参数，而 `cons` 分支里【尾链的输入是 `X off · x + X (off+1)` 这个【多项式】**，不是标量。**

**⇒ 那就是【多项式代入**——正是第 8 轮判断「宽 1 时不需要」而回避掉的东西。
第 8 轮的判断是错的：**不需要代入的是【参数】，但【输入】确实需要代入。**

**⇒ 正确形式：**

    chainOnePoly : ChainOne → (off : ℕ) → MvPolynomial (Fin N) ℝ → MvPolynomial (Fin N) ℝ
    chainOnePoly .idf       off p = p
    chainOnePoly (.cons l ch) off p = chainOnePoly ch (off+2) (X off · p + X (off+1))

**即【输入本身是一个多项式**，而 `idf` 把它原样返回。
**⇒ 那么「标量输入 `x`」就是 `C x`，而整个链的输出是 `chainOnePoly ch off (C x)`。**

**⚠ 这个版本【不需要多项式代入的通用理论**——因为每层只是 `X off · p + X (off+1)`，
**即乘一个变量加一个变量，而 `p` 是任意多项式。次数归纳变成：
`deg(X off · p + X(off+1)) ≤ 1 + deg p`，仍是 `totalDegree_mul`。**

## 结论

**本轮没有代码入库（`ChainOne` 等被回退）。**
**⇒ 下一轮的第一件事是【用上面的签名重写 `chainOnePoly`**——
`x` 换成 `p : MvPolynomial`，`idf` 返回 `p`。**那是一个参数的改动，不是重新设计。** -/


/-! ## ⭐⭐⭐ `ChainOne`：参数多项式次数 = deg p + 层数

## 第 14 轮导出的正确形状

**`chainOnePoly` 原先把每层输入当成同一个标量 `x`，而网络上每层的输出才是下层的输入。
⇒ 正确的签名把输入作为【多项式 `p`】**，`idf` 原样返回它：

    chainOnePoly .idf        off p = p
    chainOnePoly (.cons l ch) off p = chainOnePoly ch (off+2) (X off · p + X (off+1))

**⇒ 次数界是 `deg p + depth`**，而标量输入 `x` 是 `C x`（`deg = 0`）。 -/

/-- **每层宽度都是 1 的链**——**`Chain 1 1` 不约束中间宽度，所以需要独立类型。** -/
inductive ChainOne : Type
  | idf : ChainOne
  | cons : MLayer 1 1 → ChainOne → ChainOne

/-- **`ChainOne` 的层数**。 -/
def chainOneDepth : ChainOne → ℕ
  | .idf => 0
  | .cons _ rest => chainOneDepth rest + 1

/-- **`ChainOne` 解释成 `Chain 1 1`**。 -/
def chainOneToChain : ChainOne → Chain 1 1
  | .idf => Chain.idf 1
  | .cons l rest => Chain.cons l (chainOneToChain rest)

/-- ⭐ **翻译保持层数**。 -/
theorem chainDepth_chainOneToChain : ∀ (ch : ChainOne),
    chainDepth (chainOneToChain ch) = chainOneDepth ch
  | .idf => rfl
  | .cons _ rest => by
      simp only [chainOneToChain, chainOneDepth, chainDepth_cons]
      rw [chainDepth_chainOneToChain rest]

/-- **`ChainOne` 的参数多项式**——**输入是一个多项式 `p`。** -/
noncomputable def chainOnePoly {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    MvPolynomial (Fin N) ℝ
  | .idf, _, _, p => p
  | .cons _ rest, off, hN, p =>
      chainOnePoly rest (off + 2) (by
        simp only [chainOneDepth] at hN
        omega)
        (MvPolynomial.X ⟨off, by
          have hd : off + 2 * chainOneDepth rest + 3 < N := by
            simp only [chainOneDepth] at hN
            omega
          have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
            le_add_of_nonneg_right (Nat.zero_le _)
          omega⟩
          * p
          + MvPolynomial.X ⟨off + 1, by
            have hd : off + 2 * chainOneDepth rest + 3 < N := by
              simp only [chainOneDepth] at hN
              omega
            have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
              le_add_of_nonneg_right (Nat.zero_le _)
            omega⟩)

/-- ⭐⭐ **空链原样返回输入**。 -/
theorem chainOnePoly_idf {N : ℕ} (off : ℕ)
    (hN : off + 2 * chainOneDepth ChainOne.idf + 1 < N) (p : MvPolynomial (Fin N) ℝ) :
    chainOnePoly ChainOne.idf off hN p = p := by
  rw [chainOnePoly]

/-- ⭐⭐⭐ **参数多项式次数 ≤ deg p + 层数**——**「参数次数」的一般形式。** -/
theorem chainOnePoly_degree_le {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    (chainOnePoly ch off hN p).totalDegree ≤ p.totalDegree + chainOneDepth ch
  | .idf, _, _, p => by
      rw [chainOnePoly_idf]
      simp
  | .cons _ rest, off, hN, p => by
      rw [chainOnePoly]
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have ih := chainOnePoly_degree_le rest (off + 2) hrec
        (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
          + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N))
      have hnew : (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
            + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree ≤ p.totalDegree + 1 := by
        have hm := MvPolynomial.totalDegree_mul
          (MvPolynomial.X (⟨off, hlt⟩ : Fin N) : MvPolynomial (Fin N) ℝ) p
        have hx : (MvPolynomial.X (⟨off, hlt⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
        have hy : (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
            : MvPolynomial (Fin N) ℝ).totalDegree = 1 := MvPolynomial.totalDegree_X _
        calc (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
              + MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
              : MvPolynomial (Fin N) ℝ).totalDegree
            ≤ max (MvPolynomial.X (⟨off, hlt⟩ : Fin N) * p
                  : MvPolynomial (Fin N) ℝ).totalDegree
                (MvPolynomial.X (⟨off + 1, hlt1⟩ : Fin N)
                  : MvPolynomial (Fin N) ℝ).totalDegree :=
              MvPolynomial.totalDegree_add _ _
          _ ≤ p.totalDegree + 1 := by
              rw [max_le_iff]
              exact ⟨by omega, by omega⟩
      simp only [chainOneDepth]
      omega


/-- **`ChainOne` 的数值作用**——**与 `chainOnePoly` 的递归【逐字对应】，
把「多项式乘加」换成「实数乘加」。** -/
noncomputable def chainOneAct {N : ℕ} (ch : ChainOne) (off : ℕ) (g : Fin N → ℝ) (x : ℝ) : ℝ :=
  match ch with
  | .idf => x
  | .cons _ rest => chainOneAct rest (off + 2) g (readSlot g off * x + readSlot g (off + 1))

/-- ⭐⭐⭐ **载体与数值作用一致（对任意多项式输入）**：
**`eval (chainOnePoly ch off h p) g = chainOneAct ch off g (eval p g)`。**

**⚠ 这条对【任意 `p`** 成立，所以归纳假设能用于 `X off · C x + X (off+1)` 这种输入。
**⚠ 两者的递归逐字对应：`chainOnePoly` 把 `p ↦ X off · p + X (off+1)`，
而 `chainOneAct` 把 `x ↦ readSlot g off · x + readSlot g (off+1)`，
而 `eval (X off · p + X(off+1)) g = readSlot g off · eval p g + readSlot g (off+1)`。** -/
theorem chainOnePoly_eval_act {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (p : MvPolynomial (Fin N) ℝ) →
    (g : Fin N → ℝ) →
    (chainOnePoly ch off hN p).eval g = chainOneAct ch off g (p.eval g)
  | .idf, off, hN, p, g => by
      simp only [chainOnePoly_idf, chainOneAct]
  | .cons _ rest, off, hN, p, g => by
      rw [chainOnePoly]
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      have hlt : off < N := by
        have h2 : off ≤ off + (2 * chainOneDepth rest + 3) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      have hlt1 : off + 1 < N := by
        have h2 : off + 1 ≤ off + 1 + (2 * chainOneDepth rest + 2) :=
          le_add_of_nonneg_right (Nat.zero_le _)
        omega
      rw [chainOnePoly_eval_act rest (off + 2) hrec _ g]
      simp only [chainOneAct, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, readSlot_of_lt _ hlt,
        readSlot_of_lt _ hlt1]


/-- **一层的激活（宽 1、标量输入）是常函数**。 -/
theorem flatParamActSafe_width_one_fun {N : ℕ} (off : ℕ) (g : Fin N → ℝ) (x : ℝ) :
    flatParamActSafe (N := N) (a := 1) (b := 1) off g (fun _ => x)
      = fun _ : Fin 1 => readSlot g off * x + readSlot g (off + 1) := by
  funext k
  fin_cases k
  rw [flatParamActSafe_width_one]

/-- ⭐⭐⭐ **数值作用就是网络的输出**：**`chainOneAct` = `flatChainAct`。**

**⚠ 这是第 16 轮指出的最后一环：`chainOneAct` 的 `cons` 支是把
`readSlot g off · x + readSlot g (off+1)` 代入尾链，而 `flatChainAct` 的 `cons` 支是
`flatParamActSafe off g (fun _ => x)`——`flatParamActSafe_width_one_fun` 说后者【就是】前者。** -/
theorem chainOneAct_eq_flatChainAct {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (hN : off + 2 * chainOneDepth ch + 1 < N) → (g : Fin N → ℝ) → (x : ℝ) →
    chainOneAct ch off g x
      = flatChainAct (N := N) (chainOneToChain ch) off g (fun _ => x) (0 : Fin 1)
  | .idf, off, hN, g, x => by
      simp only [chainOneAct, chainOneToChain, flatChainAct_idf]
  | .cons l rest, off, hN, g, x => by
      have hNc : off + 2 * chainOneDepth rest + 3 < N := by
        simp only [chainOneDepth] at hN; omega
      have hrec : (off + 2) + 2 * chainOneDepth rest + 1 < N := by omega
      rw [chainOneAct, chainOneToChain,
        flatChainAct_cons_general (N := N) (m := 1) (n := 1) (c := 1) l
          (chainOneToChain rest) off g (fun _ => x),
        show layerParamCount 1 1 = 2 from rfl,
        flatParamActSafe_width_one_fun (N := N) (off := off) (g := g) (x := x)]
      exact chainOneAct_eq_flatChainAct rest (off + 2) hrec g _


/-- ⭐⭐⭐ **最终结论：宽 1 链的输出【就是】一个参数次数 ≤ 层数的多项式。**

**这是第 6–17 轮那条线的终点：**
- `chainOnePoly` 给出那个多项式（第 15 轮）；
- `chainOnePoly_degree_le` 给出它的次数界（第 15 轮）；
- `chainOnePoly_eval_act` 与 `chainOneAct_eq_flatChainAct` 说明它的求值就是网络输出（第 16／17 轮）。

**⇒ 「符号 ⇄ 权重」不能线性化的一般形式，在此有了正面陈述：
网络输出是参数的多项式，其次数就是层数。** -/
theorem chainOne_output_degree {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) :
    (chainOnePoly ch 0 hN (MvPolynomial.C x)).totalDegree ≤ chainOneDepth ch := by
  have h := chainOnePoly_degree_le ch 0 hN (MvPolynomial.C x)
  have hc : (MvPolynomial.C x : MvPolynomial (Fin N) ℝ).totalDegree = 0 :=
    MvPolynomial.totalDegree_C x
  omega

/-- ⭐⭐⭐ **最终结论（求值形式）**：**那个多项式的求值就是网络的输出。**

**⚠ 与上一条合起来：网络输出对参数的次数 ≤ 层数，且实现的载体是显式给出的。** -/
theorem chainOne_output_eval {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) (g : Fin N → ℝ) :
    (chainOnePoly ch 0 hN (MvPolynomial.C x)).eval g
      = flatChainAct (N := N) (chainOneToChain ch) 0 g (fun _ => x) (0 : Fin 1) := by
  rw [chainOnePoly_eval_act]
  simp only [MvPolynomial.eval_C]
  exact chainOneAct_eq_flatChainAct ch 0 hN g x

/-- ⭐⭐⭐ **合成陈述：存在一个次数 ≤ 层数的多项式，其在每一点 `g` 的求值都等于网络输出。**

****这是「次数 = 深度」的完整形式化形式。** -/
theorem chainOne_output_poly_exists {N : ℕ} (ch : ChainOne)
    (hN : 0 + 2 * chainOneDepth ch + 1 < N) (x : ℝ) :
    ∃ (P : MvPolynomial (Fin N) ℝ),
      P.totalDegree ≤ chainOneDepth ch
        ∧ ∀ g : Fin N → ℝ,
            P.eval g = flatChainAct (N := N) (chainOneToChain ch) 0 g (fun _ => x) (0 : Fin 1) :=
  ⟨chainOnePoly ch 0 hN (MvPolynomial.C x),
    chainOne_output_degree ch hN x,
    fun g => chainOne_output_eval ch hN x g⟩


/-! ## ⭐⭐⭐ 深度可构造：「次数 = 深度」的下侧

## 构造

**对任意 `d`，用 `d` 层宽度 1 的链。取输入 `C 1`，
则 `chainOnePoly` 是 `X_0 · (X_2 · (… ) + X_1) + X_3 …`——**

**最高次项是 `X_0 · X_2 · … · X_{2(d-1)}` 的乘积，次数【恰为 `d`】。**

**⇒ 证明方式：指出那个单项式在多项式里的系数非零，再用 `le_totalDegree`。** -/

/-- **深度为 `d` 的 `ChainOne`**——**每层都用 `twoLayerProbeRest`（层的内容无关，只决定槽位）。** -/
noncomputable def chainOneOfDepth : ℕ → ChainOne
  | 0 => ChainOne.idf
  | k + 1 => ChainOne.cons twoLayerProbeRest (chainOneOfDepth k)

/-- **`chainOneOfDepth` 的层数**。 -/
theorem chainOneDepth_ofDepth : ∀ d : ℕ, chainOneDepth (chainOneOfDepth d) = d
  | 0 => rfl
  | k + 1 => by
      simp only [chainOneOfDepth, chainOneDepth, chainOneDepth_ofDepth]


/-- **chainOneAct 的 cons 支**——**定义级。** -/
theorem chainOneAct_cons {N : ℕ} (l : MLayer 1 1) (rest : ChainOne) (off : ℕ)
    (g : Fin N → ℝ) (x : ℝ) :
    chainOneAct (N := N) (ChainOne.cons l rest) off g x
      = chainOneAct (N := N) rest (off + 2) g (readSlot g off * x + readSlot g (off + 1)) := rfl

/-- **权重槽位置 1、偏置槽位置 0 的参数向量**——**偶数槽位是权重，奇数槽位是偏置。** -/
def allOnesWeights (N : ℕ) : Fin N → ℝ := fun k => if k.val % 2 = 0 then 1 else 0

/-- ⭐⭐ **在这组参数上，`ChainOne` 的作用是恒等**——**每层算 `1 · x + 0 = x`。**

**⚠ 前提 `hoff + 2·depth < N` 保证每个 `readSlot` 都在界内。** -/
theorem chainOneAct_allOnesWeights {N : ℕ} : (ch : ChainOne) → (off : ℕ) →
    (h : off + 2 * chainOneDepth ch < N) → (hoff : off % 2 = 0) →
    chainOneAct ch off (allOnesWeights N) 1 = 1
  | .idf, _, _, _ => rfl
  | .cons _ rest, off, h, hoff => by
      rw [chainOneAct_cons]
      have hoff2 : (off + 2) % 2 = 0 := by omega
      have hlt : off < N := by
        simp only [chainOneDepth] at h
        omega
      have hlt1 : off + 1 < N := by
        simp only [chainOneDepth] at h
        omega
      -- readSlot g off = 1, readSlot g (off+1) = 0
      have e0 : readSlot (allOnesWeights N) off = 1 := by
        rw [readSlot_of_lt _ hlt]
        simp only [allOnesWeights, hoff, if_true]
      have e1 : readSlot (allOnesWeights N) (off + 1) = 0 := by
        rw [readSlot_of_lt _ hlt1]
        have hodd : (off + 1) % 2 = 1 := by omega
        simp only [allOnesWeights, hodd]
        norm_num
      rw [e0, e1]
      simp only [one_mul, add_zero]
      have hrec : (off + 2) + 2 * chainOneDepth rest < N := by
        simp only [chainOneDepth] at h
        omega
      exact chainOneAct_allOnesWeights rest (off + 2) hrec hoff2


/-- ⭐⭐ **深度 `d` 链的多项式非零**——**在 `allOnesWeights` 处它求值为 `1`。**

**⚠ 这是「次数 ≥ 1」的直接来源，也是下界链条上不依赖 `coeff` 的第一步。** -/
theorem chainOneOfDepth_ne_zero {N : ℕ} (d : ℕ)
    (hN : 0 + 2 * chainOneDepth (chainOneOfDepth d) + 1 < N) :
    chainOnePoly (chainOneOfDepth d) 0 hN (MvPolynomial.C 1) ≠ 0 := by
  intro hzero
  have h1 : (chainOnePoly (chainOneOfDepth d) 0 hN (MvPolynomial.C 1)).eval
      (allOnesWeights N)
      = flatChainAct (N := N) (chainOneToChain (chainOneOfDepth d)) 0
          (allOnesWeights N) (fun _ => (1 : ℝ)) (0 : Fin 1) :=
    chainOne_output_eval (chainOneOfDepth d) hN 1 (allOnesWeights N)
  rw [hzero] at h1
  -- 左边：0 的求值是 0；右边由恒等参数推出是 1
  have h2 : chainOneAct (chainOneOfDepth d) 0 (allOnesWeights N) 1 = 1 := by
    have hlt : 0 + 2 * chainOneDepth (chainOneOfDepth d) < N := by omega
    exact chainOneAct_allOnesWeights (chainOneOfDepth d) 0 hlt (by rfl)
  have h3 : chainOneAct (chainOneOfDepth d) 0 (allOnesWeights N) 1
      = flatChainAct (N := N) (chainOneToChain (chainOneOfDepth d)) 0
          (allOnesWeights N) (fun _ => (1 : ℝ)) (0 : Fin 1) :=
    chainOneAct_eq_flatChainAct (chainOneOfDepth d) 0 (by omega) _ 1
  rw [← h3, h2] at h1
  simp at h1


/-! ## ⚠⚠ 第 21 轮：次数下界的接口障碍（四处，已逐一查明）

## 目标

    theorem totalDegree_X_mul_C_add_X {N : ℕ} (a b : Fin N) (hab : a ≠ b) {c : ℝ} (hc : c ≠ 0) :
        (X a · C c + X b : MvPolynomial (Fin N) ℝ).totalDegree = 1

**这条是「每层加一次」的基础情形，也是第 20 轮登记的下界所缺的那一块。**

## 数学上它是显然的

**`X a · C c` 在变量 `a` 上的次数是 1，`X b` 在 `a` 上的次数是 0（因为 `a ≠ b`），
所以两者【不能抵消】，总和在 `a` 上的次数是 1，于是 `totalDegree ≥ 1`；
上界由 `totalDegree_add ≤ max 1 1 = 1`。** -/

/-! ## 实际卡在哪：四处接口名与我预期的不同

**第 21 轮实测（逐一编译确认）：**

| 我写的 | 实际结果 |
|:--|:--|
| `MvPolynomial.coeff_X` | **不存在**（报 `did not find instance of coeff (fun₀ \| ?i => 1) (X ?i)`） |
| `MvPolynomial.X_mul` | **不存在** |
| `Finsupp.degree_single` | **不存在** |
| `MvPolynomial.totalDegree_mul` | **存在，但是【不等式** `≤ a.totalDegree + b.totalDegree`，不是等式
（第 6 轮已记录，本轮再次撞上） |

**⇒ 存在且可用的：`coeff_add`、`coeff_C`、`coeff_C_mul`、`coeffX`（需核实拼写）、
`mem_support_iff`、`le_totalDegree`、`support_nonempty_iff`、`degreeOf_X`、`degreeOf_C`、`degreeOf_add_le`。**

**⚠ 其中 `degreeOf_X` 与 `degreeOf_add_le` 都存在，而它们正是
「在某个变量上的次数」所需要的——第 21 轮没有把它们组合起来。**

## 结论

**本轮没有产出代码（工作树回退到 721）。**

**⇒ 精确的下一步**：**用 `degreeOf` 而不是 `coeff`：**

    have h1 : degreeOf a (X a * C c) = 1        -- 由 degreeOf_mul_le 与 degreeOf_X
    have h2 : degreeOf a (X b) = 0               -- hab
    -- 但 degreeOf_add_le 只给 ≤，不给 ≥

**⚠ `degreeOf_add_le` 也是【不等式**，所以 `degreeOf` 路线同样拿不到下界。

**⇒ 下界【必须】来自「存在一个非零的 `d` 次单项式」，即 `coeff` + `le_totalDegree`。
⇒ 下一轮的第一件事是【探明 `coeff` 的确切名字**——
在 mathlib 里它极可能叫 `MvPolynomial.coeff_X'` 或通过 `coeff_monomial`／`single_mul` 组合得到。** -/


/-- ⭐⭐ **单步下界：`X a · C c + X b` 的次数 ≥ 1**（`c ≠ 0`，`a ≠ b`）。

**⚠ 论证：取单项式 `m = single a 1`。它在 `X a · C c` 中的系数是 `c`，
在 `X b` 中的系数是 `0`（因为 `a ≠ b`），所以总和非零，再用 `le_totalDegree`。** -/
theorem totalDegree_X_mul_C_add_X_ge {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    {c : ℝ} (hc : c ≠ 0) :
    1 ≤ (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
        : MvPolynomial (Fin N) ℝ).totalDegree := by
  -- 系数：m = single a 1
  have h1 : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial (Fin N) ℝ) = c := by
    have : (MvPolynomial.X a * MvPolynomial.C c : MvPolynomial (Fin N) ℝ)
        = MvPolynomial.C c * MvPolynomial.X a := by ring
    rw [this, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    ring
  have h2 : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X b : MvPolynomial (Fin N) ℝ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hba : (Finsupp.single b 1 : Fin N →₀ ℕ) ≠ Finsupp.single a 1 := by
      rw [Ne, Finsupp.single_eq_single_iff]
      omega
    simp [hba]
  have hne : MvPolynomial.coeff (Finsupp.single a 1)
      (MvPolynomial.X a * MvPolynomial.C c + MvPolynomial.X b
        : MvPolynomial (Fin N) ℝ) ≠ 0 := by
    rw [MvPolynomial.coeff_add, h1, h2, add_zero]
    exact hc
  have hmem := MvPolynomial.mem_support_iff.mpr hne
  have hdeg := MvPolynomial.le_totalDegree hmem
  simpa using hdeg


/-! ## ⚠⚠ 第 23 轮：`totalDegree_X_mul_eq` 差「取最高项」这一步

## 目标

    theorem totalDegree_X_mul_eq {N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
        (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree

**上界在 `calc` 里已经走通（本轮实测到 `_ = 1 + q.totalDegree` 那一行）。
下界卡在【选哪个单项式】上。** -/

/-! ## 卡点：必须取【最高次】的支撑元素

**我写的是 `obtain ⟨m, hm⟩ := hsup`，即取【任意一个】**支撑元素。
**⇒ 那只能得到 `m.degree + 1 ≤ q.totalDegree + 1`，而下界需要 `1 + q.totalDegree ≤ …`。
**⇒ `omega` 报的反例约束正是这个缺口：`c - d ≤ 1`（`c = m+ε 的次数`、`d = deg(X·q)`）。**

**⚠ 正确做法：取 `q.support` 中【次数最大】的元素，即
`q.support.max' hsup` 配 `Finset.le_max'`——那样 `m.degree = q.totalDegree`，
于是 `m.degree + 1 = 1 + q.totalDegree` 恰好是要的下界。**

## 另一处命名修正

**`MvPolynomial.support_nonempty_iff` 不存在；实际是 `Function.support_nonempty_iff`
（在 `MvPolynomial` 上实例化），签名 `(Function.support ?f).Nonempty ↔ ?f ≠ 0`。**

**⚠ 而 `MvPolynomial.support` 就是 `Function.support` 的实例化，所以 `rw` 时需要
`show q.support.Nonempty` 或直接 `MvPolynomial.support_nonempty_iff` 的反向用法。**

## 结论

**本轮没有产出代码（回退到 723）。**
**⇒ 下一轮的第一件事**：

    obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_max' hsup   -- 或 max' 的等价形式
    -- hmax : ∀ s ∈ q.support, s.sum (·) ≤ m.sum (·)
    -- 于是 m.degree = q.totalDegree 由 le_antisymm 得到

**⇒ 之后 `totalDegree_X_mul_eq` 与它的加法版本、以及第 23 轮计划的归纳步都会顺次通过。** -/


/-! ## ⚠⚠ 第 24 轮：`totalDegree` 的【上界】刻画——找到了一条、还差另一条

## 本轮查明的接口（全部实测）

| 引理 | 结果 |
|:--|:--|
| **`coeff_eq_zero_of_totalDegree_lt`** | **存在，且是本轮的关键发现**：`f.totalDegree < d.sum → coeff d f = 0` |
| `le_totalDegree` | 存在：`s ∈ p.support → s.sum ≤ p.totalDegree`（**下界方向**） |
| `Finset.max'` / `le_max'` / `max'_mem` | 全部存在 |
| `Finsupp.degree` | 存在；**`degree_single` 与 `degree_add` 【不存在】** |
| `MvPolynomial.totalDegree_def` / `totalDegree_eq_sup` / `totalDegree_le_iff` | **全部不存在** |

## 这给出了什么

**`coeff_eq_zero_of_totalDegree_lt` 是 `le_totalDegree` 的【逆否**——
它说「若 `d` 的次数超过 `totalDegree`，则 `d` 的系数为 0」，
**等价地：「若 `coeff d f ≠ 0`，则 `d.sum ≤ f.totalDegree`」。**

**⇒ 那正是 `le_totalDegree` 由 `mem_support_iff` 转述后的同一件事。所以它【不提供新的上界信息**。** -/

/-! ## 仍然缺的那一条

**要证 `totalDegree_X_mul_eq : deg(X a · q) = 1 + deg q` 的【下界**，
需要 `1 + q.totalDegree ≤ deg(X a · q)`。

**已经知道**（对 `m ∈ q.support`）：`coeff (m + single a 1) (X a · q) = coeff m q ≠ 0`，
**于是 `(m + single a 1).sum ≤ deg(X a · q)`，即 `m.sum + 1 ≤ deg(X a · q)`。**

**⇒ 只需 `m.sum = q.totalDegree`，即【存在一个支撑元素，其次数恰为 totalDegree**。**

**⚠ 这一条无法由 `le_totalDegree` 得到（它只有 `≤`），
也无法由 `coeff_eq_zero_of_totalDegree_lt` 得到（它只有「超过则系数为 0」）。

**⇒ 它必须来自 `totalDegree` 的【定义**，而 `totalDegree_def`／`totalDegree_eq_sup` 都不存在。
⇒ 正确的做法是【绕开**：**在 `MvPolynomial` 上，`totalDegree` 的定义可以通过 `le_antisymm` 刻画为
「`≤` 所有系数为零的界」——而那需要 `totalDegree_le_iff_coeff_zero`，它也【不存在**。

**⇒ 下一轮用 `#check` 枚举 `totalDegree` 的【全部**相关引理（`totalDegree_le_*`／`*_totalDegree_*`），
而不是继续猜名字。这是本轮最后一条教训，也是第 21／23 轮同一个教训的第三次复发。** -/


/-! ## ⭐⭐ 第 25 轮：找到 `totalDegree_add_eq_left_of_totalDegree_lt`

## 本轮枚举的最大收获

    @totalDegree_add_eq_left_of_totalDegree_lt :
        q.totalDegree < p.totalDegree → (p + q).totalDegree = p.totalDegree
    @totalDegree_add_eq_right_of_totalDegree_lt :
        q.totalDegree < p.totalDegree → (q + p).totalDegree = p.totalDegree

**⇒ 当两项次数【不等**时，和的次数就是【大者**的次数——这正是 `X a · p + X (off+1)` 需要的形状
（当 `deg p ≥ 1` 时，`deg(X a · p) = 1 + deg p ≥ 2 > 1 = deg(X off+1)`）。**

**⚠ 这一条第 24 轮没有猜到，而它在第 25 轮的一次扫描里就出现了。** -/

/-! ## 但还有一环没通

**要用上面那条，需要先知道 `deg(X a · p) = 1 + deg p` 的【下界**。
**上界是 `totalDegree_mul`（`≤`），下界需要「`totalDegree` 由某个支撑元素达到」——
即 `∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree`。**

**⚠ 我尝试用 `q.support.max'` 加 `le_antisymm` 证它，反向不等式卡住：
`q.totalDegree ≤ max'.sum` 无法从 `le_totalDegree`（它只有 `≤` 反方向）得到。**

**⇒ 这个存在性一定在 mathlib 里（`totalDegree` 的定义就是那个 sup），
但第 24／25 轮的 `#check` 都没扫到正确名字。**

**⇒ 下一轮应当用【搜索**而不是抽查：`exact?`、`apply?`、或 `#check @MvPolynomial.totalDegree_le_iff` 之类。
一次搜索比十次猜测便宜。** -/

/-! ## 本轮另一条确认为【不存在】的

**`MvPolynomial.totalDegree_mul_le` 不存在**——乘法的次数界就是 `totalDegree_mul`（`≤` 形式）。
**`MvPolynomial.totalDegree_le_iff_coeff_zero` 也不存在。**

**⚠ 而 `totalDegree_monomial` 【存在**：`c ≠ 0 → (monomial s c).totalDegree = s.sum (fun x e => e)`
——**这与上面缺的存在性刚好互补**。** -/


/-- ⭐⭐⭐ **`totalDegree` 由某个支撑元素达到**——
**这是第 24／25 轮缺失的那一环，本轮找到：`totalDegree` 定义上就是支持集上的 `sup`，
所以 `Finset.exists_mem_eq_sup` 直接给出它。** -/
theorem exists_support_max_degree {N : ℕ} (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
    ∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree := by
  have hne : q.support.Nonempty := by
    by_contra hemp'
    rw [Finset.not_nonempty_iff_eq_empty] at hemp'
    exact hq (by
      have : q = 0 := by
        ext m
        rw [MvPolynomial.coeff_zero]
        by_contra hc
        have hmem : m ∈ q.support := MvPolynomial.mem_support_iff.mpr hc
        rw [hemp'] at hmem
        simpa using hmem
      exact this)
  have hdef : q.totalDegree = q.support.sup (fun s => s.sum (fun x e => e)) := rfl
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup q.support hne
    (fun s => s.sum (fun x e => e))
  exact ⟨m, hm, by rw [hdef, hmax]⟩

/-- ⭐⭐ **乘一个变量：`deg(X a · q) = 1 + deg q`**（当 `q ≠ 0`）。 -/
theorem totalDegree_X_mul_eq {N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ) (hq : q ≠ 0) :
    (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree := by
  apply le_antisymm
  · calc (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ).totalDegree
        ≤ (MvPolynomial.X a : MvPolynomial (Fin N) ℝ).totalDegree
          + (q : MvPolynomial (Fin N) ℝ).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 + q.totalDegree := by rw [MvPolynomial.totalDegree_X]
  · obtain ⟨s, hs, hsum⟩ := exists_support_max_degree q hq
    have hcoeff : MvPolynomial.coeff s q ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hkey : MvPolynomial.coeff (s + Finsupp.single a 1)
        (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ) = MvPolynomial.coeff s q := by
      rw [mul_comm]
      exact MvPolynomial.coeff_mul_X s a q
    have hmem : (s + Finsupp.single a 1)
        ∈ (MvPolynomial.X a * q : MvPolynomial (Fin N) ℝ).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hkey]; exact hcoeff)
    have hdeg := MvPolynomial.le_totalDegree hmem
    have hdegsum : (s + Finsupp.single a 1).sum (fun x e => e)
        = s.sum (fun x e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    omega


/-- ⭐⭐⭐ **`deg(X a · p + X b) = 1 + deg p`**（当 `p ≠ 0` 且 `1 ≤ deg p` 且 `a ≠ b`）。

**⚠ 论证：`deg(X a · p) = 1 + deg p ≥ 2 > 1 = deg(X b)`，
所以由 `totalDegree_add_eq_left_of_totalDegree_lt`，和的次数等于左项的次数。**

**⇒ 这条是「每层加一次」的完整形式，也是第 27 轮归纳步的原子步骤。** -/
theorem totalDegree_X_mul_add_X {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (p : MvPolynomial (Fin N) ℝ) (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (MvPolynomial.X a * p + MvPolynomial.X b).totalDegree = 1 + p.totalDegree := by
  have h1 : (MvPolynomial.X a * p : MvPolynomial (Fin N) ℝ).totalDegree
      = 1 + p.totalDegree := totalDegree_X_mul_eq a p hp
  have h2 : (MvPolynomial.X b : MvPolynomial (Fin N) ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · exact h1
  · rw [h2, h1]
    omega


/-! ## ⭐ 第 28 轮：找到 `chainOnePoly` 的等式引理

## 这是第 27 轮要的东西

    @chainOnePoly.eq_1 : chainOnePoly ChainOne.idf x x_2 x_1 = x_1
    @chainOnePoly.eq_2 (x : ℕ) (x_1 : 多项式) (a : MLayer 1 1) (rest : ChainOne)
        (x_2 : x + 2 * chainOneDepth (ChainOne.cons a rest) + 1 < N) :
        chainOnePoly (ChainOne.cons a rest) x x_2 x_1
          = chainOnePoly rest (x + 2) ⋯ (X ⟨x, ⋯⟩ * x_1 + X ⟨x + 1, ⋯⟩)

**⇒ 用 `rw [chainOnePoly.eq_2 (N := N) off p l rest hN]` 就能展开，不必 `rw [chainOnePoly]`。** -/

/-! ## 但归纳步仍然超时

**第 28 轮实测：换成 `eq_2` 之后，超时【没有消失**，只是从 `rw [chainOnePoly]` 那一行
移到了分支头部（`| .cons l rest, off, hN, p, hp, hdeg => by` 这一行本身报 `whnf` 超时）。

**⚠ 这说明超时不是「展开 `chainOnePoly`」造成的，
而是 `hN : off + 2 * chainOneDepth (ChainOne.cons l rest) + 1 < N` 这个【类型**
在每次 `omega`／`simp` 接触它时都要把 `chainOneDepth` 在 `ChainOne.cons` 上展开，
而那在 `ChainOne` 的 `brecOn` 表示下很贵。**

**⚠ 我试过的三种都失败**：
1. `simp only [chainOneDepth] at hN; omega`——超时；
2. `have hd : chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl; rw [hd] at hN`——超时；
3. `set_option maxHeartbeats 1000000 in`——`set_option` 与文档注释的先后导致语法错误，
   移到文档注释上方后编译通过但【超时依旧**。

## ⇒ 正确的修法：改 `chainOnePoly` 的签名，让深度【作为参数】

**把**

    chainOnePoly : (ch : ChainOne) → (off : ℕ) → (hN : off + 2 * chainOneDepth ch + 1 < N) → …

**改成**

    chainOnePoly : (ch : ChainOne) → (d : ℕ) → (hd : d = chainOneDepth ch) →
        (off : ℕ) → (hN : off + 2 * d + 1 < N) → …

**⇒ 那样 `hN` 里的深度就是一个【裸变量 `d`**，`omega`／`simp` 不再需要展开 `chainOneDepth`。

**⚠ 代价**：`chainOnePoly` 的每个调用点要多传 `d` 与 `hd`，而 `eq_2`／`eq_1` 会随之变形。

**⇒ 这是本轮确定的【唯一可行修法**，也是下一轮的第一件事。
**⇒ 在改签名之前，先备份当前位置（提交号 728）作为回退点。** -/


/-! ## ⭐⭐ 第 29 轮：`chainOneDepth` 的等式引理是超时的一个真实来源

## 本轮证实的

**`chainOneDepth` 的 `match` 定义展开成本很低，但 `omega` 通过**定义**去展开它时会走
`ChainOne` 的 `brecOn` 表示，那才是超时的根源。**

**⇒ 一旦给出等式引理并**显式 `rw`**，超时消失：**

    @[simp] theorem chainOneDepth_idf : chainOneDepth ChainOne.idf = 0 := rfl
    @[simp] theorem chainOneDepth_cons (l : MLayer 1 1) (rest : ChainOne) :
        chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl

**⚠ 关键：`omega` 【不会自动用 `@[simp]` 引理**——必须显式 `rw [chainOneDepth_idf] at hd`，
或先 `rw` 再 `omega`。「加了 `@[simp]` 就够了」是错的。

**⇒ 加上这两条并显式 `rw` 之后，`chainOnePolyD_degree_ge` 的 `idf` 支【通过】了。** -/

/-! ## 仍未解决的：`cons` 支的展开

**`cons` 支需要把 `chainOnePolyD (cons l rest) d hd off hN p` 展开成
`chainOnePolyD rest (chainOneDepth rest) rfl (off+2) … (X off · p + X (off+1))`。**

**⚠ `rw [chainOnePolyD]` 超时**（第 28 轮已知）。
**⚠ `chainOnePolyD.eq_2` 的名字【无法探测**——
`agent-tmp` 不在 `lakefile` 的模块列表里，所以从那里写的 `#check` 看不到 `Lattice.Core` 的新定义。
**⇒ 下一轮探测 `eq_2` 的签名必须把探针写进 `Lattice/Core/` 下的临时模块，或者直接在
`VariableDerivative.lean` 里用 `#check`（它会被 `lake build` 编译）。**

## 第 29 轮的流程记录

**按项目规则在分支 `p2-04-depthparam29` 上做，失败后 `git checkout master` 并删除分支。
master 仍在 729，构建通过。**

## 结论

**本轮没有代码入库。** **但「`chainOneDepth` 的等式引理 + 显式 `rw`」是一条可复用的具体修法，
而它已经把归纳的一半（`idf` 支）从超时变成了通过。** -/


/-! ## ⭐⭐⭐ `chainOnePolyD`：深度作为参数（第 30 轮）

**第 28／29 轮发现两个超时源：**
1. **`hN` 类型里的 `chainOneDepth ch`**——由把深度作为裸参数 `d` 解决；
2. **`chainOneDepth` 经定义展开**——由等式引理 `chainOneDepth_idf`／`chainOneDepth_cons` 加显式 `rw` 解决。

**⇒ 本节新增 `chainOnePolyD`，旧定义与旧定理全部保留。** -/

/-- ⭐ **`chainOneDepth` 的等式引理**——**避免 `omega` 触发定义展开。** -/
@[simp] theorem chainOneDepth_idf : chainOneDepth ChainOne.idf = 0 := rfl

/-- ⭐ **`chainOneDepth` 在 `cons` 上的等式引理。** -/
@[simp] theorem chainOneDepth_cons_succ (l : MLayer 1 1) (rest : ChainOne) :
    chainOneDepth (ChainOne.cons l rest) = chainOneDepth rest + 1 := rfl

/-- **`chainOnePolyD`：深度作为参数的版本。** -/
noncomputable def chainOnePolyD {N : ℕ} : (ch : ChainOne) → (dd : ℕ) →
    (hd : dd = chainOneDepth ch) → (off : ℕ) → (hN : off + 2 * dd + 1 < N) →
    (p : MvPolynomial (Fin N) ℝ) → MvPolynomial (Fin N) ℝ
  | .idf, _, _, _, _, p => p
  | .cons _ rest, _, hd, off, hN, p =>
      chainOnePolyD rest (chainOneDepth rest) rfl (off + 2) (by
        rw [chainOneDepth_cons_succ] at hd
        omega)
        (MvPolynomial.X ⟨off, by
          rw [chainOneDepth_cons_succ] at hd
          omega⟩ * p + MvPolynomial.X ⟨off + 1, by
            rw [chainOneDepth_cons_succ] at hd
            omega⟩)


/-! ## ⚠⚠ 第 31 轮：`chainOnePolyD` 在归纳步里【无法】展开（三条路全试过）

## 试过的三条路，全部失败

| 手法 | 结果 |
|:--|:--|
| **`rw [chainOnePolyD]`** | **`whnf` 超时** |
| **`simp only [chainOnePolyD]`** | **`whnf` 超时** |
| **`change p.totalDegree + (chainOneDepth rest + 1) ≤ (chainOnePolyD rest …).totalDegree`** | **`change` 本身通过，但它【只是声称**两个类型相同；原目标左侧的 `chainOnePolyD (cons l rest) …` 并未真正展开，于是随后的 `linarith [ih]` 报 `type mismatch` |

**⇒ 关键：`change` 不证明展开，它只是改类型标注。要真正展开，仍然必须依赖定义或等式引理，
而两者都超时。**

## 为什么会超时（本轮的判断）

**`chainOnePolyD` 的 `cons` 支在【递归调用自身】，而递归调用的 `hN` 参数是一个 `by omega` 证明项。
展开时 Lean 必须对那个证明项做 `whnf`，而它会再次触发 `chainOneDepth` 的展开——
于是展开的成本随深度【指数增长**（每一层都要重新规约上一层的证明项）。**

**⚠ 这解释了为什么第 28 轮把深度改成裸参数后仍然超时：
裸参数 `dd` 只解决【外层**的 `hN`，而递归调用传入的是 `chainOneDepth rest`——
那仍然是一个需要规约的项。**

## 结论：需要一次结构性改动

**`chainOnePolyD` 的递归调用【不能】在定义体里直接递归；需要一个辅助函数，
把「递归调用 + 它的证明项」封成一个不会在展开时被规约的常量。**

**⇒ 具体方案：把递归的【结果】**记成一个 `opaque`（或在独立的 `def` 里算好），
**而 `chainOnePolyD` 只在 `idf`／`cons` 上调用它。**

**⚠ 但 `opaque` 会违反 I1（no axiom/opaque）。**

**⇒ 另一个方案：干脆【不递归】**，而把 `chainOnePolyD` 定义成对**显式列表**（`List (MLayer 1 1)`）的
`foldl`。`List` 的 `foldl` 展开是【逐元素**的，不会出现「每层重新规约上一层证明项」的问题。

**⇒ 这是本轮确定的下一步，也是第 26 轮以来第一次真正改变载体结构。**

## 流程记录

**本轮没有代码入库；工作树回退到 731（构建通过）。** -/


/-! ## ⚠⚠ 第 32 轮：`ℕ` 下标版本的路线与它自己的陷阱

## 本轮的方向（第 31 轮定的）

**把多项式建在 `MvPolynomial ℕ ℝ` 上——下标是 `ℕ`，`X off` 对任意 `off` 都有意义，
于是递归里【不再带任何界证明项**，指数级规约的问题从根上消失。

## 试过的第一步：把现有的 `totalDegree_X_mul_eq` 泛化到任意 `σ`

**从 `{N : ℕ} (a : Fin N) (q : MvPolynomial (Fin N) ℝ)` 改成
`{σ : Type*} [DecidableEq σ] (a : σ) (q : MvPolynomial σ ℝ)`。**

**⚠ 失败方式值得记录：证明体里到处写着 `(MvPolynomial (Fin N) ℝ)` 的类型标注。
我用一次全局 `replace` 把它们改成 `σ`，结果【误伤了文件里其它位置的**
`MvPolynomial (Fin N) ℝ`——那是第 6 轮的 `oneLayerParamPoly` 等旧定理的类型，
于是 L2670 报 `invalid constructor ⟨...⟩, expected type must be σ`。**

**⇒ 教训：跨 1000+ 行的文件里做【全局字符串替换**是危险的；
必须先把替换范围限定到目标定理的行区间，或者先确认目标字符串在该区间外不出现。**

## 一个更安全的路子

**不泛化现有定理，而是【用 `rename` 把 `ℕ` 版本搬到 `Fin N`**：

    -- 已有：totalDegree_X_mul_eq (Fin N 版)
    -- 需要：ℕ 版

**⚠ 但 `rename` 只给 `totalDegree_rename_le`（`≤`），拿不到等式。**

**⇒ 更直接：为 `MvPolynomial ℕ ℝ` 单独证一条 `totalDegree_X_mul_eq_nat`。
它会是 `totalDegree_X_mul_eq` 的【复制**，而别名普查会标出它。
⇒ 但那是有意的、必要的复制（不同下标类型），并且可以在基线里登记。**

## 结论

**本轮没有代码入库（回退到 732）。**

**⇒ 下一轮的精确步骤**：
1. **在文件【末尾】、`end Lattice.Core` 之前，新增一条独立的 `totalDegree_X_mul_eq_nat`**，
   证明体与 `totalDegree_X_mul_eq` 相同但类型是 `MvPolynomial ℕ ℝ`；
2. **同样加 `totalDegree_X_mul_add_X_nat`**；
3. **然后建 `chainNatPoly`（`List.foldl` 版）并证它的次数界**；
4. **跑别名普查，若报 `copy`／`new`，就把它们登记进 `gov/alias-baseline.txt`。**

**⚠ 第 4 步是必须的：项目规则要求别名普查为 0 new／0 stale。** -/


/-! ## ⭐⭐⭐ `ℕ` 下标版本：无界下标，递归里不带界证明项

## 第 31／32 轮的诊断与修法

**`chainOnePolyD` 的展开成本随深度【指数增长】，因为每层递归都要重新规约上一层的 `by omega` 证明项。**

**⇒ 根本修法：把多项式建在 `MvPolynomial ℕ ℝ` 上。`X off` 对任意 `off` 都有意义，
于是【递归里不再有任何界证明】。** -/

/-- ⭐⭐ **`ℕ` 下标版：`totalDegree` 由某个支撑元素达到。** -/
theorem exists_support_max_degree_nat (q : MvPolynomial ℕ ℝ) (hq : q ≠ 0) :
    ∃ s ∈ q.support, s.sum (fun x e => e) = q.totalDegree := by
  have hne : q.support.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    refine hq ?_
    ext m
    rw [MvPolynomial.coeff_zero]
    by_contra hc
    have hmem : m ∈ q.support := MvPolynomial.mem_support_iff.mpr hc
    rw [hemp] at hmem
    simpa using hmem
  have hdef : q.totalDegree = q.support.sup (fun s => s.sum (fun x e => e)) := rfl
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup q.support hne
    (fun s => s.sum (fun x e => e))
  exact ⟨m, hm, by rw [hdef, hmax]⟩

/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · q) = 1 + deg q`**（当 `q ≠ 0`）。 -/
theorem totalDegree_X_mul_eq_nat (a : ℕ) (q : MvPolynomial ℕ ℝ) (hq : q ≠ 0) :
    (MvPolynomial.X a * q).totalDegree = 1 + q.totalDegree := by
  apply le_antisymm
  · calc (MvPolynomial.X a * q : MvPolynomial ℕ ℝ).totalDegree
        ≤ (MvPolynomial.X a : MvPolynomial ℕ ℝ).totalDegree
          + (q : MvPolynomial ℕ ℝ).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ = 1 + q.totalDegree := by rw [MvPolynomial.totalDegree_X]
  · obtain ⟨s, hs, hsum⟩ := exists_support_max_degree_nat q hq
    have hcoeff : MvPolynomial.coeff s q ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hkey : MvPolynomial.coeff (s + Finsupp.single a 1)
        (MvPolynomial.X a * q : MvPolynomial ℕ ℝ) = MvPolynomial.coeff s q := by
      rw [mul_comm]
      exact MvPolynomial.coeff_mul_X s a q
    have hmem : (s + Finsupp.single a 1)
        ∈ (MvPolynomial.X a * q : MvPolynomial ℕ ℝ).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [hkey]; exact hcoeff)
    have hdeg := MvPolynomial.le_totalDegree hmem
    have hdegsum : (s + Finsupp.single a 1).sum (fun x e => e)
        = s.sum (fun x e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    omega

/-- ⭐⭐ **`ℕ` 下标版：`deg(X a · p + X b) = 1 + deg p`**。 -/
theorem totalDegree_X_mul_add_X_nat (a b : ℕ) (hab : a ≠ b)
    (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (MvPolynomial.X a * p + MvPolynomial.X b).totalDegree = 1 + p.totalDegree := by
  have h1 : (MvPolynomial.X a * p : MvPolynomial ℕ ℝ).totalDegree = 1 + p.totalDegree :=
    totalDegree_X_mul_eq_nat a p hp
  have h2 : (MvPolynomial.X b : MvPolynomial ℕ ℝ).totalDegree = 1 :=
    MvPolynomial.totalDegree_X _
  rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
  · exact h1
  · rw [h2, h1]; omega


/-- **链的列表表示**——**每层都是 \MLayer 1 1\u3002** -/
abbrev ChainList := List (MLayer 1 1)

/-- **一层的累积步**：**`p ↦ X off · p + X (off+1)`，`off ↦ off + 2`**（`ℕ` 下标，无界）。 -/
noncomputable def stepNat (acc : ℕ × MvPolynomial ℕ ℝ) : ℕ × MvPolynomial ℕ ℝ :=
  (acc.1 + 2, MvPolynomial.X acc.1 * acc.2 + MvPolynomial.X (acc.1 + 1))

/-- ⭐⭐ **`stepNat` 的次数步**：**`deg` 恰好加 1**（当输入非零且 `deg ≥ 1`）。 -/
theorem stepNat_snd_totalDegree (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    (stepNat (off, p)).2.totalDegree = 1 + p.totalDegree := by
  simp only [stepNat]
  exact totalDegree_X_mul_add_X_nat off (off + 1) (by omega) p hp hdeg

/-- ⭐⭐ **`stepNat` 保持非零**。 -/
theorem stepNat_snd_ne_zero (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    (stepNat (off, p)).2 ≠ 0 := by
  intro h
  have h1 := stepNat_snd_totalDegree off p hp hdeg
  rw [h, MvPolynomial.totalDegree_zero] at h1
  omega

/-- ⭐⭐ **`stepNat` 保持 `deg ≥ 1`**。 -/
theorem stepNat_snd_degree_pos (off : ℕ) (p : MvPolynomial ℕ ℝ) (hp : p ≠ 0)
    (hdeg : 1 ≤ p.totalDegree) :
    1 ≤ (stepNat (off, p)).2.totalDegree := by
  rw [stepNat_snd_totalDegree off p hp hdeg]
  omega

/-- **链的输出多项式（`ℕ` 下标版）**——**`foldl` 逐层累积。** -/
noncomputable def chainNatPoly (ls : ChainList) (p : MvPolynomial ℕ ℝ) : MvPolynomial ℕ ℝ :=
  (ls.foldl (fun acc _ => stepNat acc) (0, p)).2


/-- ⭐⭐⭐ **`foldl` 的次数：每层恰好加一**--

**⚠ 这是 `List.foldl` 的【通用**归纳：不需要展开 `chainNatPoly` 的递归定义，
只需对列表结构递归，每步用 `stepNat_snd_totalDegree`。**

**⚠ 前提 `1 ≤ acc.2.totalDegree` 由 `stepNat_snd_degree_pos` 传递。** -/
theorem foldl_step_totalDegree :
    ∀ (ls : ChainList) (acc : ℕ × MvPolynomial ℕ ℝ),
      acc.2 ≠ 0 → 1 ≤ acc.2.totalDegree →
      (ls.foldl (fun a _ => stepNat a) acc).2.totalDegree = acc.2.totalDegree + ls.length
  | [], acc, _, _ => by
      simp
  | l :: ls, acc, hne, hdeg => by
      rw [List.foldl_cons]
      have hne' : (stepNat acc).2 ≠ 0 := stepNat_snd_ne_zero acc.1 acc.2 hne hdeg
      have hdeg' : 1 ≤ (stepNat acc).2.totalDegree :=
        stepNat_snd_degree_pos acc.1 acc.2 hne hdeg
      rw [foldl_step_totalDegree ls (stepNat acc) hne' hdeg']
      rw [stepNat_snd_totalDegree acc.1 acc.2 hne hdeg]
      simp only [List.length_cons]
      omega

/-- ⭐⭐⭐ **链多项式的次数 = deg p + 层数**（当 `p ≠ 0` 且 `1 ≤ deg p`）。

**⚠ 这是第 14–32 轮一直没能拿到的那条。** -/
theorem chainNatPoly_totalDegree (ls : ChainList) (p : MvPolynomial ℕ ℝ)
    (hp : p ≠ 0) (hdeg : 1 ≤ p.totalDegree) :
    (chainNatPoly ls p).totalDegree = p.totalDegree + ls.length := by
  simp only [chainNatPoly]
  have := foldl_step_totalDegree ls (0, p) hp hdeg
  simpa using this


/-- **`ℕ` 下标的数值累积步**——**与 `stepNat` 逐字对应**（把多项式乘加换成实数乘加）。 -/
noncomputable def stepAct (g : ℕ → ℝ) (acc : ℕ × ℝ) : ℕ × ℝ :=
  (acc.1 + 2, g acc.1 * acc.2 + g (acc.1 + 1))

/-- **链的数值作用（`ℕ` 下标版）**。 -/
noncomputable def chainNatAct (ls : ChainList) (g : ℕ → ℝ) (x : ℝ) : ℝ :=
  (ls.foldl (fun acc _ => stepAct g acc) (0, x)).2

/-- ⭐⭐ **`stepAct` 与 `stepNat` 在求值下一致**——**对接的原子步骤。** -/
theorem stepNat_eval (g : ℕ → ℝ) (off : ℕ) (p : MvPolynomial ℕ ℝ) :
    (stepNat (off, p)).2.eval g = (stepAct g (off, p.eval g)).2 := by
  simp only [stepNat, stepAct, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_X]

/-- ⭐⭐⭐ **载体与数值作用一致**：**`chainNatPoly` 的求值 = `chainNatAct`。**

**⚠ 对 `List.foldl` 归纳，每步用 `stepNat_eval`——【不展开任何递归定义**。** -/
theorem foldl_eval_act :
    ∀ (ls : ChainList) (g : ℕ → ℝ) (acc : ℕ × MvPolynomial ℕ ℝ),
      (ls.foldl (fun a _ => stepNat a) acc).2.eval g
        = (ls.foldl (fun a _ => stepAct g a) (acc.1, acc.2.eval g)).2
  | [], g, acc => rfl
  | l :: ls, g, acc => by
      obtain ⟨off, p⟩ := acc
      show (List.foldl (fun a _ => stepNat a) (stepNat (off, p)) ls).2.eval g
        = (List.foldl (fun a _ => stepAct g a) (stepAct g (off, p.eval g)) ls).2
      have := foldl_eval_act ls g (stepNat (off, p))
      simp only [stepNat, stepAct] at this ⊢
      simpa using this

/-- ⭐⭐⭐ **最终对接**：**`chainNatPoly ls p` 在 `g` 处的值 = `chainNatAct ls g (p.eval g)`。** -/
theorem chainNatPoly_eval_act (ls : ChainList) (p : MvPolynomial ℕ ℝ) (g : ℕ → ℝ) :
    (chainNatPoly ls p).eval g = chainNatAct ls g (p.eval g) := by
  simp only [chainNatPoly, chainNatAct]
  exact foldl_eval_act ls g (0, p)


/-- **列表到 `ChainOne` 的翻译**——**两者的唯一关系，是一个函数。** -/
def listToChainOne : ChainList → ChainOne
  | [] => ChainOne.idf
  | l :: ls => ChainOne.cons l (listToChainOne ls)

/-- ⭐ **翻译保持层数**：**`chainOneDepth` = 列表长度**。 -/
theorem chainOneDepth_listToChainOne : ∀ (ls : ChainList),
    chainOneDepth (listToChainOne ls) = ls.length
  | [] => rfl
  | l :: ls => by
      simp only [listToChainOne, chainOneDepth, List.length_cons,
        chainOneDepth_listToChainOne ls]

/-- ⭐⭐⭐ **数值作用一致**：**`ℕ` 下标的作用就是 `ChainOne` 的作用**，
**前提是 `g` 取 `readSlot gN`（界外为 0）。**

**⚠ 这把两个载体连了起来：`ℕ` 下标版（无界、`foldl`、次数界已知）与
`ChainOne` 版（已与 `flatChainAct` 连接，第 17 轮）。** -/
theorem chainNatAct_eq_chainOneAct {N : ℕ} : ∀ (ls : ChainList),
    ∀ (acc : ℕ × ℝ) (gN : Fin N → ℝ),
      (ls.foldl (fun a _ => stepAct (fun k => readSlot gN k) a) acc).2
        = chainOneAct (listToChainOne ls) acc.1 gN acc.2
  | [] => by
      intro acc gN
      simp only [List.foldl_nil, listToChainOne, chainOneAct]
  | l :: ls => by
      intro acc gN
      rw [List.foldl_cons]
      have hstep : stepAct (fun k => readSlot gN k) acc
          = (acc.1 + 2, readSlot gN acc.1 * acc.2 + readSlot gN (acc.1 + 1)) := rfl
      rw [hstep]
      have hcons : chainOneAct (listToChainOne (l :: ls)) acc.1 gN acc.2
          = chainOneAct (listToChainOne ls) (acc.1 + 2) gN
              (readSlot gN acc.1 * acc.2 + readSlot gN (acc.1 + 1)) := by
        simp only [listToChainOne]
        exact chainOneAct_cons l (listToChainOne ls) acc.1 gN acc.2
      rw [hcons]
      exact chainNatAct_eq_chainOneAct ls (acc.1 + 2, readSlot gN acc.1 * acc.2
        + readSlot gN (acc.1 + 1)) gN




end Lattice.Core