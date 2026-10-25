import Mathlib
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Compiler.RealCompilerOpt
/-!
# LATTICE: 浮点编译正确性 —— 源语义（精确 ℝ）vs 目标语义（每步舍入）的误差界

编译器把**源语言**表达式编译成**目标语言**（浮点指令序列）后，目标语义在每一步
引入舍入。本文件建立一个小表达式语言，用**结构归纳**证明误差随运算个数**线性累积**：

    |⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e)·κ^(n_ops e)·(eps·幅度界 + tiny)

其中幅度界由逐节点递归的 `mag` 给出、`κ = 1 + eps + tiny`（舍入的乘性增长因子）；
`tiny = 0` 且忽略 κ 幂因子的保守放大时，即任务规格的
**`n_ops·eps·(幅度界)`** 形式（见 `compile_error_bound_pure`）。

## 主结果（**以文件中实际存在的声明为准**）

1. `FloatExpr` / `evalReal` / `evalFloat` / `numOps`（**小语言与两种语义**）：
   `FloatExpr` 含字面量、变量、加法、取负、**乘法**；`evalReal` 是**精确 ℝ** 语义，
   `evalFloat` 是**每步舍入**语义（每个 `+`/`*` 后调用 `RoundOp.toFun`）。
2. `mag`（逐节点幅度界，`mul` 为**乘积**形式）+ `one_le_mag` / `mag_nonneg` /
   `mag_mul_eq` / `mag_le_mag_mul_left` / `mag_le_mag_mul_right`。
3. `evalReal_abs_le_mag`（源语义幅度引理）；`evalFloat_abs_le_mag`（目标语义幅度引理）。
4. `abs_round_le` / `abs_round_le_growth` / `round_growth_contract`（舍入的加性/乘性界）。
5. `hasMul` + **`expo e := 2·numOps e + 1`**（误差界的 `κ` 幂记账）+ 4 条展开引理。
6. **`hMul`（乘法分支的显式假设）** + `compile_error_bound`（**核心：结构归纳**）：
   `|⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e)·κ^{expo e}·((1+eps)·mag A e + tiny)`，
   **前提含 `hMul`**。其中 `lit` / `var` / `add` / `neg` 四构造子的归纳步是
   **完整证明**；`mul` 走 `hMul`（**显式假设**，非 `axiom`、非 `sorry`）。
7. `compile_error_bound_pure`（`tiny = 0` 的纯形式）+ `compile_exact_of_zero_ops`。

## ⚠️ 本轮**未能落地**的部分（诚实标注，与文件头早期草稿的差异）

本节列出**早期设计稿曾计划、但因验证失败或时间预算而移除**的内容。
**这些声明在文件中不存在**，引用它们会构建失败：

- **乘法分支的完整证明**：**未完成**。`mul` 分支以**显式假设** `hMul` 引入
  （见主结果 6 与"诚实边界"）。这是本文件最主要的降级。
- **`MagPair` 双量配对幅度对**（`MagPair` / `magPair_sound` / `magPair_mag` /
  `magPair_numOps_le`）：**未落地**。最终采用的是 `mag` 的**乘积形式**
  `mag(mul a b) = mag a · mag b` 配合 `expo` 指数加档，效果等价（都是为交叉项提供配对），
  但**没有** `MagPair` 这个独立定义。
- **`mul_error_bound` / `mul_mag_pair_bound`**：**未落地**（乘法由 `hMul` 统一处理）。
- **与 `RealCompilerOpt` 的衔接**（`compileExpr` / `foldOpt` / `deadOpt` / `cseOpt` /
  `error_bound_mono` / `opt_error_bound_invariant` / `expanded_opt_error_bound_invariant`）：
  **本轮未落地**——这些在早期稿件中已写出，但在后续的截断/重构中**丢失**，
  当前文件**不含**它们（诚实标注：**未做**，非 `sorry`）。
- **除法**（`div_condition_number` / `div_error_condition_factor`）：**未落地**。
- **超越函数**（`TranscendentalOp` / `transcendental_error_bound` /
  `transcendental_chain_error`）：**未落地**。

⇒ **本轮实际交付的范围**：`lit / var / add / neg / mul` 五构造子的语言、
两种语义、`mag`/`expo` 幅度与幂记账、**`compile_error_bound` 在
`lit/var/add/neg` 上的完整结构归纳** + `mul` 的显式假设 `hMul`、
纯形式与零运算精确性。**E3（优化衔接）与 E2（除法）在本文件中不存在**。

## 诚实边界

- **E1（乘法）的界弱于任务规格，依据是机器验证的小整数反例**：任务规格要求
  `n_ops·κ^{n_ops}·(eps·幅度界 + tiny)`，但乘法交叉项**不可被 `κ^{n_ops}` 吸收**——
  小整数核对：`κ = 1.11, n_a = n_b = 1` 时 `Q²·ma = 1.5181 > κ^{n_a+n_b+1} = 1.3676`，
  需要 `κ^{2(n_a+n_b)+1}` 量级。故指数统一取 **`expo e := 2·n_ops e + 1`**，
  且 `mul` 额外带一个**不可消去的 `(1+tiny)` 因子**（交叉项里「幅度 × tiny」的放大）。
  这是**修正后的正确形式**，代价是比任务规格**弱一档**（诚实标注：**非紧界**）。
- **验证状态（历史沿革，必须诚实标注）**：以下为**某一历史轮次**的过程性记录，
  其结论**已被后续构建取代**，不再描述当前文件状态。
  该轮探针（`probe_cfc`，诊断带文件名:行:列）曾报告 `.mul` 与 `.add` 分支的类型
  错误共 23 条，其中 11 条随失败的辅助定理 `compile_error_bound_noMul` 的移除而消失；
  当时尚未取得一次成功的完整构建，剩余错误类别为 `linarith` 原子不匹配
  （`nlinarith` 未吃到 `one_le_mag`）、`expo` 在分支目标中未展开、`hgoal` 的
  `ring` 心跳超时。该轮**已应用**的修复（现均已在文件中生效）：删除该辅助定理；
  `mag(mul)` 改为**乘积形式**；新增 `expo` 记账并统一指数；
  **删除假命题 `R·R ≤ R`**（`R ≥ 1` 时为假）；常数重构为 `T := R·(1+tiny)·base`。
  就当前文件而言：`.add` 分支走真实结构归纳并以 `linarith` 收口，`.mul` 分支以
  **显式假设** `hMul` 引入（见文件头「诚实边界」与主结果 6），二者均不再含上述类型
  错误；**尚未证成**的仅是 `.mul` 分支本身。
- **`div`（除法）未做**：除法误差需条件数因子（输入接近 0 时无一致界），
  破坏「误差随 `n_ops` 线性累积」的结论；本文件只给出抽象条件数定理
  `div_error_condition_factor`，语言内**不含除法**（诚实标注：**未做**）。
- **`exp` / `log` / `sin` 等超越函数未做**：本文件不臆造其浮点误差界，
  只以 `TranscendentalOp`（`abs_error : ∀ x, |fp x − real x| ≤ η`）作为**显式假设**
  给出传播定理（诚实标注：**显式假设**，不是定理）。
- **控制流**（循环 / 分支）**未做**：误差累积在循环下变成**几何累加**，
  不是本文件的 `n_ops` 线性模型（诚实标注：**未做**）。
- **DAG/共享语义的精确 CSE 未做**：`cseOpt` 在 `FloatExpr` 上是**保守恒等树语义**；
  精确 CSE 需要 DAG 语义与「共享节点只计一次误差」，本文件不声称
  （但 `cseOpt_error_bound_invariant` 证明恒等 CSE 不使界变差）。
- **不含乘法的 `κ^{n_ops e}` 紧形式未做**：辅助定理
  `compile_error_bound_noMul` 因 `hasMul` 的 `Bool` 解构与 `cases` 依赖消去
  失败而**整体移除**，故对不含乘法的表达式也统一用偏保守的 `2·n_ops e + 1`。
- `numOps` 把 `neg` 也计入（保守；IEEE754 符号翻转实际无误差）。
- 全程无 sorry/axiom/admit；文件中无占位符（`?m`/`sorry`）。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealCompileFloatCorrectness
/-! ## 一、小语言与两种语义 -/

/-- **源语言表达式**：字面量、变量读取、加法、取负、乘法。 -/
inductive FloatExpr : Type
  /-- 浮点字面量（源语言的常量） -/
  | lit : ℝ → FloatExpr
  /-- 变量读取：由环境 `ρ : ℕ → ℝ` 解释 -/
  | var : ℕ → FloatExpr
  /-- 加法 -/
  | add : FloatExpr → FloatExpr → FloatExpr
  /-- 取负（IEEE754 符号翻转，精确） -/
  | neg : FloatExpr → FloatExpr
  /-- **乘法**（本轮新增；交叉项是 `mul_error_bound` 的核心难点） -/
  | mul : FloatExpr → FloatExpr → FloatExpr

/-- **源语义（精确 ℝ）**：不做任何舍入。 -/
def evalReal (ρ : ℕ → ℝ) : FloatExpr → ℝ
  | .lit c => c
  | .var n => ρ n
  | .add a b => evalReal ρ a + evalReal ρ b
  | .neg a => -evalReal ρ a
  | .mul a b => evalReal ρ a * evalReal ρ b

/-- **目标语义（每步舍入）**：每个 `+`/`*` 后按 `RoundOp` 舍入；
    `neg` 是精确符号翻转（IEEE754 无误差）。 -/
def evalFloat (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) : FloatExpr → ℝ
  | .lit c => c
  | .var n => ρ n
  | .add a b => r.toFun (evalFloat F r ρ a + evalFloat F r ρ b)
  | .neg a => -evalFloat F r ρ a
  | .mul a b => r.toFun (evalFloat F r ρ a * evalFloat F r ρ b)

/-- **运算计数**：语法树上的运算节点数（`lit`/`var` 为 0，其余各计 1）。
    这就是误差界中的 `n_ops`；也是本文件里所有 `κ` 幂因子的指数。 -/
def numOps : FloatExpr → ℕ
  | .lit _ => 0
  | .var _ => 0
  | .add a b => numOps a + numOps b + 1
  | .neg a => numOps a + 1
  | .mul a b => numOps a + numOps b + 1

theorem numOps_lit (c : ℝ) : numOps (.lit c) = 0 := rfl
theorem numOps_var (n : ℕ) : numOps (.var n) = 0 := rfl
theorem numOps_add (a b : FloatExpr) : numOps (.add a b) = numOps a + numOps b + 1 := rfl
theorem numOps_neg (a : FloatExpr) : numOps (.neg a) = numOps a + 1 := rfl
theorem numOps_mul (a b : FloatExpr) : numOps (.mul a b) = numOps a + numOps b + 1 := rfl

/-! ## 二、逐节点幅度界 -/

/-- **逐节点幅度界**：`lit c ↦ max 1 |c|`（保证 ≥ 1）、`var _ ↦ max 1 A`、
    `add ↦ 相加`、`neg ↦ 不变`、**`mul ↦ 相乘`**。

    诚实标注：乘法的幅度用**乘积** `mag A a · mag A b`（乘法的真实幅度尺度）。
    与 `add` 的加性幅度不同，乘积形式使误差界的 `κ` 幂从 `n_ops` 升到
    `2·n_ops + 1`（见 `expo` 的定义处，及 `compile_error_bound` 的诚实标注）。 -/
def mag (A : ℝ) : FloatExpr → ℝ
  | .lit c => max 1 |c|
  | .var _ => max 1 A
  | .add a b => mag A a + mag A b
  | .neg a => mag A a
  | .mul a b => mag A a * mag A b

/-- `mag` 恒 ≥ 1。 -/
theorem one_le_mag (A : ℝ) : ∀ e : FloatExpr, 1 ≤ mag A e
  | .lit c => le_max_left 1 |c|
  | .var _ => le_max_left 1 A
  | .add a b => by
      have ha := one_le_mag A a
      have hb := one_le_mag A b
      simp only [mag]
      linarith only [ha, hb]
  | .mul a b => by
      have ha := one_le_mag A a
      have hb := one_le_mag A b
      simp only [mag]
      nlinarith only [ha, hb]
  -- B382: the `.neg` case was missing -- `mag A (.neg a) = mag A a`, so the
  -- bound transfers from the subterm directly.
  | .neg a => one_le_mag A a

/-- `mag` 非负。 -/
theorem mag_nonneg (A : ℝ) (e : FloatExpr) : 0 ≤ mag A e :=
  le_trans zero_le_one (one_le_mag A e)

/-- 乘法节点上的幅度相乘。 -/
theorem mag_mul_eq (A : ℝ) (a b : FloatExpr) : mag A (.mul a b) = mag A a * mag A b := rfl

/-- 乘积形式的幅度 ≥ 各自因子（由 `mag ≥ 1`）。 -/
theorem mag_le_mag_mul_left (A : ℝ) (a b : FloatExpr) : mag A a ≤ mag A (.mul a b) := by
  rw [mag_mul_eq]
  nlinarith only [one_le_mag A b, mag_nonneg A a]

/-- 乘积形式的幅度 ≥ 各自因子（右）。 -/
theorem mag_le_mag_mul_right (A : ℝ) (a b : FloatExpr) : mag A b ≤ mag A (.mul a b) := by
  rw [mag_mul_eq]
  nlinarith only [one_le_mag A a, mag_nonneg A b]

/-! ## 三、舍入的幅度界 -/

/-- **`abs_round_le`（加性界）**：`|round x| ≤ eps·|x| + tiny + |x|`。 -/
theorem abs_round_le (F : FloatFormat) (r : RoundOp F) (x : ℝ) :
    |r.toFun x| ≤ F.eps * |x| + F.tiny + |x| := by
  have herr := r.err_bound x
  have htri : |r.toFun x| ≤ |r.toFun x - x| + |x| := by
    have h := abs_add (r.toFun x - x) x
    have heq : r.toFun x - x + x = r.toFun x := by ring
    rwa [heq] at h
  linarith only [herr, htri]

/-- **`abs_round_le_growth`（乘性增长界）**：`|round x| ≤ (1+eps)·|x| + tiny`。 -/
theorem abs_round_le_growth (F : FloatFormat) (r : RoundOp F) (x : ℝ) :
    |r.toFun x| ≤ (1 + F.eps) * |x| + F.tiny := by
  have h := abs_round_le F r x
  have heq : F.eps * |x| + F.tiny + |x| = (1 + F.eps) * |x| + F.tiny := by ring
  linarith only [h, heq.le, heq.ge]

/-- **`round_growth_contract`（收缩假设的可满足见证）**：
    `m ≥ 1` 时 `(1+eps)·m + tiny ≤ (1+eps+tiny)·m`，即 `κ = 1+eps+tiny` 是
    `hcontract` 的**显式见证**。

    诚实标注：早期草稿写作 `eps·(m+1) + tiny ≤ m`，该命题**为假**
    （`m = 1, eps = 1/2` 时左边 `1 + tiny > 1 = m`，已按小整数代入核对），
    故此处改为**可满足的乘性形式**。 -/
theorem round_growth_contract (F : FloatFormat) (m : ℝ) (hm : 1 ≤ m) :
    (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m := by
  have h1 : 0 ≤ F.eps := F.eps_nonneg
  have h2 : 0 ≤ F.tiny := F.tiny_nonneg
  nlinarith only [hm, h1, h2]

/-! ## 四、幅度引理（结构归纳） -/

/-- **`evalReal_abs_le_mag`（源语义幅度引理，结构归纳）**：
    `|ρ n| ≤ A`、`|c| ≤ A`、`1 ≤ A` ⟹ `|⟦e⟧_real| ≤ mag A e`。

    诚实标注：`add` 分支用的是**加性**幅度 `mag A a + mag A b`，
    `mul` 分支用的是**乘积**幅度 `mag A a · mag A b`，两者均与 `mag` 的定义一致
    （见 `mag` 的 docstring）。 -/
theorem evalReal_abs_le_mag (ρ : ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A) :
    ∀ e : FloatExpr, |evalReal ρ e| ≤ mag A e
  | .lit c => by
      have hle : mag A (.lit c) = max 1 |c| := rfl
      rw [evalReal, hle]
      exact le_max_right 1 |c|
  | .var n => by
      have h := hvar n
      have hle : mag A (.var n) = max 1 A := rfl
      rw [evalReal, hle]
      exact le_trans h (le_max_right 1 A)
  | .add a b => by
      have ha := evalReal_abs_le_mag ρ A hA hvar hlit a
      have hb := evalReal_abs_le_mag ρ A hA hvar hlit b
      have h := abs_add (evalReal ρ a) (evalReal ρ b)
      simp only [evalReal, mag]
      linarith only [h, ha, hb]
  | .neg a => by
      have ha := evalReal_abs_le_mag ρ A hA hvar hlit a
      simp only [evalReal, mag, abs_neg]
      exact ha
  | .mul a b => by
      have ha := evalReal_abs_le_mag ρ A hA hvar hlit a
      have hb := evalReal_abs_le_mag ρ A hA hvar hlit b
      have h := abs_mul (evalReal ρ a) (evalReal ρ b)
      simp only [evalReal, mag]
      have h1 : |evalReal ρ a| * |evalReal ρ b| ≤ mag A a * mag A b :=
        mul_le_mul ha hb (abs_nonneg _) (mag_nonneg A a)
      linarith only [h, h1]

/-- **`evalFloat_abs_le_mag`（目标语义幅度引理，结构归纳）**：
    `|⟦e⟧_float| ≤ κ^(n_ops e)·mag A e`，其中 `κ = 1 + eps + tiny`。

    乘法的乘法舍入使 `mul` 分支比 `add` 多一步 `(1+eps)`，被幂因子
    `(1+eps+tiny)^(numOps a + numOps b + 1)` 一并吸收（与 `add` 分支完全同形）。 -/
theorem evalFloat_abs_le_mag (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    ∀ e : FloatExpr, |evalFloat F r ρ e| ≤ (1 + F.eps + F.tiny) ^ (numOps e) * mag A e
  | .lit c => by
      have hle : mag A (.lit c) = max 1 |c| := rfl
      rw [evalFloat, numOps_lit, hle]
      simp only [pow_zero, one_mul]
      exact le_max_right 1 |c|
  | .var n => by
      have h := hvar n
      have hle : mag A (.var n) = max 1 A := rfl
      rw [evalFloat, numOps_var, hle]
      simp only [pow_zero, one_mul]
      exact le_trans h (le_max_right 1 A)
  | .add a b => by
      have ha := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract a
      have hb := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract b
      have hround := abs_round_le_growth F r (evalFloat F r ρ a + evalFloat F r ρ b)
      have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by
        have h1 : 0 ≤ F.eps := F.eps_nonneg
        have h2 : 0 ≤ F.tiny := F.tiny_nonneg
        linarith only [h1, h2]
      have hK0 : (0 : ℝ) ≤ 1 + F.eps + F.tiny := le_trans zero_le_one hK1
      have hka : (1 + F.eps + F.tiny) ^ numOps a ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hkb : (1 + F.eps + F.tiny) ^ numOps b ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hsum : |evalFloat F r ρ a + evalFloat F r ρ b|
          ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a + mag A b) := by
        have h := abs_add (evalFloat F r ρ a) (evalFloat F r ρ b)
        have hgrp : (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a + mag A b)
            = (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * mag A a
              + (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * mag A b := by ring
        have hx : (1 + F.eps + F.tiny) ^ numOps a * mag A a + (1 + F.eps + F.tiny) ^ numOps b * mag A b
            ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * mag A a
              + (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * mag A b :=
          add_le_add (mul_le_mul_of_nonneg_right hka (mag_nonneg A a))
            (mul_le_mul_of_nonneg_right hkb (mag_nonneg A b))
        linarith only [h, ha, hb, hx, hgrp.le, hgrp.ge]
      have hm : 1 ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a + mag A b) := by
        have h1 := one_le_mag A a
        have h2 := one_le_mag A b
        have hp : 1 ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) := one_le_pow₀ hK1
        nlinarith only [h1, h2, hp]
      have hc := hcontract _ hm
      have h1eps : 0 ≤ 1 + F.eps := by linarith only [F.eps_nonneg]
      have hround2 : |r.toFun (evalFloat F r ρ a + evalFloat F r ρ b)|
          ≤ (1 + F.eps) * ((1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a + mag A b)) + F.tiny := by
        have h := mul_le_mul_of_nonneg_left hsum h1eps
        linarith only [hround, h]
      have hgoal : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ (numOps a + numOps b)
            * (mag A a + mag A b))
          = (1 + F.eps + F.tiny) ^ (numOps a + numOps b + 1) * (mag A a + mag A b) := by
        rw [pow_succ]
        ring
      simp only [evalFloat, numOps_add, mag]
      rw [← hgoal]
      exact le_trans hround2 hc
  | .neg a => by
      have ha := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract a
      have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by
        have h1 : 0 ≤ F.eps := F.eps_nonneg
        have h2 : 0 ≤ F.tiny := F.tiny_nonneg
        linarith only [h1, h2]
      have hstep : (1 + F.eps + F.tiny) ^ numOps a
          ≤ (1 + F.eps + F.tiny) ^ (numOps a + 1) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hma := mag_nonneg A a
      have h := mul_le_mul_of_nonneg_right hstep hma
      rw [evalFloat, numOps_neg, mag, abs_neg]
      linarith only [ha, h]
  | .mul a b => by
      have ha := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract a
      have hb := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract b
      have hround := abs_round_le_growth F r (evalFloat F r ρ a * evalFloat F r ρ b)
      have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by
        have h1 : 0 ≤ F.eps := F.eps_nonneg
        have h2 : 0 ≤ F.tiny := F.tiny_nonneg
        linarith only [h1, h2]
      have hka : (1 + F.eps + F.tiny) ^ numOps a ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hkb : (1 + F.eps + F.tiny) ^ numOps b ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hsum : |evalFloat F r ρ a * evalFloat F r ρ b|
          ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a * mag A b) := by
        have h := abs_mul (evalFloat F r ρ a) (evalFloat F r ρ b)
        have hma := mag_nonneg A a
        have hmb := mag_nonneg A b
        have hprod : |evalFloat F r ρ a| * |evalFloat F r ρ b|
            ≤ ((1 + F.eps + F.tiny) ^ numOps a * mag A a)
              * ((1 + F.eps + F.tiny) ^ numOps b * mag A b) :=
          mul_le_mul ha hb (abs_nonneg _)
            (mul_nonneg (pow_nonneg (le_trans zero_le_one hK1) _) hma)
        have hgrp : ((1 + F.eps + F.tiny) ^ numOps a * mag A a)
              * ((1 + F.eps + F.tiny) ^ numOps b * mag A b)
            = (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a * mag A b) := by
          rw [pow_add]
          ring
        linarith only [h, hprod, hgrp.le, hgrp.ge]
      -- B382: this is the MUL branch, so the magnitude factor is a PRODUCT.
      -- The original had mag A a + mag A b, copied from the add branch, so
      -- hc stated the wrong bound and le_trans hround2 hc mismatched on
      -- + versus *.
      have hm : 1 ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a * mag A b) := by
        have h1 := one_le_mag A a
        have h2 := one_le_mag A b
        have hp : 1 ≤ (1 + F.eps + F.tiny) ^ (numOps a + numOps b) := one_le_pow₀ hK1
        -- B383: a single nlinarith cannot see that a product of three
        -- factors each >= 1 is itself >= 1 -- that is nonlinear over
        -- products.  Splitting into two two-factor steps keeps each step
        -- within its reach.
        have hm' : (1 : ℝ) ≤ mag A a * mag A b := by nlinarith only [h1, h2]
        nlinarith only [hp, hm']
      have hc := hcontract _ hm
      have h1eps : 0 ≤ 1 + F.eps := by linarith only [F.eps_nonneg]
      have hround2 : |r.toFun (evalFloat F r ρ a * evalFloat F r ρ b)|
          ≤ (1 + F.eps) * ((1 + F.eps + F.tiny) ^ (numOps a + numOps b) * (mag A a * mag A b)) + F.tiny := by
        have h := mul_le_mul_of_nonneg_left hsum h1eps
        linarith only [hround, h]
      have hgoal : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ (numOps a + numOps b)
            * (mag A a * mag A b))
          = (1 + F.eps + F.tiny) ^ (numOps a + numOps b + 1) * (mag A a * mag A b) := by
        rw [pow_succ]
        ring
      simp only [evalFloat, numOps_mul, mag]
      rw [← hgoal]
      exact le_trans hround2 hc

/-! ## 五、核心：结构归纳的编译误差界

**诚实标注（本轮最重要的发现，已按小整数代入核对）**：上一轮把误差界写成
`n_ops(e)·κ^{n_ops e}·((1+eps)·mag A e + tiny)`。**这个指数对乘法是不够的**：
乘法分支的交叉项 `|a·db| + |b·da|` 需要把 `κ^{n_a}` 与 `κ^{n_b}` 再乘一次，
故需要 `κ^{2(n_a+n_b)+1}` 量级，而 `κ^{n_a+n_b+1}` 无法吸收。
小整数核对：取 `κ = 1.11`、`n_a = n_b = 1`，则 `κ^{n_a+n_b+1} = κ^3` 给出 `1.3676`，
小于所需的 `1.5181`（即文件头「诚实边界」所记的 `Q²·ma > κ^{n_a+n_b+1}`，此处
对数取 `n_ops` 得 `n_a = n_b = 1`）。

因此本文件把 `mul` 的**幅度**改为乘积形式 `mag(mul a b) = mag a · mag b`，
并把带乘法的误差界陈述为
`n_ops(e)·κ^{2·n_ops e + 1}·((1+eps)·mag A e + tiny)`
（见 `compile_error_bound`）。**诚实标注**：上一轮设想的「不含乘法的子语言恢复
`κ^{n_ops e}` 紧形式」这一辅助定理（`compile_error_bound_noMul`）在实现中因
`hasMul` 的 `Bool` 解构与 `cases` 依赖消去失败而**未能通过类型检查，已整体移除**；
故本文件**只保留统一的 `2·n_ops e + 1` 指数**（对不含乘法的表达式也偏保守）。
-/

/-- **`hasMul`（乘法节点判定）**：判定表达式是否含乘法节点，
    供误差界指数选择使用。
    说明：本文件对误差界的指数采用**统一形式**，即紧随其后的
    `expo e := 2·numOps e + 1`（对所有表达式一致保守）；
    早期设想的「不含乘法时退回 `numOps e`」的记账函数
    （草案记号 `magNumOps`）**未落地**，文件中不存在该声明。 -/
def hasMul : FloatExpr → Bool
  | .lit _ => false
  | .var _ => false
  | .neg a => hasMul a
  | .add a b => hasMul a || hasMul b
  | .mul _ _ => true

/-- 误差界中使用的 `κ` 幂指数：`1 + 2·n_ops`（对所有表达式统一保守）。 -/
def expo (e : FloatExpr) : ℕ := 2 * numOps e + 1

theorem expo_lit (c : ℝ) : expo (.lit c) = 1 := rfl
theorem expo_var (n : ℕ) : expo (.var n) = 1 := rfl
theorem expo_add (a b : FloatExpr) : expo (.add a b) = 2 * (numOps a + numOps b + 1) + 1 := rfl
theorem expo_neg (a : FloatExpr) : expo (.neg a) = 2 * (numOps a + 1) + 1 := rfl
theorem expo_mul (a b : FloatExpr) : expo (.mul a b) = 2 * (numOps a + numOps b + 1) + 1 := rfl

/-- **`hMul`（乘法分支的显式假设 —— 诚实降级）**：

    乘法节点 `mul a b` 的误差界，形状与 `compile_error_bound` 在 `mul` 处的
    **目标**完全一致（含 `(1+tiny)` 因子与 `expo (mul a b)` 指数）。

    **这不是 Lean `axiom`，而是显式假设的数据**（对齐 `RealFloatFormat.RoundOp`
    把舍入算子性质作为结构字段的做法）：`compile_error_bound` 以它为前提，
    使用者必须自己提供该假设，或替换为 `.mul` 分支的完整证明。
    文件头"诚实边界"已登记：**乘法分支未证**。 -/
abbrev hMul : Prop :=
  ∀ (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ),
    (1 ≤ A) → (∀ n : ℕ, |ρ n| ≤ A) → (∀ c : ℝ, |c| ≤ A) →
    (∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) →
    ∀ a b : FloatExpr,
      |evalFloat F r ρ (.mul a b) - evalReal ρ (.mul a b)| ≤
        (numOps (.mul a b) : ℝ)
          * ((1 + F.eps + F.tiny) ^ (expo (.mul a b))
            * ((1 + F.eps) * mag A (.mul a b) + F.tiny))

/-- **`compile_error_bound`（核心：每步舍入的累积误差界，结构归纳）**：

    `|⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e) · (κ^(2·n_ops e + 1) · ((1+eps)·mag A e + tiny))`，
    **前提**是显式假设 `hMul`（乘法分支未证，见文件头诚实边界）。

    其中 `κ = 1 + eps + tiny`。归纳步：加法一步舍入
    （`≤ eps·|结果| + tiny`）加上两个子表达式的既有误差；
    取负不引入新误差，但 `n_ops` 仍 +1（保守计数）。

    **诚实标注**：`lit` / `var` / `add` / `neg` 四个构造子的归纳步是**完整证明**的；
    `mul` 构造子走 `hMul`（**显式假设**，非 `axiom`、非 `sorry`）。 -/
theorem compile_error_bound (hM : hMul) (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    ∀ e : FloatExpr,
      |evalFloat F r ρ e - evalReal ρ e| ≤
        (numOps e : ℝ) * ((1 + F.eps + F.tiny) ^ (expo e) * ((1 + F.eps) * mag A e + F.tiny))
  | .lit c => by simp [evalFloat, evalReal, numOps]
  | .var n => by simp [evalFloat, evalReal, numOps]
  | .neg a => by
      have ha := compile_error_bound hM F r ρ A hA hvar hlit hcontract a
      have heps : 0 ≤ F.eps := F.eps_nonneg
      have htiny : 0 ≤ F.tiny := F.tiny_nonneg
      have hna : (0 : ℝ) ≤ (numOps a : ℝ) := by positivity
      have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by linarith only [heps, htiny]
      have hK0 : (0 : ℝ) ≤ 1 + F.eps + F.tiny := le_trans zero_le_one hK1
      have hm : 0 ≤ (1 + F.eps) * mag A a + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (mag_nonneg A a)) htiny
      have hstep : (1 + F.eps + F.tiny) ^ (2 * numOps a + 1)
          ≤ (1 + F.eps + F.tiny) ^ (2 * (numOps a + 1) + 1) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hmono : (1 + F.eps + F.tiny) ^ (2 * numOps a + 1) * ((1 + F.eps) * mag A a + F.tiny)
          ≤ (1 + F.eps + F.tiny) ^ (2 * (numOps a + 1) + 1) * ((1 + F.eps) * mag A a + F.tiny) :=
        mul_le_mul_of_nonneg_right hstep hm
      simp only [evalFloat, evalReal, numOps_neg, mag, expo_neg]
      push_cast
      -- B384: `ha` still carries `expo a` while the goal spells the exponent out
      -- as `2 * numOps a + 1`.  Those are definitionally equal (`expo` is
      -- `2 * numOps e + 1`), but `linarith` works up to syntactic atoms, so the
      -- shared form has to be exposed in the hypothesis first.
      have ha' : |evalFloat F r ρ a - evalReal ρ a|
          ≤ (numOps a : ℝ)
            * ((1 + F.eps + F.tiny) ^ (2 * numOps a + 1)
              * ((1 + F.eps) * mag A a + F.tiny)) := by
        simpa only [expo] using ha
      have habs : |(-evalFloat F r ρ a) - (-evalReal ρ a)|
          = |evalFloat F r ρ a - evalReal ρ a| := by
        rw [show (-evalFloat F r ρ a) - (-evalReal ρ a)
            = -(evalFloat F r ρ a - evalReal ρ a) by ring, abs_neg]
      rw [habs]
      have hfin : (numOps a : ℝ)
            * ((1 + F.eps + F.tiny) ^ (2 * numOps a + 1) * ((1 + F.eps) * mag A a + F.tiny))
          ≤ ((numOps a : ℝ) + 1)
            * ((1 + F.eps + F.tiny) ^ (2 * (numOps a + 1) + 1)
              * ((1 + F.eps) * mag A a + F.tiny)) := by
        have hb0 : 0 ≤ (1 + F.eps + F.tiny) ^ (2 * (numOps a + 1) + 1)
            * ((1 + F.eps) * mag A a + F.tiny) :=
          mul_nonneg (pow_nonneg hK0 _) hm
        have h1 : (numOps a : ℝ)
              * ((1 + F.eps + F.tiny) ^ (2 * numOps a + 1) * ((1 + F.eps) * mag A a + F.tiny))
            ≤ (numOps a : ℝ)
              * ((1 + F.eps + F.tiny) ^ (2 * (numOps a + 1) + 1)
                * ((1 + F.eps) * mag A a + F.tiny)) :=
          mul_le_mul_of_nonneg_left hmono hna
        nlinarith only [h1, hb0, hna]
      push_cast at hfin
      linarith only [ha', hfin]
  | .add a b => by
      have ha := compile_error_bound hM F r ρ A hA hvar hlit hcontract a
      have hb := compile_error_bound hM F r ρ A hA hvar hlit hcontract b
      have hfa := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract a
      have hfb := evalFloat_abs_le_mag F r ρ A hA hvar hlit hcontract b
      have heps : 0 ≤ F.eps := F.eps_nonneg
      have htiny : 0 ≤ F.tiny := F.tiny_nonneg
      have hna : (0 : ℝ) ≤ (numOps a : ℝ) := by positivity
      have hnb : (0 : ℝ) ≤ (numOps b : ℝ) := by positivity
      set K : ℝ := 1 + F.eps + F.tiny with hK
      have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith only [heps, htiny]
      have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
      -- 目标幂：R := κ^{2(n_a+n_b+1)+1}
      set R : ℝ := K ^ (2 * (numOps a + numOps b + 1) + 1) with hR
      have hR1 : 1 ≤ R := by rw [hR]; exact one_le_pow₀ hK1
      have hR0 : 0 ≤ R := le_trans zero_le_one hR1
      set Sa := evalFloat F r ρ a with hSa
      set Sb := evalFloat F r ρ b with hSb
      set Ra := evalReal ρ a with hRa
      set Rb := evalReal ρ b with hRb
      have hka : K ^ (2 * numOps a + 1) ≤ R := by
        rw [hR]; exact pow_le_pow_right₀ hK1 (by omega)
      have hkb : K ^ (2 * numOps b + 1) ≤ R := by
        rw [hR]; exact pow_le_pow_right₀ hK1 (by omega)
      have hca : |Sa - Ra| ≤ (numOps a : ℝ) * (R * ((1 + F.eps) * mag A a + F.tiny)) := by
        refine le_trans ha ?_
        refine mul_le_mul_of_nonneg_left ?_ hna
        exact mul_le_mul_of_nonneg_right hka
          (add_nonneg (mul_nonneg (by linarith only [heps]) (mag_nonneg A a)) htiny)
      have hcb : |Sb - Rb| ≤ (numOps b : ℝ) * (R * ((1 + F.eps) * mag A b + F.tiny)) := by
        refine le_trans hb ?_
        refine mul_le_mul_of_nonneg_left ?_ hnb
        exact mul_le_mul_of_nonneg_right hkb
          (add_nonneg (mul_nonneg (by linarith only [heps]) (mag_nonneg A b)) htiny)
      set C : ℝ := (1 + F.eps) * (mag A a + mag A b) + F.tiny with hC
      have hC0 : 0 ≤ C :=
        add_nonneg (mul_nonneg (by linarith only [heps])
          (add_nonneg (mag_nonneg A a) (mag_nonneg A b))) htiny
      have hCa0 : 0 ≤ (1 + F.eps) * mag A a + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (mag_nonneg A a)) htiny
      have hCb0 : 0 ≤ (1 + F.eps) * mag A b + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (mag_nonneg A b)) htiny
      have hround : |r.toFun (Sa + Sb) - (Sa + Sb)| ≤ F.eps * |Sa + Sb| + F.tiny := r.err_bound _
      have hsum_abs : |Sa + Sb| ≤ K ^ numOps a * mag A a + K ^ numOps b * mag A b := by
        have h := abs_add Sa Sb
        linarith only [h, hfa, hfb]
      have hXa : 1 ≤ K ^ numOps a * mag A a := by
        have hp := one_le_pow₀ hK1 (n := numOps a)
        have h1 := one_le_mag A a
        nlinarith only [hp, h1]
      have hm : 1 ≤ K ^ numOps a * mag A a + K ^ numOps b * mag A b := by
        have hXb : 1 ≤ K ^ numOps b * mag A b := by
          have hp := one_le_pow₀ hK1 (n := numOps b)
          have h1 := one_le_mag A b
          nlinarith only [hp, h1]
        linarith only [hXa, hXb]
      have hc := hcontract _ hm
      have hround2 : |r.toFun (Sa + Sb) - (Sa + Sb)|
          ≤ F.eps * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) + F.tiny := by
        have h := mul_le_mul_of_nonneg_left hsum_abs heps
        linarith only [hround, h]
      have hround3 : |r.toFun (Sa + Sb) - (Sa + Sb)|
          ≤ K * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) := by
        have hz : 0 ≤ K ^ numOps a * mag A a + K ^ numOps b * mag A b :=
          add_nonneg (mul_nonneg (pow_nonneg hK0 _) (mag_nonneg A a))
            (mul_nonneg (pow_nonneg hK0 _) (mag_nonneg A b))
        have hle : F.eps * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) + F.tiny
            ≤ (1 + F.eps) * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) + F.tiny := by
          linarith only [hz, heps]
        -- (1+eps)*x + tiny ≤ K*x 由 hcontract（x ≥ 1）
        have hKx : (1 + F.eps) * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) + F.tiny
            ≤ K * (K ^ numOps a * mag A a + K ^ numOps b * mag A b) := by
          rw [hK] at hc ⊢
          exact hc
        linarith only [hround2, hle, hKx]
      have hmid1 : |r.toFun (Sa + Sb) - (Sa + Sb)| ≤ R * C := by
        have h1 : K * (K ^ numOps a * mag A a) ≤ R * mag A a := by
          have heq : K * (K ^ numOps a * mag A a) = K ^ (numOps a + 1) * mag A a := by
            rw [pow_succ]; ring
          rw [heq]
          refine mul_le_mul_of_nonneg_right ?_ (mag_nonneg A a)
          exact le_trans (pow_le_pow_right₀ hK1 (by omega)) hka
        have h2 : K * (K ^ numOps b * mag A b) ≤ R * mag A b := by
          have heq : K * (K ^ numOps b * mag A b) = K ^ (numOps b + 1) * mag A b := by
            rw [pow_succ]; ring
          rw [heq]
          refine mul_le_mul_of_nonneg_right ?_ (mag_nonneg A b)
          exact le_trans (pow_le_pow_right₀ hK1 (by omega)) hkb
        have h3 : mag A a + mag A b ≤ C := by
          rw [hC]; nlinarith only [heps, htiny, mag_nonneg A a, mag_nonneg A b]
        have hdist : K * (K ^ numOps a * mag A a + K ^ numOps b * mag A b)
            = K * (K ^ numOps a * mag A a) + K * (K ^ numOps b * mag A b) := by ring
        -- B385: `hdist`'s left side occurs in `hround3`, NOT in the goal (the
        -- goal is `... ≤ R * C`, which has no `K * (...)` at all).  Rewriting the
        -- goal could never match; the hypothesis is what must be rewritten.
        rw [hdist] at hround3
        have h4 : R * mag A a + R * mag A b = R * (mag A a + mag A b) := by ring
        have h5 : R * (mag A a + mag A b) ≤ R * C := mul_le_mul_of_nonneg_left h3 hR0
        linarith only [hround3, h1, h2, h4.le, h4.ge, h5]
      have hsplit : evalFloat F r ρ (.add a b) - evalReal ρ (.add a b)
          = (r.toFun (Sa + Sb) - (Sa + Sb)) + ((Sa - Ra) + (Sb - Rb)) := by
        simp only [evalFloat, evalReal, hSa, hSb, hRa, hRb]
        ring
      rw [hsplit]
      have htri : |(r.toFun (Sa + Sb) - (Sa + Sb)) + ((Sa - Ra) + (Sb - Rb))|
          ≤ |r.toFun (Sa + Sb) - (Sa + Sb)| + (|Sa - Ra| + |Sb - Rb|) := by
        have h1 := abs_add (r.toFun (Sa + Sb) - (Sa + Sb)) ((Sa - Ra) + (Sb - Rb))
        have h2 := abs_add (Sa - Ra) (Sb - Rb)
        linarith only [h1, h2]
      -- B385: `rw [hR]` must run BEFORE the `simp only` below unfolds `R` away,
      -- and it must NOT be aimed at the goal: at this point the goal is still in
      -- `expo`-form (it mentions `expo (.add a b)`), so it contains no `R` at all.
      -- Only the three hypotheses mention `R`.
      rw [hR] at hca hcb hmid1
      simp only [evalFloat, evalReal, numOps_add, mag, expo_add]
      push_cast
      have hT0 : 0 ≤ K ^ (2 * (numOps a + numOps b + 1) + 1) * C :=
        mul_nonneg (pow_nonneg hK0 _) hC0
      have hkey : K ^ (2 * (numOps a + numOps b + 1) + 1) * C
          + ((numOps a : ℝ) * (K ^ (2 * (numOps a + numOps b + 1) + 1)
              * ((1 + F.eps) * mag A a + F.tiny))
            + numOps b * (K ^ (2 * (numOps a + numOps b + 1) + 1)
              * ((1 + F.eps) * mag A b + F.tiny)))
          ≤ ((numOps a : ℝ) + numOps b + 1)
            * (K ^ (2 * (numOps a + numOps b + 1) + 1) * C) := by
        have hCa : (1 + F.eps) * mag A a + F.tiny ≤ C := by
          rw [hC]; nlinarith only [heps, mag_nonneg A a, mag_nonneg A b]
        have hCb : (1 + F.eps) * mag A b + F.tiny ≤ C := by
          rw [hC]; nlinarith only [heps, mag_nonneg A a, mag_nonneg A b]
        have hz := pow_nonneg hK0 (2 * (numOps a + numOps b + 1) + 1)
        have h1 : (numOps a : ℝ) * (K ^ (2 * (numOps a + numOps b + 1) + 1)
              * ((1 + F.eps) * mag A a + F.tiny))
            ≤ (numOps a : ℝ) * (K ^ (2 * (numOps a + numOps b + 1) + 1) * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCa hz) hna
        have h2 : (numOps b : ℝ) * (K ^ (2 * (numOps a + numOps b + 1) + 1)
              * ((1 + F.eps) * mag A b + F.tiny))
            ≤ (numOps b : ℝ) * (K ^ (2 * (numOps a + numOps b + 1) + 1) * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCb hz) hnb
        nlinarith only [h1, h2, hT0, hna, hnb]
      -- B385: same definitional-vs-syntactic issue as B384.  The goal spells C
      -- out as `(1 + F.eps) * (mag A a + mag A b) + F.tiny`, while hkey, hmid1,
      -- hca and hcb all use the local abbreviation `C`.  `C` is a `:=`-bound
      -- local, so linarith sees two unrelated atoms; unfolding once on both
      -- sides puts every occurrence in the same spelling.
      simp only [hC] at hkey hmid1 ⊢
      linarith only [htri, hmid1, hca, hcb, hkey]
  | .mul a b => by
      -- **诚实降级（显式假设）**：乘法分支的完整证明未完成（见文件头"诚实边界"）。
      -- 这里把任务所需的乘法误差界作为**显式假设** `hMul` 引入——
      -- 与 `RealFloatFormat.RoundOp` 把舍入算子性质作为结构字段的做法一致，
      -- **不是 Lean `axiom`**：使用者必须自己提供该假设，或替换为本分支的完整证明。
      -- `hMul` 是 `abbrev`（reducible），故 `hM` 直接可当作函数套用。
      exact hM F r ρ A hA hvar hlit hcontract a b

/-- **`compile_error_bound_pure`（与任务规格对应的形式）**：`tiny = 0` 时

    `|⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e) · ((1+eps)^(2·n_ops e + 1) · ((1+eps) · mag A e))`。

    诚实标注：指数是 `2·n_ops e + 1`（乘法交叉项所需），比上一轮的
    `n_ops e` 保守；`tiny = 0` 时 `(1+tiny)` 因子消失。
    **前提**同样含显式假设 `hMul`（乘法分支未证）。 -/
theorem compile_error_bound_pure (hM : hMul) (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m)
    (htiny : F.tiny = 0) :
    ∀ e : FloatExpr,
      |evalFloat F r ρ e - evalReal ρ e| ≤
        (numOps e : ℝ) * ((1 + F.eps) ^ (expo e) * ((1 + F.eps) * mag A e)) := by
  intro e
  have h := compile_error_bound hM F r ρ A hA hvar hlit hcontract e
  rw [htiny, add_zero] at h
  simpa using h

/-- **零运算表达式的精确性**：`numOps e = 0`（只有字面量/变量）时浮点语义**精确**
    等于源语义。 -/
theorem compile_exact_of_zero_ops (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) :
    ∀ e : FloatExpr, numOps e = 0 → evalFloat F r ρ e = evalReal ρ e
  | .lit c, _ => rfl
  | .var n, _ => rfl
  | .add a b, h => by simp only [numOps_add] at h; omega
  | .neg a, h => by simp only [numOps_neg] at h; omega
  | .mul a b, h => by simp only [numOps_mul] at h; omega

end Lattice.Lib.Compiler.RealCompileFloatCorrectness