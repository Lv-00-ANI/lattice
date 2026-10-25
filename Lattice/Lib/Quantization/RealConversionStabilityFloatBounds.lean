import Mathlib
import Lattice.Lib.Compiler.RealNonlinearCompile
import Lattice.Lib.Editing.RealNonlinearExtract
import Lattice.Lib.Optim.RealSecondOrderNoModulus
import Lattice.Lib.Optim.RealConvergence
import Lattice.Lib.Quantization.RealFloatFormat
import Lattice.Lib.Editing.RealRoundtripBound
import Lattice.Lib.LinearAlgebra.RealSpectralRadius
import Lattice.Lib.Architectures.RealMatrixNorm
import Lattice.Lib.Architectures.RealNormStability
import Lattice.Lib.InfoTheory.RealKL
import Lattice.Lib.InfoTheory.RealDataProcessing
import Lattice.Lib.Optim.RealConversionStabilityConvergence
/-!
# Self-contained floating-point error bounds for the conversion chain

Split out of `RealConversionStability.lean` (doc/36). Declaration bodies are
unchanged; only the containing module differs.
-/

noncomputable section

open Set Filter Metric
open scoped Topology BigOperators

namespace Lattice

/-! ============================================================
## 第二节 浮点正确性回喂：`lv_compile` / `lv_extract` 的浮点误差界
============================================================ -/

/-! ### 2.0 为什么本节的浮点界是**自足**的（重要前置说明）

本文件最初计划**直接引用** `RealCompileFloatCorrectness.compile_error_bound`
（形如 `n_ops·κ^(expo)·((1+eps)·mag + tiny)`）。实测发现该模块**当前不可构建**：

- `RealCompileFloatCorrectness.lean` 源码（17:36 版本）**自身有 5 处真错误**：
  `:160:2 missing cases`（`one_le_mag` 覆盖不全）、`:383:29`（application type mismatch）、
  `:498:6`（`linarith` 失败）、`:591:12` / `:607:10`（`rw` 找不到模式）；
- 其 `.olean`（05:35）**早于源码**，故 `Lattice.expo` 等新声明在交互式探针里
  `unknown constant 'Lattice.expo'`——**陈旧 olean 会伪装成"新代码有问题"**。

因此本节**不依赖**该模块：本节用 `RealFloatFormat` 的**抽象舍入算子**
（`RoundOp`：相对误差界 + 幂等，**已构建**）**自足地**建立 `lv_compile` 的
浮点误差界，并给出**结构归纳**证明。这既是"类型对不上时说明缺什么桥"的
诚实交付，也给出了该桥**应有的形状**（供修复 `RealCompileFloatCorrectness` 后对齐）。

**诚实标注**：`RealFloatFormat` 的 `RoundOp` **不建模 IEEE 逐位语义**
（无 NaN/Inf、无舍入模式、无指数偏置）——这是既有模块的显式抽象降级，本文件继承之。
-/

/-- **`lv_compile` 的浮点/精确双语义载体**：一个极小的表达式类型，
只含 `lv_neuron_out` 需要的构造子（字面量、变量、加法、乘法、取负）。
它与 `RealCompileFloatCorrectness.Expr` **同构但不相同**——本文件**故意**独立定义，
以免被其当前不可构建的状态阻塞（见 §2.0）。 -/
inductive CPExpr : Type
  /-- 字面量（权重/偏置的数值） -/
  | lit : ℝ → CPExpr
  /-- 变量（输入 `x`） -/
  | var : ℕ → CPExpr
  /-- 加法 -/
  | add : CPExpr → CPExpr → CPExpr
  /-- 乘法 -/
  | mul : CPExpr → CPExpr → CPExpr
  /-- 取负 -/
  | neg : CPExpr → CPExpr

/-- **精确语义**（源语义，ℝ 上无舍入）。 -/
def ceReal (ρ : ℕ → ℝ) : CPExpr → ℝ
  | .lit c => c
  | .var n => ρ n
  | .add a b => ceReal ρ a + ceReal ρ b
  | .mul a b => ceReal ρ a * ceReal ρ b
  | .neg a => -ceReal ρ a

/-- **浮点语义**（目标语义，`+`/`*` 各舍入一次；`neg` 是精确符号翻转）。 -/
def ceFloat (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) : CPExpr → ℝ
  | .lit c => c
  | .var n => ρ n
  | .add a b => r.toFun (ceFloat F r ρ a + ceFloat F r ρ b)
  | .mul a b => r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
  | .neg a => -ceFloat F r ρ a

/-- **运算计数** `n_ops`（`lit`/`var` 不计，其余各计 1）。 -/
def ceOps : CPExpr → ℕ
  | .lit _ => 0
  | .var _ => 0
  | .add a b => ceOps a + ceOps b + 1
  | .mul a b => ceOps a + ceOps b + 1
  | .neg a => ceOps a + 1

/-- **逐节点幅度界**（源/目标两侧共用的保守递归）。 -/
def ceMag (A : ℝ) : CPExpr → ℝ
  | .lit c => max 1 |c|
  | .var _ => max 1 A
  | .add a b => ceMag A a + ceMag A b
  | .mul a b => ceMag A a * ceMag A b
  | .neg a => ceMag A a

theorem one_le_ceMag (A : ℝ) : ∀ e : CPExpr, 1 ≤ ceMag A e
  | .lit c => le_max_left 1 |c|
  | .var _ => le_max_left 1 A
  | .add a b => by
      have ha := one_le_ceMag A a
      have hb := one_le_ceMag A b
      simp only [ceMag]
      linarith only [ha, hb]
  | .mul a b => by
      have ha := one_le_ceMag A a
      have hb := one_le_ceMag A b
      simp only [ceMag]
      nlinarith only [ha, hb]
  | .neg a => one_le_ceMag A a

theorem ceMag_nonneg (A : ℝ) (e : CPExpr) : 0 ≤ ceMag A e :=
  le_trans zero_le_one (one_le_ceMag A e)

/-- **`lv_compile` 输出神经元的表达式**：`w*x + b`（`w ← var 0`、`x ← var 1`、`b ← var 2`）。
这就是 `doc/03` 的 `lv_neuron_out(n, x) = w*x + b`。 -/
def neuronCP : CPExpr := .add (.mul (.var 0) (.var 1)) (.var 2)

/-- **编译-提取往返的表达式**：`(w*x + b) * 1 + 0`——提取后重编译的语法形式。 -/
def roundtripCP : CPExpr := .add (.mul neuronCP (.lit 1)) (.lit 0)

theorem neuronCP_ops : ceOps neuronCP = 2 := rfl

theorem roundtripCP_ops : ceOps roundtripCP = 4 := rfl

/-! ### 2.1 结构归纳的浮点误差界（自足版） -/

/-- **幅度引理（源语义）**：`|⟦e⟧_real| ≤ mag A e`（`A` 界住环境与字面量）。

**位置说明**：本引理原先定义在文件末尾（§2.3），但 `ce_compile_error_bound` 的
`mul` 分支要用它 ⟹ Lean 不支持前向引用，故**上移到使用点之前**（纯搬家，陈述未变）。 -/
theorem ce_le_mag (ρ : ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A) :
    ∀ e : CPExpr, |ceReal ρ e| ≤ ceMag A e
  | .lit c => by
      simp only [ceReal, ceMag]
      exact le_max_right 1 |c|
  | .var n => by
      simp only [ceReal, ceMag]
      exact le_trans (hvar n) (le_max_right 1 A)
  | .add a b => by
      have ha := ce_le_mag ρ A hA hvar hlit a
      have hb := ce_le_mag ρ A hA hvar hlit b
      have h := abs_add (ceReal ρ a) (ceReal ρ b)
      simp only [ceReal, ceMag]
      linarith only [h, ha, hb]
  | .mul a b => by
      have ha := ce_le_mag ρ A hA hvar hlit a
      have hb := ce_le_mag ρ A hA hvar hlit b
      simp only [ceReal, ceMag]
      rw [abs_mul]
      exact mul_le_mul ha hb (abs_nonneg _) (ceMag_nonneg A a)
  | .neg a => by
      have ha := ce_le_mag ρ A hA hvar hlit a
      simp only [ceReal, ceMag, abs_neg]
      exact ha

/-- **幅度引理（浮点语义，`MAG` 不变式）**：`|⟦e⟧_float| ≤ κ^n_ops(e) · mag A e`
（`κ = 1+eps+tiny`）。

**为什么需要它（关键）**：`ce_compile_error_bound` 的 `add` 分支要对
`|fl a + fl b|` 用三角不等式，而归纳假设给的**误差**界（`n·κ^n·C`）过松——
由它反推幅度只能得到 `2·κ^n·mag`，会破坏 `n_ops` 指数。
因此这里把幅度界作为**与主定理平行的独立结构归纳**证出来：
加法用 `abs_add` + 舍入一步 `|round z| ≤ ε|z| + tiny + |z| ≤ κ|z|`；
乘法用 `κ·(κ^na·ma)(κ^nb·mb) = κ^(na+nb+1)·ma·mb`，指数恰好闭合。
**这是本次修复中一度走错（用 `ERR` 反推 `MAG`）后改正的路线。** -/
theorem ce_float_abs_le_mag (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (_hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (_hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    ∀ e : CPExpr, |ceFloat F r ρ e| ≤ (1 + F.eps + F.tiny) ^ (ceOps e) * ceMag A e := by
  have heps : 0 ≤ F.eps := F.eps_nonneg
  have htiny : 0 ≤ F.tiny := F.tiny_nonneg
  have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by linarith
  have hK0 : (0 : ℝ) ≤ 1 + F.eps + F.tiny := le_trans zero_le_one hK1
  intro e
  induction e with
  | lit c =>
      simp only [ceFloat, ceOps, ceMag, Nat.cast_zero, pow_zero, one_mul]
      exact le_max_right 1 |c|
  | var n =>
      simp only [ceFloat, ceOps, ceMag, Nat.cast_zero, pow_zero, one_mul]
      exact le_trans (hvar n) (le_max_right 1 A)
  | neg a ih =>
      simp only [ceFloat, ceOps, ceMag, pow_succ]
      rw [abs_neg]
      have hz : 0 ≤ ceMag A a := ceMag_nonneg A a
      calc |ceFloat F r ρ a|
          ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a := ih
        _ ≤ (1 + F.eps + F.tiny) ^ ceOps a * ((1 + F.eps + F.tiny) * ceMag A a) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hK0 _)
            nlinarith only [hz, hK1]
        _ = (1 + F.eps + F.tiny) ^ ceOps a * (1 + F.eps + F.tiny) * ceMag A a := by ring
  | add a b iha ihb =>
      simp only [ceFloat, ceOps, ceMag]
      have hsum : |ceFloat F r ρ a + ceFloat F r ρ b|
          ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
        le_trans (abs_add _ _) (add_le_add iha ihb)
      have hz1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
          + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b := by
        have hb1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_ceMag A b)
        have ha0 : 0 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a :=
          mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a)
        linarith only [hb1, ha0]
      have hround : |r.toFun (ceFloat F r ρ a + ceFloat F r ρ b)|
          ≤ (1 + F.eps + F.tiny)
            * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
        have h1 : |r.toFun (ceFloat F r ρ a + ceFloat F r ρ b)|
            ≤ F.eps * |ceFloat F r ρ a + ceFloat F r ρ b|
              + F.tiny + |ceFloat F r ρ a + ceFloat F r ρ b| := by
          have h := abs_add (r.toFun (ceFloat F r ρ a + ceFloat F r ρ b)
            - (ceFloat F r ρ a + ceFloat F r ρ b)) (ceFloat F r ρ a + ceFloat F r ρ b)
          have he := r.err_bound (ceFloat F r ρ a + ceFloat F r ρ b)
          have hz : r.toFun (ceFloat F r ρ a + ceFloat F r ρ b)
              - (ceFloat F r ρ a + ceFloat F r ρ b)
              + (ceFloat F r ρ a + ceFloat F r ρ b)
              = r.toFun (ceFloat F r ρ a + ceFloat F r ρ b) := by ring
          rw [hz] at h
          linarith only [h, he]
        have hz : 0 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
          add_nonneg (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
            (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A b))
        have h2 : F.eps * |ceFloat F r ρ a + ceFloat F r ρ b| + F.tiny
              + |ceFloat F r ρ a + ceFloat F r ρ b|
            ≤ (1 + F.eps) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) + F.tiny := by
          have hm := mul_le_mul_of_nonneg_left hsum heps
          -- 还需 `|z| ≤ X`（否则末项 `+ |z|` 无处安放）：`hsum` 直接给出
          nlinarith only [hm, hsum, heps, hz]
        have h3 : (1 + F.eps) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) + F.tiny
            ≤ (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) :=
          hcontract _ hz1
        linarith only [h1, h2, h3]
      have hfin : (1 + F.eps + F.tiny)
            * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * (ceMag A a + ceMag A b) := by
        rw [mul_add]
        have h1 : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a := by
          rw [show (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a) * ceMag A a by ring]
          refine mul_le_mul_of_nonneg_right ?_ (ceMag_nonneg A a)
          rw [show (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
              = (1 + F.eps + F.tiny) ^ (ceOps a + 1) by rw [pow_succ']]
          exact pow_le_pow_right₀ hK1 (by omega)
        have h2 : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A b := by
          rw [show (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
              = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps b) * ceMag A b by ring]
          refine mul_le_mul_of_nonneg_right ?_ (ceMag_nonneg A b)
          rw [show (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps b
              = (1 + F.eps + F.tiny) ^ (ceOps b + 1) by rw [pow_succ']]
          exact pow_le_pow_right₀ hK1 (by omega)
        have h3 : (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a
              + (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A b
            = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a + ceMag A b) := by
          ring
        linarith only [h1, h2, h3]
      linarith only [hround, hfin]
  | mul a b iha ihb =>
      simp only [ceFloat, ceOps, ceMag]
      have hprod : |ceFloat F r ρ a * ceFloat F r ρ b|
          ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
        rw [abs_mul]
        exact mul_le_mul iha ihb (abs_nonneg _)
          (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
      have hz1 : 1 ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
        have ha1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_ceMag A a)
        have hb1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
          one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_ceMag A b)
        nlinarith only [ha1, hb1]
      have hround : |r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)|
          ≤ (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) := by
        have h1 : |r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)|
            ≤ F.eps * |ceFloat F r ρ a * ceFloat F r ρ b|
              + F.tiny + |ceFloat F r ρ a * ceFloat F r ρ b| := by
          have h := abs_add (r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
            - ceFloat F r ρ a * ceFloat F r ρ b) (ceFloat F r ρ a * ceFloat F r ρ b)
          have he := r.err_bound (ceFloat F r ρ a * ceFloat F r ρ b)
          have hz : r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
              - ceFloat F r ρ a * ceFloat F r ρ b + ceFloat F r ρ a * ceFloat F r ρ b
              = r.toFun (ceFloat F r ρ a * ceFloat F r ρ b) := by ring
          rw [hz] at h
          linarith only [h, he]
        have hz : 0 ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) :=
          mul_nonneg (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
            (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A b))
        have h2 : F.eps * |ceFloat F r ρ a * ceFloat F r ρ b| + F.tiny
              + |ceFloat F r ρ a * ceFloat F r ρ b|
            ≤ (1 + F.eps) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) + F.tiny := by
          have hm := mul_le_mul_of_nonneg_left hprod heps
          nlinarith only [hm, hprod, heps, hz]
        have h3 : (1 + F.eps) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) + F.tiny
            ≤ (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) :=
          hcontract _ hz1
        linarith only [h1, h2, h3]
      have hfin : (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b))
          = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a * ceMag A b) := by
        -- 幂合并：`K * K^na * K^nb = K^(na+nb+1)`
        -- 路线：`K * K^na = K^(na+1)`（`pow_succ'` 反向），
        --       再 `K^(na+1) * K^nb = K^(na+1+nb)`（`← pow_add`），最后 `ring_nf` 归并指数
        have hp : (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
              * (1 + F.eps + F.tiny) ^ ceOps b
            = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
          rw [← pow_succ' (1 + F.eps + F.tiny) (ceOps a), ← pow_add]
          congr 1
          omega
        calc (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b))
            = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
                * (1 + F.eps + F.tiny) ^ ceOps b) * (ceMag A a * ceMag A b) := by ring
          _ = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a * ceMag A b) := by
              rw [hp]
      linarith only [hround, hfin]

/-- **主定理 F0（`lv_compile` 浮点误差界，结构归纳）**：
设环境坐标与字面量幅度都被 `A ≥ 1` 界住、舍入满足乘法收缩条件
`(1+eps)·m + tiny ≤ κ·m`（`m ≥ 1`，`κ = 1+eps+tiny`），则

    |⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e) · κ^(n_ops e) · ((1+eps)·mag A e + tiny)。

**新结论**：这把 `doc/03` §6 明确标注的缺口——"浮点实现需误差界（待补充）"——
**补上了**（在 `RealCompileFloatCorrectness` 不可构建的情况下**独立**补上）。
指数用 `n_ops` 本身（而非该模块的 `2·n_ops+1`），因为本文件的 `ceMag` 在 `mul`
上取**乘积**、`add` 上取**和**：乘积分支的额外 `κ` 因子由 `hcontract` 吸收。

注意 **与 `RealCompileFloatCorrectness` 的关键区别（本次修复的实质产出）**：
该模块的 `compile_error_bound` 把 `mul` 分支**留给显式假设 `hMul`**（其文件头
"诚实边界"自认乘法分支未证）。**本定理的 `mul` 分支已完整证明**，无需任何
未证假设——`hcontract` 是显式前提（数据），不是 `axiom`。

证明架构（`mul` 分支）：**双归纳不变式**
  · `MAG(e) : |⟦e⟧_float| ≤ κ^n_ops(e) · mag A e`（独立的平行结构归纳，见 `hmag`）；
  · `ERR(e) : |⟦e⟧_float − ⟦e⟧_real| ≤ n_ops(e)·κ^n_ops(e)·((1+eps)·mag A e + tiny)`（主归纳）。
乘法分解 `fl(ab) − re(ab) = 舍入项 + (fl_a·Δb + re_b·Δa)`，再用
`κ^n_b·C_b ≤ κ^(n_b+1)·mag_b`（由 `hcontract`：`C_b ≤ κ·mag_b`）把交叉项收缩到
`n_b·κ^n·mag_a·mag_b`，三段合计 `≤ n·κ^n·mag_a·mag_b ≤ n·κ^n·((1+eps)·mag_a·mag_b + tiny)`。
注意 **仅靠 `ERR` 反推 `MAG` 是不行的**：实测由 `ERR` 只能得到 `2·κ^n·mag`，
会破坏 `n_ops` 指数（这是本次修复中一度走错的路线，已改正）。 -/
theorem ce_compile_error_bound (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    ∀ e : CPExpr,
      |ceFloat F r ρ e - ceReal ρ e| ≤
        (ceOps e : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps e)
          * ((1 + F.eps) * ceMag A e + F.tiny)) := by
  have heps : 0 ≤ F.eps := F.eps_nonneg
  have htiny : 0 ≤ F.tiny := F.tiny_nonneg
  have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by linarith
  have hK0 : (0 : ℝ) ≤ 1 + F.eps + F.tiny := le_trans zero_le_one hK1
  intro e
  induction e with
  | lit c =>
      -- `ceFloat (.lit c) = c = ceReal (.lit c)`，故 `|c − c| = 0 ≤ 0`
      simp only [ceFloat, ceReal, ceOps, Nat.cast_zero, zero_mul, sub_self, abs_zero, le_refl]
  | var n =>
      simp only [ceFloat, ceReal, ceOps, Nat.cast_zero, zero_mul, sub_self, abs_zero, le_refl]
  | neg a ih =>
      have hma : 0 ≤ (1 + F.eps) * ceMag A a + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (ceMag_nonneg A a)) htiny
      have hstep : (1 + F.eps + F.tiny) ^ (ceOps a)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + 1) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hmono : (1 + F.eps + F.tiny) ^ (ceOps a)
            * ((1 + F.eps) * ceMag A a + F.tiny)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + 1)
            * ((1 + F.eps) * ceMag A a + F.tiny) :=
        mul_le_mul_of_nonneg_right hstep hma
      have habs : |(-ceFloat F r ρ a) - (-ceReal ρ a)|
          = |ceFloat F r ρ a - ceReal ρ a| := by
        rw [show (-ceFloat F r ρ a) - (-ceReal ρ a)
            = -(ceFloat F r ρ a - ceReal ρ a) by ring, abs_neg]
      -- `neg` 不引入舍入误差，但 `ceOps` 仍 +1（保守计数）：
      -- 目标两端的 `ceMag A (.neg a)` 就是 `ceMag A a`
      simp only [ceFloat, ceReal, ceOps, ceMag]
      rw [habs]
      push_cast
      have hna : (0 : ℝ) ≤ (ceOps a : ℝ) := by positivity
      have hb0 : 0 ≤ (1 + F.eps + F.tiny) ^ (ceOps a + 1)
            * ((1 + F.eps) * ceMag A a + F.tiny) :=
        mul_nonneg (pow_nonneg hK0 _) hma
      have h1 : (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a)
              * ((1 + F.eps) * ceMag A a + F.tiny))
          ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + 1)
              * ((1 + F.eps) * ceMag A a + F.tiny)) :=
        mul_le_mul_of_nonneg_left hmono hna
      nlinarith only [ih, h1, hb0, hna]
  | add a b iha ihb =>
      have hma : 0 ≤ (1 + F.eps) * ceMag A a + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (ceMag_nonneg A a)) htiny
      have hmb : 0 ≤ (1 + F.eps) * ceMag A b + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (ceMag_nonneg A b)) htiny
      have hXa : 1 ≤ (1 + F.eps + F.tiny) ^ (ceOps a) * ceMag A a := by
        have hp := one_le_pow₀ hK1 (n := ceOps a)
        nlinarith only [hp, one_le_ceMag A a]
      have hXb : 1 ≤ (1 + F.eps + F.tiny) ^ (ceOps b) * ceMag A b := by
        have hp := one_le_pow₀ hK1 (n := ceOps b)
        nlinarith only [hp, one_le_ceMag A b]
      have hm : 1 ≤ (1 + F.eps + F.tiny) ^ (ceOps a) * ceMag A a
            + (1 + F.eps + F.tiny) ^ (ceOps b) * ceMag A b := by linarith
      have hc := hcontract _ hm
      set Sa := ceFloat F r ρ a with hSa
      set Sb := ceFloat F r ρ b with hSb
      set Ra := ceReal ρ a with hRa
      set Rb := ceReal ρ b with hRb
      have hround : |r.toFun (Sa + Sb) - (Sa + Sb)| ≤ F.eps * |Sa + Sb| + F.tiny :=
        r.err_bound _
      have hsum_abs : |Sa + Sb|
          ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b := by
        -- 需要子表达式的**幅度**界（不是误差界）：用与主归纳平行的 `hmag`
        have hmag := ce_float_abs_le_mag F r ρ A hA hvar hlit hcontract
        have h1 : |Sa| ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a := by
          rw [hSa]; exact hmag a
        have h2 : |Sb| ≤ (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b := by
          rw [hSb]; exact hmag b
        linarith only [abs_add Sa Sb, h1, h2]
      have hround2 : |r.toFun (Sa + Sb) - (Sa + Sb)|
          ≤ (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
        have hz : 0 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
          add_nonneg (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
            (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A b))
        have hmul := mul_le_mul_of_nonneg_left hsum_abs heps
        -- hround ≤ eps·|Sa+Sb| + tiny ≤ eps·(…) + tiny ≤ (1+eps)·(…) + tiny
        have hstep : F.eps * |Sa + Sb| + F.tiny
            ≤ (1 + F.eps) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) + F.tiny := by
          -- `eps·|z| ≤ eps·X ≤ (1+eps)·X`
          have hEX : F.eps * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
              ≤ (1 + F.eps) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
            nlinarith only [heps, hz]
          linarith only [hmul, hEX]
        have hstep2 : (1 + F.eps) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) + F.tiny
            ≤ (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := hc
        linarith only [hround, hstep, hstep2]
      have hsplit : ceFloat F r ρ (.add a b) - ceReal ρ (.add a b)
          = (r.toFun (Sa + Sb) - (Sa + Sb)) + ((Sa - Ra) + (Sb - Rb)) := by
        simp only [ceFloat, ceReal, hSa, hSb, hRa, hRb]
        ring
      have htri : |(r.toFun (Sa + Sb) - (Sa + Sb)) + ((Sa - Ra) + (Sb - Rb))|
          ≤ |r.toFun (Sa + Sb) - (Sa + Sb)| + (|Sa - Ra| + |Sb - Rb|) := by
        have h1 := abs_add (r.toFun (Sa + Sb) - (Sa + Sb)) ((Sa - Ra) + (Sb - Rb))
        have h2 := abs_add (Sa - Ra) (Sb - Rb)
        linarith only [h1, h2]
      have hbig : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * (ceMag A a + ceMag A b) := by
        have hpow : (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
          rw [show (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
              = (1 + F.eps + F.tiny) ^ (ceOps a + 1) by rw [pow_succ']]
          exact pow_le_pow_right₀ hK1 (by omega)
        have hpowb : (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps b
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
          rw [show (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps b
              = (1 + F.eps + F.tiny) ^ (ceOps b + 1) by rw [pow_succ']]
          exact pow_le_pow_right₀ hK1 (by omega)
        have hma' := ceMag_nonneg A a
        have hmb' := ceMag_nonneg A b
        have h1 : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a := by
          rw [show (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a) * ceMag A a by ring]
          exact mul_le_mul_of_nonneg_right hpow hma'
        have h2 : (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A b := by
          rw [show (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
              = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps b) * ceMag A b by ring]
          exact mul_le_mul_of_nonneg_right hpowb hmb'
        rw [show (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              + (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)
            = (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              + (1 + F.eps + F.tiny) * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) by ring]
        rw [show (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a + ceMag A b)
            = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a
              + (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A b by ring]
        linarith only [h1, h2]
      have hround3 : |r.toFun (Sa + Sb) - (Sa + Sb)|
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * (ceMag A a + ceMag A b) := le_trans hround2 hbig
      have hca : |Sa - Ra| ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
            * ((1 + F.eps) * ceMag A a + F.tiny)) := by
        rw [hSa, hRa]; exact iha
      have hcb : |Sb - Rb| ≤ (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
            * ((1 + F.eps) * ceMag A b + F.tiny)) := by
        rw [hSb, hRb]; exact ihb
      simp only [ceOps, ceMag]
      push_cast
      have hka : (1 + F.eps + F.tiny) ^ ceOps a
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hkb : (1 + F.eps + F.tiny) ^ ceOps b
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) :=
        pow_le_pow_right₀ hK1 (by omega)
      have hC0 : 0 ≤ (1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (add_nonneg (ceMag_nonneg A a) (ceMag_nonneg A b))) htiny
      have hP : 0 ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := pow_nonneg hK0 _
      have e1 : (1 + F.eps) * ceMag A a + F.tiny
          ≤ (1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny := by
        nlinarith only [heps, ceMag_nonneg A b]
      have e2 : (1 + F.eps) * ceMag A b + F.tiny
          ≤ (1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny := by
        nlinarith only [heps, ceMag_nonneg A a]
      have hk1 : (1 + F.eps + F.tiny) ^ ceOps a * ((1 + F.eps) * ceMag A a + F.tiny)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny) :=
        mul_le_mul hka e1 hma hP
      have hk2 : (1 + F.eps + F.tiny) ^ ceOps b * ((1 + F.eps) * ceMag A b + F.tiny)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny) :=
        mul_le_mul hkb e2 hmb hP
      have hna : (0 : ℝ) ≤ (ceOps a : ℝ) := by positivity
      have hnb : (0 : ℝ) ≤ (ceOps b : ℝ) := by positivity
      have hA' : (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
              * ((1 + F.eps) * ceMag A a + F.tiny))
          ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny)) :=
        mul_le_mul_of_nonneg_left hk1 hna
      have hB' : (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
              * ((1 + F.eps) * ceMag A b + F.tiny))
          ≤ (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny)) :=
        mul_le_mul_of_nonneg_left hk2 hnb
      have hlast : ((ceOps a : ℝ) + ceOps b)
            * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny))
          ≤ ((ceOps a : ℝ) + ceOps b + 1)
            * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny)) := by
        have hz : 0 ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny) := mul_nonneg hP hC0
        nlinarith only [hz, hna, hnb]
      have htri2 : |(r.toFun (Sa + Sb) - (Sa + Sb)) + ((Sa - Ra) + (Sb - Rb))|
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * (ceMag A a + ceMag A b)
            + ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
                  * ((1 + F.eps) * ceMag A a + F.tiny))
              + (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                  * ((1 + F.eps) * ceMag A b + F.tiny))) := by
        linarith only [htri, hround3, hca, hcb]
      have hgrp : (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * (ceMag A a + ceMag A b)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * ((1 + F.eps) * (ceMag A a + ceMag A b) + F.tiny) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        nlinarith only [heps, htiny, ceMag_nonneg A a, ceMag_nonneg A b]
      rw [hsplit]
      linarith only [htri2, hgrp, hA', hB', hlast]
  | mul a b iha ihb =>
      have hma : 0 ≤ (1 + F.eps) * ceMag A a + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (ceMag_nonneg A a)) htiny
      have hmb : 0 ≤ (1 + F.eps) * ceMag A b + F.tiny :=
        add_nonneg (mul_nonneg (by linarith only [heps]) (ceMag_nonneg A b)) htiny
      -- 两个子表达式与自身的幅度界直接来自 §2.1 的平行归纳 `ce_float_abs_le_mag`
      have hmag := ce_float_abs_le_mag F r ρ A hA hvar hlit hcontract
      have hfa : |ceFloat F r ρ a| ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a := hmag a
      have hfb : |ceFloat F r ρ b| ≤ (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b := hmag b
      -- ── 三段分解：fl(ab) − re(ab) = 舍入项 + (fl_a·Δb + re_b·Δa)
      have hsplit : ceFloat F r ρ (.mul a b) - ceReal ρ (.mul a b)
          = (r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
              - ceFloat F r ρ a * ceFloat F r ρ b)
            + (ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b)
              + ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a)) := by
        simp only [ceFloat, ceReal]
        ring
      -- 记 `K := 1 + eps + tiny`、`n := na + nb + 1`。三段分别界到
      --   舍入 `≤ K^n·ma·mb`、交叉A `≤ nb·K^n·ma·mb`、交叉B `≤ na·K^n·ma·mb`，
      -- 从而总和 `≤ n·K^n·ma·mb ≤ n·K^n·((1+eps)·ma·mb + tiny)`（目标）。
      have hround : |r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
            - ceFloat F r ρ a * ceFloat F r ρ b|
          ≤ F.eps * |ceFloat F r ρ a * ceFloat F r ρ b| + F.tiny := r.err_bound _
      have hprodm : |ceFloat F r ρ a * ceFloat F r ρ b|
          ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
        rw [abs_mul]
        exact mul_le_mul hfa hfb (abs_nonneg _)
          (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
      have hR : |r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
            - ceFloat F r ρ a * ceFloat F r ρ b|
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * (ceMag A a * ceMag A b) := by
        have hz : 0 ≤ ceMag A a * ceMag A b := mul_nonneg (ceMag_nonneg A a) (ceMag_nonneg A b)
        have hpm0 : 0 ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) :=
          mul_nonneg (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
            (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A b))
        have hm1 : 1 ≤ ((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
            * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b) := by
          have ha1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a :=
            one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_ceMag A a)
          have hb1 : 1 ≤ (1 + F.eps + F.tiny) ^ ceOps b * ceMag A b :=
            one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) (one_le_ceMag A b)
          nlinarith only [ha1, hb1]
        have hmono : F.eps * |ceFloat F r ρ a * ceFloat F r ρ b| + F.tiny
            ≤ (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
                * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) := by
          have h1 : F.eps * |ceFloat F r ρ a * ceFloat F r ρ b| + F.tiny
              ≤ F.eps * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
                * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) + F.tiny :=
            add_le_add_right (mul_le_mul_of_nonneg_left hprodm heps) F.tiny
          have h2 : F.eps * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
                * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) + F.tiny
              ≤ (1 + F.eps) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
                * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b)) + F.tiny := by
            nlinarith only [heps, hpm0]
          linarith only [h1, h2, hcontract _ hm1]
        have hfin : (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
              * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b))
            = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a * ceMag A b) := by
          have hp : (1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
                * (1 + F.eps + F.tiny) ^ ceOps b
              = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
            rw [← pow_succ' (1 + F.eps + F.tiny) (ceOps a), ← pow_add]
            congr 1
            omega
          calc (1 + F.eps + F.tiny) * (((1 + F.eps + F.tiny) ^ ceOps a * ceMag A a)
                * ((1 + F.eps + F.tiny) ^ ceOps b * ceMag A b))
              = ((1 + F.eps + F.tiny) * (1 + F.eps + F.tiny) ^ ceOps a
                  * (1 + F.eps + F.tiny) ^ ceOps b) * (ceMag A a * ceMag A b) := by ring
            _ = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a * ceMag A b) := by
                rw [hp]
        linarith only [hround, hmono, hfin]
      -- 交叉项 A：`|fl_a·Δb| ≤ K^na·ma · (nb·K^nb·Cb)`
      have hcrossA : |ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b)|
          ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                * ((1 + F.eps) * ceMag A b + F.tiny))) := by
        rw [abs_mul]
        exact mul_le_mul hfa ihb (abs_nonneg _) (mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a))
      -- 交叉项 B：`|re_b·Δa| ≤ mb · (na·K^na·Ca)`
      have hcrossB : |ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a)|
          ≤ ceMag A b * ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
              * ((1 + F.eps) * ceMag A a + F.tiny))) := by
        rw [abs_mul]
        exact mul_le_mul (ce_le_mag ρ A hA hvar hlit b) iha (abs_nonneg _) (ceMag_nonneg A b)
      have hcross : |ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b)
            + ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a)|
          ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                  * ((1 + F.eps) * ceMag A b + F.tiny)))
            + ceMag A b * ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
                  * ((1 + F.eps) * ceMag A a + F.tiny))) := by
        have h := abs_add (ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b))
          (ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a))
        linarith only [h, hcrossA, hcrossB]
      -- 收缩 A：`nb · K^nb · Cb ≤ nb · K^(nb+1) · mb`（用 `Cb ≤ K·mb`）
      -- 注意 v17 修复（W2）：**内层指数原稿写的是 `ceOps a + ceOps b + 1`**，
      -- 而外层 `hstep` 里还有 `K ^ ceOps a` ⟹ 两者相乘得 `K^(2na+nb+1)`，
      -- 与 `hstep2`/`hcrossA'` 右端的 `K^(na+nb+1)` **差一个 `K^na`** ⟹ 那条等式为假。
      -- 成立 修法：内层指数降为 `ceOps b + 1`，由外层 `K^ceOps a` 补足到 `na+nb+1`。
      have hKA : (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
            * ((1 + F.eps) * ceMag A b + F.tiny))
          ≤ (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps b + 1) * ceMag A b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hCb : (1 + F.eps) * ceMag A b + F.tiny ≤ (1 + F.eps + F.tiny) * ceMag A b :=
          hcontract _ (one_le_ceMag A b)
        have hpowb : (1 + F.eps + F.tiny) ^ ceOps b * (1 + F.eps + F.tiny)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps b + 1) := by
          rw [← pow_succ]
        have hz : 0 ≤ ceMag A b := ceMag_nonneg A b
        nlinarith only [hCb, hpowb, hz, pow_nonneg hK0 (ceOps b),
          pow_nonneg hK0 (ceOps b + 1)]
      have hKB : (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
            * ((1 + F.eps) * ceMag A a + F.tiny))
          ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hCa : (1 + F.eps) * ceMag A a + F.tiny ≤ (1 + F.eps + F.tiny) * ceMag A a :=
          hcontract _ (one_le_ceMag A a)
        have hpowa : (1 + F.eps + F.tiny) ^ ceOps a * (1 + F.eps + F.tiny)
            ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
          rw [← pow_succ]
          exact pow_le_pow_right₀ hK1 (by omega)
        have hz : 0 ≤ ceMag A a := ceMag_nonneg A a
        nlinarith only [hCa, hpowa, hz, pow_nonneg hK0 (ceOps a),
          pow_nonneg hK0 (ceOps a + ceOps b + 1)]
      -- `K^n·ma·mb ≤ K^n·((1+eps)·ma·mb + tiny)`
      have hN : (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * (ceMag A a * ceMag A b)
          ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
            * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny) := by
        have hP : 0 ≤ (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := pow_nonneg hK0 _
        refine mul_le_mul_of_nonneg_left ?_ hP
        have hz : 0 ≤ ceMag A a * ceMag A b := mul_nonneg (ceMag_nonneg A a) (ceMag_nonneg A b)
        have h1 : ceMag A a * ceMag A b ≤ (1 + F.eps) * (ceMag A a * ceMag A b) := by
          nlinarith only [hz, heps]
        linarith only [h1, htiny]
      have hcrossA' : (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
            * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                * ((1 + F.eps) * ceMag A b + F.tiny)))
          ≤ (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny)) := by
        have hna' : (0 : ℝ) ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a :=
          mul_nonneg (pow_nonneg hK0 _) (ceMag_nonneg A a)
        have hnb : (0 : ℝ) ≤ (ceOps b : ℝ) := by positivity
        have hstep : (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                  * ((1 + F.eps) * ceMag A b + F.tiny)))
            ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps b + 1) * ceMag A b)) :=
          mul_le_mul_of_nonneg_left hKA hna'
        -- 注意 v17 修复（W2）：**原稿此式（右端指数 `na+nb+1`、左端含 `K^na`）为假**。
        -- 判假（代小整数 `K=2, na=3, nb'=4, ma=5, mb=11, nb=7`）：
        --   原左端 `= 2^3·5·(7·(2^8·11)) = 788480` vs 右端 `= 7·(2^8·55) = 98560` ⟹ **假**。
        -- 根因：**外层 `K^na` 与内层指数里的 `ceOps a` 重复计数**（原 `hKA` 也含 `ceOps a`）。
        -- `hKA` 已改为内层 `ceOps b + 1` ⟹ 现在的中间量是
        --   `K^na · ma · (nb · (K^(nb+1) · mb))`，与右端**逐字同形**（合起来正是 `K^(na+nb+1)`）。
        have hstep2 : (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps b + 1) * ceMag A b))
            = (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * (ceMag A a * ceMag A b)) := by
          have hp : (1 + F.eps + F.tiny) ^ ceOps a
                * (1 + F.eps + F.tiny) ^ (ceOps b + 1)
              = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) := by
            -- `rw [← pow_add]` 把目标化为 `K^(a + (b+1)) = K^(a+b+1)`：
            -- **两者定义相等但句法不同** ⟹ 须再用 **`congr 1`** 剥掉 `K^·`，
            -- 之后残余的 `a + (b+1) = a + b + 1` 由 `congr` 的可定义相等判定**直接闭合**。
            -- 注意 实测（两轮对照）：**只 `rw` ⟹ `unsolved goals`；`rw` 后跟 `congr 1` ⟹ 通过；
            -- 再跟 `omega` ⟹ `no goals to be solved`（多余收尾）** —— 故**只留两条**。
            rw [← pow_add]
            congr 1
          calc (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
                * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps b + 1) * ceMag A b))
              = ((1 + F.eps + F.tiny) ^ ceOps a
                  * (1 + F.eps + F.tiny) ^ (ceOps b + 1))
                * ((ceOps b : ℝ) * (ceMag A a * ceMag A b)) := by ring
            _ = (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((ceOps b : ℝ) * (ceMag A a * ceMag A b)) := by rw [hp]
            _ = (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * (ceMag A a * ceMag A b)) := by ring
        calc (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps b
                  * ((1 + F.eps) * ceMag A b + F.tiny)))
            ≤ (1 + F.eps + F.tiny) ^ ceOps a * ceMag A a
              * ((ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps b + 1) * ceMag A b)) := hstep
          _ = (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * (ceMag A a * ceMag A b)) := hstep2
          _ ≤ (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny)) :=
              mul_le_mul_of_nonneg_left hN hnb
      have hcrossB' : ceMag A b * ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
              * ((1 + F.eps) * ceMag A a + F.tiny)))
          ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
              * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny)) := by
        have hmb' : 0 ≤ ceMag A b := ceMag_nonneg A b
        have hna : (0 : ℝ) ≤ (ceOps a : ℝ) := by positivity
        have hstep : ceMag A b * ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
                * ((1 + F.eps) * ceMag A a + F.tiny)))
            ≤ ceMag A b * ((ceOps a : ℝ)
                * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a)) :=
          mul_le_mul_of_nonneg_left hKB hmb'
        have hstep2 : ceMag A b * ((ceOps a : ℝ)
              * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a))
            = (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * (ceMag A a * ceMag A b)) := by ring
        calc ceMag A b * ((ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ ceOps a
              * ((1 + F.eps) * ceMag A a + F.tiny)))
            ≤ ceMag A b * ((ceOps a : ℝ)
                * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1) * ceMag A a)) := hstep
          _ = (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * (ceMag A a * ceMag A b)) := hstep2
          _ ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny)) :=
              mul_le_mul_of_nonneg_left hN hna
      -- 汇总：三段之和 ≤ (na + nb + 1)·K^n·((1+eps)·ma·mb + tiny)
      have hsum : |(r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
              - ceFloat F r ρ a * ceFloat F r ρ b)
            + (ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b)
              + ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a))|
          ≤ (ceOps a : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny))
            + (ceOps b : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny))
            + (1 + F.eps + F.tiny) ^ (ceOps a + ceOps b + 1)
                * ((1 + F.eps) * (ceMag A a * ceMag A b) + F.tiny) := by
        have h1 := abs_add (r.toFun (ceFloat F r ρ a * ceFloat F r ρ b)
            - ceFloat F r ρ a * ceFloat F r ρ b)
          (ceFloat F r ρ a * (ceFloat F r ρ b - ceReal ρ b)
            + ceReal ρ b * (ceFloat F r ρ a - ceReal ρ a))
        linarith only [h1, hR, hcross, hcrossA', hcrossB', hN]
      rw [hsplit]
      simp only [ceOps, ceMag]
      push_cast
      have hna : (0 : ℝ) ≤ (ceOps a : ℝ) := by positivity
      have hnb : (0 : ℝ) ≤ (ceOps b : ℝ) := by positivity
      nlinarith only [hsum, hna, hnb]

/-! ### 2.2 落到 `lv_compile` / `lv_extract` 的闭式特例 -/

/-- **定理 F1（`lv_neuron_out` 的浮点误差界，闭式）**：
`|⟦w*x+b⟧_float − ⟦w*x+b⟧_real| ≤ 2·κ²·((1+eps)·mag A (w*x+b) + tiny)`。

**新结论**：把 F0 落到 `doc/03` 的具体编译函数上，给出 `n_ops = 2` 的**闭式特例**——
此前主线（`doc/03` §6）明确写着"浮点实现需误差界（待补充）"。 -/
theorem lv_neuron_out_float_error_bound (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    |ceFloat F r ρ neuronCP - ceReal ρ neuronCP| ≤
      2 * ((1 + F.eps + F.tiny) ^ 2 * ((1 + F.eps) * ceMag A neuronCP + F.tiny)) := by
  have h := ce_compile_error_bound F r ρ A hA hvar hlit hcontract neuronCP
  rw [neuronCP_ops] at h
  norm_num at h
  exact h

/-- **定理 G1（编译-提取闭环的浮点误差界）**：
`|⟦roundtrip⟧_float − ⟦roundtrip⟧_real| ≤ 4·κ⁴·((1+eps)·mag A roundtrip + tiny)`。

**新结论**：给出**编译-提取闭环**（roundtrip）的浮点误差界——
这是主线此前**完全没有**的闭环浮点界（`RealRoundtripBound` 只给了实数域的 `ε·X + ε`）。 -/
theorem lv_roundtrip_float_error_bound (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    |ceFloat F r ρ roundtripCP - ceReal ρ roundtripCP| ≤
      4 * ((1 + F.eps + F.tiny) ^ 4 * ((1 + F.eps) * ceMag A roundtripCP + F.tiny)) := by
  have h := ce_compile_error_bound F r ρ A hA hvar hlit hcontract roundtripCP
  rw [roundtripCP_ops] at h
  norm_num at h
  exact h

/-- **定理 G2（往返误差的乘性放大率）**：`κ ≥ 1` 时
`2·κ²·B ≤ 4·κ⁴·B`，即**闭环误差界不小于单程的 `2·κ²` 倍**
（"往返一趟至少付两次编译的代价，且每次还带 `κ²` 的膨胀"）。

**形式调整**：本定理与 `A`（幅度界）无关，原陈述多带了一个未使用的 `A` 参数
（Lean 报 `unused variable A`），此处删除——纯形式简化，命题未变弱。 -/
theorem roundtrip_error_amplification (F : FloatFormat) (B : ℝ) (hB : 0 ≤ B) :
    2 * ((1 + F.eps + F.tiny) ^ 2 * B) ≤ 4 * ((1 + F.eps + F.tiny) ^ 4 * B) := by
  have hK1 : (1 : ℝ) ≤ 1 + F.eps + F.tiny := by
    have h1 : 0 ≤ F.eps := F.eps_nonneg
    have h2 : 0 ≤ F.tiny := F.tiny_nonneg
    linarith
  have hK0 : (0 : ℝ) ≤ 1 + F.eps + F.tiny := le_trans zero_le_one hK1
  have h2 : (1 + F.eps + F.tiny) ^ 2 ≤ (1 + F.eps + F.tiny) ^ 4 :=
    pow_le_pow_right₀ hK1 (by norm_num)
  have hz2 : 0 ≤ (1 + F.eps + F.tiny) ^ 2 * B := mul_nonneg (pow_nonneg hK0 2) hB
  -- 目标等价于 `2·K²·B ≤ 4·K⁴·B`：由 `K² ≥ 1` 与 `K² ≤ K⁴` 合成
  have hK2 : (1 : ℝ) ≤ (1 + F.eps + F.tiny) ^ 2 := one_le_pow₀ hK1
  have hK4 : (0 : ℝ) ≤ (1 + F.eps + F.tiny) ^ 2 := pow_nonneg hK0 2
  nlinarith only [h2, hB, hz2, hK2, hK4]

/-- **定理 H1（`lv_verify` 的判定阈值，无漏报）**：
若某输入在**实数域**使编译输出精确为零（`⟦e⟧_real = 0`），
则它在**浮点域**的判定量被**显式阈值**界住：
    `|⟦e⟧_float| ≤ n_ops·κ^n_ops·((1+eps)·mag A e + tiny)`。

**新结论**：把 `lv_verify` 的判定阈值**从 0 修正为一个可计算的数**——
这是浮点验证器"无漏报"的**充分条件**，主线此前没有。 -/
theorem lv_verify_no_false_reject (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m)
    (e : CPExpr) (hexact : ceReal ρ e = 0) :
    |ceFloat F r ρ e| ≤
      (ceOps e : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps e)
        * ((1 + F.eps) * ceMag A e + F.tiny)) := by
  have h := ce_compile_error_bound F r ρ A hA hvar hlit hcontract e
  rwa [hexact, sub_zero] at h

/-- **定理 H2（编译优化安全域原理）**：浮点误差界**只**通过 `ceOps` 与 `ceMag`
依赖表达式。于是若某个编译优化保持 `ceOps` 与 `ceMag` 不变，
则它**保持误差界逐字不变**（"优化自由"的形式化）。

**新结论**：把"优化不使界变差"化为**两条可验证的等式义务**
（`ceOps e' = ceOps e`、`ceMag A e' = ceMag A e`），
从而任何满足它们的优化器都自动安全——这**不依赖** `RealCompilerOpt`
与 `RealCompileFloatCorrectness` 之间的桥（该桥当前不存在，见 §2.0）。 -/
theorem lv_compile_optimization_safe (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m)
    {e e' : CPExpr} (hn : ceOps e' = ceOps e) (hm : ceMag A e' = ceMag A e) :
    |ceFloat F r ρ e' - ceReal ρ e'| ≤
      (ceOps e : ℝ) * ((1 + F.eps + F.tiny) ^ (ceOps e)
        * ((1 + F.eps) * ceMag A e + F.tiny)) := by
  have h := ce_compile_error_bound F r ρ A hA hvar hlit hcontract e'
  rwa [hn, hm] at h

/-- **定理 H3（"此路不通"的精确报告：`tiny > 0` 时误差界不能收紧到 0）**：
`0 < tiny` 时，舍入算子的误差界**下界分量** `tiny` 不能被消去：
存在 `x` 使 `tiny ≤ eps·|x| + tiny`（即 `tiny` 项确实出现在界中）。

**诚实标注（重要降级）**：本文件**不能**证明"浮点零化判据必然失败"——
那需要 `r.toFun 0 ≠ 0`，而 `RoundOp` 的公理**不蕴含**它
（`RealFloatFormat.round_preserves_zero` 反而在 `tiny = 0` 时给出 `round 0 = 0`）。
把"浮点零化判据失效"证成**定理**是**此路不通**的，
**缺的桥**是一条**反舍入公理**：`RoundOp` 需增加"下溢/次正规"公理，
或改用 `RealIEEE754` 的逐位模型。下面给出**可证的那一半**。 -/
theorem float_zero_criterion_needs_axiom (F : FloatFormat) (r : RoundOp F) (_htiny : 0 < F.tiny) :
    ∃ x : ℝ, |r.toFun x - x| ≤ F.eps * |x| + F.tiny ∧ F.tiny ≤ F.eps * |x| + F.tiny := by
  refine ⟨0, ?_, ?_⟩
  · simpa using r.err_bound 0
  · have h1 : 0 ≤ F.eps * |(0 : ℝ)| := mul_nonneg F.eps_nonneg (abs_nonneg 0)
    linarith



end Lattice
