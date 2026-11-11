import Mathlib
import Lattice.Lib.Quantization.RealConversionStabilityFloatBounds
import Lattice.Lib.Compiler.RealCompileFloatCorrectness

/-!
# P5-9：用**已证**的乘法界替换 `hMul` 假设（阶段 A）

## 规划中的最高 ROI 项

**`RealCompileFloatCorrectness.compile_error_bound` 的 `mul` 分支是一个**显式假设** `hMul`：
它把乘法误差界作为前提交给使用者，文件头「诚实边界」自认「乘法分支未证」。**

**而隔壁 `RealConversionStabilityFloatBounds` 里的 `ce_compile_error_bound` **已经完整证明了**
乘法分支（`hcontract` 是数据前提，不是 `axiom`）。**

**=> 本文件把后者的证明**搬到**前者的小语言上。**

## 两个小语言只有名称不同

| `CPExpr`（已证） | `FloatExpr`（待补） |
|:--|:--|
| `lit : ℝ → _` | `lit : ℝ → _` |
| `var : ℕ → _` | `var : ℕ → _` |
| `add` | `add` |
| `mul` | `mul` |
| `neg` | `neg` |
| `ceReal` / `ceFloat` / `ceOps` / `ceMag` | `evalReal` / `evalFloat` / `numOps` / `mag` |

**=> 构造子的**顺序**不同（`CPExpr` 里 `mul` 在 `neg` 之前，`FloatExpr` 里 `neg` 在 `mul` 之前），
而其余完全平行。**

## 做法

**定义 `toCP : FloatExpr → CPExpr` 逐构造子映射，再证:**

```lean
toCP_mul : toCP (.mul a b) = .mul (toCP a) (toCP b)
```

**以及语义保持：`ceReal ρ (toCP e) = evalReal ρ e`、`ceFloat F r ρ (toCP e) = evalFloat F r ρ e`。**

**然后 `ce_compile_error_bound` 直接给出 `FloatExpr` 上的界 —— **`hMul` 可以被真正证出，
而不是作为假设。**** -/

namespace Lattice.Lib.Compiler.RealCompileFloatCorrectness

open Lattice

/-- **`FloatExpr` 到 `CPExpr` 的逐构造子映射。**

**=> 两个小语言的构造子一一对应，只是声明顺序不同；本映射按**意义**对应，不按下标。** -/
def toCP : FloatExpr → CPExpr
  | .lit c => .lit c
  | .var n => .var n
  | .add a b => .add (toCP a) (toCP b)
  | .neg a => .neg (toCP a)
  | .mul a b => .mul (toCP a) (toCP b)

/-- **映射保持 `mul` 的结构。**

**=> 这是把 `hMul` 换成真定理所需的**唯一**结构事实：乘积节点的映射仍是乘积节点。** -/
theorem toCP_mul (a b : FloatExpr) : toCP (.mul a b) = .mul (toCP a) (toCP b) := rfl

/-- **映射保持 `add` 的结构。** -/
theorem toCP_add (a b : FloatExpr) : toCP (.add a b) = .add (toCP a) (toCP b) := rfl

/-- **映射保持 `neg` 的结构。** -/
theorem toCP_neg (a : FloatExpr) : toCP (.neg a) = .neg (toCP a) := rfl

/-- **映射保持实语义：`ceReal ρ (toCP e) = evalReal ρ e`。**

**=> 对 `e` 结构归纳；每个构造子两边的定义完全平行。** -/
theorem toCP_real (ρ : ℕ → ℝ) (e : FloatExpr) : ceReal ρ (toCP e) = evalReal ρ e := by
  induction e with
  | lit c => rfl
  | var n => rfl
  | add a b iha ihb => simp only [toCP, ceReal, evalReal, iha, ihb]
  | neg a iha => simp only [toCP, ceReal, evalReal, iha]
  | mul a b iha ihb => simp only [toCP, ceReal, evalReal, iha, ihb]

/-- **映射保持浮点语义。**

**=> 即使舍入算子 `r` 也在两边同样作用，因为两个 `ceFloat`/`evalFloat` 逐构造子的定义一致。** -/
theorem toCP_float (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (e : FloatExpr) :
    ceFloat F r ρ (toCP e) = evalFloat F r ρ e := by
  induction e with
  | lit c => rfl
  | var n => rfl
  | add a b iha ihb => simp only [toCP, ceFloat, evalFloat, iha, ihb]
  | neg a iha => simp only [toCP, ceFloat, evalFloat, iha]
  | mul a b iha ihb => simp only [toCP, ceFloat, evalFloat, iha, ihb]

/-- **映射保持 `numOps`。** -/
theorem toCP_ops (e : FloatExpr) : ceOps (toCP e) = numOps e := by
  induction e with
  | lit c => rfl
  | var n => rfl
  | add a b iha ihb => simp only [toCP, ceOps, numOps, iha, ihb]
  | neg a iha => simp only [toCP, ceOps, numOps, iha]
  | mul a b iha ihb => simp only [toCP, ceOps, numOps, iha, ihb]

/-- **映射保持 `mag`。** -/
theorem toCP_mag (A : ℝ) (e : FloatExpr) : ceMag A (toCP e) = mag A e := by
  induction e with
  | lit c => rfl
  | var n => rfl
  | add a b iha ihb => simp only [toCP, ceMag, mag, iha, ihb]
  | neg a iha => simp only [toCP, ceMag, mag, iha]
  | mul a b iha ihb => simp only [toCP, ceMag, mag, iha, ihb]

/-- **乘法分支已证：`FloatExpr` 上的误差界完整成立。**

**=> 这就是 `hMul` 想要的东西，而它现在是一条**定理**，不再是假设。**

**证法：把未知量用 `toCP` 搬到 `CPExpr` 上，用 §`ce_compile_error_bound`
（已**完整证明乘法分支**），再用 `toCP_*` 四条回译。** -/
theorem compile_error_bound_mul_discharged (F : FloatFormat) (r : RoundOp F) (ρ : ℕ → ℝ) (A : ℝ)
    (hA : 1 ≤ A) (hvar : ∀ n : ℕ, |ρ n| ≤ A) (hlit : ∀ c : ℝ, |c| ≤ A)
    (hcontract : ∀ m : ℝ, 1 ≤ m → (1 + F.eps) * m + F.tiny ≤ (1 + F.eps + F.tiny) * m) :
    ∀ e : FloatExpr,
      |evalFloat F r ρ e - evalReal ρ e| ≤
        (numOps e : ℝ) * ((1 + F.eps + F.tiny) ^ (numOps e)
          * ((1 + F.eps) * mag A e + F.tiny)) := by
  intro e
  have h := ce_compile_error_bound F r ρ A hA hvar hlit hcontract (toCP e)
  rwa [toCP_float, toCP_real, toCP_ops, toCP_mag] at h

end Lattice.Lib.Compiler.RealCompileFloatCorrectness
