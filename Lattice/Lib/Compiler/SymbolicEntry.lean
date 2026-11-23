import Lattice.Lib.Compiler.Layout
import Lattice.Lib.Compiler.Samples
import Lattice.Lib.Compiler.ChordGeneral
import Lattice.Lib.Compiler.RealTypeSystemExt
import Lattice.Lib.Compiler.IRWeightsBridge

/-!
# **符号入口：从 `ExprExt` 项到产物**

## 规划要求什么

规划 §3.1 A.2 要求三个层次**分别**交付，且明确禁止用一层替代另一层：

| 层次 | 要求 | 本文件 |
|:--|:--|:--|
| **源语义** | 接受片段中的 `s`，解析出的表示其源语义；**若不可解析则显式失败** | `evalSym`（对不支持片段返回 `none`） |
| **构造** | 从精度到资源的函数，**并证明该选择满足预算** | `compileTarget`（`CompileRecipe` 是输入）+ §3.11 的 `budget_of_sq` |
| **执行** | 真实构造权重、走编解码、求值 | `Target.family` + `EvaluatedArtifact` |

**⇒ 本文件补的是「从符号项进入」这一层**：第 1045 轮的两个样例输入是**分段族**，
所以「这条链从符号开始」当时只是意向。现在输入是 `ExprExt` 项。

## 设计上的两个判断（都不是形式选择）

**判断一：`compileTarget` 返回 `Option`，且 `none` 有**唯一**含义——「该符号项不在支持片段内」。**
它**不表示**「数值精度不够」或「实现未完成」。这与 `evalAt` 的 `none`（「按该产物的布局解不出载荷」）
是**两个不同的失败**，故二者不在同一层混用：`compileTarget` 的 `none` 在**编译期**，
`evalAt` 的 `none` 在**求值期**。

**判断二：编译目标是一个**和类型**（`Target`），而不是单一的「分段族」。**
因为仿射片段可以**精确**编译成常分段族，而 `x²` 只能**离散化**。
把两者压成同一形状会丢掉「这一项是精确的还是近似的」这一信息，而那正是规划 D2 要求区分的东西。
-/

namespace Lattice.Lib.Compiler.SymbolicEntry

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.ChordGeneral
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.Samples
open Lattice

/-- **源语义**：在 `x` 处对 `ExprExt` 项求值，只覆盖 **{整数/实数字面量, `var 0`, `add`, `mul`}**。

**⇒ `var 0` 是自由变量（即 `x`）；`var (n+1)`、`cmp`、`letIn`、`litBool` 一律返回 `none`，
因为这四项**在目标语义域里没有被解释**——不是「还没写」，而是「本片段不包含」。** -/
def evalSym (x : ℝ) : ExprExt → Option ℝ
  | .litInt n => some (n : ℝ)
  | .litReal r => some r
  | .litBool _ => none
  | .var n => if n = 0 then some x else none
  | .add e₁ e₂ => (evalSym x e₁).bind fun a => (evalSym x e₂).map fun b => a + b
  | .mul e₁ e₂ => (evalSym x e₁).bind fun a => (evalSym x e₂).map fun b => a * b
  | .cmp _ _ => none
  | .letIn _ _ _ => none

/-- **一般插值族**：把函数 `f` 在 `n` 个等分段上取弦。 -/
noncomputable def interpFamily (n : ℕ) (f : ℝ → ℝ) : ℕ → Segment :=
  fun k => chordOf f ((k : ℝ) / n) (((k : ℝ) + 1) / n)

/-- **编译目标**：两种精度语义。

**⇒ `affine a b` 承诺**精确**表示 `x ↦ a·x + b`；`squareApprox n hn` 承诺**近似**表示 `x²`，
其误差界由 `piecewiseIRWeights` 的既有定理给出。** -/
inductive Target where
  /-- **精确**：该项就是一个仿射函数。 -/
  | affine (a b : ℝ) : Target
  /-- **近似**：该项被离散化，段数由**配方**给出。 -/
  | squareApprox : Target
  /-- **一般插值**：任意实函数的分段弦插值。

  **⇒ 这是**第二族**：`affine` 与 `squareApprox` 都是它的特例（见
  `interpFamily_affine` 与 `chordOf_sq`）。⇒ 于是「能力」从**两个特例**
  变成**一个族**。** -/
  | interp (f : ℝ → ℝ) : Target

namespace Target

/-- **目标对应的分段族（取**配方**的段数）。**

**⇒ 第 1052 轮修正：段数只有**一个来源**——`recipe.n`。
此前 `Target` 自带一个 `n`，而 `evalAt` 用 `recipe.n` 做段索引，
**于是一个产物可以用 `n₁` 的族却用 `n₂` 的格子求值**，
而误差界要求两者相同。**把段数移到配方里，这个不一致在**类型上不可表达**。** -/
noncomputable def family (r : CompileRecipe) : Target → ℕ → Segment
  | .affine a b => affineFamily a b
  | .squareApprox => decodeGrid (piecewiseIRWeights r.n)
  | .interp f => interpFamily r.n f

end Target

/-- **编译：从符号项到目标。**

**⇒ 支持的形状（其余一律 `none`）：**
- 字面量 → 常仿射；
- `var 0` → 恒等仿射；
- `litReal k · e`（`e` 为仿射）→ 数乘；
- `e₁ + e₂`（两者均为仿射）→ 相加；
- **`var 0 · var 0` → 离散化目标**（`x²`）。

**⇒ 为什么数乘只支持**左乘字面量**：因为那是一件事的**全部**内容——把仿射缩放；
一般两个非常仿射相乘不是仿射，本片段的正确答案是「不支持」，而不是给一个近似。** -/
noncomputable def compileTarget (r : CompileRecipe) : ExprExt → Option Target
  | .litReal a => some (.affine 0 a)
  | .litInt n => some (.affine 0 (n : ℝ))
  | .var 0 => some (.affine 1 0)
  -- **`x²` 单独处理：它是本片段里唯一需要离散化的项。**
  | .mul (.var 0) (.var 0) => some (.squareApprox)
  | .mul (.litReal k) e =>
      match compileTarget r e with
      | some (.affine a b) => some (.affine (k * a) (k * b))
      | some .squareApprox => none
      | some (.interp _) => none
      | none => none
  | .add e₁ e₂ =>
      match compileTarget r e₁, compileTarget r e₂ with
      | some (.affine a₁ b₁), some (.affine a₂ b₂) => some (.affine (a₁ + a₂) (b₁ + b₂))
      | _, _ => none
  | _ => none

/-- **仿射项的语法形状**：`a·x + b`。 -/
def affineTerm (a b : ℝ) : ExprExt := .add (.mul (.litReal a) (.var 0)) (.litReal b)

/-- **`x²` 的语法形状**：`x · x`。**⇒ 这依赖第 1044 轮加入的 `mul`。** -/
def squareTerm : ExprExt := .mul (.var 0) (.var 0)

/-! ## 一、源语义：两个样例在 `evalSym` 下分别是什么 -/

/-- **仿射项的源语义**就是 `a·x + b`。 -/
theorem evalSym_affineTerm (a b x : ℝ) :
    evalSym x (affineTerm a b) = some (a * x + b) := by
  simp [affineTerm, evalSym]

/-- **`x²` 项的源语义**就是 `x · x`。 -/
theorem evalSym_squareTerm (x : ℝ) : evalSym x squareTerm = some (x * x) := by
  simp [squareTerm, evalSym]

/-! ## 二、编译：两个样例落到哪个目标 -/

/-- **仿射项编译到精确目标。** -/
theorem compileTarget_affineTerm (r : CompileRecipe) (a b : ℝ) :
    compileTarget r (affineTerm a b) = some (.affine a b) := by
  simp [affineTerm, compileTarget, mul_one, mul_zero]

/-- **`x²` 项编译到离散化目标。** -/
theorem compileTarget_squareTerm (r : CompileRecipe) :
    compileTarget r squareTerm = some (.squareApprox) := by
  simp [squareTerm, compileTarget]

/-! ## 三、端到端：符号项 → 产物 → 整域保证 -/

/-- **⭐⭐ 仿射路径：符号项 `a·x + b` 编译出的产物，求值**处处**等于该仿射函数（误差为零）。**

**⇒ 这条把三件事串起来：`evalSym` 给出源语义（`some (a*x+b)`）、
`compileTarget_affineTerm` 给出编译结果、`Target.family` 与 `evalAt_ofSegments` 给出产物求值。
**⇒ 于是「链从符号开始」是一条**被证明的等式链**，不再是意向。** -/
theorem affine_path_exact (r : CompileRecipe) (a b : ℝ)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) :
    compileTarget r (affineTerm a b) = some (.affine a b)
      ∧ (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments (Target.family r (.affine a b)) dom r).evalAt x
          = some (a * x + b) := by
  refine ⟨compileTarget_affineTerm r a b, ?_⟩
  rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments]
  -- **`Target.family r (.affine a b)` 就是 `affineFamily a b`，故折叠后再用求值引理。**
  show some (gridEval (affineFamily a b) r.n x) = some (a * x + b)
  rw [gridEval_affineFamily]

/-- **⭐⭐ `x²` 路径：符号项 `x · x` 编译出的产物，在 `[0,1]` 上整域满足既有误差界。**

**⇒ 两个合取项分别是「编译落点」与「整域界」。
界来自既有的 `irWeights_error_bound`，**并且 `x * x` 与 `x ^ 2` 通过 `pow_two` 对齐**——
这一步不能省：把它们当作同一个东西正是「比较不同对象」的那类错误。** -/
theorem square_path_bound (r : CompileRecipe) (dom : Lattice.Lib.Compiler.SemDomain)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    compileTarget r squareTerm = some (.squareApprox)
      ∧ ∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
            (Target.family r (.squareApprox)) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ (1 / (r.n : ℝ)) ^ 2 / 4 := by
  refine ⟨compileTarget_squareTerm r, ?_⟩
  refine ⟨gridEval (decodeGrid (piecewiseIRWeights r.n)) r.n x, ?_, ?_⟩
  · rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments]
    rfl
  · exact irWeights_error_bound r.n r.hn x hx

/-- **⭐⭐⭐ 仿射端到端：一条定理同时给出「源语义」「编译落点」「产物求值」。**

**⇒ 这是规划 §9 里程碑的形状：**一个符号输入 → 一份带布局与资源的产物 → 保证**，
**而且源语义、编译、求值三段**在同一个陈述里**，调用者不必自己拼。**

**⇒ 三个合取项的顺序是刻意的：先「该项在 `x` 处是什么」（源语义），再「它被编译成什么」，
最后「产物求值给出什么（且与源语义一致）」。** -/
theorem affine_end_to_end (r : CompileRecipe) (a b : ℝ)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) :
    evalSym x (affineTerm a b) = some (a * x + b)
      ∧ compileTarget r (affineTerm a b) = some (.affine a b)
      ∧ (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments (Target.family r (.affine a b)) dom r).evalAt x
          = some (a * x + b) :=
  ⟨evalSym_affineTerm a b x, affine_path_exact r a b dom x⟩

/-- **⭐⭐⭐ `x²` 端到端：源语义是 `x · x`，产物在 `[0,1]` 上整域达到既有误差界。**

**⇒ 第一个合取项把**源语义**与产物求值放在同一条陈述里；第二个合取项是产物求值的**界**。
**⇒ 两者的 `x · x` 与 `x ^ 2` 用 `pow_two` 对齐——不把它们当同一个东西。** -/
theorem square_end_to_end (r : CompileRecipe) (dom : Lattice.Lib.Compiler.SemDomain)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    evalSym x squareTerm = some (x * x)
      ∧ ∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
            (Target.family r (.squareApprox)) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ (1 / (r.n : ℝ)) ^ 2 / 4 :=
  ⟨evalSym_squareTerm x, (square_path_bound r dom x hx).2⟩

/-! ## 四、第二族：一般插值**包含**仿射族 -/

/-- **⭐⭐ 仿射函数的插值族**就是**常分段族。**

**⇒ 逐段用 `chordOf_affine`：仿射函数在任意两点上的弦恰好是那个仿射函数本身。**
**⇒ 于是新族在这一类上**退化**为旧族，而不是与它并列——这就是「包含」的可计算形式。** -/
theorem interpFamily_affine (n : ℕ) (hn : 0 < n) (c d : ℝ) :
    interpFamily n (fun x : ℝ => c * x + d) = affineFamily c d := by
  funext k
  show chordOf (fun x : ℝ => c * x + d) ((k : ℝ) / n) (((k : ℝ) + 1) / n)
      = (⟨c, d⟩ : Segment)
  apply chordOf_affine
  -- **端点不同：`n > 0` 时 `k/n < (k+1)/n`。**
  intro h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- **两边同乘 `n ≠ 0` 后 `h` 变成 `k = k + 1`；`field_simp` 自己就把目标关掉了。**
  field_simp at h

/-- **⭐⭐ 一般插值目标在仿射函数上与仿射目标**给出同一个族**。** -/
theorem interp_realises_affine (r : CompileRecipe) (c d : ℝ) :
    Target.family r (.interp (fun x : ℝ => c * x + d))
      = Target.family r (.affine c d) := by
  show interpFamily r.n (fun x : ℝ => c * x + d) = affineFamily c d
  exact interpFamily_affine r.n r.hn c d

/-- **⭐⭐⭐ 第二族的产物在仿射目标上**逐点精确**。**

**⇒ 这把 `interpFamily_affine` 从族层面推到**产物层面**：
产物契约（`evalAt_ofSegments`）+ 族相等 + 常族求值（`gridEval_affineFamily`）。**
**⇒ 于是「新族能做旧族能做的事」是一条定理，
而不是「我们保留了旧族所以它也能」这种推理。** -/
theorem interp_affine_artifact_exact (r : CompileRecipe) (c d : ℝ)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) :
    (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
        (Target.family r (.interp (fun x : ℝ => c * x + d))) dom r).evalAt x
      = some (c * x + d) := by
  rw [interp_realises_affine]
  rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments]
  show some (gridEval (affineFamily c d) r.n x) = some (c * x + d)
  rw [gridEval_affineFamily]

end Lattice.Lib.Compiler.SymbolicEntry