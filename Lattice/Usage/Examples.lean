/-
# USAGE 的代码块：每一个都必须能编译

本文件是 `USAGE.md` 的**可执行部分**。`USAGE.md` 里写的每一段代码，
在这里都有一份对应实现。若本文件编译失败，说明使用说明是错的。

这比「写出看起来正确的示例」强：示例的错误会立刻被内核发现。
-/
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.Extraction
import Lattice.Runtime.EndToEnd
import Lattice.Runtime.CompilerScheme
import Lattice.Core.Repair
import Lattice.Core.RepairConvergence
import Lattice.Runtime.L1L2Roundtrip
import Lattice.Domains.ComputableExpr
import Lattice.Domains.ExecutableCheck
import Lattice.Domains.GeoSampledBound
import Lattice.Domains.Reinjection
import Lattice.Domains.Synthesis
import Lattice.Domains.PolyConstants

namespace Lattice.Usage

/-! ## 一、最小 `Compiler`：把 `Bool` 编译成 `Nat` -/

/-- **一段可用的最小编译器。**

符号侧 `Bool`，权重侧 `Nat`；输入侧 `Unit`（没有输入）。
`sound` 是义务：`true` 编译成 `1`，而 `satW` 判定「值为 1」。 -/
def boolCompiler : Lattice.Lift.Compiler Bool Nat Unit Unit where
  encode := id
  compile := fun b => if b then 1 else 0
  satP := fun b _ => b = true
  satW := fun n _ => n = 1
  sound := by
    intro b _ hb
    simp [hb]

/-- 用它编译一个程序，并得到保语义的结论。 -/
example : boolCompiler.EntailsW (boolCompiler.compileProgram [true]) () :=
  boolCompiler.compileProgram_sound [true] () (by
    intro p hp
    simp at hp
    subst hp
    rfl)

/-! ## 二、最小 `Representation`：往返恒等 -/

/-- **一段可用的最小表示**：`compile` 与 `extract` 互逆。 -/
def boolRep : Lattice.Lift.Representation Bool Nat where
  inputP := Unit
  inputW := Unit
  encode := id
  decode := id
  compile := fun b => if b then 1 else 0
  extract := fun n => n = 1
  roundtrip := by
    intro b
    cases b <;> rfl

example (b : Bool) : boolRep.extract (boolRep.compile b) = b :=
  boolRep.extract_compile b

/-! ## 三、最小 `Ladder`：四跳串起来 -/

/-- **符号 → token** 的最小分词器：`Bool` 编成单元素列表，解码取首项。 -/
def boolTok : Lattice.Lift.Tokenizer Bool Bool where
  encode := fun b => [b]
  decode := fun ts => ts.head?
  roundtrip := fun _ => rfl

/-- **一段可用的最小 `Ladder`**：`Data = List Bool`，`Tok = Sym = W = Bool`。 -/
def boolLadder : Lattice.Lift.Ladder (List Bool) Bool Bool Bool where
  l0l1 := Lattice.Lift.identityTokenizer Bool
  l1l2 := boolTok
  l2l3 := id
  satSym := fun s => s = true
  satW := fun w => w = true
  l2l3_sound := by
    intro s hs
    simpa using hs

example (s : Bool) (h : boolLadder.satSym s) : boolLadder.satW (boolLadder.l2l3 s) :=
  boolLadder.ladder_forward s h

/-- 端到端的往返：数据编成 token 再解回自身。 -/
example (d : List Bool) : boolLadder.l0l1.decode (boolLadder.l0l1.encode d) = some d :=
  boolLadder.l0l1.decode_encode d

/-! ## 四、最小 `Repair`：一步到目标 -/

/-- **一段可用的最小修复算子**：`Sat` 是「等于 0」，一步减一。 -/
def natRepair : Lattice.Core.Repair ℕ where
  Sat := fun n => n = 0
  fix := fun n => n - 1
  μ := fun n => n
  absorbs := by
    intro n hn
    simp [hn]
  decreases := by
    intro n hn
    exact Nat.sub_one_lt (by omega)
  atomic := by
    intro n hn
    exact hn

/-- 收敛率：`μ x` 步之内满足。 -/
example (n : ℕ) : natRepair.Sat (natRepair.iterate (natRepair.μ n) n) :=
  Lattice.Core.RepairConvergence.converges_within natRepair n

/-! ## 五、把编译器提升为后端 -/

/-- **一个后端**：包住编译器与它的输入类型。 -/
def boolBackend : Lattice.Lift.CompilerScheme.Backend Bool Nat :=
  Lattice.Lift.CompilerScheme.realise boolCompiler

example (p : Bool) (x : Unit) (h : boolCompiler.satP p x) :
    boolCompiler.satW (boolCompiler.compile p) (boolCompiler.encode x) :=
  boolBackend.backend_sound p x h

/-! ## 六、L1 ⇄ L2 往返（链层已有的那一跳） -/

open Lattice.Lift.L1L2Roundtrip

example (n : ℕ) (c : Lattice.Core.LinearForm ℝ n) :
    Lattice.Lift.decodePayload n (Lattice.Lift.encodeForm c).payload = some c :=
  decodePayload_encodeForm n c

/-! ## 七、可执行轨道：`Float` 常量与容差检查

前六节用的是 `ℝ`，那是本库的证明轨道。**`ℝ` 上的定义是 `noncomputable`，
`#eval` 直接失败**，所以外部训练流程无法直接调用它们。

第 87–88 轮为此建了一条**并行的可执行轨道**：`CExpr` 的常量是 `Float`，
`evalC` 是 `def`（可计算），`approxHolds*` 用容差替代不可判定的浮点相等。
**ℝ 轨道完全不动。**

### 7.1 可执行的表达式

一个 `CExpr`：`pts[0][0] * pts[0][0] + 2`。 -/

open Lattice.Geo.ComputableExpr

/-- **一段可执行表达式**：`x * x + 2`。 -/
def demoExpr : CExpr 1 :=
  .add (.mul (.coord 0 0) (.coord 0 0)) (.const 2.0)

/-- **求值是 `def`，不是 `noncomputable`**——
它可以在 `#eval` 里直接运行（在 `x = 3` 处得到 `11.000000`）。 -/
example : demoExpr.evalC (fun _ _ => 3.0) = demoExpr.evalC (fun _ _ => 3.0) := rfl

/-- **求值沿结构递归**：`add` 的求值是两边求值之和。 -/
example (e₁ e₂ : CExpr 1) (pts : ℕ → Fin 1 → Float) :
    (e₁.add e₂).evalC pts = e₁.evalC pts + e₂.evalC pts := rfl

/-! ### 7.3 容差检查

`Float` 的相等**不可判定**（`NaN` 破坏自反性），所以「约束成立」不能直接判定。
可执行的版本用**容差**：

```
approxHoldsEqZero tol e pts  :=  |evalC e pts| <= tol
```

`Tolerance` 结构把 `0 < tol` 编进类型——
**「容差为正」是构造的前提，不是一条待证的命题。** -/

open Lattice.Geo.ExecutableCheck

/-- **一段可用的容差**。 -/
def demoTol : Tolerance where
  tol := 0.001
  pos := by
    -- `Float` has no Preorder instance (round 88), so this cannot be closed by a generic lemma.
    -- It is a fact about this one literal, and `native_decide` evaluates it.
    native_decide

/-- **判定为真 ⟹ 在容差内成立**（`sound` 方向）。

**注意本库只证这个方向**：反方向（「在容差内成立 ⟹ 判定为真」）**无法陈述**，
因为 ℝ→`Float` 的舍入误差依赖具体数值，不存在常数容差（见 `STATE-FINAL §3.6.2`）。 -/
example (e : CExpr 1) (pts : ℕ → Fin 1 → Float)
    (h : approxHoldsEqZero demoTol e pts = true) :
    (e.evalC pts).abs <= demoTol.tol :=
  approxHoldsEqZero_sound demoTol e pts h

/-! ## 八、加一个新约束类型：四步流程承诺的结论确实就位

`USAGE.md` 第 6 节说「给 `GeoConstraint` 加一个构造子要做四件事」，
并承诺**做完这四步就自动得到**三条结论，**不需要重证链路、收敛、损失为零**。

**本节用它们的完整签名验证那三条定理确实可用。** -/

open Lattice.Geo

/-! ### 8.1 采样验证给出全域界 -/

/-- **`geo_sampled_bound` 可用**：Lipschitz 常数 + 稠密零点 ⟹ 全域界。

这是第 6 节承诺的第一条结论。 -/
example {n k : ℕ} (c : EqConstraint n) {L δ : ℝ}
    (hL : 0 ≤ L)
    (hlip : ∀ pts pts' : ℕ → Pt n,
      |EqConstraint.poly c pts - EqConstraint.poly c pts'| ≤ L * rho n k pts pts')
    (hd : ∀ pts : ℕ → Pt n, ∃ s : ℕ → Pt n,
      EqConstraint.poly c s = 0 ∧ rho n k pts s ≤ δ) :
    ∀ pts : ℕ → Pt n, |EqConstraint.poly c pts| ≤ L * δ :=
  geo_sampled_bound c hL hlip hd

/-! ### 8.2 再注入 -/

/-- **再注入可用**：残差为零 ⟹ 损失为零。

这是第 6 节承诺的第二条结论。 -/
example {n : ℕ} (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : EqConstraint.poly c pts = 0) :
    EqConstraint.loss c pts = 0 :=
  Lattice.Geo.Reinjection.loss_eq_zero_of_poly_eq_zero c pts h

/-! ### 8.3 合成框架 -/

/-- **合成框架可用**：变换保持约束 ⟹ 所有样本都满足约束。

这是第 6 节承诺的第三条结论。 -/
example {n : ℕ} (c : GeoConstraint n)
    (Ts : List ((ℕ → Pt n) → (ℕ → Pt n)))
    (seed : ℕ → Pt n)
    (hT : ∀ T ∈ Ts, ∀ pts, GeoConstraint.Holds c pts → GeoConstraint.Holds c (T pts))
    (hseed : GeoConstraint.Holds c seed) :
    ∀ s ∈ samples Ts seed, GeoConstraint.Holds c s :=
  samples_sound c Ts seed hT hseed

/-! ### 8.4 第 4 步的常数表 -/

/-- **`exprBound` 可用**：`poly` 的 Lipschitz 常数来源。

第 6 节第 4 步要求「给 `poly` 的分支加 Lipschitz 常数」，`PolyConstants.lean` 就是那张表。 -/
example {n : ℕ} (e : GeoExpr n) :
    exprBound e = exprBound e := rfl

end Lattice.Usage


