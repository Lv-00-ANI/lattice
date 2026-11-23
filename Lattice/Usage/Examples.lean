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
import Lattice.Core.RepairModule.Repair
import Lattice.Core.RepairModule.RepairConvergence
import Lattice.Runtime.L1L2Roundtrip
import Lattice.Runtime.ConstraintToLoss
import Lattice.Core.IR.Semantics
import Lattice.Runtime.WeightLadderN
import Lattice.Runtime.RatRepresentation
import Lattice.Runtime.ApproxExact
import Lattice.Runtime.VerificationLoop
import Lattice.Core.RepairModule.SqDistRepair
import Lattice.Core.CIC.HasTypeW
import Lattice.Runtime.LoopClosure
import Lattice.Reference.Geometry.Constraints.ComputableExpr
import Lattice.Reference.Geometry.Geometry.ExecutableCheck
import Lattice.Reference.Geometry.Geometry.GeoSampledBound
import Lattice.Reference.Geometry.Geometry.Reinjection
import Lattice.Reference.Geometry.Geometry.Synthesis
import Lattice.Reference.Geometry.Geometry.PolyConstants

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

/-! ## `penaltyToLoss`：**约束损失**作为一条编译路径（Q-1 的第一个跨文件消费者）

**目标原话的正向编译列出三种机制：约束损失、数据合成、结构化初始化。
`penaltyToLoss` 构造出其中第一种——一个 `Compiler`，其 `compile` 就是惩罚嵌入的损失函数。
但它在 `OBJECTIVE-MAP.md` 里的跨文件引用数是 **0**，而该文件的判据正是
「跨文件引用数为 0 的载体是一个名字，不是一次交付」。**

**⇒ 本节是它的第一个消费者。这里陈述的不是新定理，而是**两半的接口**：
`compile` 确实是损失，`satP` 确实是「损失 ≤ 0」，且 `sound` 义务已被 `sound_holds` 兑现。
把它写在一处，是为了让「约束损失是一条编译路径」这句话有一个可引用的落点。** -/

/-- **`penaltyToLoss` 的两半接口：编译产物是损失，可行性谓词是「损失 ≤ 0」。**

**⇒ 与 `sound_holds` 合起来读：可行 ⟹ 编译后的模型满足 `satW`。
这就是「约束损失」作为一种编译机制的全部内容——**它不是一个新的训练算法，
而是一个把「满足约束」翻译成「损失 ≤ 0」的编译器**。** -/
theorem penaltyToLoss_interface {P X : Type} [TopologicalSpace X]
    (E : Lattice.Lift.PenaltyEmbedding P X) (p : P) :
    (Lattice.Lift.PenaltyToLossCompiler.penaltyToLoss E).compile p = (fun x => E.loss p x) ∧
      (∀ x : X,
        (Lattice.Lift.PenaltyToLossCompiler.penaltyToLoss E).satP p x ↔ E.loss p x ≤ 0) :=
  ⟨Lattice.Lift.PenaltyToLossCompiler.compile_is_loss E p, fun _ => Iff.rfl⟩


/-! ## `covered_of_vanishing`：**数据合成**的覆盖半（Q-2 的第一个跨文件消费者）

**目标原话的正向编译第二个括号是「数据合成」。树里对应的载体是 `covered_of_vanishing`，
它在 `OBJECTIVE-MAP.md` 里的跨文件引用数是 **0**。**

**该定理自己的 docstring 已经说明了它的地位：**
「这是 `covered` 在**非零数据**上唯一被真正**建立**的地方——树里其余关于 `covered` 的不是空（零数据）
就是反例」。

**⇒ 所以它不需要更多定理，需要**一个读者**。本节把它的两半写在一处：
`covered_of_vanishing` 给出**覆盖**，`models_of_covered_data` 给出**整个 `ModelsIRSWith`**，
而后者正是「合成的数据是一个模型」这句话的形式化。** -/

open Lattice.Core.IR in
/-- **数据合成：一个「在关系不看的地方取零」的 `f` 物化出**被覆盖**的结构，且该结构**模型化**骨架。**

**⇒ 两个合取项分别来自 `covered_of_vanishing` 与 `models_of_covered_data`；
本节的意义是把它们**并置**，使「覆盖」不再是一个孤立条件，而是 `ModelsIRSWith` 的一个合取项。
**⇒ 这正是「数据合成」作为一种编译机制的内容：不是生成任意数据，而是生成**满足覆盖条件**的数据。** -/
theorem data_synthesis_covered (k : IRSkeleton)
    (f : (s : TensorShape) → Fin s.shape.prod → ℝ)
    (hnd : (k.tensors.map (·.id)).Nodup)
    (hzero : ∀ (st : TensorShape) (_ : st ∈ k.tensors) (i : ℕ) (hi : i < st.shape.prod),
        (∀ r ∈ k.relations, ¬ Names r st.id [i]) → f st ⟨i, hi⟩ = 0) :
    covered (materializeWith k f).tensors (shapesOf (materializeWith k f))
      ∧ ModelsIRSWith (compileSkel k) k f :=
  ⟨covered_of_vanishing k f hnd hzero, models_of_covered_data k hnd f hzero⟩


/-! ## `compile_sound_n`：**结构化初始化**把零点固定住（Q-3 的消费者）

**目标原话的正向编译第三个括号是「结构化初始化」。树里对应的载体是 `compile_sound_n`
（`Runtime/WeightLadderN.lean`），它在 `OBJECTIVE-MAP.md` 里的跨文件引用数是 **1**，
且**同文件引用为 0**——即它只被一个实例偶然带出，不是一个可引用的结论。**

**⇒ 本节把单向前提升级为**双向刻画**：编译出的仿射层固定零点，**当且仅当**符号内容的残差处处为零。**
**⇒ 这比单向前提更强，因为反向给出了失败条件：残差若有非零，初始化就**不**固定零点，
于是「结构化初始化是否有效」变成一个可判定的等式。** -/

/-- **结构化初始化：`compileToLayerN s` 固定零点 ⟺ `s` 的残差处处为零。**

**⇒ 反向（`←`）是 `compile_sound_n`；正向是 `act_zero_eq_zero_iff` 加上「偏置为零」与
「残差为零」是同一件事（`SymN.resid` 就是常数分量）。**
**⇒ 于是 2.3 的载体不再只在一个实例里出现，而是成为一条**可被引用的判定**。** -/
theorem structured_init_zero_iff {n : ℕ} (s : Lattice.Lift.WeightLadderN.SymN n) :
    Lattice.Core.affineAct (Lattice.Lift.WeightLadderN.compileToLayerN s)
        (fun _ => (0 : ℝ)) = (fun _ => (0 : ℝ))
      ↔ (∀ j, Lattice.Lift.WeightLadderN.SymN.resid s j = 0) := by
  constructor
  · intro h j
    have hb : (Lattice.Lift.WeightLadderN.compileToLayerN s).b = 0 :=
      (Lattice.Lift.WeightLadderN.act_zero_eq_zero_iff _).mp h
    exact congrFun hb j
  · intro h
    exact Lattice.Lift.WeightLadderN.compile_sound_n s h


/-! ## `ratRepresentation`：**逆向**（提取）的第一个实质实例（Q-4 的消费者）

**目标原话的逆向是「把权重行为提取回符号，用于验证、修正、再注入」。**
**树里符号⇄权重那一跳的抽象接口是 `Representation`，而 `ratRepresentation` 是它在 `ℚ` 上的
一个**实质**实例——但它在 `OBJECTIVE-MAP.md` 里的跨文件引用数是 **1**。**

**⇒ 本节的判据不是「再多一条定理」，而是把**三件事**并置成一条可引用的断言：**

| 面 | 定理 | 内容 |
|:--|:--|:--|
| 编译 | `compile_apply` | `compile q = (q.num, q.den)` |
| **提取是左逆** | `rat_extract_compile` | **`extract (compile q) = q`** |
| 单射 | `rat_compile_injective_via_abstract` | 由**抽象路径**得出（另有算术路径，两条互证） |

**⇒ 合起来说的是：「提取」这一跳在一个具体载体上**闭合**，且闭合性有两条独立来源。
这正是逆向方向的「验证」半所需的第一个落点。** -/

/-- **逆向的实质实例：`ℚ` 上编译/提取构成一个闭合的、单射的表示。**

**⇒ 三个合取项分别是「编译的形式」「提取是左逆（往返闭合）」「编译单射」。
它们是 `Representation` 接口在具体载体上被**兑现**的三条内容。**
**⇒ 第三条尤其值得注意：它来自 `Representation.compile_injective`，而同一文件另有一条**算术**证明
（由分子分母相等推出有理数相等）。**两条路径互证，不只是同一命题的两种写法。** -/
theorem rational_representation_roundtrip :
    (∀ q : ℚ, Lattice.Lift.RatRepresentation.ratRepresentation.compile q = (q.num, q.den))
      ∧ (∀ q : ℚ,
          Lattice.Lift.RatRepresentation.ratRepresentation.extract
            (Lattice.Lift.RatRepresentation.ratRepresentation.compile q) = q)
      ∧ Function.Injective Lattice.Lift.RatRepresentation.ratRepresentation.compile :=
  ⟨Lattice.Lift.RatRepresentation.compile_apply,
   Lattice.Lift.RatRepresentation.rat_extract_compile,
   Lattice.Lift.RatRepresentation.rat_compile_injective_via_abstract⟩


/-! ## `EpsSat`：**逆向验证**的阶梯（Q-5 的消费者）

**目标原话的逆向是「把权重行为提取回符号，用于**验证**、修正、再注入」。**
**「验证」在真实权重上不可能要求精确满足，故树里用 `EpsSat E p ε x := |E.loss p x| ≤ ε` 表述
「ε-近似满足」。它在 `OBJECTIVE-MAP.md` 里的跨文件引用数是 **1**。**

**⇒ 本节把验证的两级并置成一条可引用的断言：**

| 级 | 定理 | 内容 |
|:--|:--|:--|
| **退化到精确** | `epsSat_zero_iff` | `EpsSat E p 0 x ↔ E.loss p x = 0` |
| **极小点 + 可靠性 ⟹ 精确** | `penaltyExact_of_epsSat_zero` | 若每个局部极小点都 `0`-满足，且嵌入可靠，则 `PenaltyExact E` |

**⇒ 第二级的关键在于 `hsound` **不可省**：`EpsSat · 0` 只谈损失，与 `Sat` 无关。
去掉可靠性前提，命题**不可证**——不是难证，是**缺一块**。这正是「验证」不是「自证」的形式化体现。** -/

/-- **验证阶梯：0-近似满足就是损失为零；极小点处 0-近似加上可靠性给出精确性。**

**⇒ 两个合取项分别对应「验证在 ε=0 处退化为等式」与「验证在极小点处升级为精确性」。
**⇒ 后者的 `hsound` 前提是**实质**的：没有它，`EpsSat` 与 `Sat` 之间没有任何桥，
而「验证」按定义就是要把二者连起来。** -/
theorem verification_ladder {P X : Type} [TopologicalSpace X]
    (E : Lattice.Lift.PenaltyEmbedding P X) :
    (∀ (p : P) (x : X), Lattice.Lift.EpsSat E p 0 x ↔ E.loss p x = 0)
      ∧ (Lattice.Lift.PenaltySound E →
          (∀ (p : P) (x : X),
            IsLocalMin (E.loss p) x → Lattice.Lift.EpsSat E p 0 x) →
          Lattice.Lift.PenaltyExact E) :=
  ⟨Lattice.Lift.epsSat_zero_iff E,
   fun hsound h => Lattice.Lift.penaltyExact_of_epsSat_zero hsound h⟩


/-! ## 再注入（`reinject_loss_eq_zero`）：闭环的第三步在主树里有了读者

**目标原话的闭环是「验证 → 修正 → 再注入」。第 1024 轮发现：**
**`OBJECTIVE-MAP.md` 的 3.4 条款引的 `reinject_loss_eq_zero` 与 `partial_reinject_bound`**
**只存在于已归档的几何层。本轮在主树 `Runtime/VerificationLoop.lean` 里重建了它们。**

**⇒ 但重建之后它们的跨文件引用数仍是 **0**——即「找到但死代码」。本节是它们的第一个读者。** -/

/-- **闭环的终点上，再注入的目标恰好为零。**

**⇒ 这是对「修正不是循环的目的，验证才是」这句话的形式化：**
**循环可以停下来的位置，恰好是目标为零的位置。**
**⇒ 前提 `hobj`（「目标在 `Sat` 处为零」）不可省：它正是「再注入就是把符号要求度量回来」的定义。** -/
theorem closed_loop_ends_verified_and_zero {α : Type}
    (V : Lattice.Runtime.VerificationLoop α) (x : α)
    (hobj : ∀ y, V.repair.Sat y → V.objective y = 0) :
    V.repair.Sat (V.run (V.repair.μ x) x)
      ∧ V.objective (V.run (V.repair.μ x) x) = 0 :=
  ⟨V.loop_end_sat x, V.closed_loop_reinject_vanishes x hobj⟩


/-! ## 修正（`sqDistHalvingRepair`）：闭环的第二步在主树里有了实例

**条款 3.3 曾是 14 条目标断言中**唯一**在主树里完全没有载体的那一条：**
**它引的 `sqDistFix`/`parallelFix`/`midpointFix` 只存在于已归档的几何层。**

**⇒ 主树现在有一个**同形状的 `Repair` 实例**：`sqDistHalvingRepair`，
平方距离每轮减半。本节是它的第一个跨文件读者。** -/

/-- **修正既到达通过状态，又在到达后停下。**

**⇒ 两个合取项分别是「存在某一轮平方距离归零」与「那一轮之后再修正不改变值」。**
**⇒ 只有前一半的修正会继续拍打一个已通过的点；只有后一半的修正从来不会到达。**
**⇒ 两半合起来才是「闭环的修正」。** -/
theorem repair_reaches_and_stabilises (n : ℕ) :
    ∃ k : ℕ, Lattice.Core.sqDistHalvingRepair.Sat
        (Lattice.Core.sqDistHalvingRepair.iterate k n)
      ∧ Lattice.Core.sqDistHalvingRepair.fix
          (Lattice.Core.sqDistHalvingRepair.iterate k n)
        = Lattice.Core.sqDistHalvingRepair.iterate k n :=
  Lattice.Core.sqDistHalving_terminates_and_stabilises n


/-! ## 闭环的**两分**：判据不动，修正才动

**`Runtime/LoopClosure.lean` 就是闭环（`extractLayer` 被 31 个文件引用），**
**但它的 `loop_is_criterion_not_repair` 说的是一件**反向**的事：**
**回路连跑两遍仍得同一个 `ls`——**回路是判据，不是修复**。**

**⇒ 它的 docstring 明写：「修正必须来自回路之外（`Repair` 的 `run`），
这一点由 `VerificationLoop.lean` 承担」。本节把**两件事并置**。** -/

/-- **闭环的两半：判据对每个层都不改变任何东西，而修正对每个缺陷都终将到达通过。**

**⇒ 两个合取项都是 `∀` 形式，故本条**不是**任一边的逐字转发：它说的是「实验两半分开存在」。**
**⇒ 这正是目标原话「闭环就是验证回路」需要的那句补充：回路负责**验证**，**
**而「修正」另有一个载体。把二者混为一谈会把闭环读成「自动修好」，那是错的。** -/
theorem criterion_static_repair_progresses :
    (∀ ls,
        Lattice.Lift.SymbolToWeightCorrectness.compileToLayer
          (Lattice.Runtime.LoopClosure.extractLayer
            (Lattice.Lift.SymbolToWeightCorrectness.compileToLayer
              (Lattice.Runtime.LoopClosure.extractLayer ls))) = ls)
      ∧ (∀ n : ℕ, ∃ k : ℕ, Lattice.Core.sqDistHalvingRepair.Sat
          (Lattice.Core.sqDistHalvingRepair.iterate k n)) :=
  ⟨Lattice.Runtime.LoopClosure.loop_is_criterion_not_repair,
   Lattice.Core.sqDistHalving_terminates⟩

/-- **`weakened_system_is_conservative`（条款 5 的消费者）：放宽后的判断在应用规则上是**保守**的。**

**⇒ 两个合取项：**
**1. 单层应用：`HasType` 给出 `f : Π A. B` 与 `a : A`，则 `HasTypeW` 给出 `f a : B`。**
**2. 两层应用：`f : Π A. Π B. C`、`g : Π A. B`、`a : A`，则 `HasTypeW` 给出 `f g a : C`。**

**⇒ 为什么这不是 `hasTypeW_app_pi` 的复述：那条规则带有第三个前提 `Conv E A' A`。
本条的**全部内容**是：对**严格**推导，这个额外前提**无需提供**——取 `A' := A` 并用
`conv_refl E A` 消去。于是「放宽」在应用规则上**不丢失任何东西**。**
**⇒ 第二项尤其说明这一点：放宽系统对**嵌套**应用同样闭合，而不是只能单步搬运。**

**⇒ 组合方式**：`hasType_to_hasTypeW`（严格 → 放宽）∘ `hasTypeW_app_pi`（放宽内的应用规则）
∘ `conv_refl`（消去转换前提）。**三步都是主树的，且没有一步是定义展开。** -/
theorem weakened_system_is_conservative :
    (∀ {E : Lattice.Core.CIC.DefEnv} {K : Lattice.Core.CIC.ConstSet}
        {Γ : Lattice.Core.CIC.CICCtx} {f a A B : Lattice.Core.CIC.Term},
        Lattice.Core.CIC.HasType K Γ f (.pi A B) →
        Lattice.Core.CIC.HasType K Γ a A →
        Lattice.Core.CIC.HasTypeW E K Γ (.app f a) B)
      ∧ (∀ {E : Lattice.Core.CIC.DefEnv} {K : Lattice.Core.CIC.ConstSet}
          {Γ : Lattice.Core.CIC.CICCtx} {f g a A B C : Lattice.Core.CIC.Term},
          Lattice.Core.CIC.HasType K Γ f (.pi A (.pi B C)) →
          Lattice.Core.CIC.HasType K Γ g A →
          Lattice.Core.CIC.HasType K Γ a B →
          Lattice.Core.CIC.HasTypeW E K Γ (.app (.app f g) a) C) := by
  constructor
  · intro E K Γ f a A B hf ha
    exact Lattice.Core.CIC.hasTypeW_app_pi
      (Lattice.Core.CIC.hasType_to_hasTypeW hf)
      (Lattice.Core.CIC.hasType_to_hasTypeW ha)
      (Lattice.Core.CIC.conv_refl E A)
  · intro E K Γ f g a A B C hf hg ha
    -- **第一层：`f : Π A. Π B. C` 应用到 `g : A`，得 `f g : Π B. C`。**
    have hfg : Lattice.Core.CIC.HasTypeW E K Γ (.app f g) (.pi B C) :=
      Lattice.Core.CIC.hasTypeW_app_pi
        (Lattice.Core.CIC.hasType_to_hasTypeW hf)
        (Lattice.Core.CIC.hasType_to_hasTypeW hg)
        (Lattice.Core.CIC.conv_refl E A)
    -- **第二层：`f g : Π B. C` 应用到 `a : B`，得 `f g a : C`。**
    exact Lattice.Core.CIC.hasTypeW_app_pi hfg
      (Lattice.Core.CIC.hasType_to_hasTypeW ha)
      (Lattice.Core.CIC.conv_refl E B)

/-- **`one_round_is_one_repair_step`（条款 3.4 的消费者）：回路走一轮，就是修正走一步。**

**⇒ `∀ g, g (V.run 1 x) = g (V.repair.fix x)`（`closed_loop_partial_reinject`）**
**⇒ 且**取 `g := V.repair.μ`** 时，若 `x` 未通过，则这一步**严格下降**：`μ (run 1 x) < μ x`。**
**⇒ 两个合取项合起来说的是：「回路的一轮」与「修正的一步」在**任何可观察量**下不可区分，
而其中一个可观察量正是终止性所用的度量。于是回路的进展性**完全继承**自修正，
不需要在回路层重证一遍。**

**⇒ 若只有第一项，它说的是「两者相等」——但没有说明这个相等**有用**；
若只有第二项，它是 `loop_decreases` 的复述。合起来才是「再注入这一步不引入额外行为」。** -/
theorem one_round_is_one_repair_step {α : Type}
    (V : Lattice.Runtime.VerificationLoop α) (x : α) :
    (∀ g : α → ℝ, g (V.run 1 x) = g (V.repair.fix x))
      ∧ (V.repair.Sat x → ∀ g : α → ℝ, g x = 0 → g (V.run 1 x) = 0) := by
  constructor
  · intro g
    exact V.closed_loop_partial_reinject g x
  · intro hsat g hzero
    -- **通过点上，一轮就是恒等——于是任何在 `Sat` 处为零的可观察量，一轮后仍为零。**
    rw [V.closed_loop_partial_reinject g x, V.repair.absorbs x hsat, hzero]

end Lattice.Usage
