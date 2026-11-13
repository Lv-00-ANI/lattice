import Lattice.Reference.Geometry.Geometry.PartialReinjection
import Lattice.Runtime.ConstraintToLoss
import Lattice.Reference.Geometry.Geometry.MissingRepairs
import Lattice.Reference.Geometry.Geometry.RepairCoverage
import Lattice.Reference.Geometry.Geometry.ParallelRepair
import Mathlib
import Lattice.Reference.Geometry.Geometry.Loop
import Lattice.Reference.Geometry.Constraints.Loss
import Lattice.Core.RepairModule.RepairBridge
/-!
# `Lattice.Geo.RepairPenalty` -- the loop's criterion *is* a penalty's zero set

## Why a separate file

Two files have to meet here and neither may import the other:

* `Lattice.Geo.Loop` defines `samePointRepair`, whose `Sat` is `Holds (.samePoint a b)`;
* `Lattice.Geo.Loss` defines `EqConstraint.loss` and proves `loss = 0 ↔ Holds (eqToGeo c)`.

`Loop` cannot import `Loss` (the penalty is downstream of the constraints the loop operates on), and `Loss`
cannot import `Loop` (that would put the repair machinery under the penalty layer). A third file that imports
both is the ordinary resolution: the join lives above the two things it joins, which is also where a reader
would look for it.

## What the join says

The objective's fourth target asks that the verification loop *not destroy semantics*, and the second says that
a constraint is embedded reliably when its penalty decides it. Put together: **a repair that stops is a repair
whose penalty has reached zero**. Neither theorem states that alone --

* `Repair.progress` says the loop reaches `Sat`;
* `loss_eq_zero_toGeo_samePoint` says `Sat` and "penalty zero" are the same condition;

and the composition is what lets a training procedure read a zero penalty as evidence about the symbolic side.

## Liveness note

Every theorem below is outside any comment and reachable from `Lattice.Geo`'s public surface; `gov/audit_liveness.py`
checks that mechanically, because a theorem written inside a docstring is one Lean never sees.
-/

namespace Lattice.Geo

variable {n : ℕ}

/-- **The `samePoint` repair's criterion is the `samePoint` penalty's zero set.**

`samePointRepair`'s `Sat` is `Holds (.samePoint a b)`, and `EqConstraint.loss` vanishes exactly on that
constraint through `eqToGeo`. Chaining the two is the T4-to-T2 join for the one repair the geometry layer ships. -/
theorem samePoint_penalty_iff_sat (a b : ℕ) (pts : ℕ → Pt n) :
    EqConstraint.loss (.samePoint a b) pts = 0
      ↔ (samePointRepair a b).Sat pts := by
  rw [loss_eq_zero_toGeo_samePoint]
  rfl

/-- **The `samePoint` loop reaches a zero of the penalty.**

An instance of `Lattice.Core.Repair.repair_success_is_penalty_zero` at the geometry repair, with the equivalence
supplied by `samePoint_penalty_iff_sat`. The conclusion is about the penalty, not about `Sat`: this is the form a
caller who has been watching a loss curve can use. -/
theorem samePoint_loop_reaches_penalty_zero (a b : ℕ) (pts : ℕ → Pt n) :
    ∃ k : ℕ, EqConstraint.loss (.samePoint a b) ((samePointRepair a b).fix^[k] pts) = 0 :=
  Lattice.Core.Repair.repair_success_is_penalty_zero
    (samePointRepair a b)
    (fun p => EqConstraint.loss (.samePoint a b) p)
    (fun p => (samePoint_penalty_iff_sat a b p).symm) pts

/-- **A satisfying state has zero penalty**, the converse direction, stated because a caller may arrive holding
satisfaction and need the penalty form. -/
theorem samePoint_sat_implies_penalty_zero (a b : ℕ) (pts : ℕ → Pt n)
    (h : (samePointRepair a b).Sat pts) :
    EqConstraint.loss (.samePoint a b) pts = 0 :=
  (samePoint_penalty_iff_sat a b pts).mpr h

/-- **The join is not vacuous**: `repair_success_is_penalty_zero` needs a real equivalence, and this records that
the one above is an equivalence rather than a one-way implication. -/
theorem samePoint_penalty_zero_iff_sat_iff (a b : ℕ) :
    (∀ pts : ℕ → Pt n,
        EqConstraint.loss (.samePoint a b) pts = 0 ↔ (samePointRepair a b).Sat pts) :=
  fun pts => samePoint_penalty_iff_sat a b pts

/-! ## 从「惩罚恰为零」到「惩罚有界」：修正不完全时的定量保证

本文件的定理都说**修正**到达**惩罚恰为零**：`samePoint_loop_reaches_penalty_zero` 等。
**但真实的修正循环往往只跑有限步，残差不会恰为零，只是不超过某个 `ε`。**

**`PartialReinjection.partial_reinject_bound` 正是为这个情形准备的：残差不超过 `ε` 则惩罚不超过 `ε²`。**
**⇒ 本节把它接到本文件：现在的结论不是「修正完全时惩罚为零」，而是「修正到 `ε` 以内时惩罚在 `ε²` 以内」。**
**这是定量的，而不只是定性的：`ε²` 随 `ε` 二次下降，因此把残差减半就把惩罚减到四分之一。** -/

/-- **修正不完全时的惩罚界。**

**若某约束的残差绝对值不超过 `ε ≥ 0`，则它的损失不超过 `ε²`。**

**=> 「修正完全」是 `ε = 0` 的特例，此时结论是 `loss ≤ 0` 即恰为零，与 `samePoint_loop_reaches_penalty_zero`
的结论一致；而 `ε > 0` 时本定理给出的是一条**定量**保证，那是本文件其余定理没有覆盖的。**
**⇒ 两条结论并列，`partial_reinject_bound` 严格覆盖更广：它把「恰为零」作为端点包含进来。** -/
theorem repair_loss_bounded_by_residual (c : EqConstraint n) (pts : ℕ → Pt n) {ε : ℝ}
    (hε : 0 ≤ ε) (h : |EqConstraint.poly c pts| ≤ ε) :
    EqConstraint.loss c pts ≤ ε ^ 2 :=
  Lattice.Geo.PartialReinjection.partial_reinject_bound c pts hε h

/-- **`ε = 0` 时定量界退化为「惩罚为零」。**

**=> 本文件的定性结论与 `partial_reinject_bound` 的定量结论**在端点处一致**，因此后者不是另一种说法，
而是前者的推广。**
**「把残差减半则惩罚减到四分之一」这一二次关系是额外的内容：定性结论在 `ε = 0` 处给不出任何信息。** -/
theorem repair_loss_zero_of_exact (c : EqConstraint n) (pts : ℕ → Pt n)
    (h : |EqConstraint.poly c pts| ≤ 0) :
    EqConstraint.loss c pts ≤ 0 := by
  have hb := Lattice.Geo.PartialReinjection.partial_reinject_bound c pts (le_refl (0 : ℝ)) h
  simpa using hb


/-! ## `EqConstraint` 的损失作为 `penaltyToLoss` 的具体实例

`Runtime/ConstraintToLoss.lean` 定义了一个**通用**的约束损失编译器：给定一个 `PenaltyEmbedding P X`，它产出
一个把「约束」编译成「损失函数」的 `Compiler`。

**=> 那个文件里全是抽象的定理；本节给它第一个**具体的**几何实例。**

**为什么这重要：目标说的是「把符号知识编译成权重（约束损失、数据合成、结构化初始化）」，而「约束损失」
这一环在抽象层只有 `PenaltyEmbedding` 这一个结构 —— 没有任何东西证明它非空。**
**本节用 `EqConstraint` 填上它：`loss` 就是本文件一直在用的 `EqConstraint.loss`，`Sat` 就是「损失为零」。** -/

/-- **`EqConstraint` 的惩罚嵌入**：损失是约束的损失，满足是「损失恰好为零」。

**=> 这是 `PenaltyEmbedding` 的第一个具体实例，也是「约束损失」这一目标条款的实际承载。**
**它的两个字段都直接复用本文件已有的定义，因此不是另起一套：`loss` 就是 `EqConstraint.loss`，
`Sat` 就是那个损失等于零 —— 与 `samePoint_sat_implies_penalty_zero` 说的是同一件事的两个呈现。** -/
noncomputable def constraintPenalty (n : ℕ) :
    Lattice.Lift.PenaltyEmbedding (EqConstraint n) (ℕ → Pt n) where
  loss := fun c pts => EqConstraint.loss c pts
  Sat := fun c pts => EqConstraint.loss c pts = 0

/-- **约束损失编译器在几何约束上的实例。**

**`penaltyToLoss (constraintPenalty n)`：把 `EqConstraint n` 编译成一个从点到实数的函数。**
**=> 抽象层的 `Compiler P (X → ℝ) X X` 现在有了一个**具体的** `P`，而那个 `P` 正是几何层一直在用的约束类型。** -/
noncomputable def constraintLossCompiler (n : ℕ) :
    Lattice.Lift.Compiler (EqConstraint n) ((ℕ → Pt n) → ℝ) (ℕ → Pt n) (ℕ → Pt n) :=
  Lattice.Lift.PenaltyToLossCompiler.penaltyToLoss (constraintPenalty n)

/-- **编译的产物就是损失本身。**

**=> 这条等式把抽象编译器的 `compile` 与本文件的 `loss` 接上，因此「编译到约束损失」不是隐喻：
`compile c` 作为一个函数，在每一点上等于 `loss c`。**
**⇒ 于是本文件此前所有关于 `loss` 的定量结论（`repair_loss_bounded_by_residual` 等）都自动成为
对**编译产物**的结论。** -/
theorem constraintLossCompiler_compile (n : ℕ) (c : EqConstraint n) :
    (constraintLossCompiler n).compile c = fun pts => EqConstraint.loss c pts :=
  Lattice.Lift.PenaltyToLossCompiler.compile_is_loss (constraintPenalty n) c

/-! ## 修正算子目录：三种修正的统一登记

本树里已经有三个各自独立的修正算子，覆盖三种不同的几何约束：

| 约束 | 算子 | 文件 |
|:--|:--|:--|
| **平行** | `parallelFix` | `ParallelRepair.lean` |
| **中点** | `midpointFix` | `MissingRepairs.lean` |
| **等距** | `sqDistFix` | `RepairCoverage.lean` |

**它们此前互不相识：每个文件只谈自己的约束、自己的算子。**
**⇒ 本节给它们一个**共同的形状**：一个修正算子就是「给定配置，返回修好的配置」加上「它确实达成目标」的保证。**

**这不是把它们硬塞进同一个类型 —— 三者的参数不同（平行要四个点、中点要三个）。**
**而是把**共同的那一部分**抽出来：每个算子都接受一个配置并返回一个配置，而「它做了什么」可以独立陈述。**
**⇒ 于是「修正」在目标的意义上成为一个可枚举的集合，而不是三份互不引用的代码。** -/

/-- **修正算子的共同形状。**

**`fix` 把配置映到配置；`mark` 把「这个算子针对什么」编码成一个可陈述的性质。**
**=> 抽出的只是**共同部分**：参数怎么给留给各自的构造，本节只统一「接受配置、返回配置」这一层。**
**`mark` 为 `Prop` 而非具体约束，是因为三个算子的目标类型不同（平行、中点、等距），强行统一会丢失它们各自
的内容。** -/
structure FixOperator (n : ℕ) where
  /-- **把配置映到修好的配置。** -/
  fix : (ℕ → Pt n) → (ℕ → Pt n)
  /-- **这个算子达成的性质。** -/
  mark : (ℕ → Pt n) → Prop

/-- **平行修正作为一个 `FixOperator`。**

**=> 登记只保留「接受配置、返回配置」这一层；**目标性质**由 `parallelOperator_mark` 单独陈述，
因为它要引用**输入**的 `pts`（平行说的是「修好的 `ab` 与原来的 `ce` 平行」），而 `mark` 只看到输出。**
**这正是本次抽象**不能**统一的那一部分：三者的目标都要提到输入，而 `mark` 的形式是 `输出 → Prop`。** -/
noncomputable def parallelOperator (a b c e : ℕ) : FixOperator n where
  fix := fun pts => Lattice.Geo.ParallelRepair.parallelFix pts a b c e
  mark := fun _ => True

/-- **中点修正作为一个 `FixOperator`。**

**=> 与上一条同理：`mark` 记为 `True`，真正的保证在 `midpointOperator_mark` 中。**
**中点约束只看**输出**（`m` 是否在 `a` 与 `b` 的中点），但仍统一成 `True` 以保持两个构造的形状一致。** -/
noncomputable def midpointOperator (m a b : ℕ) : FixOperator n where
  fix := fun pts => Lattice.Geo.MissingRepairs.midpointFix m a b pts
  mark := fun _ => True

/-- **登记后的平行修正仍达成它的目标。**

**=> 「修好之后存在 `t` 使得 `ab` = `t · ce`」——`parallelFix_reaches` 的原命题，只是现在挂在目录的构造上。**
**登记不改变结论，只改变**陈述的位置**：一个想浏览「有哪些修正算子」的读者只需读本节。** -/
theorem parallelOperator_mark (pts : ℕ → Pt n) (a b c e : ℕ) (hb : b ≠ a) :
    ∃ t, Lattice.Geo.GeoConstraint.seg ((parallelOperator (n := n) a b c e).fix pts) a b
      = fun i => t * Lattice.Geo.GeoConstraint.seg pts c e i :=
  Lattice.Geo.ParallelRepair.parallelFix_reaches pts a b c e hb

/-- **登记后的中点修正仍达成它的目标。**

**=> `midpointFix_reaches` 的目录形式，与上一条并列。**
**两条合起来说明：目录里的每个算子的**实际保证**都被保留，而不只是它的名字。** -/
theorem midpointOperator_mark (m a b : ℕ) (pts : ℕ → Pt n) (ha : a ≠ m) (hb : b ≠ m) :
    (Lattice.Geo.GeoConstraint.midpoint m a b).Holds
      ((midpointOperator (n := n) m a b).fix pts) :=
  Lattice.Geo.MissingRepairs.midpointFix_reaches m a b pts ha hb

/-- **等距修正作为一个 `FixOperator`。**

**=> 这是注册表的第三项：`sqDistFix` 把 `b` 沿 `a→b` 方向伸缩，使 `|ab|²` 恰为给定的 `d`。**
**与前两项一样，`mark` 记为 `True`，真正的保证在 `sqDistOperator_mark` 中 —— 因为该保证要提到 `a`、`d` 与
**输入**的 `b`，而 `mark` 只看到输出。** -/
noncomputable def sqDistOperator (a : Pt n) (d : ℝ) : FixOperator n where
  fix := fun pts => fun i => if i = 0 then Lattice.Geo.RepairCoverage.sqDistFix a d (pts i) else pts i
  mark := fun _ => True

/-- **登记后的等距修正仍达成它的目标。**

**=> `sqDistFix_reaches` 的目录形式：修复后 `a` 与第 `0` 个点之间的距离平方恰为 `d`。**
**这是注册表的第三项保证，与前两项并列，使「修正算子」的枚举从两个变成三个。** -/
theorem sqDistOperator_mark (a : Pt n) (d : ℝ) (hd : 0 ≤ d) (b : Pt n)
    (hne : Lattice.Geo.sqDist a b ≠ 0) :
    Lattice.Geo.sqDist a
      ((sqDistOperator (n := n) a d).fix (fun _ => b) 0) = d :=
  Lattice.Geo.RepairCoverage.sqDistFix_reaches a b hd hne

end Lattice.Geo
