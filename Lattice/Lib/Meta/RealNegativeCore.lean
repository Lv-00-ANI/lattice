import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealSymbolToWeightNonlinear
import Lattice.Lib.Editing.RealSymbolToWeightWidened
import Lattice.Lib.Editing.RealReversibilityBoundary
/-!
# LATTICE: RealNegativeCore —— 不可回退否定定理的**契约形态护栏**

## 为什么需要它

D04 发现：五条「不可回退」的否定定理**「12 个文件引用，0 个文件 import」**
—— **删掉它无人编译失败**。也就是说「接线后必须仍可证」目前是**口头承诺**，
不是**编译期事实**。本文件把它变成编译期事实。

## 护栏的**唯一价值区间**（K04 实测定位，勿夸大）

* ⚠ **改语义**（如 `ZeroFixing := True`、`reluZ := n`）会被**上游自身证明**先抓到
  ⟹ 此时本护栏是**冗余**的；
* ✅ **改语句形态**（改名 / 改陈述形状 / 改 binders）库 `BUILD_EXIT=0` **完全无感**
  ⟹ **只有本护栏能抓**。

⇒ 本文件应定位为「**契约形态回归测试**」，**不是**「证明回归护栏」。

## 验证三步法（缺第 ② 步则**任何**护栏恒绿，K04 实测）

```
① 改上游 def
② lake build <上游模块>          # 刷 olean —— lake env lean 不重编 import 源
③ 跑本文件，必须失败
```

K04 的决定性实验（改名，库无感）：`dot_append_false → X` 后
库 `BUILD_EXIT=0`（成立 [5699/5699]）而本护栏 `GUARD_EXIT=1`。

## 结构

* **A. 上游 `def` 形态钉**（`rfl` 级）—— 护栏的**回滚面**
* **B. 否定定理陈述钉** —— 断言其**语句形态**未漂移
* **C. 公理审计尾** —— 必须**无 `sorryAx`**

来源：K04（sweep2），7 条公理审计全部无反 `sorryAx`（2 条零公理）。
-/

noncomputable section
open Lattice.Lib.Editing.RealReversibilityBoundary


open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## A. 上游 `def` 形态钉（回滚面） -/

example (a x : List Int) : dot a x = (a.zip x).foldl (fun s p => s + p.1 * p.2) 0 := rfl
example (act : Int → Int) : ZeroFixing act = (∀ y, act y = 0 ↔ y = 0) := rfl
example (n : Int) : reluZ n = max n 0 := rfl
example (c : VectorConstraint) (lam : Int) :
    scaleVec c lam = { a := c.a.map (fun t => t * lam), b := c.b * lam } := rfl
example (c : VectorConstraint) : convertVec c = ({ w := c.a, b := c.b } : LinearLayer) := rfl

/-! ## B. 否定定理陈述钉 -/

example : ¬ ZeroFixing reluZ := reluZ_not_zeroFixing

example : NonlinearLayerOut reluZ (convertVec cEx) [-5] = 0 ∧
    ¬ VectorConstraintSat cEx [-5] := reluZ_counterexample

example (act : Int → Int) :
    (∀ (cs : ConstraintSet) (x : List Int), AllSatisfied cs x ↔ actAllZero act cs x) ↔
      ZeroFixing act := activated_closure_iff_zeroFixing act

example (cs : ConstraintSet) (x : List Int) :
    (AllSatisfied (extractLayer (compileToLayer cs)) x ↔
        AllZeroOutputs (compileToLayer cs) x) ↔
      (AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) :=
  closed_loop_adds_nothing cs x

example : ¬ (∀ a1 a2 x1 x2 : List Int,
    dot (a1 ++ a2) (x1 ++ x2) = dot a1 x1 + dot a2 x2) := dot_append_false

example : scaleVec revC 2 ≠ revC := scaleVec_ne_self_two

example : ¬ (∃ extract : LinearLayer → VectorConstraint,
    (∀ c : VectorConstraint, extract (convertVec c) = c) ∧
    (extract (convertVec revC) = extract (convertVec (scaleVec revC 2)))) :=
  no_extractor_preserves_both

/-! ## C. 公理审计尾（必须无 `sorryAx`） -/

#print axioms reluZ_not_zeroFixing
#print axioms reluZ_counterexample
#print axioms activated_closure_iff_zeroFixing
#print axioms closed_loop_adds_nothing
#print axioms dot_append_false
#print axioms scaleVec_ne_self_two
#print axioms no_extractor_preserves_both

end Lattice
