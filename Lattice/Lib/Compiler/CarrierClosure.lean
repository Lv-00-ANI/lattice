import Mathlib
import Lattice.Runtime.SemanticFaithfulness
import Lattice.Lib.Compiler.ReluClosure
import Lattice.Lib.Compiler.Expressiveness
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# 载体无关的闭环：把线性和 relu 的判据**推广**成一个结构（阶段 C，P6）

## 为什么要这一轮

**第 899-905 轮为两个载体各写了一份闭环：**

| 载体 | 判据 | 位置 |
|:--|:--|:--|
| **线性 `VectorConstraint`** | **`VectorConstraintSat c x ↔ dot c.a x + c.b = 0`** | **`Runtime/`** |
| **relu** | **`ReluConstrSat a b x ↔ reluCompile a b x = 0`** | **`Lib/Compiler/`** |

**=> 两者**形状完全相同**：「符号约束成立 ⟺ 编译输出为零」。**

**这说明闭环**不是**某个载体的性质，而是「编译 ⇄ 验证」这个**结构**的性质。
本文件把这个结构提取出来，于是：**

1. **新增一个载体时，只需证明两条义务，不必重写整个闭环；**
2. **两个既有载体成为该结构的**实例**，因而共享同一组定理。**

## 本文件建的结构

```lean
structure Carrier where
  Symbol  : Type          -- 符号侧
  Weight  : Type          -- 权重侧
  Sat     : Symbol → Prop -- 符号侧的满足判定
  out     : Weight → Prop -- 权重侧的零化判定
  compile : Symbol → Weight
  -- 两条义务
  sound   : ∀ s, Sat s → out (compile s)
  complete: ∀ s, out (compile s) → Sat s
```

**=> 闭环 = `sound` + `complete`，即 `Sat s ↔ out (compile s)`。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| `Carrier.criterion` | **⭐ 判据：`Sat s ↔ out (compile s)`** |
| `Carrier.verify_sound` | **验证的可靠性：`out` 为真 ⟹ `Sat`** |
| `Carrier.repair_stable` | **修正的稳定性：已满足的不需要修正** |
| **`Carrier.closure`** | **⭐⭐ 闭环的合取形式** |
| **`linearCarrier` / `reluCarrier`** | **⭐⭐ 两个既有载体成为实例** |

**`linearCarrier` 与 `reluCarrier` 的 `sound`/`complete` 分别由
`symbolToWeight_correct` 与 `reluCompile_preserves` 提供 —— 因此本文件**不新增假设**，
它只是把已经证过的东西**归并**到一个名字下。** -/

namespace Lattice.Lib.Compiler.CarrierClosure

open Lattice
open Lattice.Lib.Compiler
open Lattice.Lift.SymbolToWeightCorrectness

/-- **载体结构：闭环所需的**最小**信息。**

**=> 只有六个字段，其中 `sound` 与 `complete` 是**义务**：
它们是「编译保语义」的两个方向。**
**=> 任何满足这两条义务的 `(Symbol, Weight, Sat, out, compile)` 都自带完整闭环。** -/
structure Carrier where
  /-- 符号侧的类型。 -/
  Symbol : Type
  /-- 权重侧的类型。 -/
  Weight : Type
  /-- 符号侧的满足判定。 -/
  Sat : Symbol → Prop
  /-- 权重侧的零化判定。 -/
  out : Weight → Prop
  /-- 符号编译成权重。 -/
  compile : Symbol → Weight
  /-- **义务一（可靠性）**：约束成立 ⟹ 编译输出为零。 -/
  sound : ∀ s : Symbol, Sat s → out (compile s)
  /-- **义务二（完备性）**：编译输出为零 ⟹ 约束成立。 -/
  complete : ∀ s : Symbol, out (compile s) → Sat s

namespace Carrier

variable (C : Carrier)

/-- **⭐ 判据：约束成立 ⟺ 编译输出为零。**

**=> 由 `sound` 与 `complete` 合成。这是**任何**载体上验证的形式。** -/
theorem criterion (s : C.Symbol) : C.Sat s ↔ C.out (C.compile s) :=
  ⟨C.sound s, C.complete s⟩

/-- **验证的可靠性：`out` 为真 ⟹ 约束成立。**

**=> 这是验证器报告「通过」时必须成立的论断。** -/
theorem verify_sound (w : C.Weight) (s : C.Symbol) (h : w = C.compile s)
    (hout : C.out w) : C.Sat s := by
  subst h
  exact (C.criterion s).mpr hout

/-- **修正的稳定性：已满足的约束编译后输出为零，因而无需修复。**

**=> 与线性侧的 `repair_preserves_verdict`、relu 侧的 `relu_repair_preserves_sat` 同义，
但这里对**所有**载体一次说完。** -/
theorem repair_stable (s : C.Symbol) (h : C.Sat s) : C.out (C.compile s) :=
  C.sound s h

/-- **⭐⭐ 闭环的合取形式：判据成立 **且** 已满足者稳定。**

**=> 这是载体层面「验证 + 修正」的最弱充分陈述。** -/
theorem closure (s : C.Symbol) :
    (C.Sat s ↔ C.out (C.compile s)) ∧ (C.Sat s → C.out (C.compile s)) :=
  ⟨C.criterion s, C.repair_stable s⟩

end Carrier

/-- **⭐⭐ 线性载体是 `Carrier` 的实例。**

**=> `sound`/`complete` 由既有的 `symbolToWeight_correct` 直接提供，
**不新增任何假设**。** -/
def linearCarrier : Carrier where
  Symbol := List VectorConstraint
  Weight := Layer
  Sat := fun cs => AllSatisfied cs ([] : List Int)
  out := fun ls => AllZeroOutputs ls ([] : List Int)
  compile := fun cs => compileToLayer cs
  sound := by
    intro cs h
    exact (symbolToWeight_correct cs ([] : List Int)).mp h
  complete := by
    intro cs h
    exact (symbolToWeight_correct cs ([] : List Int)).mpr h

/-- **⭐⭐ relu 载体是 `Carrier` 的实例。**

**=> `sound`/`complete` 由既有的 `reluCompile_preserves` 提供。** -/
def reluCarrier : Carrier where
  Symbol := ℝ × ℝ × ℝ
  Weight := ℝ
  Sat := fun p => ReluConstrSat p.1 p.2.1 p.2.2
  out := fun y => y = 0
  compile := fun p => reluCompile p.1 p.2.1 p.2.2
  sound := by
    intro p h
    exact (reluCompile_preserves p.1 p.2.1 p.2.2).mp h
  complete := by
    intro p h
    exact (reluCompile_preserves p.1 p.2.1 p.2.2).mpr h

/-- **两个载体上判据**同形**：它们都是 `Carrier.criterion` 的实例。**

**=> 这条把「载体无关」写成可引用的事实：线性与 relu 的验证判据来自**同一个**定理。** -/
theorem both_carriers_share_criterion :
    (∀ s, linearCarrier.Sat s ↔ linearCarrier.out (linearCarrier.compile s)) ∧
    (∀ s, reluCarrier.Sat s ↔ reluCarrier.out (reluCarrier.compile s)) :=
  ⟨fun s => Carrier.criterion linearCarrier s,
   fun s => Carrier.criterion reluCarrier s⟩

end Lattice.Lib.Compiler.CarrierClosure
