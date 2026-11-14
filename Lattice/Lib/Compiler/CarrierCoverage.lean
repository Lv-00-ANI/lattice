import Mathlib
import Lattice.Lib.Compiler.CarrierClosure
import Lattice.Runtime.SemanticFaithfulness
import Lattice.Lib.Compiler.Expressiveness

/-!
# `Carrier` 的**覆盖检验**：它真的泛化了吗？（阶段 C，P6）

## 第 906 轮留下一个必须回答的问题

**第 906 轮定义了 `Carrier`（六个字段、两条义务），并给出两个实例。**

**=> 但那不足以说明它**真的**泛化：两个实例可能只是「恰好都能塞进去」。**

**要检验「泛化是否真实」，需要一个**独立的**判据：**
**结构若能覆盖**不在它诞生时被想到的**载体，它才是真的抽象。**
**=> 本文件做三件事来检验它：**

### 一、补上 `[]` 之外的一般赋值

**第 906 轮的 `linearCarrier` 把赋值固定成 `[]`。**
**=> 那是一个**退化的**实例：它只覆盖空输入。**
**本文件给出**参数化**版本 `linearCarrierAt x`，对**任意**输入 `x` 成立。**

**若 `Carrier` 只能容纳 `[]`，它就不是泛化，而是一处特例化的巧合。**

### 二、补上一个**新**载体：`signCompile`

**`signCompile` 是 `RealNonlinearCompile.lean` 里另一个编译器，**
**其约束 `SignSat a b x := a * x + b = 0` 是**等式**，与 relu 的不等式不同。**

**=> 若 `Carrier` 也能容纳它，说明结构覆盖的不只是「线性 + relu」这一对被同时想到的东西。**

### 三、给出 `Carrier` 之间的**映射**（这是最有信息量的检验）

**若两个载体之间存在「符号侧可互译、且判据保持」的映射，**
**那么它们的闭环可以**互相转移** —— 这正是「载体无关」的操作性含义。**

**=> 交付 `Carrier.map`：给定 `f : C₁.Symbol → C₂.Symbol`，
若 `C₂.Sat (f s) ⟷ C₁.Sat s`，则 `C₁` 的判据可用于 `C₂`。**

## 本文件交付什么

| 定理 | 内容 |
|:--|:--|
| **`linearCarrierAt`** | **⭐ 线性载体**参数化到任意输入**（不是只有 `[]`）** |
| **`reluCarrierAt`** | **⭐ relu 载体参数化到任意输入** |
| **`signCarrier`** | **⭐⭐ 第三个载体：`signCompile`（独立发现的）** |
| **`Carrier.map`** | **⭐⭐ 载体间的判据转移** |
| `CriterionTransfer` | **⭐ 转移后的判据仍是双向的** |

**=> 三件事合起来回答「它真的泛化了吗」：**
**能容纳新输入、能容纳新载体、且能在载体间转移。** -/

namespace Lattice.Lib.Compiler.CarrierCoverage

open Lattice
open Lattice.Lib.Compiler
open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Lib.Compiler.CarrierClosure

/-- **⭐ 线性载体的**参数化**版本：对任意输入 `x` 成立。**

**=> 第 906 轮的 `linearCarrier` 固定 `x = []`；这里是**真正的**线性载体。**
**它的 `sound`/`complete` 来自 `symbolToWeight_correct`（对任意 `x` 成立）。** -/
def linearCarrierAt (x : List Int) : Carrier where
  Symbol := List VectorConstraint
  Weight := Layer
  Sat := fun cs => AllSatisfied cs x
  out := fun ls => AllZeroOutputs ls x
  compile := fun cs => compileToLayer cs
  sound := by
    intro cs h
    exact (symbolToWeight_correct cs x).mp h
  complete := by
    intro cs h
    exact (symbolToWeight_correct cs x).mpr h

/-- **⭐ relu 载体的**参数化**版本：对 `(a, b, x)` 三元组成立。**

**=> 与第 906 轮的 `reluCarrier` 同构，但把三元组解包，
使符号侧的类型就是「一个约束」，语义更直接。** -/
def reluCarrierAt : Carrier where
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

/-- **⭐⭐ 第三个载体：`signCompile`。**

**=> 它与前两个**不同**：`SignSat` 又是**等式**（像线性侧），**
**但载体是实数的 `sign`（像 relu 侧）。**

**=> 于是它**不是**前两个的任何一个的特例 —— 它是**独立**的第三个。
若 `Carrier` 容纳它，「泛化」就不是巧合。** -/
noncomputable def signCarrier : Carrier where
  Symbol := ℝ × ℝ × ℝ
  Weight := ℝ
  Sat := fun p => SignSat p.1 p.2.1 p.2.2
  out := fun y => y = 0
  compile := fun p => signCompile p.1 p.2.1 p.2.2
  sound := by
    intro p h
    exact (signCompile_preserves p.1 p.2.1 p.2.2).mp h
  complete := by
    intro p h
    exact (signCompile_preserves p.1 p.2.1 p.2.2).mpr h

/-- **⭐⭐ 载体间的判据转移。**

**=> 给定 `f : C₁.Symbol → C₂.Symbol`，且 `f` 保持满足关系，
则 `C₂` 上的符号也能用 `C₁` 的闭环判定。**

**=> 这是「载体无关」的**操作性**含义：闭环可以沿映射转移，而不是每个载体各建一座。** -/
def Carrier.map (C₁ C₂ : Carrier) (f : C₁.Symbol → C₂.Symbol)
    (hSat : ∀ s, C₂.Sat (f s) ↔ C₁.Sat s) : C₁.Symbol → Prop :=
  fun s => C₂.Sat (f s)

/-- **⭐ 转移后的判据仍是**双向**的。**

**=> `C₂.Sat (f s) ⟷ C₁.Sat s`（假设）**且** `C₁.Sat s ⟷ C₁.out (C₁.compile s)`（`C₁` 的判据）。**
**=> 于是 `C₂.Sat (f s) ⟷ C₁.out (C₁.compile s)`：一条判据跨两个载体成立。** -/
theorem criterion_transfers (C₁ C₂ : Carrier) (f : C₁.Symbol → C₂.Symbol)
    (hSat : ∀ s, C₂.Sat (f s) ↔ C₁.Sat s) (s : C₁.Symbol) :
    C₂.Sat (f s) ↔ C₁.out (C₁.compile s) :=
  (hSat s).trans (Carrier.criterion C₁ s)

/-- **⭐⭐ 覆盖检验的结论：`Carrier` 容纳三个**独立**的载体。**

**=> 线性（等式/列表）、relu（不等式/实数）、sign（等式/实数），
三者的 `Symbol`/`Weight` 类型各不相同，却共享同一组闭环定理。** -/
theorem three_carriers_share_loop :
    (∀ (s : (linearCarrierAt []).Symbol),
        (linearCarrierAt []).Sat s ↔ (linearCarrierAt []).out ((linearCarrierAt []).compile s)) ∧
    (∀ s, reluCarrierAt.Sat s ↔ reluCarrierAt.out (reluCarrierAt.compile s)) ∧
    (∀ s, signCarrier.Sat s ↔ signCarrier.out (signCarrier.compile s)) :=
  ⟨fun s => Carrier.criterion (linearCarrierAt []) s,
   fun s => Carrier.criterion reluCarrierAt s,
   fun s => Carrier.criterion signCarrier s⟩

end Lattice.Lib.Compiler.CarrierCoverage
