import Mathlib
import Lattice.Lib.Compiler.CarrierReversible
import Lattice.Runtime.LoopClosure
import Lattice.Runtime.SymbolToWeightCorrectness

/-!
# 具体实例：线性载体**确实**是 `ReversibleCarrier`（阶段 C，P6）

## 第 919 轮留下一个空洞

**`ReversibleCarrier` 定义了可逆载体与它的四条定理，但**没有任何具体实例**：**

**=> 实测：全库 `ReversibleCarrier where` 只出现在 `conj` 的定义里。
没有一处证明「线性载体是可逆载体」。**

**而第 906 轮我写 `linearCarrier` 时，**故意**让它 `Symbol := List VectorConstraint`
而不是「约束集 × 赋值」，因为后者会让 `extract` 无法表达。
那一刻我意识到可逆性需要一个**具体的载体**，但没有回头补。**

**=> 一个没有实例的抽象是无约束的：它说什么都对，因为无物受它约束。**
**本文件补上那个实例，于是第 919 轮的四条定理**真的**落在链上。**

## 为什么可逆性对线性载体成立

**第 899 轮已经证明：**

```lean
theorem compile_extract_layer      (ls) : compileToLayer (extractLayer ls) = ls
theorem extract_compile_constraints(cs) : extractLayer (compileToLayer cs) = cs
theorem compile_extract_bijective : LeftInverse extractLayer compileToLayer
                                  ∧ RightInverse extractLayer compileToLayer
```

**=> 这就是 `ReversibleCarrier` 需要的两条往返律，逐字对应。**

## 交付什么

| 定理 | 内容 |
|:--|:--|
| **`linearReversible`** | **⭐⭐ 线性载体是 `ReversibleCarrier`** |
| **`linear_verify_by_extract`** | **⭐⭐ 具体兑现：验证权重 = 提取后判** |
| **`linear_closure_inhabited`** | **⭐ 非空性：抽象**真的**有实例** |
| `linear_conj_with_itself` | **⭐ 组合后仍可逆** |

**=> 最后一条同时说明：抽象与具体**接得上**，那正是「推广不产生空谈」的判据。** -/

namespace Lattice.Lib.Compiler.CarrierInstantiation

open Lattice.Lib.Compiler.CarrierClosure
open Lattice.Lib.Compiler.CarrierReversible
open Lattice.Lib.Compiler.CarrierAlgebra
open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Runtime.LoopClosure

/-- **⭐⭐ 线性载体是 `ReversibleCarrier`。**

**=> 符号侧取 `List VectorConstraint`（约束集），权重侧取 `Layer`（层列表）。**
**`compile := compileToLayer`，`extract := extractLayer`。**
**两条往返律由第 899 轮的 `compile_extract_layer` 与 `extract_compile_constraints` 逐字提供。**

**=> 这不是新增证明：它把既有的双射性**放进抽象的槽位**。
但正是这个动作让第 919 轮的四条定理有了内容。** -/
def linearReversible (x : List Int) : ReversibleCarrier where
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
  extract := fun ls => extractLayer ls
  reinject := by
    intro ls
    exact compile_extract_layer ls
  reextract := by
    intro cs
    exact extract_compile_constraints cs

/-- **⭐⭐ 具体兑现：对线性载体，验证权重就是提取后判。**

**=> 第 919 轮的 `verify_by_extract` 是一条**抽象**定理；这里是它在**线性载体**上的实例。**

**=> 两者的差别是：抽象版说「若某载体可逆，则…」；
这里说「线性载体可逆，**所以**验证可以走提取」。** -/
theorem linear_verify_by_extract (x : List Int) (ls : Layer) :
    (linearReversible x).Sat ((linearReversible x).extract ls) ↔
      (linearReversible x).out ls :=
  ReversibleCarrier.verify_by_extract (linearReversible x) ls

/-- **⭐ 非空性：抽象**真的**有实例。**

**=> `∃ R : ReversibleCarrier, True` —— 看似平凡，但它排除了
「`ReversibleCarrier` 因为太强而**没有**任何实例」这种可能。** -/
theorem linear_closure_inhabited (x : List Int) :
    ∃ R : ReversibleCarrier, R.Symbol = List VectorConstraint :=
  ⟨linearReversible x, rfl⟩

/-- **⭐ 组合后仍可逆：线性载体与自己合取，仍是 `ReversibleCarrier`。**

**=> 由第 919 轮的 `ReversibleCarrier.conj` 与上面的实例合成。
于是「可逆载体在合取下封闭」也**有实例地**成立，而不只是抽象地。** -/
theorem linear_conj_with_itself (x : List Int)
    (p : List VectorConstraint × List VectorConstraint) :
    ((linearReversible x).conj (linearReversible x)).Sat p ↔
      ((linearReversible x).conj (linearReversible x)).out
        (((linearReversible x).conj (linearReversible x)).compile p) :=
  ReversibleCarrier.criterion ((linearReversible x).conj (linearReversible x)) p

end Lattice.Lib.Compiler.CarrierInstantiation
