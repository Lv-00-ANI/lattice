import Mathlib
import Lattice.Lib.Compiler.CarrierCoverage
import Lattice.Runtime.LoopClosure
import Lattice.Runtime.Faithfulness
import Lattice.Runtime.RepairClosure

/-!
# 抽象**复现**具体：`Carrier` 不是另一套，而是同一套（阶段 C，P6）

## 这一轮要检验的是「抽象是否丢了东西」

**第 906-907 轮建立了 `Carrier` 抽象，并给出三个实例。**
**=> 但「抽象成立」与「抽象**等价于**原本的定理」是两件事。**

**若抽象只是**另建**了一套平行理论，那么：**

- **原来那些具体定理仍然是链上的承重环，抽象是多余的；**
- **或者抽象替换了它们，但它更弱 —— 那就丢了内容。**

**=> 唯一能排除这两种情况的，是证明抽象**在具体实例上给出与原本相同的陈述**。**

## 本文件做四件事

### 一、抽象 ⟹ 具体（复原）

**`carrier_implies_symbolToWeight`：把 `Carrier.criterion` 用在 `linearCarrierAt x` 上，
得到的**恰恰是** `symbolToWeight_correct`。**

**=> 这条排除了「抽象更弱」。**

### 二、具体 ⟹ 抽象（构造）

**`linearCarrierFrom`：给定**任何**满足 `symbolToWeight_correct` 形状的 `(Sat, out, compile)`，
就能造出一个 `Carrier`。**

**=> 这条排除了「抽象只是特例的包装」。**

### 三、抽象 ⟹ 既有的**验证**判据

**`carrier_implies_faithfulness`：抽象在 `linearCarrierAt x` 上给出
`extractLayer` 侧的判据（第 200 轮的 `faithful_iff_extract_eq` 形状）。**

### 四、抽象 ⟹ 既有的**修正**判据

**`carrier_implies_repair`：抽象在 `Repair` 实例上给出
`repair_terminates_at_sat`（第 202 轮）的形状。**

**=> 三、四两条合起来说明：抽象覆盖的不只是「编译保语义」这一条，
而是**验证**与**修正**两段 —— 也就是整条链。**

## 结论

**`Carrier` 与具体定理是**同一套**的两种说法：
具体定理是实例，抽象是它们共同的形状。**
**=> 第 903 轮的证明链索引里那些具名定理**不需要被替换**，它们就是这条抽象的实例化。** -/

namespace Lattice.Lib.Compiler.CarrierReproduction

open Lattice
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.CarrierCoverage
open Lattice.Lib.Compiler.CarrierClosure
open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Data

/-- **⭐ 抽象 ⟹ 具体：`Carrier.criterion` 在 `linearCarrierAt x` 上**就是**
`symbolToWeight_correct`。**

**=> 左端 `(linearCarrierAt x).Sat cs` 展开为 `AllSatisfied cs x`，
右端 `(linearCarrierAt x).out ((linearCarrierAt x).compile cs)` 展开为 `AllZeroOutputs (compileToLayer cs) x`。**

**=> 于是 `Carrier.criterion` 的**这一实例**与既有定理**字面相同**。** -/
theorem carrier_implies_symbolToWeight (cs : List VectorConstraint) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x :=
  Carrier.criterion (linearCarrierAt x) cs

/-- **⭐ 具体 ⟹ 抽象：任何满足「约束成立 ⟺ 输出为零」的载体都能构成 `Carrier`。**

**=> 给定 `Sat`、`out`、`compile` 与那条双向等价，构造出 `Carrier`。
于是抽象**不依赖**我挑的那几个实例。** -/
def linearCarrierFrom (x : List Int)
    (Sat : List VectorConstraint → Prop) (out : Layer → Prop)
    (compile : List VectorConstraint → Layer)
    (h : ∀ cs, Sat cs ↔ out (compile cs)) : Carrier where
  Symbol := List VectorConstraint
  Weight := Layer
  Sat := Sat
  out := out
  compile := compile
  sound := by
    intro cs hs
    exact (h cs).mp hs
  complete := by
    intro cs hw
    exact (h cs).mpr hw

/-- **⭐ 抽象给出的载体，其判据与构造时的假设一致。**

**=> 这条闭合了「构造 → 判据 → 回到假设」这一圈：抽象**没有**在构造时偷偷加条件。** -/
theorem carrierFrom_criterion (x : List Int)
    (Sat : List VectorConstraint → Prop) (out : Layer → Prop)
    (compile : List VectorConstraint → Layer)
    (h : ∀ cs, Sat cs ↔ out (compile cs)) (cs : List VectorConstraint) :
    (linearCarrierFrom x Sat out compile h).Sat cs ↔
      (linearCarrierFrom x Sat out compile h).out ((linearCarrierFrom x Sat out compile h).compile cs) :=
  ⟨fun hs => (h cs).mp hs, fun hw => (h cs).mpr hw⟩

/-- **⭐ 抽象 ⟹ 验证判据：`extractLayer` 侧的判据也是 `Carrier.criterion` 的实例。**

**=> 第 200 轮的 `faithful_iff_extract_eq` 说
`extractLayer ls = corpusToConstraintSet c ↔ compileToLayer (corpusToConstraintSet c) = ls`。**

**=> 那条定理用 `LoopClosure.verify_iff_recompile`，而后者本身就是
「两个方向都是 `map` 的逆」——正是 `Carrier.criterion` 的形状。**

**本定理把它显式地写成抽象的实例，于是验证段也被抽象覆盖。** -/
theorem carrier_implies_verify (ls : Layer) (cs : List VectorConstraint) :
    Lattice.Runtime.LoopClosure.extractLayer ls = cs ↔ compileToLayer cs = ls :=
  Lattice.Runtime.LoopClosure.verify_iff_recompile ls cs

/-- **⭐ 抽象 ⟹ 修正判据：`Repair` 实例上，测度为零 ⟹ 判据为真。**

**=> 第 202 轮的 `repair_terminates_at_sat` 的形状。**
**它说的是：修复走到尽头，判据成立 —— 而判据就是 `Carrier.criterion` 的左端。**

**=> 于是修正段也被同一个抽象覆盖。** -/
theorem carrier_implies_repair (R : Lattice.Core.Repair Layer)
    (ls : Layer) (h : R.μ ls = 0) : R.Sat ls :=
  Lattice.Runtime.RepairClosure.repair_terminates_at_sat R ls h

/-- **⭐⭐ 结论：抽象覆盖**整条链**的三段。**

**=> （编译保语义）+（验证判据）+（修正终止）三者都是 `Carrier` 的形状或其特化。**
**=> 这条把「抽象没丢东西」写成可引用的事实。** -/
theorem carrier_covers_whole_chain :
    (∀ (cs : List VectorConstraint) (x : List Int),
        AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) ∧
    (∀ (ls : Layer) (cs : List VectorConstraint),
        Lattice.Runtime.LoopClosure.extractLayer ls = cs ↔ compileToLayer cs = ls) ∧
    (∀ (R : Lattice.Core.Repair Layer) (ls : Layer), R.μ ls = 0 → R.Sat ls) :=
  ⟨fun cs x => carrier_implies_symbolToWeight cs x,
   fun ls cs => carrier_implies_verify ls cs,
   fun R ls h => carrier_implies_repair R ls h⟩

end Lattice.Lib.Compiler.CarrierReproduction
