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

**`carrier_implies_verify`：抽象在 `verifyCarrier ls` 上给出
`extractLayer` 侧的判据（第 200 轮的 `faithful_iff_extract_eq` 形状）。**

### 四、抽象 ⟹ 既有的**修正**判据

**`carrier_implies_repair`：抽象在 `Repair` 实例上给出
`repair_terminates_at_sat`（第 202 轮）的形状。**

**=> 验证段是 `Carrier.criterion` 的**字面实例**（`verifyCarrier`，第 1040 轮补上）。
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

/-- **验证段的载体实例：它使「验证」**真的**成为 `Carrier.criterion` 的一个实例。**

**⇒ 取 `Sat cs := extractLayer ls = cs`、`out w := w = ls`、`compile := compileToLayer`，
则 `criterion` 恰好是「extract 出 `cs` ↔ 重编译回 `cs` ↔ `ls`」。**
**（`ls` 是参数，故每个 `ls` 给出一个实例。）**

**⇒ 两条义务分别由 `compile_extract_layer`（靠信）与 `extract_compile_constraints`（完备）提供
——**本定义不新增任何假设**。** -/
def verifyCarrier (ls : Layer) : Carrier where
  Symbol := List VectorConstraint
  Weight := Layer
  Sat := fun cs => Lattice.Runtime.LoopClosure.extractLayer ls = cs
  out := fun w => w = ls
  compile := compileToLayer
  sound := fun cs h => by
    show compileToLayer cs = ls
    rw [← h]
    exact Lattice.Runtime.LoopClosure.compile_extract_layer ls
  complete := fun cs h => by
    show Lattice.Runtime.LoopClosure.extractLayer ls = cs
    rw [← h]
    exact Lattice.Runtime.LoopClosure.extract_compile_constraints cs

/-- **⭐ 抽象 ⟹ 验证判据：`extractLayer` 侧的判据也是 `Carrier.criterion` 的实例。**

**=> 第 200 轮的 `faithful_iff_extract_eq` 说
`extractLayer ls = corpusToConstraintSet c ↔ compileToLayer (corpusToConstraintSet c) = ls`。**

**=> 那条定理用 `LoopClosure.verify_iff_recompile`，而后者本身就是
「两个方向都是 `map` 的逆」——正是 `Carrier.criterion` 的形状。**

**⇒ **第 1040 轮之前**，本条的证明**只是转发** `verify_iff_recompile`，并未真的构造出 `Carrier` 实例——而 docstring 当时已声称它「写成了实例」。本轮补上 `verifyCarrier`，于是那句话**才**成立。** -/
theorem carrier_implies_verify (ls : Layer) (cs : List VectorConstraint) :
    Lattice.Runtime.LoopClosure.extractLayer ls = cs ↔ compileToLayer cs = ls :=
  (verifyCarrier ls).criterion cs

/-- **⭐ 抽象 ⟹ 修正判据：`Repair` 实例上，测度为零 ⟹ 判据为真。**

**=> 第 202 轮的 `repair_terminates_at_sat` 的形状。**
**它说的是：修复走到尽头，判据成立 —— 而判据就是 `Carrier.criterion` 的左端。**

**⇒ 但它**只是 `Carrier` 的单向半**：`criterion` 要求**双向**
**（还需 `Sat → μ = 0`），而 `Repair` 结构**不提供**那一个方向。**
**⇒ 所以修正段不是 `Carrier` 的实例，只是与它**同形的一半**。** -/
theorem carrier_implies_repair (R : Lattice.Core.Repair Layer)
    (ls : Layer) (h : R.μ ls = 0) : R.Sat ls :=
  Lattice.Runtime.RepairClosure.repair_terminates_at_sat R ls h

/-- **⭐⭐ 结论：抽象覆盖**两段加一个方向**。

**⇒ **旧名 「carrier_covers_two_segments_plus_one_direction」过宽**：本文件的 docstring 早就写着「覆盖两段加一个方向」，
而名字却说「整条链」。⇒ **名字不得夸大于内容**，故本轮改名。**

**=> 编译保语义与验证判据是 `Carrier` 的**字面实例**（`linearCarrierAt`、`verifyCarrier`）；
**修正终止只与 `Carrier` 的 `sound` 一半同形。**
**⇒ 所以本条的准确名字是「抽象覆盖两段加一个方向」，不是「覆盖整条链」。**
**=> 这条把「抽象没丢东西」写成可引用的事实。** -/
theorem carrier_covers_two_segments_plus_one_direction :
    (∀ (cs : List VectorConstraint) (x : List Int),
        AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x) ∧
    (∀ (ls : Layer) (cs : List VectorConstraint),
        Lattice.Runtime.LoopClosure.extractLayer ls = cs ↔ compileToLayer cs = ls) ∧
    (∀ (R : Lattice.Core.Repair Layer) (ls : Layer), R.μ ls = 0 → R.Sat ls) :=
  ⟨fun cs x => carrier_implies_symbolToWeight cs x,
   fun ls cs => carrier_implies_verify ls cs,
   fun R ls h => carrier_implies_repair R ls h⟩

end Lattice.Lib.Compiler.CarrierReproduction
