import Lattice.Core.IR.Semantics
import Lattice.Lib.Editing.RealCompileExtractClosed

/-!
# **两个编译器的**同一条律**：编译后提取，回到原处**

## 为什么抽象层面上它们是同一件事

- `compileWith k f : IRWeights`，且 `extract (compileWith k f) = some k`；
- `compileToLayer cs : Layer`，且 `extractLayer (compileToLayer cs) = cs`，反向也成立。

**⇒ 两者都是**其提取器的左逆**。⇒ 这条律此前没有一条定理一起陈述。**

## 一个**真实的**技术困难（也是本文件只能写到这里的原因）

**⇒ `ConstraintSet` 与 `Layer` 在树里有**两套同名 `abbrev`**：`Lattice.{ConstraintSet,Layer}`
与 `Lattice.Lift.SymbolToWeightCorrectness.{ConstraintSet,Layer}`。**
**⇒ 它们底层**相同**（都是 `List VectorConstraint` / `List LinearLayer`），故定理**可以**写成；**
**⇒ 但同时 `open` 两个命名空间会使这两个名字**歧义**。**
**⇒ 故本文件**只用全限定名写法**，不 `open` 任何一侧——那本身就是一条可记录的结构事实。**
-/

namespace Lattice.Lib.Editing.CompileLaw

/-- **⭐⭐⭐ 两个编译器的同一条律。**

**⇒ 三个合取项：结构化初始化的编译被召回；层编译被召回；层提取被召回（即双向）。** -/
theorem compile_round_trip_law :
    (∀ (k : Lattice.Core.IR.IRSkeleton)
       (f : (s : Lattice.Core.IR.TensorShape) → Fin s.shape.prod → ℝ),
        Lattice.Core.IR.extract (Lattice.Core.IR.compileWith k f) = some k) ∧
    (∀ cs : Lattice.Lift.SymbolToWeightCorrectness.ConstraintSet,
        Lattice.extractLayer (Lattice.Lift.SymbolToWeightCorrectness.compileToLayer cs) = cs) ∧
    (∀ ls : Lattice.Lift.SymbolToWeightCorrectness.Layer,
        Lattice.Lift.SymbolToWeightCorrectness.compileToLayer (Lattice.extractLayer ls) = ls) :=
  ⟨fun k f => Lattice.Core.IR.extract_compileWith k f,
   fun cs => Lattice.extractLayer_compileToLayer cs,
   fun ls => Lattice.compileToLayer_extractLayer ls⟩

end Lattice.Lib.Editing.CompileLaw
