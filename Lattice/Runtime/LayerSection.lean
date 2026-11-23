import Lattice.Core.PartialSection
import Lattice.Runtime.LoopClosure

/-!
# **层那一跳是同构：同一个抽象，`Option` 不出现的原因**

## 与权重那一跳的对照

| 载体 | 正向 | 逆向 | 形态 |
|:--|:--|:--|:--|
| `IRSkeleton ⇄ IRWeights` | `compileSkel`（全） | `extract`（**部分**） | `PartialSection` |
| **`ConstraintSet ⇄ Layer`** | `compileToLayer`（全） | `extractLayer`（**全**） | **`BiSection`** |

**⇒ 两个方向在层那一跳上**都有往返**：**
`extractLayer (compileToLayer cs) = cs`（`extract_compile_constraints`）
`compileToLayer (extractLayer ls) = ls`（`compile_extract_layer`）

**⇒ 于是「为什么权重那一跳要 `Option`、层那一跳不要」不再是两套代码的偶然差别：
`Core/PartialSection.lean` 的 `isIso_iff_image_total` 说**`Option` 消失 ⟺ 每个权重都在像中**。
层那一跳满足「每个层都在像中」（`layer_image_total`），故它是同构；
权重那一跳不满足（`extract_not_injective`），故它只能是部分截面。**
-/

namespace Lattice.Runtime.LayerSection

open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Runtime.LoopClosure

/-- **层那一跳是同构。**

**⇒ `left` 是 `extract_compile_constraints`（先编译再提取，回到原约束集），
`right` 是 `compile_extract_layer`（先提取再编译，回到原层）。
**两条都是主树已有的定理，本结构的作用是把它们**放在一起**，使「双向互逆」成为一个可引用的对象，
而不是两条需要读者自己配对的事实。** -/
def layerBiSection : Lattice.Core.BiSection ConstraintSet Layer where
  compile := compileToLayer
  extract := extractLayer
  left := extract_compile_constraints
  right := compile_extract_layer

/-- **每个层都在 `compileToLayer` 的像中。**

**⇒ 直接由 `right` 得出：`ls = compileToLayer (extractLayer ls)`。**
**⇒ 这一条与 `isIso_iff_image_total` 合起来，就是层那一跳是 `BiSection` 的**判据侧**证明。** -/
theorem layer_image_total (ls : Layer) : ls ∈ Set.range compileToLayer :=
  ⟨extractLayer ls, compile_extract_layer ls⟩

/-- **层的 `PartialSection` 与权重那一跳同类型，但它的 `extract` 从不失败。**

**⇒ 由 `BiSection.toPartialSection` 得到；两个合取项分别说：
它与权重那一跳属于**同一个抽象**，而它的 `Option` **永远是 `some`**。
**⇒ 这正是两跳差别的最小陈述：同类型，不同性质。** -/
theorem layer_partial_section_never_fails :
    (∀ cs : ConstraintSet, layerBiSection.toPartialSection.extract (compileToLayer cs)
        = some cs)
      ∧ (∀ w : Layer, (layerBiSection.toPartialSection.extract w).isSome) :=
  ⟨fun cs => layerBiSection.toPartialSection.retract cs,
   fun w => layerBiSection.extract_isSome w⟩

end Lattice.Runtime.LayerSection