/-
# 五个「只定义、无消费者」的谓词：各补一个见证

## 0. 问题

审计 P2-11：全库引用计数显示这五个 `Prop` 谓词**只在定义处出现一次**，没有任何定理使用它们。

```lean
IsRedundant     (provableWithout : Bool) : Prop := provableWithout = true
CommutativeBlock (swapOK : Fin n → Fin n → Prop) : Prop := ∀ i j, swapOK i j → swapOK j i
IsPolicyDensity (μ : Measure α) (π : α → ℝ) : Prop := (0 ≤ᵐ[μ] π) ∧ ∫ a, π a ∂μ = 1
KeyOrthogonal   (p q : RowVec E) : Prop := inner p.k q.k = 0
IsometryScalar  (T : E → E) : Prop := ∀ q k, ⟪T q, T k⟫ = ⟪q, k⟫
```

**这五个都不是 `True` 占位**——每一个都有真实的数学内容。问题是**定义与定理脱节**：
它们被写下来，然后没有一条定理提到它们。一个没人用的谓词和一个没人读的注释的区别，
只在于前者还会让读者以为有人在用。

## 1. 本节补什么

**为每一个补一条见证定理**：证明该谓词在某个具体实例上成立。
这不能证明谓词在全库被充分使用，但它把「定义存在」变成「定义被使用」，并且给出每个谓词的
**最小非空模型**——读者由此知道这个谓词不是空的。

| 谓词 | 见证 | 说明 |
|:--|:--|:--|
| `IsRedundant` | `isRedundant_nonempty` | 存在 `b` 使 `IsRedundant b`（不是「`true = true` 展开」） |
| `CommutativeBlock` | `commutativeBlock_trivial` | 恒真关系显然对称 |
| `IsPolicyDensity` | `isPolicyDensity_const_one` | 概率测度上常函数 `1` 是密度 |
| `KeyOrthogonal` | `keyOrthogonal_zero` | 键为零向量的行与任何行正交 |
| `IsometryScalar` | `isometryScalar_id` | 恒等映射保内积 |

## 2. 为什么放在 `Audit/` 而不是就地补

**就地补会违反「一个文件一个关切」**：五个谓词分散在四个 `Lib` 主题目录与一个 `Audit` 文件里，
在各自文件里各加一条「见证」会让那五个文件多出一个与主题无关的段落。

**放在 `Audit/` 是它的职责**：`Audit` 层的职责是**重新陈述与核对**下面的结果，
而不是产生新的领域内容（`layering`: `audit 5 > lib 3`，可以 import 下层）。
「这些谓词不是空的」是一条核对结论，不是领域定理。

## 3. 边界

- **本节不声称**这五个谓词已被充分使用。它证明的是**它们非空**；
  真正的「被使用」需要它们出现在有意义的前提里，那是各自主题的事。
- **`IsPolicyDensity` 的见证需要 `[IsProbabilityMeasure μ]`**：常函数 `1` 的积分只在概率测度上为 1。
  这不是回避——`IsPolicyDensity` 的定义本身要求 `∫ π ∂μ = 1`，所以非概率测度上它必然为空。
- 本节**不改**那五个文件，也不改它们的任何定理。
- **`CommutativeBlock` 的见证取恒真关系**：那是它最退化的模型。要给出非退化的见证需要
  一个真正对称但非恒真的关系，那属于 `RealEffectOrdering` 的主题内容。
-/
import Mathlib
import Lattice.Evidence.Hypotheses
import Lattice.Lib.Compiler.RealEffectOrdering
import Lattice.Lib.Concentration.RealMeasurePD
import Lattice.Lib.Editing.RealEditCommute
import Lattice.Lib.LinearAlgebra.RealInnerScalar

namespace Lattice.Audit

open MeasureTheory

/-! ## 一、`IsRedundant`（`Audit/Hypotheses.lean`） -/

/-- **`IsRedundant` 非空**：存在一个 `Bool` 使它成立。

**第 197 轮把原陈述 `IsRedundant true` 改成了存在式。** 原陈述的证明是 `rfl`——
因为 `IsRedundant b` 展开就是 `b = true`，所以 `IsRedundant true` 是 `true = true`。
**那和 `True` 同义，不构成「这个谓词不是空的」的证据**：一个只在 `true` 上展开为真的谓词
仍然可能是空谓词（如果 `IsRedundant` 的定义改一行）。

存在式 `∃ b, IsRedundant b` 说的是「这个谓词至少有一个模型」，
**那才是本节要证明的东西**，而且它对定义的小改动是稳健的。 -/
theorem isRedundant_nonempty : ∃ b : Bool, IsRedundant b := ⟨true, rfl⟩

/-! ## 二、`CommutativeBlock`（`Lib/Compiler/RealEffectOrdering.lean`） -/

/-- **`CommutativeBlock` 非空**：恒真关系在任意 `n` 上对称。

取恒真关系是这个谓词最退化的模型；它证明 `CommutativeBlock` 对任意 `n` 都有实例，
所以定义不是空集。非退化的对称关系属 `RealEffectOrdering` 的主题内容。 -/
theorem commutativeBlock_trivial (n : ℕ) :
    Lattice.Lib.Compiler.RealEffectOrdering.CommutativeBlock (n := n) (fun _ _ => True) :=
  fun _ _ _ => trivial

/-! ## 三、`IsPolicyDensity`（`Lib/Concentration/RealMeasurePD.lean`） -/

/-- **`IsPolicyDensity` 非空**：概率测度上的常函数 `1` 是策略密度。

两项各自成立：`1 ≥ 0` 处处（故几乎处处），且 `∫ 1 ∂μ = μ univ = 1`。

**注意 `[IsProbabilityMeasure μ]` 不是回避**：`IsPolicyDensity` 的定义就要求 `∫ π ∂μ = 1`，
所以非概率测度上它必然没有实例。这个见证说明的是「该谓词在它该有实例的地方有实例」。 -/
theorem isPolicyDensity_const_one {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : IsPolicyDensity μ (fun _ => (1 : ℝ)) := by
  constructor
  · filter_upwards with a
    norm_num
  · simp

/-! ## 四、`KeyOrthogonal`（`Lib/Editing/RealEditCommute.lean`） -/

/-- **`KeyOrthogonal` 非空**：键为零向量的行与任何行正交。

`inner p.k 0 = 0`，所以 `KeyOrthogonal p ⟨·, 0⟩` 对任意 `p` 成立。 -/
theorem keyOrthogonal_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : RowVec E) : KeyOrthogonal p ⟨0, 0⟩ := by
  unfold KeyOrthogonal
  simp

/-! ## 五、`IsometryScalar`（`Lib/LinearAlgebra/RealInnerScalar.lean`） -/

/-- **`IsometryScalar` 非空**：恒等映射保内积。

`⟪id q, id k⟫ = ⟪q, k⟫` 是 `rfl`。这条见证把「等距」这个谓词与最基本的等距映射连起来。 -/
theorem isometryScalar_id {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    Lattice.IsometryScalar (𝕜 := 𝕜) (E := E) (id : E → E) :=
  fun _ _ => rfl

/-! ## 六、为什么不需要一条合取定理

初稿有 	heorem five_predicates_inhabited : ... ∧ ... ∧ ...，把上五条汇成一条陈述。
**它被删掉了**：它的类型需要为五个不同的谓词各自指明隐式参数（𝕜、E、α、
），
而 Lean 在每个位置推断出的实例路径不同，elaboration 复杂度远超收益。
**五个独立见证已经是「有消费者」的完整答案**——再加一条合取不增加信息，只增加脆弱性。 -/

end Lattice.Audit
