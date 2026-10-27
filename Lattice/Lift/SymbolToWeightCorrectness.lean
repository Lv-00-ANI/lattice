import Mathlib
import Lattice.Lift.ConvertVectorLinear
/-!
# LATTICE: SymbolToWeightCorrectness（最小版本）—— 约束集合 → 单层网络

doc/02 §4.3 中 `SymbolToWeightCorrectness` 的最小实例：
符号程序 = 有限个向量约束的集合；权重 = 单层线性网络（每约束一个神经元）。
编译 = 逐个 convertVec（约束系数拷贝为神经元权重）。

定理：编译保语义——
  全部约束满足  ⟺  网络对同一输入的所有神经元输出为零。

这建立了"符号程序 → 权重网络"保语义的**组合式证明骨架**：
列表级全称量词 + 每个元素用 ConvertVectorLinear.convertVec_preserves_semantics。

注意 **订正 B400**：此处原写「纯 Std（无 mathlib）」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的符号程序与权重网络的表示只用到 `List`/`Int` 等核心类型**
（`ConstraintSet`、`Layer` 皆为 `List` 的别名，字段都是 `Int`，不依赖 mathlib 的专用结构），
但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertVectorLinear 的文件头「订正 B400」。**以本段为准。**
-/


namespace Lattice.Lift.SymbolToWeightCorrectness
/-! ## 符号程序：约束集合 -/

abbrev ConstraintSet := List VectorConstraint

/-! ## 权重网络：单层线性网络（每约束一个神经元） -/

abbrev Layer := List LinearLayer

/-! ## 编译：逐约束转换为神经元 -/

def compileToLayer (cs : ConstraintSet) : Layer :=
  cs.map convertVec

/-! ## 语义：全部约束满足 -/

def AllSatisfied (cs : ConstraintSet) (x : List Int) : Prop :=
  ∀ c ∈ cs, VectorConstraintSat c x

/-! ## 权重行为：所有神经元输出为零 -/

def AllZeroOutputs (ls : Layer) (x : List Int) : Prop :=
  ∀ l ∈ ls, LayerOut l x = 0

/-! ## 引理：列表映射上的全称量词等价
(∀ c ∈ cs, P c) ↔ (∀ l ∈ cs.map f, Q l)，当 P c ↔ Q (f c) 时。
逐元素桥接。-/

lemma forall_mem_map_iff {α β : Type} (f : α → β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ a, P a ↔ Q (f a)) (xs : List α) :
    (∀ a ∈ xs, P a) ↔ (∀ b ∈ xs.map f, Q b) := by
  constructor
  · intro hp b hb
    rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
    exact (h a).mp (hp a ha)
  · intro hq a ha
    exact (h a).mpr (hq (f a) (List.mem_map.mpr ⟨a, ha, rfl⟩))

/-! ## 定理：SymbolToWeightCorrectness（最小版本）

编译保语义：全部约束满足 ⟺ 网络所有输出为零。

⚠ **这条定理的强度上限由 `convertVec_preserves_semantics` 决定，而那条有两处弱点**
（第 195 轮补，此前本节没有说明）：

1. **结构上它是真的**：本定理是 `convertVec_preserves_semantics` 经 `forall_mem_map_iff`
   对 `List` 的逐点提升，不是重言——`compileToLayer` 真的遍历了约束表。
2. **但内容上它不超出它提升的那条**：那条是定义展开（`convertVec` 只是拷贝系数与偏置），
   且两侧共享 `dot` 的 `List.zip` 截断，**对元数错误零诊断力**。

所以「编译保语义」在本库里**只保证**：「约束表逐条满足」与「编译出的层逐条输出零」同真同假。
它**不保证**这些式子彼此之间有意义对应（那是下标化载体 `VecConstraint`/`vecDot` 的事），
也**不保证**元数不足的输入会被拒绝（那是被证明的盲区，见 `symbolToWeight_correct_blind_to_arity`）。 -/

theorem symbolToWeight_correct (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x := by
  unfold AllSatisfied AllZeroOutputs compileToLayer
  exact forall_mem_map_iff convertVec (fun c => VectorConstraintSat c x)
    (fun l => LayerOut l x = 0)
    (fun c => convertVec_preserves_semantics c x) cs

/-- **N · 「编译保语义」看不见元数错误**：存在约束表与输入，使
`AllSatisfied` 与 `AllZeroOutputs` **同时**成立，而输入元数不足。

`cs = [{a := [3,5], b := 0}]` 配 `x = []`。编译出的层走同一个截断 `dot`，输出也是零，
所以等价成立——**但那个 `x` 根本不是这个约束的合法赋值**。

**这是 `symbolToWeight_correct` 的真实强度上限**：两侧共享同一个截断，
等价关系两边一起错，因此它对这类错误**永远**抓不到。
同一反例的 Lib 层版本见 `Lib/Editing/RealSymbolToWeightWidened.sat_ragged_false_positive`。 -/
theorem symbolToWeight_correct_blind_to_arity :
    ∃ (cs : ConstraintSet) (x : List Int),
      (∃ c ∈ cs, x.length < c.a.length) ∧
        AllSatisfied cs x ∧ AllZeroOutputs (compileToLayer cs) x := by
  refine ⟨[{ a := [3, 5], b := 0 }], [], ⟨{ a := [3, 5], b := 0 }, by simp, by decide⟩, ?_, ?_⟩
  · intro c hc
    have h1 : c = { a := [3, 5], b := 0 } := by simpa using hc
    rw [h1]
    unfold VectorConstraintSat
    decide
  · intro l hl
    rcases List.mem_map.mp hl with ⟨c, hc, rfl⟩
    have h1 : c = { a := [3, 5], b := 0 } := by simpa using hc
    rw [h1]
    unfold LayerOut convertVec
    decide

/-! ## 推论：验证器判定
网络输出全零 ⟹ 全部约束满足（可直接用于验证器）。-/

theorem symbolToWeight_verify (cs : ConstraintSet) (x : List Int)
    (h : AllZeroOutputs (compileToLayer cs) x) : AllSatisfied cs x :=
  (symbolToWeight_correct cs x).mpr h

/-! ## 推论：空程序与空网络
空符号程序（无约束）编译为空网络，语义平凡成立（恒真）。-/

theorem symbolToWeight_empty (x : List Int) :
    AllSatisfied [] x ∧ AllZeroOutputs (compileToLayer []) x := by
  constructor <;> simp [AllSatisfied, AllZeroOutputs, compileToLayer]

end Lattice.Lift.SymbolToWeightCorrectness
