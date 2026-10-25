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
编译保语义：全部约束满足 ⟺ 网络所有输出为零。-/

theorem symbolToWeight_correct (cs : ConstraintSet) (x : List Int) :
    AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x := by
  unfold AllSatisfied AllZeroOutputs compileToLayer
  exact forall_mem_map_iff convertVec (fun c => VectorConstraintSat c x)
    (fun l => LayerOut l x = 0)
    (fun c => convertVec_preserves_semantics c x) cs

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
