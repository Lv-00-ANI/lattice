import Mathlib
import Lattice.Runtime.ComboN
/-!
# LATTICE: 符号→权重转换的最小保语义证明

证明对象：整条链路中最简单的一环——**符号侧的一个线性约束**，
转换为**权重侧的一个线性神经元**，转换保持语义。

这是「转换正确性」证明框架的第一块基石（对齐 doc/02 §4）：
后续复杂证明（向量约束、多层网络、非线性、Gröbner）都在此结构上生长——
语义定义 → 转换函数 → 保语义定理 → 组合律架桥。

设计约定（对齐既有 Lean 形式化实践）：
  **注意** **订正 B400**：此处原写「无 mathlib 依赖，仅 Lean 标准库（Std）——零外部依赖、编译秒级」，
  而**本文件第 1 行就是 `import Mathlib`**（所 import 的 `ComboN` 亦然）—— 自相矛盾。
  真实情况是：**本文件的符号/权重表示只用到 `Int`/`Nat` 等核心类型**
  （`LinearConstraint`、`LinearNeuron` 的字段皆为 `Int`，不依赖 mathlib 的专用结构），
  但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
  订正模板见 ConvertVectorLinear 的文件头「订正 B400」。**以本段为准。**

符号侧（L2）：
  约束：f(x) = a·x + b，满足集 S = {x | f(x) = 0}
权重侧（L3）：
  神经元：g(x) = w·x + b'，输出为零即"激活"
转换 T：
  约束系数直接拷贝为权重：(a, b) ↦ (w, b') = (a, b)
-/

namespace Lattice

/-! ## 通用转换框架
任何「符号→权重」转换的正确性都可以实例化此结构：
  sat      符号侧约束满足
  out      权重侧激活条件（输出满足）
  convert  转换映射
  preserves  保语义：∀ x, sat x ↔ out (convert x)
-/

structure Conversion (X : Type) where
  sat : X → Prop
  out : X → Prop
  convert : X → X
  preserves : ∀ x, sat x ↔ out (convert x)

/-! ## 符号侧：整数上的线性约束及其满足语义 -/

structure LinearConstraint where
  a : Int
  b : Int
deriving Repr

def ConstraintSat (c : LinearConstraint) (x : Int) : Prop :=
  c.a * x + c.b = 0

/-! ## 权重侧：线性神经元及其输出 -/

structure LinearNeuron where
  w : Int
  b : Int
deriving Repr

def NeuronOut (n : LinearNeuron) (x : Int) : Int :=
  n.w * x + n.b

/-! ## 转换：约束 → 神经元（系数直接拷贝） -/

def convert (c : LinearConstraint) : LinearNeuron :=
  { w := c.a, b := c.b }

/-! ## 定理一：转换保语义
约束满足 ⟺ 神经元输出为零。-/

theorem convert_preserves_semantics (c : LinearConstraint) (x : Int) :
    ConstraintSat c x ↔ NeuronOut (convert c) x = 0 := by
  simp [ConstraintSat, NeuronOut, convert]

/-! ## 定理二：转换不改变解集
转换前后解集相同（语义保持的集合论表述）。-/

theorem convert_preserves_solution_set (c : LinearConstraint) :
    {x : Int | ConstraintSat c x} = {x : Int | NeuronOut (convert c) x = 0} := by
  ext x
  exact convert_preserves_semantics c x

/-! ## 实例化：线性约束转换填入通用框架 -/

def linearConversion : Conversion Int :=
  { sat := fun x => ∃ c : LinearConstraint, ConstraintSat c x
    out := fun x => ∃ c : LinearConstraint, NeuronOut (convert c) x = 0
    convert := id
    preserves := by
      intro x
      constructor
      · intro ⟨c, h⟩; exact ⟨c, (convert_preserves_semantics c x).mp h⟩
      · intro ⟨c, h⟩; exact ⟨c, (convert_preserves_semantics c x).mpr h⟩ }

/-! ## 定理三：组合律架桥（符号组合 → 权重组合）
doc/01 中「符号组合律 → 权重组合律」的最小实例。
用自然数同余：约束 = 偶数判定，权重侧 = 取模输出。
合取（∧）对应两个输出的和为零。
关键性质：余数 ∈ {0,1}，两个非负项之和为零 ⟹ 各项为零。-/

/-! **注意** **R01 去重（2026-09-29）**：此处原有 `EvenSat`/`EvenOut` 的**本地副本**，
与 `ComboN.lean:19-20` **逐字相同**。两份同名是 `Lattice.EvenSat` 命名冲突
（内核实测：`import ComboN` + `import ConvertLinear` = `environment already
contains 'Lattice.EvenSat'`）。现改为**单一权威源** `ComboN`（下方 `import ComboN`）。
注意 `EvenSat` 在 `ComboN` 中**不在任何 namespace 内层**，与本地版本同形，故零改名。 -/

theorem even_combo_preserves (x y : Nat) :
    EvenSat x ∧ EvenSat y ↔ EvenOut x + EvenOut y = 0 := by
  constructor
  · intro h
    rcases h with ⟨hx, hy⟩
    unfold EvenSat at hx
    unfold EvenSat at hy
    unfold EvenOut
    rw [hx, hy]
  · intro h
    unfold EvenOut at h
    -- 非负和为零 ⟹ 各项为零
    constructor
    · unfold EvenSat
      have hs : x % 2 ≤ 0 := by
        calc
          x % 2 ≤ x % 2 + y % 2 := by omega
          _ = 0 := h
      omega
    · unfold EvenSat
      have hs : y % 2 ≤ 0 := by
        calc
          y % 2 ≤ x % 2 + y % 2 := by omega
          _ = 0 := h
      omega

/-! ## 推论：偶数约束的合取保持 = 输出和为零（可直接用作验证器判定） -/

theorem even_combo_verify (x y : Nat) (h : EvenOut x + EvenOut y = 0) : EvenSat x ∧ EvenSat y :=
  (even_combo_preserves x y).mpr h

end Lattice
