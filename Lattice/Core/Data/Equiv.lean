import Mathlib
import Lattice.Core.Data.Basic

/-!
# 数据等价

## 这个文件为什么存在

**链的每一步都需要「两个数据是同一个」这句话。`Data` 是两个 `List` 的结构，
所以 `=` 是可以用的 —— 但 `=` 在**证明里**太强：它要求两个表达式在定义上相同。**

**⇒ `DataEquiv` 是**逐字段相等**的谓词，它比 `=` 弱（在证明里更容易达到），但可证明与 `=` 等价。**
**⇒ 本节的关键定理是 `dataEquiv_iff_eq`：两者其实**同强**，所以「用哪个」是书写便利问题，不是表达能力问题。
这条必须先证，否则「用较弱的相等」这句话没有依据。**

## 与链的关系

**`Encode`/`Bridge` 的正确性都以「编码相同 ⟺ 数据等价」的形式陈述，
所以等价关系本身必须先是一个可用的等价关系 —— 这就是自反、对称、传递三条。**
-/

namespace Lattice.Data

/-- **数据等价：逐字段相等。**

**=> 比 `=` 弱的形式，方便逐字段证明；后面 `dataEquiv_iff_eq` 说明它与 `=` 同强。** -/
def DataEquiv (d₁ d₂ : Data) : Prop :=
  d₁.corpus = d₂.corpus ∧ d₁.indices = d₂.indices

/-- **等价关系是自反的。**

**=> 任何数据与自身等价。这条使 `DataEquiv` 能作为重写规则使用。** -/
theorem dataEquiv_refl (d : Data) : DataEquiv d d :=
  ⟨rfl, rfl⟩

/-- **等价关系是对称的。**

**=> 逐字段相等交换方向。** -/
theorem dataEquiv_symm {d₁ d₂ : Data} (h : DataEquiv d₁ d₂) : DataEquiv d₂ d₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- **等价关系是传递的。**

**=> 两条逐字段相等可以串起来，这是 `Encode` 里的链式推理所必需的。** -/
theorem dataEquiv_trans {d₁ d₂ d₃ : Data} (h₁ : DataEquiv d₁ d₂) (h₂ : DataEquiv d₂ d₃) :
    DataEquiv d₁ d₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- **相等蕴含等价。**

**=> 从 `=` 到 `DataEquiv` 的下降。没有它，任何 `rfl` 证明都接不上逐字段形式。** -/
theorem dataEquiv_of_eq {d₁ d₂ : Data} (h : d₁ = d₂) : DataEquiv d₁ d₂ := by
  rw [h]
  exact dataEquiv_refl d₂

/-- **等价蕴含相等。**

**`DataEquiv d₁ d₂ → d₁ = d₂`。**
**=> 这条是本节的核心：`DataEquiv` **不比** `=` 弱，两者同强。**
**因此「用逐字段相等是为了书写方便」这句话是有依据的，而不是一个未证的断言。**
**证明走 `Data` 的 `cases`：两个字段分别相等时，结构本身相等。** -/
theorem eq_of_dataEquiv {d₁ d₂ : Data} (h : DataEquiv d₁ d₂) : d₁ = d₂ := by
  obtain ⟨c, i⟩ := d₁
  obtain ⟨c', i'⟩ := d₂
  simp only [DataEquiv] at h
  rw [h.1, h.2]

/-- **等价与相等可以互换。**

**=> 把上一对合成一条双向陈述：`DataEquiv d₁ d₂ ↔ d₁ = d₂`。**
**⇒ 这条让后续定理可以在两种形式之间自由转换，而不必每次重复两条证明。**
**它也说明了抽象层的取舍：`DataEquiv` 存在的原因是**证明便利**，而不是表达力的差异。** -/
theorem dataEquiv_iff_eq (d₁ d₂ : Data) : DataEquiv d₁ d₂ ↔ d₁ = d₂ :=
  ⟨eq_of_dataEquiv, dataEquiv_of_eq⟩

end Lattice.Data
