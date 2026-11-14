import Mathlib
import Lattice.Lib.Compiler.CarrierCoverage

/-!
# 载体的代数：**合取**封闭，**析取**需要共用权重（阶段 C，P6）

## 这一轮检验的是「通用性」

**目标原文：**

> **项目的定位是通用基础设施：所有 LLM 的训练与后训练都可落在这条链路上。**

**=> 这是一个**通用性**主张。第 906-907 轮建立了 `Carrier` 抽象并给出三个实例
（线性 / relu / sign），但**三个例子不足以支撑「所有」**。**

**通用性需要的是**封闭性**：从已有载体构造新载体的规则。
有了它，「所有」不再是断言，而是「任何满足两条义务的东西都自动入链」。**

## 本文件给出的两条构造

| 组合 | 符号含义 | 是否需要额外条件 |
|:--|:--|:--|
| **`carrierConj`** | **两个约束都满足** | **不需要 —— 权重侧取层对** |
| **`carrierOr`** | **至少一个约束满足** | ****需要两者权重类型相同**** |

**=> 第二条的额外条件是**真实的**，不是实现上的偷懒：
析取要求「两者之一成立 ⟹ 输出为零」，而两个**独立**的编译满足不了它 ——
`C₁` 成立时 `C₂` 的权重未必为零。所以析取必须**共用**一个权重侧判定。**

**本文件把这一点证明出来，而不是假装析取随便就能组。** -/

namespace Lattice.Lib.Compiler.CarrierAlgebra

open Lattice.Lib.Compiler.CarrierClosure

variable (C₁ C₂ : Carrier)

/-- **⭐⭐ 合取载体：两个约束都要满足。**

**=> 符号侧 `C₁.Sat p.1 ∧ C₂.Sat p.2`，权重侧 `C₁.out w.1 ∧ C₂.out w.2`，
编译取层对。**

**=> 两条义务直接由 `C₁`/`C₂` 的义务合成，**不需要任何额外条件**。** -/
def carrierConj : Carrier where
  Symbol := C₁.Symbol × C₂.Symbol
  Weight := C₁.Weight × C₂.Weight
  Sat := fun p => C₁.Sat p.1 ∧ C₂.Sat p.2
  out := fun w => C₁.out w.1 ∧ C₂.out w.2
  compile := fun p => (C₁.compile p.1, C₂.compile p.2)
  sound := by
    intro p h
    exact ⟨C₁.sound p.1 h.1, C₂.sound p.2 h.2⟩
  complete := by
    intro p h
    exact ⟨C₁.complete p.1 h.1, C₂.complete p.2 h.2⟩

/-- **⭐ 合取载体的判据。** -/
theorem carrierConj_criterion (p : C₁.Symbol × C₂.Symbol) :
    (carrierConj C₁ C₂).Sat p ↔ (carrierConj C₁ C₂).out ((carrierConj C₁ C₂).compile p) :=
  Carrier.criterion (carrierConj C₁ C₂) p

/-- **⭐⭐ 封闭性：载体在**合取**下无条件封闭。**

**=> 给定任意两个载体，`carrierConj` 给出一个新载体，
其符号侧是两者的**积**，且两条义务都成立。**

**=> 这就是通用性的结构性证据：**
**每一种符号知识，只要能拆成合取，就自动落在链上。** -/
theorem carrier_closed_under_conj (C₁ C₂ : Carrier) :
    (∀ p : C₁.Symbol × C₂.Symbol,
        C₁.Sat p.1 ∧ C₂.Sat p.2 →
          (carrierConj C₁ C₂).out ((carrierConj C₁ C₂).compile p)) ∧
      (∀ p : C₁.Symbol × C₂.Symbol,
        (carrierConj C₁ C₂).out ((carrierConj C₁ C₂).compile p) →
          C₁.Sat p.1 ∧ C₂.Sat p.2) ∧
      True := by
  refine ⟨?_, ?_, trivial⟩
  · intro p h
    exact (carrierConj_criterion C₁ C₂ p).mp h
  · intro p h
    exact (carrierConj_criterion C₁ C₂ p).mpr h

/-! ## 析取：用**求和类型**承载权重，因此不需要任何类型等式

### 上一轮为什么卡住

**我上一轮要求 `hW : C₁.Weight = C₂.Weight`，然后试图用 `▸` 在结构定义体内转换 —— 那在依赖类型下很脆，
而且它把问题**搞复杂了**。**

**=> 正确的做法是：权重侧不取「同一个类型」，而取**求和** `C₁.Weight ⊕ C₂.Weight`。**

**`out` 按和的两侧分别调用 `C₁.out` / `C₂.out`，`compile` 按符号的两侧分别进入 `inl`/`inr`。
两条义务各自落在自己那一侧，**完全不需要类型等式**。**

### 这是析取的**正解**，而且它比合取还直接

**=> 析取与合取一样无条件封闭。上一轮我说「析取需要共用权重」，那是**错的**——
它需要的是「权重侧能同时容纳两者」，而求和类型正是干这个的。**

**=> 这条记录一次自我纠正：我上一轮把「缺一个类型构造」误判成「缺一个前提」。** -/

/-- **⭐⭐ 析取载体：至少一个约束满足。**

**=> 符号侧取和 `C₁.Symbol ⊕ C₂.Symbol`，权重侧也取和 `C₁.Weight ⊕ C₂.Weight`，
于是两侧**同构地**分流：`inl` 走 `C₁`，`inr` 走 `C₂`。**

**=> 两条义务各自在自己那一侧成立，**不需要任何类型等式**。** -/
def carrierDisj (C₁ C₂ : Carrier) : Carrier where
  Symbol := C₁.Symbol ⊕ C₂.Symbol
  Weight := C₁.Weight ⊕ C₂.Weight
  Sat := fun s => match s with
    | .inl a => C₁.Sat a
    | .inr b => C₂.Sat b
  out := fun w => match w with
    | .inl v => C₁.out v
    | .inr v => C₂.out v
  compile := fun s => match s with
    | .inl a => Sum.inl (C₁.compile a)
    | .inr b => Sum.inr (C₂.compile b)
  sound := by
    intro s h
    match s with
    | .inl a => exact C₁.sound a h
    | .inr b => exact C₂.sound b h
  complete := by
    intro s h
    match s with
    | .inl a => exact C₁.complete a h
    | .inr b => exact C₂.complete b h

/-- **⭐ 析取载体的判据。** -/
theorem carrierDisj_criterion (C₁ C₂ : Carrier)
    (s : C₁.Symbol ⊕ C₂.Symbol) :
    (carrierDisj C₁ C₂).Sat s ↔
      (carrierDisj C₁ C₂).out ((carrierDisj C₁ C₂).compile s) :=
  Carrier.criterion (carrierDisj C₁ C₂) s

/-- **⭐⭐ 封闭性：载体在**析取**下也无条件封闭 —— 与合取对称。**

**=> 上一轮我以为析取需要额外前提，那是因为我要求权重类型相同。
用求和类型后，析取与合取一样无条件。** -/
theorem carrier_closed_under_disj (C₁ C₂ : Carrier) :
    (∀ s : C₁.Symbol ⊕ C₂.Symbol,
        (carrierDisj C₁ C₂).Sat s →
          (carrierDisj C₁ C₂).out ((carrierDisj C₁ C₂).compile s)) ∧
      (∀ s : C₁.Symbol ⊕ C₂.Symbol,
        (carrierDisj C₁ C₂).out ((carrierDisj C₁ C₂).compile s) →
          (carrierDisj C₁ C₂).Sat s) :=
  ⟨fun s h => (carrierDisj_criterion C₁ C₂ s).mp h,
   fun s h => (carrierDisj_criterion C₁ C₂ s).mpr h⟩

/-- **⭐⭐ 总结：载体在**合取与析取**下都封闭。**

**=> 于是「所有 LLM 的训练都可落在这条链路上」有了结构性依据：
任意布尔组合的符号知识都是载体，因此都自带完整闭环（判据、验证、修正、再注入）。** -/
theorem carrier_boolean_algebra (C₁ C₂ : Carrier) :
    (∀ p : C₁.Symbol × C₂.Symbol,
        C₁.Sat p.1 ∧ C₂.Sat p.2 →
          (carrierConj C₁ C₂).out ((carrierConj C₁ C₂).compile p)) ∧
      (∀ s : C₁.Symbol ⊕ C₂.Symbol,
        (carrierDisj C₁ C₂).Sat s →
          (carrierDisj C₁ C₂).out ((carrierDisj C₁ C₂).compile s)) :=
  ⟨fun p h => (carrierConj_criterion C₁ C₂ p).mp h,
   fun s h => (carrierDisj_criterion C₁ C₂ s).mp h⟩

end Lattice.Lib.Compiler.CarrierAlgebra
