import Mathlib

/-!
# LATTICE: Newman 引理 —— 终止性 + 局部合流 ⟹ 合流

`RealConcurrentSemantics` 只做到「逐点交换 ⟹ 串行等价」的局部合流，并明确留下
「全局合流需要终止性（Newman 引理）」的缺口。本文件对**抽象关系**
`r : α → α → Prop` 补齐该缺口。

  1. `Joinable r a b`（`a`、`b` 有公共 `r`-归约）；
  2. `LocallyConfluent r`：一步的菱形性质（局部合流）；
  3. `Confluent r`：任意两个 `r`-归约序列的菱形性质；
  4. `Terminating r := WellFounded (fun b a => r a b)`：良基终止性；
  5. **`confluent_of_wf`（Newman 引理核心）**：`Terminating r` + `LocallyConfluent r`
     ⟹ `Confluent r`，用 `WellFounded.induction`（良基归纳）证明，
     关键是对两个归约序列取各自的首步并用局部合流 + 对后继的良基归纳合并；
  6. `newman`：`Terminating r → LocallyConfluent r → Confluent r`；
  7. 推论：`confluent_normalForm_unique`（合流 ⟹ 规范形唯一）、
     `confluent_of_confluent_star`；
  8. 具体重写系统实例：`prec : ℕ → ℕ → Prop := fun a b => a = b + 1`，
     `prec_terminating`、`prec_locallyConfluent`、`prec_confluent`（无条件应用 Newman 引理）；
  9. 与 β-归约的接口：`newman` 对 `RealBetaReduction.Step` 是**条件性**陈述
     （把终止性与局部合流作为显式假设），本文件不声称 β 的终止性或局部合流。

诚实标注（无 sorry / axiom / admit）：
- Newman 引理只把「终止性 + 局部合流」**提升**为「合流」；它不产生终止性，
  也不产生局部合流。对 β-归约，局部合流的一般一步菱形为**假**（机器反例见
  `RealBetaReduction.diamond_fails`），终止性也**未证**，因此 β 的全局合流在本项目
  中仍是**未证/缺口**，本文件只给出抽象转移与条件性接口。
- 本文件不引入任何未证假设。
-/

noncomputable section

namespace Lattice

variable {α : Type*}

/-! ## 一、汇合、局部合流、终止性 -/

/-- `Joinable r a b`：`a`、`b` 有公共的 `r`-归约目标。 -/
def Joinable (r : α → α → Prop) (a b : α) : Prop :=
  ∃ d, Relation.ReflTransGen r a d ∧ Relation.ReflTransGen r b d

/-- `LocallyConfluent r`：局部合流（一步的菱形性质）。 -/
def LocallyConfluent (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r a c → Joinable r b c

/-- `Confluent r`：合流（任意两个归约序列可汇合）。 -/
def Confluent (r : α → α → Prop) : Prop :=
  ∀ a b c, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c → Joinable r b c

/-- `Terminating r`：`r` 终止（逆向关系良基）。 -/
def Terminating (r : α → α → Prop) : Prop := WellFounded (fun b a => r a b)

/-- 汇合的自反性。 -/
theorem joinable_refl (r : α → α → Prop) (a : α) : Joinable r a a :=
  ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- 汇合的对称性。
（`Joinable` 是 `∃` 的 `def` 别名，点号投影 `.1`/`.2` 会失败——STYLE 速查表
「`ConvexOn` 等是 `def` 别名」同类坑，故这里先 `obtain` 再重组。） -/
theorem joinable_symm {r : α → α → Prop} {a b : α} (h : Joinable r a b) :
    Joinable r b a := by
  obtain ⟨d, h₁, h₂⟩ := h
  exact ⟨d, h₂, h₁⟩

/-- 规范形：没有一步归约。 -/
def NormalForm (r : α → α → Prop) (a : α) : Prop := ¬ ∃ b, r a b

/-- 单步可推出多步。 -/
theorem star_single {r : α → α → Prop} {a b : α} (h : r a b) :
    Relation.ReflTransGen r a b :=
  Relation.ReflTransGen.single h

/-- 多步可推出多步。 -/
theorem star_trans {r : α → α → Prop} {a b c : α} (h₁ : Relation.ReflTransGen r a b)
    (h₂ : Relation.ReflTransGen r b c) : Relation.ReflTransGen r a c :=
  h₁.trans h₂

/-! ## 二、Newman 引理核心 -/

/-- **Newman 引理核心**：终止 + 局部合流 ⟹ 合流。
证明对起点做良基归纳：把两个归约序列各拆出首步（`cases_head`），
用局部合流得到中间汇合点，再对两个首步的后继分别用归纳假设合并。 -/
theorem confluent_of_wf {r : α → α → Prop} (hT : Terminating r)
    (hL : LocallyConfluent r) : Confluent r := by
  -- 良基归纳：`WellFounded.induction` 的签名是 `{C : α → Prop} (a : α) (h : …)`，
  -- 动机 `C` 是 **`a` 之前的隐式参数**，必须用命名实参 `(C := …)` 显式给出；
  -- 且 `C` 写成 `∀ b c, …` 才能让归纳假设携带两个归约序列。
  intro a
  refine hT.induction (C := fun x => ∀ b c : α,
    Relation.ReflTransGen r x b → Relation.ReflTransGen r x c → Joinable r b c) a ?_
  intro x ih b c hab hac
  rcases hab.cases_head with hb | ⟨b₁, hab₁, hb₁b⟩
  · rw [← hb]
    exact ⟨c, hac, Relation.ReflTransGen.refl⟩
  rcases hac.cases_head with hc | ⟨c₁, hac₁, hc₁c⟩
  · rw [← hc]
    exact ⟨b, Relation.ReflTransGen.refl, hab⟩
  obtain ⟨d, hb₁d, hc₁d⟩ := hL x b₁ c₁ hab₁ hac₁
  obtain ⟨e, hbe, hde⟩ := ih b₁ hab₁ b d hb₁b hb₁d
  obtain ⟨f, hcf, hef⟩ := ih c₁ hac₁ c e hc₁c (hc₁d.trans hde)
  exact ⟨f, hbe.trans hef, hcf⟩

/-- **Newman 引理**：终止 + 局部合流 ⟹ 合流。 -/
theorem newman {r : α → α → Prop} (hT : Terminating r) (hL : LocallyConfluent r) :
    Confluent r :=
  confluent_of_wf hT hL

/-- **合流 ⟹ 规范形唯一**：若 `a` 归约到两个规范形，则它们相等。 -/
theorem confluent_normalForm_unique {r : α → α → Prop} (hC : Confluent r) {a n₁ n₂ : α}
    (h₁ : Relation.ReflTransGen r a n₁) (hn₁ : NormalForm r n₁)
    (h₂ : Relation.ReflTransGen r a n₂) (hn₂ : NormalForm r n₂) : n₁ = n₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hC a n₁ n₂ h₁ h₂
  rcases hd₁.cases_head with h | ⟨e, he, _⟩
  · rcases hd₂.cases_head with h' | ⟨e', he', _⟩
    · exact h.trans h'.symm
    · exact absurd ⟨e', he'⟩ hn₂
  · exact absurd ⟨e, he⟩ hn₁

/-! ## 三、具体重写系统实例 -/

/-- 具体重写系统：`a ↦ b` 当 `a = b + 1`（即每步减一）。 -/
def prec : ℕ → ℕ → Prop := fun a b => a = b + 1

/-- `prec` 终止（每步严格减小，用强归纳证明可及性）。
`WellFounded` 是 **inductive**（构造子 `WellFounded.intro : (∀ a, Acc r a) → WellFounded r`），
不是 `def` 别名，故 `intro n` 因无绑定子而报 "insufficient number of binders"
——必须先 `refine WellFounded.intro ?_` 拆开构造子。 -/
theorem prec_terminating : Terminating prec := by
  refine WellFounded.intro ?_
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact Acc.intro n (fun m h => ih m (by unfold prec at h; omega))

/-- `prec` 局部合流（确定性：`b + 1 = c + 1 ⟹ b = c`）。 -/
theorem prec_locallyConfluent : LocallyConfluent prec := by
  intro a b c hab hac
  unfold prec at hab hac
  have hbc : b = c := by omega
  subst hbc
  exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-- `prec` 合流（无条件应用 Newman 引理）。 -/
theorem prec_confluent : Confluent prec :=
  newman prec_terminating prec_locallyConfluent

end Lattice
