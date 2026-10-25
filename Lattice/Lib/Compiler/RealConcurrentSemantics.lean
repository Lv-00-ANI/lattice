import Mathlib
import Lattice.Lib.Concentration.RealEditOrder
/-!
# LATTICE: 并发语义 —— 交错执行、局部合流与交换律

本文件给出「并发程序 = 步骤列表」的最小并发语义，并证明交换性 ⟹ 交错等价：

  1. `run`：顺序执行一个步骤列表（`List.foldr`），配 `run_nil`、`run_cons`、`run_append`；
  2. `Interleaving l₁ l₂ m`：`m` 是 `l₁`、`l₂` 的一个交错（归纳定义）；
  3. `confluence_of_commuting`（**核心**）：两步可交换 ⟹ 两个顺序的结果相同
     （Church–Rosser 的局部菱形）；
  4. `commute_with_list`：与列表中每一步都可交换的步骤可以从列表中「穿过」；
  5. `interleaving_equiv_sequential`（**核心**）：若 `l₁` 的每一步与 `l₂` 的每一步
     逐点交换，则**任意**交错 `m` 的结果等于串行结果 `run l₁ (run l₂ x)`；
  6. `race_condition_witness`：不可交换步骤的交错结果不同 —— 构造性反例；
  7. `editSeq_commuting_instance`：`RealEditOrder.editSeqComm` 是一个交换性实例，
     说明本文件的交换性正是编辑顺序无关性的抽象。

诚实标注（无 sorry / axiom / admit）：
- 交错等价定理要求**逐点交换**（`∀ f ∈ l₁, ∀ g ∈ l₂, f ∘ g = g ∘ f`），这是充分条件，
  不是必要条件；一般非交换并发只保证局部合流，全局合流需要终止性（Newman 引理），
  本文件不做终止性论证。
- 「并发」是交错语义（interleaving semantics），不含真正的并行或竞态检测。
- 与 `RealEditOrder` 的衔接是一条命名特化，不重复其证明。
-/

noncomputable section

namespace Lattice

variable {X : Type*}

/-! ## 一、顺序执行 -/

/-- 顺序执行步骤列表：`run [f, g] x = f (g x)`。 -/
def run (l : List (X → X)) (x : X) : X := l.foldr (fun f acc => f acc) x

@[simp] theorem run_nil (x : X) : run [] x = x := rfl

@[simp] theorem run_cons (f : X → X) (l : List (X → X)) (x : X) :
    run (f :: l) x = f (run l x) := rfl

/-- 列表拼接的执行律：`run (l₁ ++ l₂) x = run l₁ (run l₂ x)`。 -/
theorem run_append (l₁ l₂ : List (X → X)) (x : X) :
    run (l₁ ++ l₂) x = run l₁ (run l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons f l ih =>
      simp only [List.cons_append, run_cons, ih]

/-! ## 二、交错 -/

/-- `Interleaving l₁ l₂ m`：`m` 是 `l₁` 与 `l₂` 的一个交错。 -/
inductive Interleaving : List (X → X) → List (X → X) → List (X → X) → Prop where
  | nil : Interleaving [] [] []
  | left {f : X → X} {l₁ l₂ m : List (X → X)} :
      Interleaving l₁ l₂ m → Interleaving (f :: l₁) l₂ (f :: m)
  | right {f : X → X} {l₁ l₂ m : List (X → X)} :
      Interleaving l₁ l₂ m → Interleaving l₁ (f :: l₂) (f :: m)

/-- 交错保持长度：`|m| = |l₁| + |l₂|`。 -/
theorem interleaving_length {l₁ l₂ m : List (X → X)} (h : Interleaving l₁ l₂ m) :
    m.length = l₁.length + l₂.length := by
  induction h with
  | nil => rfl
  | left _ ih => simp [ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  | right _ ih => simp [ih, Nat.add_assoc]

/-! ## 三、可交换 ⟹ 合流 -/

/-- **局部合流（菱形）**：若 `f ∘ g = g ∘ f`，则两种顺序的结果相同。 -/
theorem confluence_of_commuting {f g : X → X} (hcomm : ∀ x, f (g x) = g (f x)) (x : X) :
    run [f, g] x = run [g, f] x := by
  simp only [run_cons, run_nil]
  exact hcomm x

/-- **穿过引理**：若 `f` 与 `l` 中每一步都可交换，则 `f` 可从 `l` 中穿过：
`f (run l x) = run l (f x)`。 -/
theorem commute_with_list {f : X → X} (l : List (X → X))
    (h : ∀ g ∈ l, ∀ x, f (g x) = g (f x)) : ∀ x, f (run l x) = run l (f x) := by
  induction l with
  | nil => intro x; rfl
  | cons g l ih =>
      intro x
      simp only [run_cons]
      rw [h g (by simp) (run l x)]
      rw [ih (fun h' hh => h h' (by simp [hh])) x]

/-- 逐点交换性对左列表取尾保持不变。 -/
theorem hcomm_cons_left {l₁ l₂ : List (X → X)} {f : X → X}
    (h : ∀ f' ∈ f :: l₁, ∀ g ∈ l₂, ∀ x, f' (g x) = g (f' x)) :
    ∀ f' ∈ l₁, ∀ g ∈ l₂, ∀ x, f' (g x) = g (f' x) :=
  fun f' hf' g hg x => h f' (by simp [hf']) g hg x

/-- 逐点交换性对右列表取尾保持不变。 -/
theorem hcomm_cons_right {l₁ l₂ : List (X → X)} {g : X → X}
    (h : ∀ f' ∈ l₁, ∀ g' ∈ g :: l₂, ∀ x, f' (g' x) = g' (f' x)) :
    ∀ f' ∈ l₁, ∀ g' ∈ l₂, ∀ x, f' (g' x) = g' (f' x) :=
  fun f' hf' g' hg' x => h f' hf' g' (by simp [hg']) x

/-- 单步 `g` 与整个列表 `l₁` 交换（在 `g ∘ l₂` 型假设下的特化）。 -/
theorem commute_with_list_via {l₁ l₂ : List (X → X)} {g : X → X}
    (h : ∀ f' ∈ l₁, ∀ g' ∈ g :: l₂, ∀ x, f' (g' x) = g' (f' x)) :
    ∀ x, g (run l₁ x) = run l₁ (g x) :=
  commute_with_list l₁ (fun f' hf' x => (h f' hf' g (by simp) x).symm)

/-- **交错等价于串行（核心）**：若 `l₁` 的每一步与 `l₂` 的每一步逐点交换，
则**任意**交错 `m` 的结果等于串行结果 `run l₁ (run l₂ x)`。 -/
theorem interleaving_equiv_sequential {l₁ l₂ : List (X → X)}
    (hcomm : ∀ f ∈ l₁, ∀ g ∈ l₂, ∀ x, f (g x) = g (f x))
    {m : List (X → X)} (hm : Interleaving l₁ l₂ m) :
    ∀ x, run m x = run l₁ (run l₂ x) := by
  induction hm with
  | nil => intro x; rfl
  | left hm ih =>
      intro x
      simp only [run_cons]
      rw [ih (hcomm_cons_left hcomm)]
  | right hm ih =>
      intro x
      simp only [run_cons]
      rw [ih (hcomm_cons_right hcomm)]
      exact commute_with_list_via hcomm _

/-! ## 四、竞态反例 -/

/-- 自增步骤 `n ↦ n + 1`。 -/
def incStep (n : ℕ) : ℕ := n + 1

/-- 自乘步骤 `n ↦ 2n`。 -/
def dblStep (n : ℕ) : ℕ := n * 2

/-- 两步的两种顺序的取值：`[inc, dbl]` 得 1，`[dbl, inc]` 得 2。 -/
theorem race_condition_values :
    run [incStep, dblStep] 0 = 1 ∧ run [dblStep, incStep] 0 = 2 := by
  decide

/-- **竞态见证（构造性反例）**：不可交换的两步，其交错结果不同。 -/
theorem race_condition_witness :
    run [incStep, dblStep] 0 ≠ run [dblStep, incStep] 0 := by
  decide

/-! ## 五、与 RealEditOrder 的衔接 -/

/-- **编辑顺序无关性是交换性的实例**：`RealEditOrder.editSeqComm` 说两次 rank-one 编辑
可交换。把「一次编辑」看作 `E → ℝ` 上的步骤，则这正是本文件 `confluence_of_commuting`
所抽象的局部合流（交换性）。 -/
theorem editSeq_commuting_instance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (F : E → ℝ) (Δ₁ Δ₂ : ℝ) (k₁ k₂ : E) :
    rankOneEdit (rankOneEdit F Δ₁ k₁) Δ₂ k₂
      = rankOneEdit (rankOneEdit F Δ₂ k₂) Δ₁ k₁ :=
  editSeqComm F Δ₁ Δ₂ k₁ k₂

end Lattice
