import Mathlib

/-!
# LATTICE: 布尔代数完备性 —— 范式等价与功能完备性

本文件形式化布尔表达式的**完备性**：任意布尔函数都可由仅含 `∧`、`∨`、`¬` 的
表达式表示，并且每个表达式等价于其真值表构造的析取范式（DNF）。

  1. `BoolExpr`：语法（`var` / `and` / `or` / `not` / `impl`）；
  2. `evalBool`：赋值 `σ : ℕ → Bool` 下的求值；
  3. `vars`：表达式中出现的变量集合；`eval_congr`：求值只依赖 `vars` 上的取值；
  4. `LitClause` / `DNF` / `evalClause` / `evalDNF`：文字合取子句与析取范式；
     `minterm`：赋值在变量集上的**极小项**；
  5. `evalClause_minterm`：极小项为真 ⟺ 赋值在变量集上一致；
  6. `normalForm`：真值表 DNF（枚举变量子集，取使表达式为真的那些极小项）；
  7. `evalDNF_iff`：`evalDNF σ (normalForm e) = true` ⟺ 存在使 `e` 为真的子集赋值
     且与 `σ` 一致；
  8. `eval_eq_true_iff` 与 **`normal_form_equiv`**（**核心**）：
     任意布尔式 ⟺ 其真值表 DNF；
  9. `truthTableDNF` / `evalDNF_truthTable` / `ofDNF` / `eval_ofDNF`：
     把 DNF 翻译回语法并保持求值；
  10. **`completeness`**：任意 `f : (Fin n → Bool) → Bool` 都可由某个 `BoolExpr` 表达；
  11. `OnlyAndOrNot`：只使用 `∧`、`∨`、`¬` 的语法谓词；
      **`and_or_not_complete`**：`{∧,∨,¬}` 功能完备（由 10 显式构造的式子只含此三算子得到）；
  12. `impl_expressible`：`impl` 可由 `¬`、`∨` 表达，说明 `{∧,∨,¬}` 覆盖 `impl`。

诚实标注（无 sorry / axiom / admit）：
- **真值表路线**：`normalForm` 以「变量子集」枚举赋值（子集 `s` 给出赋值
  `n ↦ decide (n ∈ s)`），因此只用到 `Finset` 的幂集枚举，不依赖函数型的 `Fintype`
  枚举细节；`completeness` 的变量数固定为 `n`，用 `Fin n → Bool` 的 `Finset.univ` 枚举。
- **不做最小化**：本文件不涉及 DNF 最小化、奎因–麦克拉斯基化简或 CNF 对偶；
  `normalForm` 是真值表构造（可能指数大小）。
- 变量的 `ℕ → Bool` 赋值是全域定义；`completeness` 中 `f` 只依赖前 `n` 个变量
  （由 `Fin n → Bool` 表示），与 `evalBool` 的 `σ` 通过 `fun i => σ i` 衔接。
-/

noncomputable section

namespace Lattice.Lib.Compiler.RealBoolCompleteness

/-! ## 一、语法与求值 -/

/-- 布尔表达式。 -/
inductive BoolExpr where
  | var (n : ℕ) : BoolExpr
  | and (e₁ e₂ : BoolExpr) : BoolExpr
  | or (e₁ e₂ : BoolExpr) : BoolExpr
  | not (e : BoolExpr) : BoolExpr
  | impl (e₁ e₂ : BoolExpr) : BoolExpr
deriving DecidableEq, Repr

/-- 赋值 `σ : ℕ → Bool` 下的求值。 -/
def evalBool (σ : ℕ → Bool) : BoolExpr → Bool
  | .var n => σ n
  | .and e₁ e₂ => evalBool σ e₁ && evalBool σ e₂
  | .or e₁ e₂ => evalBool σ e₁ || evalBool σ e₂
  | .not e => !evalBool σ e
  | .impl e₁ e₂ => !evalBool σ e₁ || evalBool σ e₂

/-- `impl` 可由 `¬` 与 `∨` 表达。 -/
theorem impl_expressible (σ : ℕ → Bool) (a b : BoolExpr) :
    evalBool σ (.impl a b) = evalBool σ (.or (.not a) b) := by
  simp only [evalBool]

/-- 表达式出现的变量集合。 -/
def vars : BoolExpr → Finset ℕ
  | .var n => {n}
  | .and e₁ e₂ => vars e₁ ∪ vars e₂
  | .or e₁ e₂ => vars e₁ ∪ vars e₂
  | .not e => vars e
  | .impl e₁ e₂ => vars e₁ ∪ vars e₂

/-- 两个赋值在变量集 `s` 上一致。 -/
def AgreeOn {α β : Type*} (σ τ : α → β) (s : Finset α) : Prop := ∀ a ∈ s, σ a = τ a

/-- **求值只依赖 `vars`**：在 `vars e` 上一致的赋值给出相同求值。 -/
theorem eval_congr {σ τ : ℕ → Bool} {e : BoolExpr} (h : AgreeOn σ τ (vars e)) :
    evalBool σ e = evalBool τ e := by
  induction e with
  | var n => exact h n (by simp [vars])
  | and e₁ e₂ ih₁ ih₂ =>
      have h1 : AgreeOn σ τ (vars e₁) := fun n hn => h n (Finset.mem_union_left _ hn)
      have h2 : AgreeOn σ τ (vars e₂) := fun n hn => h n (Finset.mem_union_right _ hn)
      simp only [evalBool]
      rw [ih₁ h1, ih₂ h2]
  | or e₁ e₂ ih₁ ih₂ =>
      have h1 : AgreeOn σ τ (vars e₁) := fun n hn => h n (Finset.mem_union_left _ hn)
      have h2 : AgreeOn σ τ (vars e₂) := fun n hn => h n (Finset.mem_union_right _ hn)
      simp only [evalBool]
      rw [ih₁ h1, ih₂ h2]
  | not e ih =>
      simp only [evalBool]
      rw [ih h]
  | impl e₁ e₂ ih₁ ih₂ =>
      have h1 : AgreeOn σ τ (vars e₁) := fun n hn => h n (Finset.mem_union_left _ hn)
      have h2 : AgreeOn σ τ (vars e₂) := fun n hn => h n (Finset.mem_union_right _ hn)
      simp only [evalBool]
      rw [ih₁ h1, ih₂ h2]

/-! ## 二、析取范式与极小项 -/

/-- 文字合取子句：`(变量, 期望值)` 的列表。 -/
abbrev LitClause := List (ℕ × Bool)

/-- 析取范式：子句列表。 -/
abbrev DNF := List LitClause

/-- 子句求值：所有文字同时命中。 -/
def evalClause (σ : ℕ → Bool) (l : LitClause) : Bool :=
  l.all (fun p => σ p.1 == p.2)

/-- DNF 求值：某个子句命中。 -/
def evalDNF (σ : ℕ → Bool) (d : DNF) : Bool :=
  d.any (evalClause σ)

/-- 赋值 `σ` 在变量集 `s` 上的极小项。 -/
def minterm (σ : ℕ → Bool) (s : Finset ℕ) : LitClause :=
  s.toList.map (fun v => (v, σ v))

/-- **极小项刻画**：`minterm τ s` 在 `σ` 下为真 ⟺ `σ`、`τ` 在 `s` 上一致。 -/
theorem evalClause_minterm {σ τ : ℕ → Bool} {s : Finset ℕ} :
    evalClause σ (minterm τ s) = true ↔ AgreeOn σ τ s := by
  unfold evalClause minterm AgreeOn
  rw [List.all_eq_true]
  constructor
  · intro h v hv
    have hp : (v, τ v) ∈ s.toList.map (fun v => (v, τ v)) :=
      List.mem_map.mpr ⟨v, by simpa using hv, rfl⟩
    have := h (v, τ v) hp
    simpa using this
  · intro h p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    have hv' : v ∈ s := by simpa using hv
    simpa using h v hv'

/-- 子集 `s` 导出的赋值：`n ↦ decide (n ∈ s)`。 -/
def assignmentOfSubset (s : Finset ℕ) : ℕ → Bool := fun n => decide (n ∈ s)

/-- **真值表 DNF**：枚举 `vars e` 的子集，取使 `e` 为真的那些极小项。 -/
def normalForm (e : BoolExpr) : DNF :=
  (((vars e).powerset.filter (fun s => evalBool (assignmentOfSubset s) e)).image
    (fun s => minterm (assignmentOfSubset s) (vars e))).toList

/-- **DNF 真值表刻画**。 -/
theorem evalDNF_iff (σ : ℕ → Bool) (e : BoolExpr) :
    evalDNF σ (normalForm e) = true ↔
      ∃ s ∈ (vars e).powerset,
        evalBool (assignmentOfSubset s) e = true ∧
          AgreeOn σ (assignmentOfSubset s) (vars e) := by
  unfold evalDNF normalForm
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hl'⟩
    rw [Finset.mem_toList, Finset.mem_image] at hl
    obtain ⟨s, hs, hsl⟩ := hl
    rw [Finset.mem_filter] at hs
    rw [← hsl] at hl'
    exact ⟨s, hs.1, hs.2, evalClause_minterm.mp hl'⟩
  · rintro ⟨s, hs, hse, hag⟩
    refine ⟨minterm (assignmentOfSubset s) (vars e), ?_, evalClause_minterm.mpr hag⟩
    rw [Finset.mem_toList, Finset.mem_image]
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hse⟩, rfl⟩

/-- **范式等价（真值，核心）**：`evalBool σ e = true ⟺ evalDNF σ (normalForm e) = true`。 -/
theorem eval_eq_true_iff (σ : ℕ → Bool) (e : BoolExpr) :
    evalBool σ e = true ↔ evalDNF σ (normalForm e) = true := by
  constructor
  · intro h
    rw [evalDNF_iff]
    let s : Finset ℕ := (vars e).filter (fun n => σ n)
    have hs : s ∈ (vars e).powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    have hag : AgreeOn (assignmentOfSubset s) σ (vars e) := by
      intro n hn
      have hmem : n ∈ s ↔ σ n = true := by
        rw [Finset.mem_filter]
        exact ⟨fun hh => hh.2, fun hh => ⟨hn, hh⟩⟩
      cases hσ : σ n with
      | false =>
          have : n ∉ s := fun hns => by
            have := hmem.mp hns
            rw [hσ] at this
            exact Bool.false_ne_true this
          simp [assignmentOfSubset, this, hσ]
      | true =>
          have : n ∈ s := hmem.mpr hσ
          simp [assignmentOfSubset, this, hσ]
    have hev : evalBool (assignmentOfSubset s) e = true := by
      rw [eval_congr (e := e) hag]
      exact h
    exact ⟨s, hs, hev, fun n hn => (hag n hn).symm⟩
  · intro h
    rw [evalDNF_iff] at h
    obtain ⟨s, hs, hse, hag⟩ := h
    rw [eval_congr (e := e) hag]
    exact hse

/-- **范式等价（核心）**：任意布尔式等价于其真值表 DNF。 -/
theorem normal_form_equiv (σ : ℕ → Bool) (e : BoolExpr) :
    evalBool σ e = evalDNF σ (normalForm e) := by
  by_cases h : evalBool σ e = true
  · exact h.trans ((eval_eq_true_iff σ e).mp h).symm
  · have hf : evalBool σ e = false := by cases hh : evalBool σ e <;> simp_all
    have hd : evalDNF σ (normalForm e) = false := by
      by_contra hne
      have hdt : evalDNF σ (normalForm e) = true := by
        cases hh : evalDNF σ (normalForm e) with
        | false => exact absurd hh hne
        | true => rfl
      exact h ((eval_eq_true_iff σ e).mpr hdt)
    rw [hf, hd]

/-! ## 三、DNF 翻译回语法 -/

/-- 恒真式（只含 `∧`、`∨`、`¬`）。 -/
def truth : BoolExpr := .or (.var 0) (.not (.var 0))

/-- 恒假式（只含 `∧`、`∨`、`¬`）。 -/
def falsity : BoolExpr := .and (.var 0) (.not (.var 0))

theorem eval_truth (σ : ℕ → Bool) : evalBool σ truth = true := by
  cases h : σ 0 <;> simp [truth, evalBool, h]

theorem eval_falsity (σ : ℕ → Bool) : evalBool σ falsity = false := by
  cases h : σ 0 <;> simp [falsity, evalBool, h]

/-- 文字翻译：`(n, true) ↦ var n`，`(n, false) ↦ ¬ var n`。 -/
def lit (p : ℕ × Bool) : BoolExpr := if p.2 then .var p.1 else .not (.var p.1)

theorem eval_lit (σ : ℕ → Bool) (p : ℕ × Bool) : evalBool σ (lit p) = (σ p.1 == p.2) := by
  obtain ⟨n, b⟩ := p
  cases b <;> cases h : σ n <;> simp [lit, evalBool, h]

/-- 子句翻译：文字的合取。 -/
def ofClause : LitClause → BoolExpr
  | [] => truth
  | p :: l => .and (lit p) (ofClause l)

/-- DNF 翻译：子句的析取。 -/
def ofDNF : DNF → BoolExpr
  | [] => falsity
  | l :: d => .or (ofClause l) (ofDNF d)

theorem eval_ofClause (σ : ℕ → Bool) (l : LitClause) :
    evalBool σ (ofClause l) = evalClause σ l := by
  induction l with
  | nil => simp [ofClause, evalClause, eval_truth]
  | cons p l ih => simp [ofClause, evalClause, evalBool, eval_lit, ih]

theorem eval_ofDNF (σ : ℕ → Bool) (d : DNF) : evalBool σ (ofDNF d) = evalDNF σ d := by
  induction d with
  | nil => simp [ofDNF, evalDNF, eval_falsity]
  | cons l d ih => simp [ofDNF, evalDNF, evalBool, eval_ofClause, ih]

/-! ## 四、功能完备性 -/

/-- 固定 `n` 个变量的极小项：`i ↦ (i, b i)`。 -/
def finMinterm (n : ℕ) (b : Fin n → Bool) : LitClause :=
  (List.finRange n).map (fun i => (i.val, b i))

/-- `Fin n` 上极小项的刻画。 -/
theorem evalClause_finMinterm (σ : ℕ → Bool) (n : ℕ) (b : Fin n → Bool) :
    evalClause σ (finMinterm n b) = true ↔
      AgreeOn (fun i : Fin n => σ i) b Finset.univ := by
  unfold evalClause finMinterm AgreeOn
  rw [List.all_eq_true]
  constructor
  · intro h i _
    have hp : (i.val, b i) ∈ (List.finRange n).map (fun i => (i.val, b i)) :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    have := h (i.val, b i) hp
    simpa using this
  · intro h p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    simpa using h i (Finset.mem_univ i)

/-- **真值表 DNF（固定变量数）**：枚举 `Fin n → Bool` 中使 `f` 为真的赋值。 -/
def truthTableDNF (n : ℕ) (f : (Fin n → Bool) → Bool) : DNF :=
  ((Finset.univ.filter (fun b : Fin n → Bool => f b)).image (finMinterm n)).toList

/-- **真值表 DNF 的刻画**。 -/
theorem evalDNF_truthTable (σ : ℕ → Bool) (n : ℕ) (f : (Fin n → Bool) → Bool) :
    evalDNF σ (truthTableDNF n f) = true ↔ f (fun i : Fin n => σ i) = true := by
  unfold evalDNF truthTableDNF
  rw [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hl'⟩
    rw [Finset.mem_toList, Finset.mem_image] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    rw [Finset.mem_filter] at hb
    have hag := (evalClause_finMinterm σ n b).mp hl'
    have hbσ : b = (fun i : Fin n => σ i) :=
      funext (fun i => (hag i (Finset.mem_univ i)).symm)
    rw [← hbσ]
    exact hb.2
  · intro hf
    refine ⟨finMinterm n (fun i : Fin n => σ i), ?_, ?_⟩
    · rw [Finset.mem_toList, Finset.mem_image]
      exact ⟨fun i => σ i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, rfl⟩
    · exact (evalClause_finMinterm σ n (fun i => σ i)).mpr (fun i _ => rfl)

/-- **真值表构造的正确性**：翻译回语法的 DNF 正好表达 `f`。 -/
theorem ofTruthTable_spec (n : ℕ) (f : (Fin n → Bool) → Bool) (σ : ℕ → Bool) :
    evalBool σ (ofDNF (truthTableDNF n f)) = f (fun i : Fin n => σ i) := by
  rw [eval_ofDNF]
  by_cases h : f (fun i : Fin n => σ i) = true
  · rw [h]
    exact (evalDNF_truthTable σ n f).mpr h
  · have hf : f (fun i : Fin n => σ i) = false := by
      cases hh : f (fun i : Fin n => σ i) <;> simp_all
    have hd : evalDNF σ (truthTableDNF n f) = false := by
      by_contra hne
      have hdt : evalDNF σ (truthTableDNF n f) = true := by
        cases hh : evalDNF σ (truthTableDNF n f) with
        | false => exact absurd hh hne
        | true => rfl
      exact h ((evalDNF_truthTable σ n f).mp hdt)
    rw [hf, hd]

/-- **完备性**：任意 `n` 元布尔函数都可由一个 `BoolExpr` 表达。 -/
theorem completeness (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ e : BoolExpr, ∀ σ : ℕ → Bool, evalBool σ e = f (fun i : Fin n => σ i) :=
  ⟨ofDNF (truthTableDNF n f), ofTruthTable_spec n f⟩

/-- 只使用 `∧`、`∨`、`¬` 的语法谓词。 -/
def OnlyAndOrNot : BoolExpr → Prop
  | .var _ => True
  | .and e₁ e₂ => OnlyAndOrNot e₁ ∧ OnlyAndOrNot e₂
  | .or e₁ e₂ => OnlyAndOrNot e₁ ∧ OnlyAndOrNot e₂
  | .not e => OnlyAndOrNot e
  | .impl _ _ => False

theorem lit_onlyAndOrNot (p : ℕ × Bool) : OnlyAndOrNot (lit p) := by
  obtain ⟨n, b⟩ := p
  cases b <;> simp [lit, OnlyAndOrNot]

theorem ofClause_onlyAndOrNot (l : LitClause) : OnlyAndOrNot (ofClause l) := by
  induction l with
  | nil => simp [ofClause, truth, OnlyAndOrNot]
  | cons p l ih => simp [ofClause, OnlyAndOrNot, lit_onlyAndOrNot, ih]

theorem ofDNF_onlyAndOrNot (d : DNF) : OnlyAndOrNot (ofDNF d) := by
  induction d with
  | nil => simp [ofDNF, falsity, OnlyAndOrNot]
  | cons l d ih => simp [ofDNF, OnlyAndOrNot, ofClause_onlyAndOrNot, ih]

/-- **`{∧,∨,¬}` 功能完备**：任意 `n` 元布尔函数都可由只含 `∧`、`∨`、`¬` 的式子表达。 -/
theorem and_or_not_complete (n : ℕ) (f : (Fin n → Bool) → Bool) :
    ∃ e : BoolExpr, OnlyAndOrNot e ∧ ∀ σ : ℕ → Bool, evalBool σ e = f (fun i : Fin n => σ i) :=
  ⟨ofDNF (truthTableDNF n f), ofDNF_onlyAndOrNot _, ofTruthTable_spec n f⟩

end Lattice.Lib.Compiler.RealBoolCompleteness
