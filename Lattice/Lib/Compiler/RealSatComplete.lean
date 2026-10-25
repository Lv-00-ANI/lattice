import Mathlib
import Lattice.Lib.Compiler.RealConstraintSat
/-!
# LATTICE: 完备判定 —— 有限候选集上的回溯搜索（DPLL 风格）

`RealConstraintSat` 在有限候选输入上给出 ℚ/ℤ 可满足性的 `Decidable` 实例
（`instDecidableQSatisfiableOn`）与逐点判定器 `qSatAllB`，但没有给出**搜索过程**本身。
本文件补上「DPLL 风格」的有限搜索，并证明它**可靠且完备**：

  1. `dpllSearch`：在 `List (R × R)`（约束列表，每条为 `a·x + b = 0`）与候选集
     `Finset R` 上的结构递归回溯搜索：空约束列表 ⟺ 候选集非空；否则对头部约束
     在候选中逐个试探，并把候选集收缩到当前取值 `{v}`（保证同一取值满足全部约束）；
  2. `dpllSearch_iff`（**核心**）：`= true ⟺ ∃ v ∈ cand, ∀ c ∈ cs, c.1 * v + c.2 = 0`；
  3. `dpllSearch_map`：把搜索提升到 `QConstraint`/`ZConstraint` 列表（取投影 `(a,b)`）；
  4. `dpllLikeSearch` / `dpllLikeSearch_iff`：ℚ 版入口；
  5. `dpllLikeSearchZ` / `dpllLikeSearchZ_iff`：ℤ 版入口（ℤ 上 `decide` 完全可归约）；
  6. `search_sound` / `search_complete`：搜索返回 `true` ⟺ 存在候选满足全部约束；
  7. `search_terminates`：搜索是 Bool 值结构递归函数，对任意输入都有返回值；
  8. `candidateSearch` / `candidateSearch_iff`：朴素的「遍历候选集」判定器（与搜索等价）；
  9. `sat_complete_decidable` / `sat_complete_decidable_z`：有限候选集上可满足性的
     **完全可判定**刻画（`⟺ dpll ... = true`）。

诚实标注（无 sorry / axiom / admit）：
- **ℝ 版不可计算**：本文件只做 ℚ/ℤ（甚至更一般的 `[DecidableEq R] [Mul R] [Add R] [Zero R]`）
  的有限候选集判定。ℝ 上线性算术的可判定性/可计算性不在本文件范围（不可计算）。
- 搜索的「DPLL 风格」指**对候选取值分支并收缩候选集**；本文件不做子句学习、
  单元传播或剪枝启发式，也不涉及 CNF/子句表示。
- 候选集有限是完备性的**前提**：`∃ v ∈ cand` 中的 `cand` 必须有限，
  否则 `Finset` 无从枚举。
-/

noncomputable section

namespace Lattice

/-! ## 一、通用回溯搜索 -/

/-- **DPLL 风格回溯搜索**：约束列表 `cs`（每条 `c.1 * x + c.2 = 0`）与候选集 `cand`。
空约束列表成立 ⟺ `cand` 非空；否则对头部约束在候选中逐个试探，
命中后把候选集收缩到 `{v}` 继续搜索剩余约束（保证同一 `v` 满足全部约束）。 -/
def dpllSearch {R : Type*} [DecidableEq R] [Zero R] [Add R] [Mul R] :
    List (R × R) → Finset R → Bool
  | [], cand => decide (0 < cand.card)
  | c :: rest, cand =>
      cand.toList.any (fun v => decide (c.1 * v + c.2 = 0) && dpllSearch rest {v})

/-- **搜索的可靠性 + 完备性（核心）**。 -/
theorem dpllSearch_iff {R : Type*} [DecidableEq R] [Zero R] [Add R] [Mul R]
    (cs : List (R × R)) (cand : Finset R) :
    dpllSearch cs cand = true ↔ ∃ v ∈ cand, ∀ c ∈ cs, c.1 * v + c.2 = 0 := by
  induction cs generalizing cand with
  | nil =>
      simp only [dpllSearch, decide_eq_true_eq, Finset.card_pos]
      constructor
      · intro h
        obtain ⟨v, hv⟩ := h
        exact ⟨v, hv, fun c hc => absurd hc (List.not_mem_nil c)⟩
      · rintro ⟨v, hv, -⟩
        exact ⟨v, hv⟩
  | cons c rest ih =>
      simp only [dpllSearch, List.any_eq_true, Finset.mem_toList]
      constructor
      · rintro ⟨v, hv, hb⟩
        rw [Bool.and_eq_true] at hb
        obtain ⟨hd, hr⟩ := hb
        have hcv : c.1 * v + c.2 = 0 := of_decide_eq_true hd
        obtain ⟨w, hw, hrest⟩ := (ih {v}).mp hr
        have hwv : w = v := by simpa using hw
        rw [hwv] at hrest
        refine ⟨v, hv, ?_⟩
        intro c' hc'
        rcases List.mem_cons.mp hc' with h | h
        · subst h; exact hcv
        · exact hrest c' h
      · rintro ⟨v, hv, hall⟩
        refine ⟨v, hv, ?_⟩
        rw [Bool.and_eq_true]
        exact ⟨decide_eq_true (hall c (by simp)),
          (ih {v}).mpr ⟨v, by simp, fun c' hc' => hall c' (by simp [hc'])⟩⟩

/-- **提升到结构列表**：约束以任意类型 `S` 给出、经 `g` 投影为 `(a,b)` 对。 -/
theorem dpllSearch_map {R S : Type*} [DecidableEq R] [Zero R] [Add R] [Mul R]
    (cs : List S) (g : S → R × R) (cand : Finset R) :
    dpllSearch (cs.map g) cand = true ↔ ∃ v ∈ cand, ∀ c ∈ cs, (g c).1 * v + (g c).2 = 0 := by
  rw [dpllSearch_iff]
  constructor
  · rintro ⟨v, hv, hall⟩
    exact ⟨v, hv, fun c hc => hall (g c) (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  · rintro ⟨v, hv, hall⟩
    refine ⟨v, hv, fun p hp => ?_⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact hall c hc

/-! ## 二、ℚ 版入口 -/

/-- ℚ 约束列表上的 DPLL 风格搜索（取投影 `(a,b)`）。 -/
def dpllLikeSearch (cs : QProgram) (cand : Finset ℚ) : Bool :=
  dpllSearch (cs.map fun c => (c.a, c.b)) cand

/-- **ℚ 版搜索刻画**：`= true ⟺ ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0`。 -/
theorem dpllLikeSearch_iff (cs : QProgram) (cand : Finset ℚ) :
    dpllLikeSearch cs cand = true ↔ ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0 := by
  unfold dpllLikeSearch
  exact dpllSearch_map cs (fun c => (c.a, c.b)) cand

/-- **搜索可靠**：返回 `true` 给出满足全部约束的候选。 -/
theorem search_sound (cs : QProgram) (cand : Finset ℚ)
    (h : dpllLikeSearch cs cand = true) :
    ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0 :=
  (dpllLikeSearch_iff cs cand).mp h

/-- **搜索完备**：若存在候选满足全部约束，则搜索返回 `true`。 -/
theorem search_complete (cs : QProgram) (cand : Finset ℚ)
    (h : ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0) :
    dpllLikeSearch cs cand = true :=
  (dpllLikeSearch_iff cs cand).mpr h

/-! ## 三、ℤ 版入口（`decide` 完全可归约） -/

/-- ℤ 约束列表上的 DPLL 风格搜索（取投影 `(a,b)`）。 -/
def dpllLikeSearchZ (cs : ZProgram) (cand : Finset ℤ) : Bool :=
  dpllSearch (cs.map fun c => (c.a, c.b)) cand

/-- **ℤ 版搜索刻画**：`= true ⟺ ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0`。 -/
theorem dpllLikeSearchZ_iff (cs : ZProgram) (cand : Finset ℤ) :
    dpllLikeSearchZ cs cand = true ↔ ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0 := by
  unfold dpllLikeSearchZ
  exact dpllSearch_map cs (fun c => (c.a, c.b)) cand

/-- ℤ 版搜索可靠。 -/
theorem search_sound_z (cs : ZProgram) (cand : Finset ℤ)
    (h : dpllLikeSearchZ cs cand = true) :
    ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0 :=
  (dpllLikeSearchZ_iff cs cand).mp h

/-- ℤ 版搜索完备。 -/
theorem search_complete_z (cs : ZProgram) (cand : Finset ℤ)
    (h : ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0) :
    dpllLikeSearchZ cs cand = true :=
  (dpllLikeSearchZ_iff cs cand).mpr h

/-! ## 四、终止性与朴素判定器 -/

/-- **搜索终止（平凡）**：搜索是 Bool 值结构递归函数，对任意输入返回 `true` 或 `false`。 -/
theorem search_terminates {R : Type*} [DecidableEq R] [Zero R] [Add R] [Mul R]
    (cs : List (R × R)) (cand : Finset R) :
    dpllSearch cs cand = true ∨ dpllSearch cs cand = false := by
  cases dpllSearch cs cand <;> simp

/-- **朴素判定器**：遍历候选集、逐个检查全部约束（`Finset.any` + `qSatAllB`）。 -/
def candidateSearch (cand : Finset ℚ) (cs : QProgram) : Bool :=
  cand.toList.any (fun v => qSatAllB cs v)

/-- 朴素判定器的刻画。 -/
theorem candidateSearch_iff (cand : Finset ℚ) (cs : QProgram) :
    candidateSearch cand cs = true ↔ ∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0 := by
  unfold candidateSearch
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hb⟩
    exact ⟨v, Finset.mem_toList.mp hv, (qSatAllB_iff cs v).mp hb⟩
  · rintro ⟨v, hv, hall⟩
    exact ⟨v, Finset.mem_toList.mpr hv, (qSatAllB_iff cs v).mpr hall⟩

/-- **ℚ 完全可判定性**：有限候选集上的可满足性等价于搜索返回 `true`。 -/
theorem sat_complete_decidable (cs : QProgram) (cand : Finset ℚ) :
    (∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0) ↔ dpllLikeSearch cs cand = true :=
  (dpllLikeSearch_iff cs cand).symm

/-- **ℤ 完全可判定性**：有限候选集上的可满足性等价于搜索返回 `true`。 -/
theorem sat_complete_decidable_z (cs : ZProgram) (cand : Finset ℤ) :
    (∃ v ∈ cand, ∀ c ∈ cs, c.a * v + c.b = 0) ↔ dpllLikeSearchZ cs cand = true :=
  (dpllLikeSearchZ_iff cs cand).symm

end Lattice
