import Lattice.Lib.Compiler.AnalyticRow

/-!
# **把选择逻辑上提到解析层：能力层的选择成为它的**特例**

## 为什么必须上提

**第 1077 轮把「解析能力」与「符号证据」分开，但**选择逻辑仍只存在于能力层**：
`sufficient` 与 `select` 的类型都是 `CapabilityRow`。**
**⇒ 后果是荒谬的：解析层覆盖**任意度数**，却**无法被选择**。**

**⇒ 本文件把选择逻辑放到**最小假设**下（只需要 `covers` 与 `constant`），
再证明能力层的选择是它的**特例**（沿 `analytic_of_capability` 加细）。**

## 两层的关系应当是一条**等式**，不是一句类比

```lean
capability_select_is_analytic :
    (select req rows).map analytic_of_capability
      = analyticSelect (toAnalyticReq req) (rows.map analytic_of_capability)
```

**⇒ 这条等式的含义是：**在能力表上选择的加细** 与 **在加细后的解析表上选择** 是同一件事。
⇒ 若它不成立，两层就是两套逻辑；若成立，「符号层只是解析层的加细」才有内容。**
-/

namespace Lattice.Lib.Compiler.AnalyticSelection

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.CapabilityTable
open Lattice.Lib.Compiler.AnalyticRow

/-- **解析层的请求**：只要目标函数、精度与网格。**⇒ 不需要符号项，也不需要配方。** -/
structure AnalyticRequest where
  /-- The target function. -/
  goal : ℝ → ℝ
  /-- The requested uniform precision on `[0,1]`. -/
  eps : ℝ
  /-- The grid resolution. -/
  n : ℕ
  /-- The grid is non-degenerate. -/
  hn : 0 < n

/-- **解析层的充分条件**：族的归属与代价。**⇒ 与能力层同一个形状，但不需要符号证据。** -/
def analyticSufficient (row : AnalyticRow) (req : AnalyticRequest) : Prop :=
  row.covers req.goal ∧ row.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps

/-- **⭐⭐ 解析层的充分条件 ⟹ 整域达标本。** -/
theorem analytic_sufficient_implies_meets (row : AnalyticRow) (req : AnalyticRequest)
    (h : analyticSufficient row req) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps := by
  obtain ⟨hcov, hcost⟩ := h
  intro x hx
  exact le_trans (row.covers_bound req.goal hcov req.n req.hn x hx) hcost

/-- **解析层的选择器**。 -/
noncomputable def analyticSelect (req : AnalyticRequest) (rows : List AnalyticRow) :
    Option AnalyticRow := by
  classical
  exact rows.find? (fun row => decide (analyticSufficient row req))

/-- **⭐⭐ 被选中的解析行满足充分条件。** -/
theorem analytic_select_sound {req : AnalyticRequest} {rows : List AnalyticRow}
    {row : AnalyticRow} (h : analyticSelect req rows = some row) : analyticSufficient row req := by
  classical
  unfold analyticSelect at h
  exact of_decide_eq_true
    (List.find?_some (p := fun row => decide (analyticSufficient row req)) h)

/-- **⭐⭐⭐ 解析层的主定理：被选中的行整域达到请求精度。**

**⇒ 与能力层的 `select_gives_precision` 同形，但**假设更少**（无符号证据）。
⇒ 故能力层那条其实是**这一条的特例**——见 `capability_select_is_analytic`。** -/
theorem analytic_select_gives_precision {req : AnalyticRequest} {rows : List AnalyticRow}
    {row : AnalyticRow} (h : analyticSelect req rows = some row) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |req.goal x - gridEval (interpFamily req.n req.goal) req.n x| ≤ req.eps :=
  analytic_sufficient_implies_meets row req (analytic_select_sound h)

/-! ## 一、能力层的选择是解析层选择的特例 -/

/-- **把能力层的请求弱化为解析层的请求**。 -/
def toAnalyticReq (req : Request) : AnalyticRequest :=
  ⟨req.goal, req.eps, req.n, req.hn⟩

/-- **⭐⭐加细后的请求下，两层的充分条件**逻辑等价**。

**⇒ 这条是一个 `Iff`，而不是一句类比：它说「同一个行在两层里被判为充分的条件相同」。
⇒ 而它之所以成立，是因为 `analytic_of_capability` **逐字段保留**了 `covers` 与 `constant`。** -/
theorem analyticSufficient_of_capability (row : CapabilityRow) (req : Request) :
    analyticSufficient (analytic_of_capability row) (toAnalyticReq req)
      ↔ sufficient row req := by
  unfold analyticSufficient sufficient applicable toAnalyticReq
  rfl

/-- **⭐⭐⭐ **能力层选中的行**，就是解析层在加细表上选中的那个行。

**⇒ 这是本文件的收口：两层不是两套逻辑，而是同一套逻辑在**两个假设强度**下的两次执行。** -/
theorem capability_select_is_analytic (req : Request) (rows : List CapabilityRow) :
    (select req rows).map analytic_of_capability
      = analyticSelect (toAnalyticReq req) (rows.map analytic_of_capability) := by
  classical
  induction rows with
  | nil => rfl
  | cons r rest ih =>
      -- **两边都按「表头是否充分」分支。**
      by_cases h : sufficient r req
      · have h' : analyticSufficient (analytic_of_capability r) (toAnalyticReq req) :=
          (analyticSufficient_of_capability r req).mpr h
        have hp : decide (sufficient r req) = true := decide_eq_true h
        have hp' : decide (analyticSufficient (analytic_of_capability r) (toAnalyticReq req))
            = true := decide_eq_true h'
        simp only [select, analyticSelect, List.find?_cons, hp, hp', if_true, Option.map,
          List.map]
      · have h' : ¬ analyticSufficient (analytic_of_capability r) (toAnalyticReq req) :=
          fun hc => h ((analyticSufficient_of_capability r req).mp hc)
        have hp : decide (sufficient r req) = false := decide_eq_false h
        have hp' : decide (analyticSufficient (analytic_of_capability r) (toAnalyticReq req))
            = false := decide_eq_false h'
        simp only [select, analyticSelect, List.find?_cons, hp, hp', if_false, List.map]
        exact ih

/-! ## 二、解析层的落点：任意度数都能被**选中** -/

/-- **解析层的度数表**：度数 `d` 从 `2` 开始，每个度数一行。

**⇒ 为何从 `2` 开始：`0` 与 `1` 没有“近似”的意义（仿射是**精确**的，它在能力层里）。
⇒ 因此解析层从二次起记录近似族。** -/
noncomputable def powRowsTo : ℕ → List AnalyticRow
  | 0 => []
  | (n + 1) => powRowsTo n ++ (if h : 2 ≤ n then [powAnalyticRow n h] else [])

/-- **⭐ `powRowsTo 6` 的具体形状**：度数 `2,3,4,5` 四行。** -/
theorem powRowsTo_six :
    powRowsTo 6
      = [powAnalyticRow 2 (by norm_num), powAnalyticRow 3 (by norm_num),
         powAnalyticRow 4 (by norm_num), powAnalyticRow 5 (by norm_num)] := by
  simp [powRowsTo, Nat.reduceLeDiff]

/-! ## 三、五次目标落在五次行上 -/

/-- **⭐ `t⁵` 与 `t²`、`t³`、`t⁴` 都不同**（均在 `t = 2` 处）。** -/
theorem five_ne_two : (fun t : ℝ => t ^ 5) ≠ (fun t : ℝ => t ^ 2) := by
  intro h
  have h2 : (2 : ℝ) ^ 5 = (2 : ℝ) ^ 2 := by simpa using congrFun h 2
  norm_num at h2

/-- **⭐ `t⁵ ≠ t³`。** -/
theorem five_ne_three : (fun t : ℝ => t ^ 5) ≠ (fun t : ℝ => t ^ 3) := by
  intro h
  have h2 : (2 : ℝ) ^ 5 = (2 : ℝ) ^ 3 := by simpa using congrFun h 2
  norm_num at h2

/-- **⭐ `t⁵ ≠ t⁴`。** -/
theorem five_ne_four : (fun t : ℝ => t ^ 5) ≠ (fun t : ℝ => t ^ 4) := by
  intro h
  have h2 : (2 : ℝ) ^ 5 = (2 : ℝ) ^ 4 := by simpa using congrFun h 2
  norm_num at h2

/-- **⭐⭐⭐ 五次目标在解析层落到**五次行**。

**⇒ 路径与能力层完全同形：三次 `find?_cons_of_neg` 跳过 `t²`/`t³`/`t⁴`，
再 `find?_cons_of_pos` 取 `t⁵`。**
**⇒ 故它说明的是「任意度数**可被选中**」这件事的具体一例，
而不是又一条存在性陈述。** -/
theorem quintic_lands (n : ℕ) (hn : 0 < n) (eps : ℝ)
    (heps : ((5 * (5 - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2 ≤ eps) :
    analyticSelect ⟨(fun t : ℝ => t ^ 5), eps, n, hn⟩ (powRowsTo 6)
      = some (powAnalyticRow 5 (by norm_num)) := by
  classical
  rw [powRowsTo_six]
  unfold analyticSelect
  -- **第一次跳过：`t²` 行不适用于 `t⁵`。**
  rw [List.find?_cons_of_neg]
  · rw [List.find?_cons_of_neg]
    · rw [List.find?_cons_of_neg]
      · apply List.find?_cons_of_pos
        apply decide_eq_true
        constructor
        · show (powAnalyticRow 5 (by norm_num)).covers (fun t : ℝ => t ^ 5)
          rfl
        · show (powAnalyticRow 5 (by norm_num)).constant * (1 / (n : ℝ)) ^ 2 ≤ eps
          show ((5 * (5 - 1) : ℕ) : ℝ) / 8 * (1 / (n : ℝ)) ^ 2 ≤ eps
          exact heps
      · have hf : decide (analyticSufficient (powAnalyticRow 4 (by norm_num))
            ⟨(fun t : ℝ => t ^ 5), eps, n, hn⟩) = false :=
          decide_eq_false (by
            intro hs
            exact five_ne_four hs.1)
        simpa using hf
    · have hf : decide (analyticSufficient (powAnalyticRow 3 (by norm_num))
          ⟨(fun t : ℝ => t ^ 5), eps, n, hn⟩) = false :=
        decide_eq_false (by
          intro hs
          exact five_ne_three hs.1)
      simpa using hf
  · have hf : decide (analyticSufficient (powAnalyticRow 2 (by norm_num))
        ⟨(fun t : ℝ => t ^ 5), eps, n, hn⟩) = false :=
      decide_eq_false (by
        intro hs
        exact five_ne_two hs.1)
    simpa using hf

end Lattice.Lib.Compiler.AnalyticSelection