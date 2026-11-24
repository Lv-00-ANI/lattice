import Lattice.Lib.Compiler.PolyTable

/-!
# **从「选中的行」到「可求值的产物」：最后一针**

## 这一层为什么必须存在

**能力层挑出的 `row` 携带 `semantics` / `compiled` / `family_eq`：它说「哪个符号项、编译到哪个目标、
族的插值是什么」。而 `select_gives_precision` 直接跳到 `gridEval`，**跳过了产物的 `evalAt`**。**

**⇒ 于是「能力选择」的输出仍是一个**抽象的行**，而不是一个**可以求值的产物**。
⇒ 本文件补这一段：用 `row.target` 造 `EvaluatedArtifact`，并证明**该产物的 `evalAt` 满足该行的界**。**

## 一个必须说清的边界

**`covers` 不一定是单元素族。`affineFamilyRow` 覆盖**所有**仿射函数，而它的代表项是 `0·t+0`。
⇒ 因此由它造出的产物求值的是 `0·t+0`，**不是**调用者的目标 `c·t+d`（尽管两者都是仿射）。**

**⇒ 所以本文件分两步，而不是一步到位：**
1. `selected_row_artifact_bound`：产物求值满足**该行自己的**界（对 `row.fn`）；
2. `selected_row_artifact_meets_request`：当 `row.fn = req.goal`（单元素族）时，它满足**请求的精度**。

**⇒ 把这两个情形分开，是为了不让「族行」冒充「具体行」——那正是第 1065 轮修掉的缺陷。**
-/

namespace Lattice.Lib.Compiler.ArtifactStitch

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.CapabilityTable
open Lattice.Lib.Compiler.PolyTable
open Lattice.Lib.Compiler

/-- **⭐ 逐点相等的两个族有相同的网格求值。**

**⇒ 这条是本节唯一的技术性引理：`Target.family` 与 `interpFamily` 只保证**逐点**相等（`family_eq`），
而 `gridEval` 要按**同一段号**取值，故需要把逐点相等搬到求值上。** -/
theorem gridEval_congr {g h : ℕ → Segment} (hg : ∀ k, g k = h k) (n : ℕ) (x : ℝ) :
    gridEval g n x = gridEval h n x := by
  unfold gridEval
  rw [hg]

/-- **⭐⭐⭐ 由选中行造出的产物，其求值满足**该行自己的界**。**

**⇒ `row.family_eq` 把产物的族换成 `interpFamily req.n row.fn`，再由 `gridEval_congr` 搬到求值上，
最后 `row.bound` 给出界。⇒ 三步都是引用，没有一步是新的分析。** -/
theorem selected_row_artifact_bound (req : Request) (rows : List CapabilityRow)
    (row : CapabilityRow) (h : select req rows = some row)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family ⟨req.n, req.hn⟩ row.target) dom ⟨req.n, req.hn⟩).evalAt x = some v →
      |row.fn x - v| ≤ row.constant * (1 / (req.n : ℝ)) ^ 2 := by
  intro v hv
  -- **\u4ea7\u7269\u5951\u7ea6\uff1a\u6c42\u503c\u5c31\u662f\u8be5\u65cf\u7684\u7f51\u683c\u6c42\u503c\u3002**
  rw [Lattice.Lib.Compiler.EvaluatedArtifact.evalAt_ofSegments] at hv
  have hsome : gridEval (Target.family ⟨req.n, req.hn⟩ row.target) req.n x = v :=
    Option.some.inj hv
  -- **把 `v` 换成那个网格求值（`hsome` 的方向是右到左）。**
  rw [← hsome]
  -- **\u628a\u4ea7\u7269\u7684\u65cf\u6362\u6210\u8be5\u884c\u7684\u63d2\u503c\u65cf\u3002**
  have hfam : ∀ k, Target.family ⟨req.n, req.hn⟩ row.target k = interpFamily req.n row.fn k :=
    fun k => row.family_eq ⟨req.n, req.hn⟩ k
  rw [gridEval_congr hfam req.n x]
  exact row.bound req.n req.hn x hx

/-- **⭐⭐⭐ 当该行的代表项**就是**请求的目标时，产物满足**请求的精度**。

**⇒ 这一条把三段接起来：选择（`sufficient`）→ 产物（`ofSegments`）→ 精度（`req.eps`）。**
**⇒ 与上一条的区别仅在 `hfn : row.fn = req.goal`：**族行不满足它**，故族行只得到自身界。** -/
theorem selected_row_artifact_meets_request (req : Request) (rows : List CapabilityRow)
    (row : CapabilityRow) (h : select req rows = some row) (hfn : row.fn = req.goal)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family ⟨req.n, req.hn⟩ row.target) dom ⟨req.n, req.hn⟩).evalAt x = some v →
      |req.goal x - v| ≤ req.eps := by
  intro v hv
  have hb := selected_row_artifact_bound req rows row h dom x hx v hv
  rw [hfn] at hb
  -- **\u5145\u5206\u6761\u4ef6\u4ece\u9009\u62e9\u4e2d\u6765\u3002**
  have hsuf : sufficient row req := select_sound h
  have hcost : row.constant * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps := hsuf.2
  exact le_trans hb hcost

/-- **⭐⭐⭐ 端到端：二次目标 → 选中二次行 → 产物 → 精度。**

**⇒ 三个前提：目标是 `t²`、`1/4·(1/n)² ≤ eps`。
⇒ 结论是：由 `squareRow` 的目标所造的**产物**，其 `evalAt` 处处在 `eps` 内。**

**⇒ 这就是本文件存在的目的：此前能力层的输出是**一个行**，
而现在它的输出是**一个可求值的产物**加一条精度保证。** -/
theorem square_artifact_meets_request (req : Request)
    (hgoal : req.goal = fun t : ℝ => t ^ 2)
    (heps : 1 / 4 * (1 / (req.n : ℝ)) ^ 2 ≤ req.eps)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v : ℝ,
      (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
          (Target.family ⟨req.n, req.hn⟩ squareRow.target) dom ⟨req.n, req.hn⟩).evalAt x
        = some v →
      |req.goal x - v| ≤ req.eps := by
  have hsel : select req [affineFamilyRow, squareRow, cubeRow] = some squareRow :=
    select_quadratic_goal_lands_on_square req hgoal heps
  have hfn : squareRow.fn = req.goal := by
    rw [hgoal]
    rfl
  exact selected_row_artifact_meets_request req [affineFamilyRow, squareRow, cubeRow]
    squareRow hsel hfn dom x hx

end Lattice.Lib.Compiler.ArtifactStitch