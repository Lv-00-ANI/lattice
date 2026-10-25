import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerLanguage
/-! # RealLv00CompilerIR

拆分自 `RealLv00Compiler.lean`（第 187–307 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 二、中间表示 IR（自 Lv-00 `IR.lean`，整理后搬运）

原文件 `lvFormal/Theory/IR.lean`。几何基元（`dist`/`dot`/`cross`）与
`ir_sem` 的 15 个构造子全部搬运。 -/

/-- 点 x 坐标。`(B)`。 -/
def ptX (p : ℝ × ℝ) : ℝ := p.1

/-- 点 y 坐标。`(B)`。 -/
def ptY (p : ℝ × ℝ) : ℝ := p.2

/-- 两点欧氏距离。`(B)`。
**与 mathlib 的重复项**：mathlib 有 `dist`（度量空间距离）与 `EuclideanSpace`；
本定义是 `ℝ × ℝ` 上 `Prod` 实例的特化写法。保留是为了**逐字对齐 Lv-00 语义**，
但属于重复建设（见 §8 重复清单）。 -/
def dist (p q : ℝ × ℝ) : ℝ := Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

/-- 二维点积。`(B)`。**与 mathlib 重复**：`inner`。 -/
def dot (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

/-- 二维叉积（标量）。`(B)`。mathlib 的 `crossProduct` 是 3 维的，此处为**新定义**。 -/
def cross (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

/-- IR 表达式。`(B)` 规格定义。 -/
inductive IRExpr where
  | var (name : String)
  | const (value : ℝ)
  | add (e1 e2 : IRExpr)
  | sub (e1 e2 : IRExpr)
  | mul (e1 e2 : IRExpr)
  | div (e1 e2 : IRExpr)
  | sqrt (e : IRExpr)
  deriving DecidableEq

/-- IR 表达式求值。
**注意 诚实标注**：`var n` 求值为 `ptX (env n)`——**只取 x 坐标**。
这意味着 IR 表达式层是**一维投影**的：`IRExpr` 无法表达 y 坐标。
Lv-00 未对此作任何说明（见 §7 降级 D4）。 -/
def eval_expr (env : String → ℝ × ℝ) : IRExpr → ℝ
  | .var n => ptX (env n)
  | .const v => v
  | .add e1 e2 => eval_expr env e1 + eval_expr env e2
  | .sub e1 e2 => eval_expr env e1 - eval_expr env e2
  | .mul e1 e2 => eval_expr env e1 * eval_expr env e2
  | .div e1 e2 => eval_expr env e1 / eval_expr env e2
  | .sqrt e => Real.sqrt (eval_expr env e)

/-- IR 约束（15 个构造子）。`(B)` 规格定义。 -/
inductive IRConstraint where
  | distance (a b : String) (d : IRExpr)
  | collinear (a b c : String)
  | perpendicular (a b c d : String)
  | parallel (a b c d : String)
  | angle (a b c d : String) (theta : IRExpr)
  | eq_expr (e1 e2 : IRExpr)
  | lt_expr (e1 e2 : IRExpr)
  | gt_expr (e1 e2 : IRExpr)
  | radius (center a : String) (r : IRExpr)
  | tangent (circle_center circle_pt line_a line_b : String)
  | midpoint (m a b : String)
  | rightAngle (a b c : String)
  | equalLength (a b c d : String)
  | equalAngle (a b c d e f : String)
  | ratioDivision (p a b : String) (r : IRExpr)
  deriving DecidableEq

/-- IR 约束的 ℝ 语义。`(B)` 规格定义（15 条语义规则，是本包**真正有价值**的接口形式）。 -/
def ir_sem (env : String → ℝ × ℝ) : IRConstraint → Prop
  | .distance a b d => dist (env a) (env b) = eval_expr env d
  | .collinear a b c => cross (env a - env b) (env c - env b) = 0
  | .perpendicular a b c d =>
      dot (ptX (env a) - ptX (env b), ptY (env a) - ptY (env b))
          (ptX (env c) - ptX (env d), ptY (env c) - ptY (env d)) = 0
  | .parallel a b c d =>
      cross (ptX (env a) - ptX (env b), ptY (env a) - ptY (env b))
            (ptX (env c) - ptX (env d), ptY (env c) - ptY (env d)) = 0
  | .angle a b c d theta =>
      Real.cos (eval_expr env theta) =
        dot (ptX (env b) - ptX (env a), ptY (env b) - ptY (env a))
            (ptX (env d) - ptX (env c), ptY (env d) - ptY (env c)) /
        (dist (env a) (env b) * dist (env c) (env d))
  | .eq_expr e1 e2 => eval_expr env e1 = eval_expr env e2
  | .lt_expr e1 e2 => eval_expr env e1 < eval_expr env e2
  | .gt_expr e1 e2 => eval_expr env e1 > eval_expr env e2
  | .radius c a r => dist (env c) (env a) = eval_expr env r
  | .tangent ctr pt la lb =>
      ∃ t : ℝ, dist (env ctr) (ptX (env la) + t * (ptX (env la) - ptX (env lb)),
                                  ptY (env la) + t * (ptY (env la) - ptY (env lb)))
                 = dist (env ctr) (env pt)
  | .midpoint m a b =>
      ptX (env m) = (ptX (env a) + ptX (env b)) / 2 ∧
      ptY (env m) = (ptY (env a) + ptY (env b)) / 2
  | .rightAngle a b c =>
      dot (ptX (env a) - ptX (env b), ptY (env a) - ptY (env b))
          (ptX (env c) - ptX (env b), ptY (env c) - ptY (env b)) = 0
  | .equalLength a b c d => dist (env a) (env b) = dist (env c) (env d)
  | .equalAngle a b c d e f =>
      dot (ptX (env b) - ptX (env a), ptY (env b) - ptY (env a))
          (ptX (env d) - ptX (env c), ptY (env d) - ptY (env c)) /
        (dist (env a) (env b) * dist (env c) (env d)) =
      dot (ptX (env e) - ptX (env f), ptY (env e) - ptY (env f))
          (ptX (env b) - ptX (env a), ptY (env b) - ptY (env a)) /
        (dist (env e) (env f) * dist (env a) (env b))
  | .ratioDivision p a b r =>
      ∃ t : ℝ, t = eval_expr env r ∧
        ptX (env p) = ptX (env a) + t * (ptX (env b) - ptX (env a)) ∧
        ptY (env p) = ptY (env a) + t * (ptY (env b) - ptY (env a))

/-- 约束图 = IR 约束列表。`(B)`。 -/
abbrev CompilerConstraintGraph := List IRConstraint

/-- 图在环境 `env` 下被满足。`(B)`。 -/
def graph_satisfied (g : CompilerConstraintGraph) (env : String → ℝ × ℝ) : Prop := ∀ c ∈ g, ir_sem env c

/-- 图可满足。`(B)`。 -/
def graph_satisfiable (g : CompilerConstraintGraph) : Prop := ∃ env, graph_satisfied g env

/-- 空图恒可满足。`(B)`（证明为构造退化环境 + 空列表消解，平凡但有接口价值）。 -/
theorem empty_graph_satisfiable : graph_satisfiable [] :=
  ⟨fun _ => (0, 0), by intro c hc; simp at hc⟩


end Lattice.Lv00.Compiler
