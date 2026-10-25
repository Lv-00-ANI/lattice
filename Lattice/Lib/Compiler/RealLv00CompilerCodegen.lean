import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerIR
/-! # RealLv00CompilerCodegen

拆分自 `RealLv00Compiler.lean`（第 308–369 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 三、编译器（自 Lv-00 `Compiler.lean`，整理后搬运） -/

/-- 点 → (名, 坐标) 对。`(B)`。 -/
def compile_point (p : lvPoint) : String × (ℝ × ℝ) := (p.name, (p.x, p.y))

/-- 点列表 → 环境映射。`(B)`。
注意：后出现者覆盖先出现者（`go` 把新点放在 `else` 分支之后），
与 `addPoint` 的「重名报错」语义**不一致**——Lv-00 未说明此不一致。
**关键**：此函数在编译管道中**从未被调用**（见 §7 降级 D5）。 -/
def compile_points (ps : List lvPoint) : String → ℝ × ℝ :=
  let rec go (acc : String → ℝ × ℝ) (pts : List lvPoint) : String → ℝ × ℝ :=
    match pts with
    | [] => acc
    | p :: rest =>
      let (n, coord) := compile_point p
      go (fun s => if s = n then coord else acc s) rest
  go (fun _ => (0, 0)) ps

/-- 约束编译（12 种 name-dispatch，按 arity 匹配）。`(B)` 规格定义。
**注意 关键诚实标注**：`distance`/`radius`/`ratioDivision` 的数值载荷被**硬编码为 `(.const 0)`**，
`angle` 被编译为**恒真占位** `(.const 0) = (.const 0)`（源码注释自述 *「等价于不施加额外 IR 约束」*）。
⇒ 编译**丢弃了源约束的全部数值信息**，因此**不可能是语义保持的**（§7 降级 D1 的直接证据）。 -/
def compile_constraint (_ps : List lvPoint) (c : lvConstraint) : Option IRConstraint :=
  match c.kind with
  | .collinear => match c.args with | [a, b, c'] => some (.collinear a b c') | _ => none
  | .parallel => match c.args with | [a, b, c', d] => some (.parallel a b c' d) | _ => none
  | .perpendicular =>
      match c.args with | [a, b, c', d] => some (.perpendicular a b c' d) | _ => none
  | .distance => match c.args with | [a, b] => some (.distance a b (.const 0)) | _ => none
  | .angle => match c.args with | [_a, _b, _c', _d] => some (.eq_expr (.const 0) (.const 0)) | _ => none
  | .midpoint => match c.args with | [m, a, b] => some (.midpoint m a b) | _ => none
  | .rightAngle => match c.args with | [a, b, c'] => some (.rightAngle a b c') | _ => none
  | .equalLength => match c.args with | [a, b, c', d] => some (.equalLength a b c' d) | _ => none
  | .equalAngle =>
      match c.args with | [a, b, c', d, e, f] => some (.equalAngle a b c' d e f) | _ => none
  | .radius => match c.args with | [c', a] => some (.radius c' a (.const 0)) | _ => none
  | .tangent =>
      match c.args with | [c_ctr, c_pt, la, lb] => some (.tangent c_ctr c_pt la lb) | _ => none
  | .ratioDivision =>
      match c.args with | [p, a, b] => some (.ratioDivision p a b (.const 0)) | _ => none

/-- 单语句编译。`(B)` 规格定义（`point`/`prove`/`normalize` 不产生 IR）。 -/
def compile_stmt (c : lvStmt) (ps : List lvPoint) : List IRConstraint :=
  match c with
  | .point _ => []
  | .constraint cst => match compile_constraint ps cst with | some ir => [ir] | none => []
  | .prove => []
  | .normalize => []

/-- 程序编译的递归辅助。`(B)`（`point` 语句把点压入 `pts`，但 `compile_constraint` **忽略** `_ps`）。
实现上按语句直接分派（不用 `let`），以便 `simp only [compile_program_go]` 能顺利归约 `match`。 -/
def compile_program_go (pts : List lvPoint) (rest : lvProgram) : List IRConstraint :=
  match rest with
  | [] => []
  | .point p :: sts => compile_stmt (.point p) pts ++ compile_program_go (p :: pts) sts
  | .constraint c :: sts => compile_stmt (.constraint c) pts ++ compile_program_go pts sts
  | .prove :: sts => compile_stmt .prove pts ++ compile_program_go pts sts
  | .normalize :: sts => compile_stmt .normalize pts ++ compile_program_go pts sts

/-- 程序编译。`(B)`。 -/
def compile_program (prog : lvProgram) : CompilerConstraintGraph := compile_program_go [] prog


end Lattice.Lv00.Compiler
