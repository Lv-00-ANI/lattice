import Mathlib

/-! # RealLv00CompilerLanguage

拆分自 `RealLv00Compiler.lean`（第 76–186 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 一、源语言 `lvLang`（自 Lv-00 `lvLang.lean`，整理后搬运）

原文件 `lvFormal/Theory/lvLang.lean`。此处只搬运编译管道**实际引用**的部分：
语法（点 / 约束 / 语句 / 程序）、状态、大步语义。
`eval_point_preserves_other` 等 8 条状态引理属于 H4（语义/DSL）主题，此处不取。 -/

/-- 变量名。`(B)` 原为 `abbrev VarName := String`。 -/
abbrev VarName := String

/-- 坐标（实数）。`(B)` 原为 `abbrev Coord := ℝ`。 -/
abbrev Coord := ℝ

/-- Lv-00 点：变量名 + 二维坐标。`(B)` 规格定义，编译器的输入单位。 -/
structure lvPoint where
  /-- 点名 -/
  name : VarName
  /-- x 坐标 -/
  x : Coord
  /-- y 坐标 -/
  y : Coord
  deriving DecidableEq

/-- Lv-00 约束种类（12 种）。`(B)` 规格定义——**注意它不含任何数值载荷**，
这是 §7 降级 D1 的根源。 -/
inductive lvConstraintKind where
  | collinear | parallel | perpendicular | distance | angle | midpoint
  | rightAngle | equalLength | equalAngle | radius | tangent | ratioDivision
  deriving DecidableEq

/-- Lv-00 约束：唯一名称 + 种类 + 参数点名列表。`(B)` 规格定义。 -/
structure lvConstraint where
  /-- 约束名 -/
  name : VarName
  /-- 约束种类 -/
  kind : lvConstraintKind
  /-- 关联点名 -/
  args : List VarName
  deriving DecidableEq

/-- Lv-00 语句。`(B)` 规格定义。 -/
inductive lvStmt where
  | point (p : lvPoint)
  | constraint (c : lvConstraint)
  | prove
  | normalize
  deriving DecidableEq

/-- Lv-00 程序 = 语句序列。`(B)`。 -/
abbrev lvProgram := List lvStmt

/-- 程序执行状态。`(B)` 规格定义。 -/
structure State where
  /-- 已定义的点 -/
  points : List lvPoint
  /-- 已加入的约束 -/
  constraints : List lvConstraint
  /-- 是否已进入 prove 模式 -/
  proveFlag : Bool
  /-- 是否已归一化 -/
  normalizeFlag : Bool
  /-- 诊断信息 -/
  errors : List String

/-- 初始状态。`(B)`。 -/
def initialState : State :=
  { points := [], constraints := [], proveFlag := false, normalizeFlag := false, errors := [] }

/-- 加点（重名则记错误）。`(B)` 语义规则。 -/
def addPoint (s : State) (p : lvPoint) : State :=
  if s.points.any (fun q => q.name = p.name) then
    { s with errors := ("duplicate point name: " ++ p.name) :: s.errors }
  else { s with points := p :: s.points }

/-- 加约束（重名则记错误）。`(B)` 语义规则。 -/
def addConstraint (s : State) (c : lvConstraint) : State :=
  if s.constraints.any (fun d => d.name = c.name) then
    { s with errors := ("duplicate constraint name: " ++ c.name) :: s.errors }
  else { s with constraints := c :: s.constraints }

/-- 置 prove 标志（重复则记错误）。`(B)`。 -/
def setProve (s : State) : State :=
  if s.proveFlag then { s with errors := "duplicate prove statement" :: s.errors }
  else { s with proveFlag := true }

/-- 置 normalize 标志（重复则记错误）。`(B)`。 -/
def setNormalize (s : State) : State :=
  if s.normalizeFlag then { s with errors := "duplicate normalize statement" :: s.errors }
  else { s with normalizeFlag := true }

/-- 单条语句求值。`(B)` 大步语义。 -/
def eval_stmt (s : State) : lvStmt → State
  | .point p => addPoint s p
  | .constraint c => addConstraint s c
  | .prove => setProve s
  | .normalize => setNormalize s

/-- 程序求值：逐条执行。`(B)` 大步语义。 -/
def eval_program (s : State) : lvProgram → State
  | [] => s
  | st :: sts => eval_program (eval_stmt s st) sts

/-- 状态无错误。`(B)`。 -/
def no_errors (s : State) : Prop := s.errors = []

/-- Lv-00 的「可满足性」。
**注意 关键诚实标注（B，且近乎空洞）**：原定义注释为
*「状态无错误且所有约束在 ℝ² 坐标系下有解」*，但**实现只检查 `errors = []`**——
它**不涉及任何几何语义**，是一个**纯语法良构性谓词**。
文件名 `satisfiable` 因此是**误导性的**（这是 §7 降级 D2 的直接证据）。 -/
def satisfiable (s : State) : Prop := no_errors s


end Lattice.Lv00.Compiler
