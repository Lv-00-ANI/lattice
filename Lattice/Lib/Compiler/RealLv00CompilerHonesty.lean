import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerSat
/-! # RealLv00CompilerHonesty

拆分自 `RealLv00Compiler.lean`（第 1234–1307 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 七、诚实降级（本项目新增的**机器验证反例**）

本节条目**不属于 Lv-00 原产**，是本项目按 `doc/10-falsified-proposition-playbook.md`
纪律对 Lv-00 声称的**证伪**。每条都给出机器验证的反例或机器验证的退化事实。 -/

/-- **降级 D1（Lv-00 声称「编译保持语义」为假）**：
`compile_constraint` 把 `distance [a,b]`（**无载荷**）编译为 `distance a b (const 0)`，
即「a 与 b 重合」。于是**两个不同的点**满足源约束（源侧无约束）却不满足编译产物。
⇒ 同环境方向的语义保持**不成立**。 -/
theorem D1_compile_loses_distance_value :
    ¬ ir_sem (fun s => if s = "a" then ((1 : ℝ), 0) else (0, 0)) (.distance "a" "b" (.const 0)) := by
  simp only [ir_sem, eval_expr, dist, ptX, ptY]
  intro h
  have h1 : Real.sqrt ((1 - 0) ^ 2 + ((0 : ℝ) - 0) ^ 2) = 0 := h
  rw [show ((1 : ℝ) - 0) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 by norm_num, Real.sqrt_one] at h1
  exact one_ne_zero h1

/-- **降级 D1'（编译丢弃约束名）**：只需 kind 与 arity 相同，编译结果就完全相同——
源约束的**名字**在编译产物中消失。 -/
theorem D1_compile_ignores_constraint_name (n1 n2 : VarName) (a b : VarName) :
    compile_constraint [] { name := n1, kind := .distance, args := [a, b] } =
    compile_constraint [] { name := n2, kind := .distance, args := [a, b] } := rfl

/-- **降级 D2'（桥接引理对源程序无信息）**：
退化环境满足**任意**两个点名（甚至不同点）的编译后距离约束——
即 `compile_bridge_sem` 的内容与 `c`、`pts` 完全无关。 -/
theorem D2_bridge_independent_of_source (a b : VarName) :
    ir_sem (fun _ => ((0 : ℝ), (0 : ℝ))) (.distance a b (.const 0)) := by
  simp [ir_sem, dist, eval_expr, ptX]

/-- **降级 D2''**：退化环境满足**任意点名的任意组合**的中点约束，
说明桥接引理的「证明」实质是「把所有点压到原点」。 -/
theorem D2_bridge_midpoint_trivial (m a b : VarName) :
    ir_sem (fun _ => ((0 : ℝ), (0 : ℝ))) (.midpoint m a b) := by
  simp [ir_sem, ptX, ptY]

/-- **降级 D3（`angle` 约束被编译为恒真占位，语义完全丢失）**：
`compile_constraint` 把 `angle` 编译为 `.eq_expr (.const 0) (.const 0)`。 -/
theorem D3_angle_compiles_to_tautology (ps : List lvPoint) (a b c d : VarName) :
    compile_constraint ps { name := "A", kind := .angle, args := [a, b, c, d] } =
    some (.eq_expr (.const 0) (.const 0)) := rfl

/-- **降级 D3'**：上述占位约束在任意环境下为真（「恒真占位」名副其实）。 -/
theorem D3_angle_placeholder_always_true (env : String → ℝ × ℝ) :
    ir_sem env (.eq_expr (.const 0) (.const 0)) := by
  simp [ir_sem, eval_expr]

/-- **降级 D4（`IRExpr.var` 只读 x 坐标 ⇒ 表达式层是一维投影）**：
两个 y 坐标不同、x 坐标相同的点在 IR 表达式层**不可区分**——
`IRExpr` 无法表达任何依赖 y 的约束。 -/
theorem D4_eval_expr_ignores_y :
    eval_expr (fun s => if s = "p" then ((3 : ℝ), 5) else (0, 0)) (.var "p") =
    eval_expr (fun s => if s = "p" then ((3 : ℝ), 9) else (0, 0)) (.var "p") := by
  simp [eval_expr, ptX]

/-- **降级 D4'**：更强的表述——`eval_expr` 对变量求值**完全不看 y**。 -/
theorem D4_eval_expr_eq_fst (env : String → ℝ × ℝ) (v : String) :
    eval_expr env (.var v) = (env v).1 := rfl

/-- **降级 D5（编译是无状态重写，点环境从未进入编译产物）**：
`compile_constraint` 的第一个参数 `_ps` 被下划线标记为**未使用**；
这里机器验证：点列表参数对编译结果**完全无影响**。因此 Lv-00 的「编译」不建立任何
「点名 → 坐标」的绑定，`compile_points`（构造环境）在编译管道中**从未被调用**。 -/
theorem D5_point_env_never_enters_compilation (ps : List lvPoint) (c : lvConstraint) :
    compile_constraint ps c = compile_constraint [] c :=
  congrFun (compile_constraint_ps_irrelevant ps []) c

/-- **降级 D6（`tangent` 语义过弱）**：
`ir_sem` 的 `tangent` 只要求直线上**存在一点**落在圆上，
而非「直线与圆相切」（唯一公共点）。在退化环境（圆退化为一个点）下，
**任意**两条直线都「满足」该约束——语义过弱。 -/
theorem D6_tangent_sem_too_weak :
    ir_sem (fun _ => ((0 : ℝ), (0 : ℝ))) (.tangent "o" "p" "l1" "l2") :=
  ⟨0, by simp [ir_sem, dist, ptX, ptY]⟩

end Lattice.Lv00.Compiler
