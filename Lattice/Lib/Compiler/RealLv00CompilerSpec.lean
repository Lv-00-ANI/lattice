import Mathlib
import Lattice.Lib.Compiler.RealLv00CompilerReal
/-! # RealLv00CompilerSpec

拆分自 `RealLv00Compiler.lean`（第 646–968 行），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Compiler` 仍有效。

本模块重新声明了原文件的模块级设置：`noncomputable section`（原 :72）与
`namespace Lattice.Lv00.Compiler`（原 :74）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Compiler

/-! ## 五、(B) 规格声明 —— 编译边正确性（按原样保留，明确标注为规格）

原 `CompilerCorrectness.lean` §「语句编译边正确性」的 4 条。它们的证明体是
`rfl` 或一句 `simp [h]`——**这是规格声明，不是有分量的正确性定理**。
保留价值在于它们**钉死了 `compile_stmt` 的逐语句形状**（接口锚点）。 -/

/-- **(B) `point` 语句不产生 IR 约束**。规格声明（`rfl`）。 -/
theorem stmt_compiled_edge_correct_point (pts : List lvPoint) (p : lvPoint) :
    compile_stmt (.point p) pts = [] := rfl

/-- **(B) `constraint` 语句编译成功时产生单元素列表**。规格声明（一句 `simp`）。 -/
theorem stmt_compiled_edge_correct_constraint (pts : List lvPoint) (c : lvConstraint)
    (ir : IRConstraint) (h : compile_constraint pts c = some ir) :
    compile_stmt (.constraint c) pts = [ir] := by
  unfold compile_stmt; simp [h]

/-- **(B) `prove` 语句不产生 IR 约束**。规格声明（`rfl`）。 -/
theorem stmt_compiled_edge_correct_prove (pts : List lvPoint) :
    compile_stmt .prove pts = [] := rfl

/-- **(B) `normalize` 语句不产生 IR 约束**。规格声明（`rfl`）。 -/
theorem stmt_compiled_edge_correct_normalize (pts : List lvPoint) :
    compile_stmt .normalize pts = [] := rfl

/-! ### (B) 编译桥接引理 —— **明确标注为规格，且近乎空洞**

原 `compile_constraint_trivially_satisfied` / `compile_bridge_sem`。
**诚实评估**：这两条的证明体确实进行了 12 个 kind × arity 的穷举分派
（比 `rfl` 重），但**数学内容是平凡的**：它们证明的是
「退化环境 `fun _ => (0,0)` 满足编译产物」——而退化环境把**所有点压成同一个点**，
使共线 / 垂直 / 平行 / 中点 / 直角 / 等长 / 相切全部**恒真**。

更关键：**这两条对源约束毫无信息**（见 §7 降级 D2 的机器验证——
退化环境满足**任意**两点名的 `distance a b (const 0)`）。
故这是 **(B) 规格**，其地位等同于「退化环境是一个模型」，**不是语义保持定理**。 -/

/-- **(B/空洞) 退化环境满足 `compile_constraint` 能产生的每一种 IR 形状**。

`compile_constraint` 的输出形状是**有限枚举**的（12 种，见 §3）：
`.collinear`、`.parallel`、`.perpendicular`、`.distance _ _ (.const 0)`、
`.eq_expr (.const 0) (.const 0)`（angle 占位）、`.midpoint`、`.rightAngle`、
`.equalLength`、`.equalAngle`、`.radius _ _ (.const 0)`、`.tangent`、
`.ratioDivision _ _ _ (.const 0)`。

**这张表就是本包（B/空洞）类判定的全部内容**——它说明「退化环境是一个模型」，
而**与源约束的语义无关**。逐形状验证如下。 -/
theorem degenerate_collinear (a b c : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.collinear a b c) := by
  simp [ir_sem, cross, ptX, ptY]
theorem degenerate_parallel (a b c d : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.parallel a b c d) := by
  simp [ir_sem, cross, ptX, ptY]
theorem degenerate_perpendicular (a b c d : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.perpendicular a b c d) := by
  simp [ir_sem, dot, ptX, ptY]
theorem degenerate_distance_zero (a b : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.distance a b (.const 0)) := by
  simp [ir_sem, dist, eval_expr, ptX]
theorem degenerate_eq_expr_zero :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.eq_expr (.const 0) (.const 0)) := by
  simp [ir_sem, eval_expr]
theorem degenerate_midpoint (m a b : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.midpoint m a b) := by
  simp [ir_sem, ptX, ptY]
theorem degenerate_rightAngle (a b c : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.rightAngle a b c) := by
  simp [ir_sem, dot, ptX, ptY]
theorem degenerate_equalLength (a b c d : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.equalLength a b c d) := by
  simp [ir_sem, dist]
theorem degenerate_equalAngle (a b c d e f : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.equalAngle a b c d e f) := by
  simp [ir_sem, dot, dist, ptX, ptY]
theorem degenerate_radius_zero (c a : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.radius c a (.const 0)) := by
  simp [ir_sem, dist, eval_expr, ptX]
theorem degenerate_tangent (ctr pt la lb : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.tangent ctr pt la lb) :=
  ⟨0, by simp [ir_sem, dist, ptX, ptY]⟩
theorem degenerate_ratioDivision_zero (p a b : String) :
    ir_sem (fun _ => ((0:ℝ),(0:ℝ))) (.ratioDivision p a b (.const 0)) :=
  ⟨0, by simp [ir_sem, ptX, ptY, eval_expr]⟩

/-- **(B/空洞) 编译产物在退化环境（所有点坐标为零）下恒成立**。
按原样保留，但注明：证明**不依赖源约束的语义**，只依赖
`compile_constraint` 的输出形状 + 上述 12 条形状表的恒真性。

证明策略：`cases kind` 展开 `compile_constraint` 的外层 `match`，
再用 `cases args` 穷举 arity。**命中分支**由 `h : <构造子> = some ir` 经 `cases h`
把 `ir` **替换**成该构造子，交给上表对应引理；**未命中分支**由 `none ≠ some _` 收尾。

**注意 修法记录（F3）**：原实现把收尾写成
`first | (cases h; first | exact degenerate_* | …) | (simp [compile_constraint] at h)`，
**已实测失败**：报 **24 条 `unsolved goals`**（形状统一为 `h : IRConstraint.collinear … = ir ⊢ ir_sem (fun x => (0,0)) ir`）。
根因有二，**互相叠加**：

1. **`cases h` 在 `ir` 是局部假设时会朝错误方向消去**：`h : <具体构造子> = some ir` 中
   `ir` 是**局部假设**，`cases h` 消去 `ir`、把目标里的 `ir` 改成 `some …` ⟹
   目标变成 `ir_sem (fun _ => (0,0)) (some …)`，**不可证**（报 `unsolved goals` / `motive is not type correct`）。
   正解是用 **`injection h with h'`** 取出 `ir = <构造子>` 再 **`subst h'`**（见下）。
2. **`first` 组合子只要求「不报错」**：`(simp [compile_constraint] at h)` 在失败分支上会**成功化简 `h` 却留下未闭合的目标**，
   于是 `first` **静默回退**到该分支 ⟹ 24 条 error **全部伪装成"`cases` 分派失败"**，实为收尾未闭合。
   ⟹ 与 STYLE §4 的 `first` 条目同源：**`first` 不是"证完才算成功"，而是"没报错就算成功"**。 -/
theorem compile_constraint_degenerately_satisfied (c : lvConstraint) (ir : IRConstraint)
    (h : compile_constraint [] c = some ir) :
    ir_sem (fun _ => (0, 0)) ir := by
  -- 注意 **关键教训（F3）**：`cases … with | arm => tac` 的 `| arm =>` **各自作用域独立**，
  -- 尾部的 `<;>` **不会**作用到前面 arm 产生的目标上——这正是前几轮"收尾从不生效"的真因。
  -- 故**把收尾写进每个 arm 内部**：命中 arity 的 arm 直接给形状表引理，
  -- 其余 arm 用 `simp [compile_constraint] at h` 由 `none ≠ some _` 矛盾收尾。
  obtain ⟨_, kind, args⟩ := c
  cases kind with
  | collinear =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              exact degenerate_collinear a1 a2 a3
          | cons _ _ => simp [compile_constraint] at h
  | parallel =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                exact degenerate_parallel a1 a2 a3 a4
            | cons _ _ => simp [compile_constraint] at h
  | perpendicular =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                exact degenerate_perpendicular a1 a2 a3 a4
            | cons _ _ => simp [compile_constraint] at h
  | distance =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil =>
          · simp only [compile_constraint] at h
            injection h with h'
            subst h'
            exact degenerate_distance_zero a1 a2
        | cons _ _ => simp [compile_constraint] at h
  | angle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                exact degenerate_eq_expr_zero
            | cons _ _ => simp [compile_constraint] at h
  | midpoint =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              exact degenerate_midpoint a1 a2 a3
          | cons _ _ => simp [compile_constraint] at h
  | rightAngle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              exact degenerate_rightAngle a1 a2 a3
          | cons _ _ => simp [compile_constraint] at h
  | equalLength =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                exact degenerate_equalLength a1 a2 a3 a4
            | cons _ _ => simp [compile_constraint] at h
  | equalAngle =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil => simp [compile_constraint] at h
            | cons a5 r5 => cases r5 with
              | nil => simp [compile_constraint] at h
              | cons a6 r6 => cases r6 with
                | nil =>
                  · simp only [compile_constraint] at h
                    injection h with h'
                    subst h'
                    exact degenerate_equalAngle a1 a2 a3 a4 a5 a6
                | cons _ _ => simp [compile_constraint] at h
  | radius =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil =>
          · simp only [compile_constraint] at h
            injection h with h'
            subst h'
            exact degenerate_radius_zero a1 a2
        | cons _ _ => simp [compile_constraint] at h
  | tangent =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil => simp [compile_constraint] at h
          | cons a4 r4 => cases r4 with
            | nil =>
              · simp only [compile_constraint] at h
                injection h with h'
                subst h'
                exact degenerate_tangent a1 a2 a3 a4
            | cons _ _ => simp [compile_constraint] at h
  | ratioDivision =>
    cases args with
    | nil => simp [compile_constraint] at h
    | cons a1 r1 => cases r1 with
      | nil => simp [compile_constraint] at h
      | cons a2 r2 => cases r2 with
        | nil => simp [compile_constraint] at h
        | cons a3 r3 => cases r3 with
          | nil =>
            · simp only [compile_constraint] at h
              injection h with h'
              subst h'
              exact degenerate_ratioDivision_zero a1 a2 a3
          | cons _ _ => simp [compile_constraint] at h

/-- **(B/空洞) 编译桥接引理**：`compile_constraint pts c = some ir` ⟹
`ir` 在退化环境下成立。原文同名。**标注为规格**：对源程序无信息（§7 D2）。 -/
theorem compile_bridge_sem (c : lvConstraint) (pts : List lvPoint) (ir : IRConstraint)
    (h : compile_constraint pts c = some ir) : ir_sem (fun _ => (0, 0)) ir :=
  compile_constraint_degenerately_satisfied c ir
    (by rw [congrFun (compile_constraint_ps_irrelevant [] pts) c]; exact h)

/-- **(B/空洞) 「编译保持可满足性」——Lv-00 声称的核心定理**。
**注意 它是平凡真且与源程序无关的。** 如实标注：
- 假设 `satisfiable (eval_program initialState prog)` 展开为 `errors = []`（**纯语法**）；
- 证明体**没有用到该假设**；
- 结论由退化环境直接给出。
因此本条是**规格声明（近乎空洞）**，**不是**编译正确性定理。 -/
theorem compile_preserves_satisfiability (prog : lvProgram) :
    satisfiable (eval_program initialState prog) → graph_satisfiable (compile_program prog) := by
  intro _h_sat
  refine ⟨fun _ => (0, 0), ?_⟩
  intro ir hir
  rcases compile_program_contains_compiled_constraints prog ir hir with ⟨c, _hc, hcc⟩
  exact compile_constraint_degenerately_satisfied c ir hcc

/-- **(B/空洞，本采集包的「证伪钉」)** 上面的定理**不需要假设**也能成立。
这条把「假设未被使用」这一事实**机器化**：结论无条件为真。 -/
theorem compile_preserves_satisfiability_hypothesis_unused (prog : lvProgram) :
    graph_satisfiable (compile_program prog) := by
  refine ⟨fun _ => (0, 0), ?_⟩
  intro ir hir
  rcases compile_program_contains_compiled_constraints prog ir hir with ⟨c, _hc, hcc⟩
  exact compile_constraint_degenerately_satisfied c ir hcc


end Lattice.Lv00.Compiler
