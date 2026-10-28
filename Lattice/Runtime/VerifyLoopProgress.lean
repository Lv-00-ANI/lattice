import Mathlib
import Lattice.Runtime.ConvertLinear
/-!
# LATTICE: VerifyLoopProgress（最小版本）—— 验证回路不破坏已满足语义

doc/02 §4.3 的 `VerifyLoopProgress` 的最小实例：

验证回路（验证失败 → 修正 → 再验证）在迭代中**不破坏已满足的语义**：
若某输入已满足约束，任意步修正迭代后仍满足（修正保持性 + 归纳）。

这是回路正确性的基础性质：
- 修正操作 repair 保持已满足状态（repair_preserves）；
- 任意 n 步迭代保持（loop_preserves_semantics，归纳）。
- 收敛性（最终必满足）依赖具体 repair 的下降性，留待接入真实修正器。

  注意 **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
  真实情况是：**本文件的表示层与数学内容只用 `Int`/`Nat` 等核心类型**
  （`LinearConstraint` 为 `Int × Int`、满足语义 `ConstraintSat` 为 `Int` 上的等式、
  修正器对 `Int` 作用，均不依赖 mathlib 的专用结构），
  但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
  订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**

---

## 注意 平凡性声明（**R5 / P1-5，必读**）

注意 **本文件的修正器 `repair` 是**恒等函数**（`:repair`），因此以下三条定理
**平凡真（trivially true）—— 它们对 `repair` 本身不构成任何断言**：

| 定理 | 为什么平凡真 |
|:--|:--|
| `repair_preserves` | 证明体展开后逐字是 `h` 本身：它说的是 `ConstraintSat c x → ConstraintSat c x`（**`fun h => h` 形态**，见 `PROCESS.md` §2.2 / **B222.2**） |
| `loop_preserves_semantics` | `iterateRepair c n x` 在 `repair := id` 下**恒等于 `x`**，故它也只是 `h` 的换装 |
| `verify_stable` | 结论 `iterateRepair c 1 x = x` 在 `repair := id` 下即 `rfl` |

要点 **判据（B234.4「把已知结果做双射替换」）**：把 `repair` 换成**任意**函数后，
这三条**全部不再成立** —— 例如 `fun _ y => y + 1` 对约束 `⟨1, 0⟩`（解集 `{0}`）
**不保持** `ConstraintSat`。**故这三条的真值与 `repair` 的定义无关，只与
"`id` 是 `id`"有关。** 唯一被真正检验的东西是 `LinearConstraint` 上的
`ConstraintSat` 可展开，以及归纳骨架良构。

注意 **`:repair` 的约束参数 `c` 在三个证明体中均未被使用** —— 按 **B142/B216**
（`unused variable` 是"假设写松"的最强机械信号），这正是平凡性的**机械证据**：
本文件对 `c` 没有任何实质使用，因为恒等修正器不需要看约束。

注意 **不要**据此认为"验证回路保持语义"是错的或空洞的**命题** —— 它是**正确但在此实例上
退化的**陈述。真实内容需要**非恒等**的 `repair`，即要求它是解集上的**投影**：
（i）保持已满足点，**且**（ii）从任意点**有限步到达**解集。本文件的 `repair` 满足 (i)
而**完全违反 (ii)**。要点 这两条律的显式形式与一个可证的**非平凡实例**见
`_r5_p15_repair.lean`（探针，**未登记进 roots**）：其中 `IsRepair` 记录两律，
`id_is_not_a_repair_when_unsat_exists` 证明**恒等修正器在存在不满足点时不是修正器**。

注意 **收敛性的真实承担者**：`VerifyLoopConvergence.lean:73` `even_loop_converges` 用
**真实修复器** `repairEven`（奇数降 1）证明了 `∃ n, EvenSat (iterateRepairEven n x)`。
注意 **但它只对"偶数判定"这一个**具体实例**成立**，不是本文件的一般形式。
⇒ 一般收敛定理**未证**，理由是结构性的：`LinearConstraint` 上的 `ConstraintSat`
**未给出任何序/度量**，故"下降性"无量可依；补它需要先选一个度量（如 `|a·x+b|` 严格递减），
属新工作而非本最小版的接线。
-/



namespace Lattice

/-! ## 修正器：验证通过则保持，验证失败则施加修正（本最小版：保持）

注意 **本定义是恒等函数** ⟹ 下游三条定理**平凡真**（见文件头「平凡性声明」）。

注意 **`c` 参数有意保留但未使用** —— 签名与既有下游保持一致，**不得改动**
（PROCESS.md §3.2：改名/降强度会级联）。要点 **`c` 无处可用，正是平凡性的
机械证据**（**B142/B216**）：恒等修正器不需要看约束。
注意 用 `_c` 显式标注，**不**用 `set_option linter.unusedVariables false` 掩盖
（**B224.5 明确拒绝**）。 -/

def repair (_c : LinearConstraint) (x : Int) : Int :=
  x

/-! ## 迭代：repair 的 n 次迭代

注意 **在 `repair := id` 下本函数恒等于 `x`**（见 `iterateRepair_eq_self`）。 -/

def iterateRepair (c : LinearConstraint) : Nat → Int → Int
  | 0, x => x
  | n + 1, x => iterateRepair c n (repair c x)

/-- 注意 **平凡性的机械证明**：恒等修正器下，任意步迭代都不改变输入。

要点 这一条是 `loop_preserves_semantics` / `verify_stable` 平凡真的**共同根因**：
两者的 LHS 与 RHS 在 `ConstraintSat` 之下是同一个项。 -/
theorem iterateRepair_eq_self (c : LinearConstraint) (n : Nat) (x : Int) :
    iterateRepair c n x = x := by
  induction n with
  | zero => simp [iterateRepair]
  | succ n ih => simp [iterateRepair, repair, ih]

/-! ## 定理一：修正保持已满足状态
已满足的输入经 repair 后仍满足（修正不破坏既有语义）。

注意 **平凡真（trivially true）** —— 证明体逐字是 `h` 本身（**`fun h => h` 形态**，
**B222.2**）。把它换成 `repair := fun _ y => y + 1` 即**为假**（反例见
`_r5_p15_repair.lean` 的 `shift_by_one_fails_to_preserve`）⟹
**该定理的真值不依赖 `repair` 的定义**。 -/

theorem repair_preserves (c : LinearConstraint) (x : Int) (h : ConstraintSat c x) :
    ConstraintSat c (repair c x) := by
  simpa [repair] using h

/-! ## 定理二：任意步迭代保持已满足状态（回路正确性归纳）
从满足态出发，修正回路任意步后仍满足——验证回路不破坏已满足语义。

注意 **平凡真** —— 由 `iterateRepair_eq_self`，结论项与假设项是**同一个项**，
归纳只是走形式。 -/

theorem loop_preserves_semantics (c : LinearConstraint) (x : Int) (n : Nat)
    (h : ConstraintSat c x) : ConstraintSat c (iterateRepair c n x) := by
  rw [iterateRepair_eq_self]
  exact h

/-! ## 定理三：验证通过即停止（回路终止条件）
若验证通过（满足），回路无需再修正——验证器判定稳定。

注意 **平凡真** —— 结论即 `iterateRepair_eq_self c 1 x`，在 `repair := id` 下是 `rfl`。
注意 **`h` 参数有意保留但未使用**（同 `repair` 的 `_c`）：终止条件不依赖"是否已满足"，
因为恒等修正器**永远**不动 —— 这正是"验证通过即停止"在此实例上**无内容**的证据。 -/

theorem verify_stable (c : LinearConstraint) (x : Int) (_h : ConstraintSat c x) :
    iterateRepair c 1 x = x := by
  exact iterateRepair_eq_self c 1 x

/-! ## 定理四：不动点刻画（**唯一不含平凡性的结果**）
`x` 是 `repair c` 的不动点 ⟺ `x` 在 `c` 的迭代下静止。

注意 本条**不是**平凡真：它对 `repair` 的**任意**定义成立且**刻画**了不动点，
不预设 `repair = id`；但它同样**不声称**任何"收敛到满足"。 -/

theorem repair_fixpoint_iff_stationary (c : LinearConstraint) (x : Int) :
    repair c x = x ↔ ∀ n : Nat, iterateRepair c n x = x := by
  constructor
  · intro hfix n
    induction n with
    | zero => simp [iterateRepair]
    | succ n ih => simp [iterateRepair, ih, hfix]
  · intro h
    simpa [iterateRepair] using h 1

/-! ## 注：收敛性（最终必满足）——**未证，且理由是结构性的**

真实修正器需满足**两条律**：(i) 保持已满足点；(ii) 从任意点**有限步到达**解集。
才能在 Lean 中证明 `∃ n, ConstraintSat c (iterateRepair c n x)`。

注意 **为什么本文件证不了 (ii)**：`LinearConstraint` 上的 `ConstraintSat` 是
`c.a * x + c.b = 0`，本文件**没有为它配备任何序或度量** ⟹ "下降"无量可依。
补 (ii) 需先选定度量（如 `Int.natAbs (c.a * x + c.b)` 严格递减），属**新工作**。

注意 **已有但受限的真实修正器**：`VerifyLoopConvergence.lean:73` `even_loop_converges`
用 `repairEven`（奇数降 1 变偶数）证了 `∃ n, EvenSat (iterateRepairEven n x)` ——
**但只对"偶数判定"这一个实例**，不是本文件的一般形式。

要点 **两律与一个可证的非平凡实例**见探针 `_r5_p15_repair.lean`（**未进 roots**）：
`IsRepair`（两律）、`id_is_not_a_repair_when_unsat_exists`（恒等不是修正器）、
`repairTo` 系列（约束 `⟨1,-k⟩` 上的**真实**恒等外修正器，一步收敛）。 -/

end Lattice
