import Mathlib
import Lattice.Lift.ComboN
/-!
# LATTICE: VerifyLoopProgress 收敛性 —— 真实修复器的最终满足

补上 VerifyLoopProgress.lean 标注的缺口：收敛性（∃ n，最终满足）。

真实修复器（非平凡）：对偶数判定约束 EvenSat，
  repairEven x = 若 x 偶数则保持，否则 x - 1（奇数降 1 变偶数）
度量（x 的奇偶）严格向满足推进：奇数 → 偶数（1 步收敛）。

证明：
  1. repairEven 保持已满足（满足时不动）；
  2. 奇数 x 一步修复为偶数（Nat.div_add_mod）；
  3. 收敛定理：∀ x, ∃ n, EvenSat (iterateRepairEven n x)（偶数 0 步、奇数 1 步）；
  4. 一旦满足永久停留（保持性归纳）。

注意 **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`** —— 自相矛盾。
真实情况是：**本文件的表示层只用到 `Nat` 等核心类型**
（`EvenSat`、`repairEven`、`iterateRepairEven` 皆以 `Nat` 表达，不依赖 mathlib 的专用结构），
但**文件整体 import 了 Mathlib**。⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
另：本文件证明所用的 `omega`（`repairEven_odd_to_even`、`even_loop_converges`）并非 Lean core 内置，
而是 **Mathlib 提供的策略**（其可用性来自文件整体 import 的 Mathlib）。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/

namespace Lattice

open scoped Classical

/-! ## 偶数判定约束（要点 R01 去重：改用单一权威源 `ComboN.EvenSat`）

原此处有 `def EvenSat (x : Nat) : Prop := x % 2 = 0`，与
`ComboN.lean:19`、`ConvertLinear.lean:99` **逐字相同**，构成三路命名冲突
（内核：`environment already contains 'Lattice.EvenSat'`）。
现由 `import ComboN` 提供，定义体零改动、调用点零改名。 -/

/-! ## 真实修复器：奇数降 1，偶数保持 -/

noncomputable def repairEven (x : Nat) : Nat :=
  if EvenSat x then x else x - 1

/-! ## 迭代 -/

noncomputable def iterateRepairEven : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => repairEven (iterateRepairEven n x)

/-! ## 引理一：奇数大于零（保证 x - 1 不下溢） -/

lemma odd_gt_zero (x : Nat) (h : x % 2 = 1) : 1 ≤ x := by
  by_contra hlt
  have hx : x = 0 := Nat.eq_zero_of_not_pos hlt
  simp [hx] at h

/-! ## 引理二：奇数一步修复为偶数
x % 2 = 1 → (x - 1) % 2 = 0。-/

lemma repairEven_odd_to_even (x : Nat) (h : x % 2 = 1) : EvenSat (x - 1) := by
  unfold EvenSat
  -- x = (x/2)*2 + 1（Nat.div_add_mod）
  have hdiv : x = x / 2 * 2 + x % 2 := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod x 2).symm
  rw [h] at hdiv
  have hx : x = x / 2 * 2 + 1 := hdiv
  -- 代入 x - 1
  have hsub : x - 1 = x / 2 * 2 := by omega
  rw [hsub]
  -- (k*2) % 2 = 0
  exact Nat.mul_mod_left (x / 2) 2

/-! ## 引理三：修复器保持已满足（满足时不动） -/

lemma repairEven_preserves (x : Nat) (h : EvenSat x) : EvenSat (repairEven x) := by
  unfold repairEven
  simp [h]

/-! ## 定理：收敛 —— 任意输入最终满足
偶数 0 步收敛，奇数 1 步收敛。-/

theorem even_loop_converges (x : Nat) : ∃ n : Nat, EvenSat (iterateRepairEven n x) := by
  -- 余数二分：x % 2 = 0 或 x % 2 = 1
  have hmod : x % 2 < 2 := Nat.mod_lt x (by decide)
  have hcases : x % 2 = 0 ∨ x % 2 = 1 := by
    omega
  rcases hcases with h0 | h1
  · -- x % 2 = 0：已满足，0 步
    exact ⟨0, by simp [iterateRepairEven, EvenSat, h0]⟩
  · -- x % 2 = 1：奇数，1 步修复
    refine ⟨1, ?_⟩
    simp [iterateRepairEven, repairEven, EvenSat, h1]
    exact repairEven_odd_to_even x h1

/-! ## 引理四：迭代次数可加
iterateRepairEven (n+m) x = iterateRepairEven m (iterateRepairEven n x)。-/

lemma iterateRepairEven_add (n m x : Nat) :
    iterateRepairEven (n + m) x = iterateRepairEven m (iterateRepairEven n x) := by
  induction m with
  | zero => simp [iterateRepairEven]
  | succ m ih =>
      calc
        iterateRepairEven (n + (m + 1)) x = iterateRepairEven ((n + m) + 1) x := by
          rw [Nat.add_assoc]
        _ = repairEven (iterateRepairEven (n + m) x) := by simp [iterateRepairEven]
        _ = repairEven (iterateRepairEven m (iterateRepairEven n x)) := by rw [ih]
        _ = iterateRepairEven (m + 1) (iterateRepairEven n x) := by simp [iterateRepairEven]

/-! ## 定理：一旦满足永久停留
满足后任意步迭代仍满足（收敛 + 保持 = 稳定不动点）。-/

theorem even_loop_stays (x : Nat) (n : Nat) (h : EvenSat x) :
    EvenSat (iterateRepairEven n x) := by
  induction n generalizing x with
  | zero => simpa [iterateRepairEven] using h
  | succ n ih => simpa [iterateRepairEven] using repairEven_preserves (iterateRepairEven n x) (ih x h)

/-! ## 推论：验证回路的最终状态是稳定满足点
存在步数使回路到达满足态，且之后保持——修复回路停机且结果可靠。-/

theorem even_loop_fixpoint (x : Nat) :
    ∃ n : Nat, EvenSat (iterateRepairEven n x) ∧
      ∀ m : Nat, EvenSat (iterateRepairEven (n + m) x) := by
  rcases even_loop_converges x with ⟨n, hn⟩
  exact ⟨n, hn, fun m => by
    rw [iterateRepairEven_add n m x]
    exact even_loop_stays (iterateRepairEven n x) m hn⟩

end Lattice
