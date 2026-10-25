import Mathlib

/-!
# LATTICE: 循环控制流 —— 不变量保持（约束程序的循环语义）

控制流三要素收官（顺序 AllSatisfied ✅、分支 RealBranch ✅、**循环本文件**）：

  循环不变量定理：若 P 是 f 的不变量（∀y, P y → P (f y)）且初始 P x，
  则 P 在 n 次迭代后保持（验证循环/修复循环的语义基础）：

    P (iterate f n x)

泛化：本文件只在抽象层给出上述全称命题（对任意谓词 P 与任意步函数成立），
  不作「约束满足」这一具体谓词的实例化：

  · 约束满足是 repair 的不变量——「已满足保持」即不变量特例，但该具体实例
    不在本文件：本文件既不 import 也不引用 VerifyLoopProgress/Convergence 的
    任何声明，其衔接须由 VerifyLoop 侧另行提供；
  · 循环输出的约束满足（不变量的具体化）同样留待验证侧实例化。

模型无关：任意类型、任意谓词、任意步函数。
-/

namespace Lattice

/-! ## 迭代（固定步循环） -/

def iterate {X : Type} (f : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => iterate f n (f x)

/-! ## 辅助引理：iterate 步进可交换
iterate f n (f x) = f (iterate f n x)（第 n 步的输入可提前应用）。-/

lemma iterate_step_swap {X : Type} (f : X → X) (n : Nat) (x : X) :
    iterate f n (f x) = f (iterate f n x) := by
  induction n generalizing x with
  | zero => simp [iterate]
  | succ n ih =>
      -- 归纳假设对任意输入成立：对 (f x) 应用即可（generalizing 已引入 x）
      exact ih (f x)

/-! ## 定理一：循环不变量保持（核心）
P 是 f 的不变量且初始 P x ⟹ P 在 n 次迭代后保持。-/

theorem invariant_preserves_iteration {X : Type} (P : X → Prop) (f : X → X)
    (n : Nat) (x : X) (hP : P x) (hstep : ∀ y : X, P y → P (f y)) :
    P (iterate f n x) := by
  induction n with
  | zero =>
      simpa [iterate] using hP
  | succ n ih =>
      -- iterate f (n+1) x = iterate f n (f x) = f (iterate f n x)
      change P (iterate f n (f x))
      rw [iterate_step_swap]
      exact hstep _ ih

/-! ## 定理二：满足性的循环不变量（衔接 VerifyLoop）
约束满足是 repair 的不变量 ⟹ 迭代修复后仍满足（已证 loop_preserves_semantics
的泛化：任意谓词不变量形式）。-/

theorem satisfaction_loop_invariant {X : Type} (P : X → Prop) (repair : X → X)
    (n : Nat) (x : X) (hP : P x) (hpres : ∀ y : X, P y → P (repair y)) :
    P (iterate repair n x) :=
  invariant_preserves_iteration P repair n x hP hpres

/-! ## 定理三：两个不变量的合取保持（不变量闭包）
P、Q 都是 f 的不变量 ⟹ P∧Q 也是（验证多性质循环）。-/

theorem invariant_conjunction {X : Type} (P Q : X → Prop) (f : X → X)
    (hP : ∀ y, P y → P (f y)) (hQ : ∀ y, Q y → Q (f y)) :
    ∀ y : X, (P y ∧ Q y) → (P (f y) ∧ Q (f y)) := by
  intro y hy
  exact ⟨hP y hy.1, hQ y hy.2⟩

/-! ## 定理四：复合循环的不变量保持
两步循环（f 后 g）的不变量：P 是 f、g 各自的不变量 ⟹ P 在 f∘g 迭代下保持。 -/

theorem invariant_composed_loop {X : Type} (P : X → Prop) (f g : X → X)
    (n : Nat) (x : X) (hP : P x)
    (hpf : ∀ y, P y → P (f y)) (hpg : ∀ y, P y → P (g y)) :
    P (iterate (fun y => g (f y)) n x) := by
  -- f∘g 的迭代保持：不变量在 f 与 g 下都保持 ⟹ 复合保持
  have hstep : ∀ y : X, P y → P (g (f y)) := fun y hy => hpg (f y) (hpf y hy)
  exact invariant_preserves_iteration P (fun y => g (f y)) n x hP hstep

end Lattice
