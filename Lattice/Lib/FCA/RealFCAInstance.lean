import Lattice.Lib.FCA.RealFCA
import Lattice.Lib.FCA.RealImplication
import Mathlib

/-!
# LATTICE: FCA ↔ 约束系统实例化 —— 提取方向落地桥

RealFCA（pan-meme 移植的概念格）实例化到 LATTICE 的约束系统：
满足关系 R x c = 「解 x 满足约束 c」（RealConstraintSat），
则 FCA 的提取语义落到约束世界：

  1. 单解概念：从单个解 x₀ 提取的概念
     (extent(intent{x₀}), intent{x₀}) 是稳定的形式概念
     （幂等：再提取不变）；
  2. 逻辑后承 = 内涵闭包：intent(extent(C)) 恰是 C 的全部
     逻辑后承（所有满足 C 的解也满足的约束）——连接
     RealImplication 的约束蕴含（impl_via_alignment）；
  3. 后承闭包幂等：约束集合的蕴含闭包是闭包算子（稳定）。

意义（提取方向）：WeightToSymbolEquivalence 的提取候选 =
约束集合 C 经满足关系提取概念；FCA 保证提取到闭包即稳定，
且闭包 = 逻辑后承（蕴含闭包）——「非线性层提取不可逆」的
约束落地：提取候选 → 概念闭包 → 幂等稳定。

模型无关：任意满足关系（此处实例化为 RealConstraintSat）。
-/

namespace Lattice

/-! ## 定理一：单解提取的稳定概念
从单个解 x₀ 提取的概念 (extent(intent{x₀}), intent{x₀}) 是
形式概念（幂等：再提取不变）。-/

theorem single_solution_constraint_concept (x₀ : ℝ) :
    IsFormalConcept (fun x c => RealConstraintSat c x)
      (extent (fun x c => RealConstraintSat c x)
        (intent (fun x c => RealConstraintSat c x) ({x₀} : Set ℝ)))
      (intent (fun x c => RealConstraintSat c x) ({x₀} : Set ℝ)) := by
  constructor
  · -- IsFormalConcept 首分量 O' = extent B：此处 O' 即定义为 extent(intent{x₀}) = extent B，
    -- 故首分量为定义性 rfl（原 closure_idempotent 引用与目标不匹配，已改为 rfl，语义不变）
    rfl
  · -- intent{x₀} = intent(extent(intent{x₀}))（内涵端闭包幂等）
    exact (intent_closure_idempotent (fun x c => RealConstraintSat c x) ({x₀} : Set ℝ)).symm

/-! ## 定理二：逻辑后承 = 内涵闭包
intent(extent(C)) 恰是 C 的全部逻辑后承：所有满足 C 的解
也满足的约束集合（连接约束蕴含 impl_via_alignment）。-/

theorem constraint_entailment_closure (C : Set RealConstraint) :
    intent (fun x c => RealConstraintSat c x) (extent (fun x c => RealConstraintSat c x) C)
      = {c : RealConstraint | ∀ x : ℝ, x ∈ extent (fun x c => RealConstraintSat c x) C → RealConstraintSat c x} := by
  rfl

/-! ## 定理三：后承闭包幂等（约束蕴含闭包稳定）
约束集合的蕴含闭包是闭包算子：intent(extent(intent(extent C))) = intent(extent C)。-/

theorem entailment_closure_idempotent (C : Set RealConstraint) :
    intent (fun x c => RealConstraintSat c x)
      (extent (fun x c => RealConstraintSat c x)
        (intent (fun x c => RealConstraintSat c x) (extent (fun x c => RealConstraintSat c x) C)))
      = intent (fun x c => RealConstraintSat c x) (extent (fun x c => RealConstraintSat c x) C) := by
  exact intent_closure_idempotent (fun x c => RealConstraintSat c x)
    (extent (fun x c => RealConstraintSat c x) C)

/-! ## 注：提取方向闭环
  满足关系（ConstraintSat）实例化 FCA ⟹ 提取候选 = 概念闭包：
  单解提取稳定（定理一）、逻辑后承 = 内涵闭包（定理二，
  连接约束蕴含）、蕴含闭包幂等（定理三）——「非线性层提取
  不可逆」的约束落地：提取到闭包即稳定，闭包 = 逻辑后承。
  衔接 WeightToSymbolEquivalence（提取候选稳定性判定）。-/

end Lattice
