import Mathlib
import Lattice.Lib.Chain.RealGeometry
/-!
# LATTICE: RoPE 相对位置保点积（纯参数化，模型无关）

transformer 调研（research/real-world/transformer-semantics.md 目标 C）：
RoPE（旋转位置编码）的核心性质——**相对位置保点积**

  ⟨R(mθ)·q, R(nθ)·k⟩ = ⟨q, R((n−m)θ)·k⟩

模型无关性：θ 是任意实数参数（任何基频实例化都成立），
q、k 是任意 2D 向量。不依赖任何具体模型的维度/基频配置。

证明：
  1. 2D 旋转 R(θ) 是正交变换：⟨Rθ q, Rθ k⟩ = ⟨q, k⟩（cos²+sin²=1）；
  2. 旋转组合：R(a)·R(b) = R(a+b)（cos_add/sin_add）；
  3. R(nθ) = R(mθ)·R((n−m)θ) ⟹ 保点积。
-/


noncomputable section

namespace Lattice

/-! ## 2D 旋转 -/

def rotateR (θ : ℝ) (p : Point2R) : Point2R :=
  { x := p.x * Real.cos θ - p.y * Real.sin θ
    y := p.x * Real.sin θ + p.y * Real.cos θ }

/-! ## 引理一：旋转是正交变换（同一角度）
⟨Rθ q, Rθ k⟩ = ⟨q, k⟩。-/

lemma rotate_preserves_dot (θ : ℝ) (q k : Point2R) :
    rdot (rotateR θ q) (rotateR θ k) = rdot q k := by
  unfold rdot rotateR
  dsimp
  -- 展开后需要 cos²+sin²=1
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  calc
    (q.x * Real.cos θ - q.y * Real.sin θ) * (k.x * Real.cos θ - k.y * Real.sin θ) +
        (q.x * Real.sin θ + q.y * Real.cos θ) * (k.x * Real.sin θ + k.y * Real.cos θ)
        = q.x * k.x * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          q.y * k.y * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = q.x * k.x + q.y * k.y := by rw [hcs]; ring

/-! ## 引理二：旋转组合
R(a)·R(b) = R(a+b)。-/

lemma rotate_compose (a b : ℝ) (p : Point2R) :
    rotateR a (rotateR b p) = rotateR (a + b) p := by
  unfold rotateR
  dsimp
  -- 需要 cos(a+b) = cos a cos b - sin a sin b
  have hcos : Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b := Real.cos_add a b
  -- 需要 sin(a+b) = sin a cos b + cos a sin b
  have hsin : Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b := Real.sin_add a b
  -- 按分量相等（x、y 两个投影）
  rw [Point2R.mk.injEq]
  constructor
  · rw [hcos, hsin]
    ring
  · rw [hcos, hsin]
    ring

/-! ## 定理：RoPE 相对位置保点积
⟨R(mθ)q, R(nθ)k⟩ = ⟨q, R((n−m)θ)k⟩，对任意 θ、m、n、q、k 成立（模型无关）。-/

theorem rope_relative_preserves_dot (m n θ : ℝ) (q k : Point2R) :
    rdot (rotateR (m * θ) q) (rotateR (n * θ) k) = rdot q (rotateR ((n - m) * θ) k) := by
  -- R(nθ) = R(mθ)·R((n-m)θ)（旋转组合）
  have hcompose : rotateR (n * θ) k = rotateR (m * θ) (rotateR ((n - m) * θ) k) := by
    have hsum : m * θ + (n - m) * θ = n * θ := by ring
    -- rotateR (nθ) k = rotateR (mθ + (n-m)θ) k = rotateR (mθ) (rotateR ((n-m)θ) k)
    calc
      rotateR (n * θ) k = rotateR (m * θ + (n - m) * θ) k := by rw [hsum]
      _ = rotateR (m * θ) (rotateR ((n - m) * θ) k) := (rotate_compose (m * θ) ((n - m) * θ) k).symm
  -- ⟨R(mθ)q, R(mθ)R((n-m)θ)k⟩ = ⟨q, R((n-m)θ)k⟩（正交）
  rw [hcompose]
  exact rotate_preserves_dot (m * θ) q (rotateR ((n - m) * θ) k)

/-! ## 推论：旋转是等距（位置编码稳定性的基础）
⟨Rθ p, Rθ q⟩ = ⟨p, q⟩ 已证（rotate_preserves_dot）——任意向量的旋转不变，
注意力分数的点积在位置编码下稳定。整向量块簿记（Fin n 分块旋转）为后续。-/

end Lattice
