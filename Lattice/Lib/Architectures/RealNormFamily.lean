import Mathlib
import Lattice.Lib.Architectures.RealLayerNorm
import Lattice.Lib.Architectures.RealRMSNorm
/-!
# LATTICE: 规范化族类化 —— 缩放不变规范化（统一规律）

审计建议（research/audit/GENERALITY-AUDIT.md）与规范化调研
（research/real-world/norm-topk-family.md）的核心规律：

  **共享统计量 T(αx) = α·T(x) ⟹ 归一化缩放不变（ε=0）**

抽象为类：ScaleInvariantNorm n := ∀x α, 0<α → n(α·x) = n(x)。
「谁共享统计量」（token 内/组内/批内/无）是唯一分轴：
  · LayerNorm（T = √centerSq，token 内）
  · RMSNorm（T = RMS，token 内无中心化）
  · GroupNorm（T = 组内统计量，组内）——后续实例

本文件给出类的定义、统一规律（商归一化缩放不变）与 LN/RMS 实例，
消除两组重复证明（归一化族对输入缩放不敏感的通用性质）。
-/


noncomputable section

namespace Lattice

variable {ι : Type*} [Fintype ι]

/-! ## 缩放不变规范化类 -/

def ScaleInvariantNorm (n : (ι → ℝ) → (ι → ℝ)) : Prop :=
  ∀ x : ι → ℝ, ∀ α : ℝ, 0 < α → n (fun i => α * x i) = n x

/-! ## 定理一：统一规律 —— 共享统计量商归一化缩放不变
T(αx) = α·T(x)（统计量 1-齐次）⟹ 商归一化 x/T(x) 缩放不变。-/

omit [Fintype ι] in
theorem quotient_norm_scale_invariant (T : (ι → ℝ) → ℝ) (x : ι → ℝ) (α : ℝ)
    (hα : 0 < α) (hT : T (fun j => α * x j) = α * T x) :
    (fun i => α * x i / T (fun j => α * x j)) = fun i => x i / T x := by
  funext i
  rw [hT]
  -- α·xᵢ / (α·T) = xᵢ / T（α ≠ 0，无需 T x ≠ 0：除零两侧均为 0）
  exact mul_div_mul_left (x i) (T x) (ne_of_gt hα)

/-! ## 实例一：LayerNorm 是缩放不变族成员
normalize(αx) = normalize(x)（既有 normalize_scale_invariant）。-/

theorem layerNorm_in_family : ScaleInvariantNorm (fun x : ι → ℝ => normalize x) := by
  intro x α hα
  exact normalize_scale_invariant x α hα

/-! ## 实例二：RMSNorm 是缩放不变族成员
rmsNorm(αx) = rmsNorm(x)（既有 rmsNorm_scale_invariant）。-/

theorem rmsNorm_in_family : ScaleInvariantNorm (fun x : ι → ℝ => rmsNorm x) := by
  intro x α hα
  exact rmsNorm_scale_invariant x α hα

/-! ## 实例三（统一规律实例化）：RMSNorm 的统计量是 1-齐次
rms(αx) = α·rms(x)——商归一化的统一规律直接适用。-/

theorem rms_is_homogeneous (x : ι → ℝ) (α : ℝ) (hα : 0 ≤ α) :
    rms (fun i => α * x i) = α * rms x := rms_scale x α hα

/-! ## 推论：由统一规律重推 RMSNorm 缩放不变
（展示类抽象消除重复证明：商归一化定理 + 齐次统计量 ⟹ 实例性质，
无需逐文件重证。）-/

theorem rmsNorm_scale_invariant_via_family (x : ι → ℝ) (α : ℝ) (hα : 0 < α) :
    (fun i => α * x i / rms (fun j => α * x j)) = fun i => x i / rms x := by
  -- 统一规律 + rms 齐次（hα > 0 ⟹ ≥ 0）
  exact quotient_norm_scale_invariant rms x α hα (rms_is_homogeneous x α (le_of_lt hα))

/-! ## 注：GroupNorm 实例化（调研推荐）
GroupNorm 的统计量是「组内」的（T_G(x) = sqrt(Σ_{i∈G} xᵢ²/|G|)），
组内缩放不变由同一统一规律给出——本文件确立类，组实例化见后续。 -/

end Lattice
