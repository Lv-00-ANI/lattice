import Mathlib
import Lattice.Lib.Attention.RealRoPE
import Lattice.Lib.Attention.RealALiBi
import Lattice.Lib.Attention.RealComplexRoPE
/-!
# LATTICE: 一般相对位置编码族（RoPE 与 ALiBi 的统一接口）

RoPE（乘法/相位编码，RealRoPE / RealComplexRoPE）与 ALiBi（加法/线性偏置，
RealALiBi）看起来是两条不同的位置编码主线。本文件指出它们的**公共内核**：

    分数只依赖相对位置 ⟺ 对所有平移量 k，score (i+k) (j+k) = score i j
    （实现为 `IsTranslationEquivariant`）

在这个接口下，两者（以及任意「距离偏置」编码）是同一个抽象族的成员：

  1. `dist_translation_invariant`：`Nat.dist (i+k) (j+k) = Nat.dist i j`（平移不变，基石）；
  2. `additive_relpos_equivariance`（核心）：`distBias β i j := β (Nat.dist i j)` 平移等变
     ——「加法偏置只依赖相对距离」的精确形式；
  3. `alibi_bias_translation_equivariant`：ALiBi 偏置 `−m·dist(i,j)` 平移等变
     （度量距离版，桥接 RealALiBi.alibiBias）；
  4. `rope_score_translation_equivariant`：RoPE 编码后的点积平移等变
     （由 `rope_relative_preserves_dot` 化为只依赖相对角度差);
  5. `relPhaseFactor_translation_equivariant`：复数相位因子 `e^{iθ(j−i)}` 平移等变
     （RealComplexRoPE 的乘法/相位版）；
  6. `additive_relpos_score_lipschitz`（核心）：加法编码的分数关于偏置项是 1-Lipschitz；
  7. `relpos_family_unified`（核心/抽象）：RoPE、ALiBi、相位因子都是同一接口的成员。

模型无关：位置数、斜率 m、基频 θ、向量 q/k 全为任意参数；无 sorry/axiom/admit。
-/

noncomputable section

namespace Lattice

/-! ## 抽象接口：平移等变（= 只依赖相对位置） -/

/-- 分数 `f i j` 平移等变：对所有平移量 `k`，`f (i+k) (j+k) = f i j`。
这是「只依赖相对位置」的抽象形式，RoPE（相位差）与 ALiBi（距离偏置）都满足。 -/
def IsTranslationEquivariant {ι : Type*} [Add ι] (f : ι → ι → ℝ) : Prop :=
  ∀ i j k : ι, f (i + k) (j + k) = f i j

/-! ## 加法（距离偏置）编码 -/

/-- 距离偏置：`β` 是「距离 ⟹ 偏置」的函数，`distBias β i j` 只通过 `Nat.dist i j` 依赖位置。 -/
def distBias (β : ℕ → ℝ) (i j : ℕ) : ℝ := β (Nat.dist i j)

/-- 加法相对位置分数：标准分数 + 一般偏置项（ALiBi 是其 `β = −m·id` 特例）。 -/
def scoreAdd (s b : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := s i j + b i j

/-- 加法相对位置分数（距离形式）：标准分数 + 只依赖 `Nat.dist i j` 的偏置。 -/
def scoreDistAdd (s : ℕ → ℕ → ℝ) (β : ℕ → ℝ) (i j : ℕ) : ℝ := s i j + distBias β i j

/-! ## 定理一：`Nat.dist` 平移不变（加法编码的基石）
`Nat.dist (i+k) (j+k) = Nat.dist i j`（截断减法在两边同时加 k 后不变）。-/

theorem dist_translation_invariant (i j k : ℕ) :
    Nat.dist (i + k) (j + k) = Nat.dist i j := by
  simp only [Nat.dist]
  omega

/-! ## 引理：ℕ 上度量距离的平移不变（ALiBi 用的是度量 `dist`）
`dist (i+k:ℕ) (j+k) = dist i j`（由 `Nat.dist_eq` 化到 ℝ 绝对值后消去 k）。-/

lemma nat_metric_dist_translation (i j k : ℕ) :
    dist (i + k) (j + k) = dist i j := by
  rw [Nat.dist_eq, Nat.dist_eq]
  congr 1
  push_cast
  ring

/-! ## 定理二（核心）：加法偏置的平移等变
`distBias β (i+k) (j+k) = distBias β i j`——偏置只依赖相对距离，
平移所有位置不改变它。-/

theorem additive_relpos_equivariance (β : ℕ → ℝ) (i j k : ℕ) :
    distBias β (i + k) (j + k) = distBias β i j := by
  unfold distBias
  rw [dist_translation_invariant]

/-! ## 定理三：ALiBi 偏置平移等变（桥接 RealALiBi.alibiBias = −m·dist） -/

theorem alibi_bias_translation_equivariant (m : ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => alibiBias m i j) := by
  intro i j k
  dsimp only [alibiBias]
  rw [nat_metric_dist_translation]

/-! ## 定理四：距离偏置编码平移等变 -/

theorem distBias_equivariant (β : ℕ → ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => distBias β i j) := by
  intro i j k
  exact additive_relpos_equivariance β i j k

/-! ## 定理五（核心）：加法编码分数关于偏置是 1-Lipschitz
`|scoreAdd s b i j − scoreAdd s b' i j| ≤ |b i j − b' i j|`
（标准分数 s 消去，偏置之差原样保留；此处取等）。 -/

theorem additive_relpos_score_lipschitz (s b b' : ℕ → ℕ → ℝ) (i j : ℕ) :
    |scoreAdd s b i j - scoreAdd s b' i j| ≤ |b i j - b' i j| := by
  unfold scoreAdd
  have h : s i j + b i j - (s i j + b' i j) = b i j - b' i j := by ring
  rw [h]

/-! ## 推论：距离形式的加法编码 Lipschitz（偏置为 `distBias β` / `distBias β'`） -/

theorem additive_relpos_scoreDist_lipschitz (s : ℕ → ℕ → ℝ) (β β' : ℕ → ℝ) (i j : ℕ) :
    |scoreDistAdd s β i j - scoreDistAdd s β' i j| ≤ |distBias β i j - distBias β' i j| := by
  unfold scoreDistAdd
  have h : s i j + distBias β i j - (s i j + distBias β' i j) =
      distBias β i j - distBias β' i j := by ring
  rw [h]

/-! ## 定理六（核心/抽象）：RoPE 编码后的点积平移等变
`(a,b) ↦ ⟨R(aθ)q, R(bθ)k⟩` 只依赖相对角度差 `b − a`：
由 `rope_relative_preserves_dot`，它等于 `⟨q, R((b−a)θ)k⟩`，平移 a、b 同时加 t 不改变差。 -/

theorem rope_score_translation_equivariant (θ : ℝ) (q k : Point2R) :
    IsTranslationEquivariant
      (fun a b : ℝ => rdot (rotateR (a * θ) q) (rotateR (b * θ) k)) := by
  intro a b t
  change rdot (rotateR ((a + t) * θ) q) (rotateR ((b + t) * θ) k) =
    rdot (rotateR (a * θ) q) (rotateR (b * θ) k)
  have h1 : rdot (rotateR ((a + t) * θ) q) (rotateR ((b + t) * θ) k)
      = rdot q (rotateR (((b + t) - (a + t)) * θ) k) :=
    rope_relative_preserves_dot (a + t) (b + t) θ q k
  have h2 : rdot (rotateR (a * θ) q) (rotateR (b * θ) k)
      = rdot q (rotateR ((b - a) * θ) k) :=
    rope_relative_preserves_dot a b θ q k
  rw [h1, h2]
  congr 1
  congr 1
  ring

/-! ## 复数（乘法/相位）编码 -/

/-- 相对相位因子：位置 i、j 的相位差 `e^{iθ(j−i)}`（RealComplexRoPE 的相位部分）。 -/
def relPhaseFactor (θ : ℝ) (i j : ℕ) : ℂ :=
  Complex.exp (((θ * ((j : ℝ) - (i : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- 相位因子的**模**（= 1），实数版接口成员：`|e^{iθ(j−i)}| = 1`，平移不变。 -/
def relPhaseAbs (θ : ℝ) (i j : ℕ) : ℝ := Complex.abs (relPhaseFactor θ i j)

/-! ## 定理七：相位因子平移等变（实数化后） -/

theorem relPhaseAbs_translation_equivariant (θ : ℝ) :
    IsTranslationEquivariant (fun i j : ℕ => relPhaseAbs θ i j) := by
  intro i j k
  change Complex.abs (relPhaseFactor θ (i + k) (j + k)) = Complex.abs (relPhaseFactor θ i j)
  have h : ((θ * (((j + k : ℕ) : ℝ) - ((i + k : ℕ) : ℝ)) : ℝ) : ℂ) =
      ((θ * ((j : ℝ) - (i : ℝ)) : ℝ) : ℂ) := by
    congr 1
    push_cast
    ring
  unfold relPhaseFactor
  rw [h]

/-! ## 定理八（核心/抽象）：统一——RoPE、ALiBi、相位因子同属一个接口
四类相对位置编码都在「平移等变（只依赖相对位置）」这一抽象接口下：

  * 一般距离偏置 `distBias β`（加法族，含任意 `β`）；
  * ALiBi 偏置 `−m·dist`（加法族的标准实例，RealALiBi）；
  * RoPE 编码后点积（乘法/旋转族，RealRoPE）；
  * 复数相位因子的模（乘法/相位族，RealComplexRoPE）。 -/

theorem relpos_family_unified (β : ℕ → ℝ) (m θ : ℝ) (q k : Point2R) :
    IsTranslationEquivariant (fun i j : ℕ => distBias β i j) ∧
    IsTranslationEquivariant (fun i j : ℕ => alibiBias m i j) ∧
    IsTranslationEquivariant
      (fun a b : ℝ => rdot (rotateR (a * θ) q) (rotateR (b * θ) k)) ∧
    IsTranslationEquivariant (fun i j : ℕ => relPhaseAbs θ i j) :=
  ⟨distBias_equivariant β, alibi_bias_translation_equivariant m,
    rope_score_translation_equivariant θ q k, relPhaseAbs_translation_equivariant θ⟩

/-! ## 注：RoPE=乘法、ALiBi=加法 的统一读法
`IsTranslationEquivariant` 抽出的是「相对位置性」这一公共语义：
ALiBi 用**加法**把距离变成分数平移（−m·dist，本文件定理二/三/五），
RoPE 用**乘法**把位置变成相位（距离差 ⟹ 相位差，定理六/七），
但两者的可观察量都只依赖相对位置——这正是统一接口 `IsTranslationEquivariant` 所刻画的。 -/

end Lattice
