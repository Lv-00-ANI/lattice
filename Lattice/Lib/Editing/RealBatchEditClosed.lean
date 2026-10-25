import Lattice.Lib.Editing.RealBatchEdit
import Mathlib

/-!
# LATTICE: m 元正交批量编辑的精确闭式（batchN_pointwise_bound 的精确版）

VERIFICATION.md §5 展望「三层以上批量编辑闭式」：RealBatchEdit 的
`batchN_pointwise_bound` 对**任意**键只给逐点**上界**（三角不等式）：

    |BatchN(x) − W·x| ≤ Σᵢ |⟨kᵢ,x⟩|·|vᵢ−W·kᵢ|/‖kᵢ‖²

它是界，不是精确值。本文件在**键两两正交**（i ≠ j ⟹ ⟨kᵢ,kⱼ⟩ = 0）的
诚实假设下给出**精确闭式**——同时写入多个事实且互不干扰（正交键下逐目标解耦）：

    W' = W + Σᵢ Δᵢ⊗kᵢ,   Δᵢ = (vᵢ − W·kᵢ)/‖kᵢ‖²

（标量行语义：Δᵢ⊗kᵢ : x ↦ Δᵢ·⟨kᵢ,x⟩，与 RealROME 单层 rank-one 编辑
ROME W k₀ v x = W x + ⟨k₀,x⟩·(v−W·k₀)/‖k₀‖² 形式一致；既有
RealBatchEdit.BatchEditN 正是该闭式的展开，本文件把同一构造显式化为
RankOnePatch/BatchEditClosed，并证明其正交键下的精确性质。）

  ① **同时精确写入**：∀i, W'·kᵢ = vᵢ。展开求和后，j ≠ i 的项因
     ⟨kⱼ,kᵢ⟩=0 全部消失（正交性消去引理 sum_orthogonal_kill），只剩
     j = i 项 = Δᵢ·‖kᵢ‖² = vᵢ − W·kᵢ，补上 W·kᵢ 得 vᵢ
     （‖kᵢ‖² 消去需 ‖kᵢ‖ ≠ 0，即键非零假设）；
  ② **正交补精确不变**：x ⊥ span{k₁..k_m}（即 ∀i, ⟨kᵢ,x⟩=0）⟹
     W'·x = W·x，批量版 RealROME.ROME_preserves_orthogonal
     （此方向只需 x 与各键正交，无需键两两正交）；
  ③ **逐目标解耦**：kᵢ 处结果只依赖自己的目标 vᵢ，与其他目标无关
     （batchClosed_other_targets_irrelevant），且与单键 ROME 编辑一致
     （batchClosed_decouples_at_key）；
  ④ **m=2 退化**：batch2_orthogonal_writes_both（**本文件**对
     RealEditCrosstalk.BatchEdit2 的双键正交精确写入，与上游的「界」版
     batch2_pointwise_bound 相对照）；顺序编辑语义下正交键亦精确保持
     第一事实（RealEditCrosstalk.edit2_orthogonal_preserves_first，
     顺序/批量两种语义在正交键下于键值处一致，仅非键点行为不同）。

与「界」版本的区别：batchN_pointwise_bound 不需任何假设但只给上界；
本文件以正交假设换取**等式**闭式，且同时覆盖全部 m 个目标
（逐目标精确写入、互不干扰）。诚实假设：键非零（‖kᵢ‖² 可除）、
键两两正交（有序对全部成立）、域为 ℝ 欧氏内积。
-/

noncomputable section

namespace Lattice

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## rank-one 补丁 Δ⊗k（标量行语义：x ↦ Δ·⟨k,x⟩）与批量闭式 W' = W + Σᵢ Δᵢ⊗kᵢ -/

def RankOnePatch {m : ℕ} (Δ : Fin m → ℝ) (k : Fin m → E) (x : E) : ℝ :=
  ∑ i : Fin m, inner (k i) x * Δ i

def BatchEditClosed {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ) (x : E) : ℝ :=
  W x + RankOnePatch (fun i => (v i - W (k i)) / ‖k i‖ ^ 2) k x

/-! ## 与既有 BatchEditN 定义一致（rfl 桥，闭式即 RealBatchEdit 的批量编辑） -/

omit [CompleteSpace E] in
theorem batchClosed_eq_batchN {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ) (x : E) :
    BatchEditClosed W k v x = BatchEditN W k v x := by
  rfl

/-! ## 正交性消去引理：j ≠ i 的项因 ⟨kⱼ,kᵢ⟩=0 全部消失，只剩 j = i -/

omit [CompleteSpace E] in
lemma sum_orthogonal_kill {m : ℕ} (c : Fin m → ℝ) (k : Fin m → E)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ)) (i : Fin m) :
    (∑ j : Fin m, inner (k j) (k i) * c j) = inner (k i) (k i) * c i := by
  refine Finset.sum_eq_single i ?_ ?_
  · intro j hjin hne
    rw [horth j i hne]
    simp
  · intro hni
    exact (hni (Finset.mem_univ i)).elim

/-! ## 定理一：m 个事实同时精确写入（核心闭式）
∀i, W'·kᵢ = vᵢ：正交键下批量编辑逐目标精确命中，互不干扰。-/

theorem batchClosed_orthogonal_writes {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    ∀ i : Fin m, BatchEditClosed W k v (k i) = v i := by
  intro i
  unfold BatchEditClosed RankOnePatch
  rw [sum_orthogonal_kill (fun j => (v j - W (k j)) / ‖k j‖ ^ 2) k horth i]
  have hnorm : inner (k i) (k i) = ‖k i‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) (k i)
  rw [hnorm]
  have hk' : ‖k i‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero (k i) (hk i)
  field_simp [hk']

/-! ## 定理二：正交补精确不变（批量版 ROME_preserves_orthogonal）
x ⊥ span{k₁..k_m}（∀i, ⟨kᵢ,x⟩=0）⟹ W'·x = W·x，其余保持的精确版（ε = 0）。-/

omit [CompleteSpace E] in
theorem batchClosed_orthogonal_preserves {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (x : E) (hx : ∀ i : Fin m, inner (k i) x = (0 : ℝ)) :
    BatchEditClosed W k v x = W x := by
  unfold BatchEditClosed RankOnePatch
  have hsum : (∑ j : Fin m, inner (k j) x * ((v j - W (k j)) / ‖k j‖ ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hx j]
    simp
  rw [hsum]
  ring

/-! ## 定理三：组合闭式（同时写入 + 其余保持 一并陈述） -/

theorem batchClosed_orthogonal_closed_form {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    (∀ i : Fin m, BatchEditClosed W k v (k i) = v i) ∧
      (∀ x : E, (∀ i : Fin m, inner (k i) x = (0 : ℝ)) → BatchEditClosed W k v x = W x) := by
  constructor
  · exact batchClosed_orthogonal_writes W k v horth hk
  · intro x hx
    exact batchClosed_orthogonal_preserves W k v x hx

/-! ## 同一闭式在既有 BatchEditN 上的精确陈述
（其「界」版本见 RealBatchEdit.batchN_pointwise_bound；此处升级为等式。） -/

theorem batchN_orthogonal_writes {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) :
    ∀ i : Fin m, BatchEditN W k v (k i) = v i := by
  intro i
  rw [← batchClosed_eq_batchN]
  exact batchClosed_orthogonal_writes W k v horth hk i

theorem batchN_orthogonal_preserves {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (x : E) (hx : ∀ i : Fin m, inner (k i) x = (0 : ℝ)) :
    BatchEditN W k v x = W x := by
  rw [← batchClosed_eq_batchN]
  exact batchClosed_orthogonal_preserves W k v x hx

/-! ## 定理四：逐目标解耦 —— kᵢ 处结果只依赖 vᵢ，与其他目标无关 -/

theorem batchClosed_other_targets_irrelevant {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E)
    (v v' : Fin m → ℝ) (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) (i : Fin m) (hii : v i = v' i) :
    BatchEditClosed W k v (k i) = BatchEditClosed W k v' (k i) := by
  rw [batchClosed_orthogonal_writes W k v horth hk i]
  rw [batchClosed_orthogonal_writes W k v' horth hk i]
  exact hii

/-! ## 定理五：kᵢ 处批量结果与单键 ROME 编辑一致（单层退化的精确衔接） -/

theorem batchClosed_decouples_at_key {m : ℕ} (W : E →L[ℝ] ℝ) (k : Fin m → E) (v : Fin m → ℝ)
    (horth : ∀ i j : Fin m, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin m, k i ≠ 0) (i : Fin m) :
    BatchEditClosed W k v (k i) = ROME W (k i) (v i) (k i) := by
  rw [batchClosed_orthogonal_writes W k v horth hk i]
  exact (ROME_writes_fact W (k i) (v i) (hk i)).symm

/-! ## m=2 特例：双键精确写入（RealEditCrosstalk.BatchEdit2）
批量语义下正交双键同时精确写入两事实（其「界」特例 batch2_pointwise_bound
在此成为等式）；顺序编辑语义的对照见 edit2_orthogonal_preserves_first。-/

theorem batch2_orthogonal_writes_first (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (horth : inner k₂ k₁ = (0 : ℝ)) (hk₁ : k₁ ≠ 0) :
    BatchEdit2 W k₁ k₂ v₁ v₂ k₁ = v₁ := by
  unfold BatchEdit2
  have hz : inner k₂ k₁ * ((v₂ - W k₂) / ‖k₂‖ ^ 2) = 0 := by
    rw [horth]
    simp
  rw [hz]
  have hnorm : inner k₁ k₁ = ‖k₁‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₁
  rw [hnorm]
  have hk' : ‖k₁‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₁ hk₁
  field_simp [hk']

theorem batch2_orthogonal_writes_second (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (horth : inner k₁ k₂ = (0 : ℝ)) (hk₂ : k₂ ≠ 0) :
    BatchEdit2 W k₁ k₂ v₁ v₂ k₂ = v₂ := by
  unfold BatchEdit2
  have hz : inner k₁ k₂ * ((v₁ - W k₁) / ‖k₁‖ ^ 2) = 0 := by
    rw [horth]
    simp
  rw [hz]
  have hnorm : inner k₂ k₂ = ‖k₂‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℝ) k₂
  rw [hnorm]
  have hk' : ‖k₂‖ ^ 2 ≠ 0 := key_norm_sq_ne_zero k₂ hk₂
  field_simp [hk']

theorem batch2_orthogonal_writes_both (W : E →L[ℝ] ℝ) (k₁ k₂ : E) (v₁ v₂ : ℝ)
    (horth12 : inner k₁ k₂ = (0 : ℝ)) (horth21 : inner k₂ k₁ = (0 : ℝ))
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) :
    BatchEdit2 W k₁ k₂ v₁ v₂ k₁ = v₁ ∧ BatchEdit2 W k₁ k₂ v₁ v₂ k₂ = v₂ := by
  constructor
  · exact batch2_orthogonal_writes_first W k₁ k₂ v₁ v₂ horth21 hk₁
  · exact batch2_orthogonal_writes_second W k₁ k₂ v₁ v₂ horth12 hk₂

/-! ## m=2 特例（Fin 指标形式）：主定理（batchN_orthogonal_writes）直接实例化 -/

theorem batchN_m2_orthogonal_writes (W : E →L[ℝ] ℝ) (k : Fin 2 → E) (v : Fin 2 → ℝ)
    (horth : ∀ i j : Fin 2, i ≠ j → inner (k i) (k j) = (0 : ℝ))
    (hk : ∀ i : Fin 2, k i ≠ 0) :
    BatchEditN W k v (k 0) = v 0 ∧ BatchEditN W k v (k 1) = v 1 := by
  constructor
  · exact batchN_orthogonal_writes W k v horth hk 0
  · exact batchN_orthogonal_writes W k v horth hk 1

/-! ## 注：编辑语义对照与后续方向
  批量编辑（本文件）：所有补丁基准为原 W，正交键下逐目标精确闭式（等式）；
  顺序编辑（RealEditCrosstalk.ApplyEdits2）：第二编辑基准含第一编辑，正交键下
  第一事实精确保持（edit2_orthogonal_preserves_first，既有）——两种语义在正交键
  下于键值处一致；批量编辑在非键点也只是各补丁之和（无二次串扰）。
  向量值版本（W : E →L[ℝ] E，Δᵢ : E，用 ContinuousLinearMap.smulRight 构造
  Δᵢ⊗kᵢ）留作后续：正交消去与 ‖kᵢ‖² 消去的证明结构与本文标量行版完全相同。 -/

end Lattice
