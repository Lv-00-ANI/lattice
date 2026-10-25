import Mathlib
import Lattice.Lib.Architectures.RealLoop
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Optim.RealConvergence
/-!
# LATTICE: 递归程序语义 —— 自引用状态转移 + 有限最小不动点

`RealLoop` 把「固定步循环」的语义钉在不变量上（`invariant_preserves_iteration`），
`RealChain` 给出 n 层前向链的误差传播。本文件补**递归语义**这一维度：以自引用
状态转移 `recFwd`（`Nat.rec` 式定义：`recFwd f 0 = id`，`recFwd f (n+1) = f ∘ recFwd f n`）
为程序，给出

  1. `recFwd_eq_iterate`：递归定义的常数层等于 `RealLoop.iterate`（两种迭代同型），
     从而 `RealLoop` 的循环不变量定理对递归程序直接可用；
     `recFwd_eq_chainFwd` 进一步说明 `recFwd` 是 `RealChain.ChainFwd` 的常数层情形
     （同型前向链），把递归语义接进前向链的误差传播框架；
  2. `recursive_invariant`：递归程序保持不变量 P（初始成立 + 每步保持 ⟹ 任意深度成立），
     直接由 `invariant_preserves_iteration` 给出；`recursive_invariant_chain`
     是逐层（非同态步）版本，衔接 `RealChain.ChainFwd`；
  3. `recursive_termination`：**变式（variant）论证** —— 停机谓词 `Stop` 尚未成立时
     度量严格递减，则停机在 `≤ μ x` 步内发生（∃ n ≤ μ x，`Stop (recFwd f n x)`）；
     `recursive_termination_eps` 把 `RealConvergence.contraction_converges` 的
     ε-终止接到递归迭代上（收缩递归 ⟹ 迭代误差最终任意小）；
  4. `least_fixed_point_finite`：**有限状态（`Fintype`）上单调算子的最小不动点
     = 从 ⊥ 出发的迭代极限** —— 存在 `N ≤ Fintype.card α`，使迭代在 N 处稳定，
     该稳定值是 f 的不动点，且 ≤ 任意不动点（最小性 = Knaster–Tarski 的有限情形）；
  5. `recFwd_monotone`：f 单调 ⟹ 其任意次迭代单调。

诚实标注（无 sorry / axiom / admit）：
- `recursive_termination` 的度量版**必须带停机谓词** `Stop`。若不加 `Stop` 而要求
  `∀ y, μ (f y) < μ y` 对所有 y 成立，则由 ℕ 的良基性该假设**自相矛盾**
  （不存在处处严格递减的 ℕ 值函数：取 μ 最小的元素即得矛盾）。故终止性以
  「尚未停机时度量严格递减」表述，结论是「停机在 ≤ μ x 步内发生」——
  这正是标准的部分正确性 + 变式（variant）终止论证。
- `least_fixed_point_finite` 在 `Fintype + PartialOrder + OrderBot` 上**自证**。
  mathlib 另有 `OrderHom.lfp`（需 `CompleteLattice`）与 `lfp_eq_sSup_iterate`
  （需 ωScottContinuous）；本文件不复用它们，以免为一个有限状态引理引入完整格结构。
- 模型无关：任意类型 X（迭代语义）、任意范数空间（ε-终止）、任意有限偏序（不动点）。
-/

noncomputable section

namespace Lattice

/-! ## 一、递归前向：自引用状态转移 -/

/-- **递归前向**（自引用状态转移）：`recFwd f 0 = id`，
`recFwd f (n+1) = f ∘ recFwd f n`。展开即为 `f` 的 n 次自应用，
用 `Nat.rec`（结构递归）定义，天然终止（无通用递归/不动点组合子）。 -/
def recFwd {X : Type*} (f : X → X) : ℕ → X → X
  | 0 => id
  | n + 1 => f ∘ recFwd f n

/-- 递归展开（定义等式）：`recFwd f (n+1) = f ∘ recFwd f n`。 -/
theorem recFwd_succ {X : Type*} (f : X → X) (n : ℕ) :
    recFwd f (n + 1) = f ∘ recFwd f n :=
  rfl

/-- 逐点展开：`recFwd f (n+1) x = f (recFwd f n x)`。 -/
theorem recFwd_succ_apply {X : Type*} (f : X → X) (n : ℕ) (x : X) :
    recFwd f (n + 1) x = f (recFwd f n x) :=
  rfl

/-! ## 二、递归 = 有限迭代（衔接 RealLoop.iterate） -/

/-- **递归定义 = 有限迭代**：`recFwd f n x = iterate f n x`
（`RealLoop.iterate`）。两种书写（`Nat.rec` 式 vs 尾递归式）在同一函数上同型，
故 `RealLoop` 的不变量定理对 `recFwd` 直接可用。 -/
theorem recFwd_eq_iterate {X : Type} (f : X → X) (n : ℕ) (x : X) :
    recFwd f n x = iterate f n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change f (recFwd f n x) = iterate f n (f x)
      rw [ih x]
      exact (iterate_step_swap f n x).symm

/-- **递归 = 同型前向链**：`recFwd f n` 等于 `RealChain.ChainFwd` 在常数层族
`fun _ => f` 下的 n 层链。递归语义因此是前向链语义的常层特例。 -/
theorem recFwd_eq_chainFwd {X : Type*} (f : X → X) (n : ℕ) (x : X) :
    recFwd f n x = ChainFwd (fun _ : ℕ => f) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change f (recFwd f n x) = f (ChainFwd (fun _ : ℕ => f) n x)
      rw [ih x]

/-! ## 三、递归程序的不变量 -/

/-- **递归程序保持不变量**：P 初始成立、且每步保持，则 P 在任意深度成立
（直接由 `RealLoop.invariant_preserves_iteration` 经 `recFwd_eq_iterate` 给出）。 -/
theorem recursive_invariant {X : Type} (P : X → Prop) (f : X → X)
    (n : ℕ) (x : X) (hP : P x) (hstep : ∀ y : X, P y → P (f y)) :
    P (recFwd f n x) := by
  rw [recFwd_eq_iterate]
  exact invariant_preserves_iteration P f n x hP hstep

/-- **逐层（非同态）递归程序的不变量**：程序为「n 层依次作用」的链 `ChainFwd Fs n`
（自引用语义的非同态推广；`recFwd_eq_chainFwd` 说明常数层是特例）。
每层都保持 P，则任意深度保持。 -/
theorem recursive_invariant_chain {X : Type} (P : X → Prop) (Fs : ℕ → X → X)
    (n : ℕ) (x : X) (hP : P x) (hstep : ∀ (i : ℕ) (y : X), P y → P (Fs i y)) :
    P (ChainFwd Fs n x) := by
  induction n with
  | zero => simpa [ChainFwd] using hP
  | succ n ih =>
      change P (Fs n (ChainFwd Fs n x))
      exact hstep n _ ih

/-! ## 四、递归程序的终止 -/

/-- **递归终止（变式论证）**：若在「尚未停机」的状态上度量 `μ` 严格递减，
则从任意 `x` 出发，停机在 `≤ μ x` 步内发生。
反证：若前 `μ x` 步都未停机，则归纳可得 `μ (recFwd f k x) + k ≤ μ x`（每步至少
消耗 1 个度量单位）；在 `k = μ x` 处仍有 `¬ Stop` 且度量已耗尽，再走一步即得
`μ < 0` 的矛盾。 -/
theorem recursive_termination {X : Type*} (f : X → X) (Stop : X → Prop) (μ : X → ℕ)
    (hμ : ∀ y : X, ¬ Stop y → μ (f y) < μ y) (x : X) :
    ∃ n : ℕ, n ≤ μ x ∧ Stop (recFwd f n x) := by
  by_contra h
  push_neg at h
  have key : ∀ n : ℕ, n ≤ μ x → μ (recFwd f n x) + n ≤ μ x := by
    intro n
    induction n with
    | zero => intro _; simp [recFwd]
    | succ n ih =>
        intro hn
        have hn' : n ≤ μ x := by omega
        have hns : ¬ Stop (recFwd f n x) := h n hn'
        have hdec : μ (f (recFwd f n x)) < μ (recFwd f n x) := hμ _ hns
        change μ (f (recFwd f n x)) + (n + 1) ≤ μ x
        have := ih hn'
        omega
  have hN := key (μ x) le_rfl
  have hns : ¬ Stop (recFwd f (μ x) x) := h (μ x) le_rfl
  have hdec : μ (f (recFwd f (μ x) x)) < μ (recFwd f (μ x) x) := hμ _ hns
  omega

/-- **收缩递归的 ε-终止**：若递归步 `f` 以系数 `c < 1` 压缩到不动点 `xstar`
（`‖f y − xstar‖ ≤ c‖y − xstar‖`），则迭代误差最终任意小 ——
把 `RealConvergence.contraction_converges` 直接实例化到 `recFwd` 的轨道上。 -/
theorem recursive_termination_eps {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → X) (x xstar : X) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcon : ∀ y : X, ‖f y - xstar‖ ≤ c * ‖y - xstar‖) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ‖recFwd f n x - xstar‖ < ε := by
  intro ε hε
  have hstep : ∀ n : ℕ,
      ‖recFwd f (n + 1) x - xstar‖ ≤ c * ‖recFwd f n x - xstar‖ := by
    intro n
    change ‖f (recFwd f n x) - xstar‖ ≤ c * ‖recFwd f n x - xstar‖
    exact hcon (recFwd f n x)
  have hnonneg : ∀ n : ℕ, 0 ≤ ‖recFwd f n x - xstar‖ := fun n => norm_nonneg _
  exact contraction_converges (e := fun n : ℕ => ‖recFwd f n x - xstar‖)
    c hc0 hc1 hstep hnonneg ε hε

/-! ## 五、迭代的单调性 -/

/-- **迭代保序**：`f` 单调 ⟹ 其任意次迭代 `recFwd f n` 单调。 -/
theorem recFwd_monotone {X : Type} [Preorder X] (f : X → X) (hf : Monotone f) (n : ℕ) :
    Monotone (recFwd f n) := by
  induction n with
  | zero =>
      change Monotone (id : X → X)
      exact monotone_id
  | succ n ih =>
      change Monotone (f ∘ recFwd f n)
      exact hf.comp ih

/-! ## 六、有限状态上的最小不动点 -/

/-- 从 `⊥` 出发的迭代序列逐步增大：`B n ≤ B (n+1)`。 -/
lemma recFwd_bot_le_succ {α : Type*} [Preorder α] [OrderBot α] (f : α → α) (hf : Monotone f) :
    ∀ n : ℕ, recFwd f n ⊥ ≤ recFwd f (n + 1) ⊥ := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      change f (recFwd f n ⊥) ≤ f (recFwd f (n + 1) ⊥)
      exact hf ih

/-- 从 `⊥` 出发的迭代序列关于步数单调（单调算子的迭代不降）。 -/
lemma recFwd_bot_monotone {α : Type*} [Preorder α] [OrderBot α] (f : α → α) (hf : Monotone f) :
    Monotone (fun n : ℕ => recFwd f n ⊥) := by
  intro n m hnm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      exact ih.trans (recFwd_bot_le_succ f hf (n + d))

/-- **有限状态上的迭代稳定**：`Fintype α` 上的单调算子的 `⊥`-轨道在
`≤ Fintype.card α` 步内出现不动步（`B N = B (N+1)`）。
反证：若前 `card α` 步都严格增，则 `Fin (card α + 1) → α` 的单射给出
`card α + 1 ≤ card α` 的矛盾（鸽笼原理的基数形式）。 -/
theorem recFwd_stabilizes_finite {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, N ≤ Fintype.card α ∧ recFwd f N ⊥ = recFwd f (N + 1) ⊥ := by
  by_contra h
  push_neg at h
  have hle : ∀ n : ℕ, recFwd f n ⊥ ≤ recFwd f (n + 1) ⊥ := recFwd_bot_le_succ f hf
  have hlt : ∀ n : ℕ, n ≤ Fintype.card α → recFwd f n ⊥ < recFwd f (n + 1) ⊥ :=
    fun n hn => lt_of_le_of_ne (hle n) (h n hn)
  have hmono : Monotone (fun n : ℕ => recFwd f n ⊥) := recFwd_bot_monotone f hf
  -- 前段严格增 + 后段单调 ⟹ 严格增（对 i < j 且 i ≤ card α）
  have hltj : ∀ i j : ℕ, i ≤ Fintype.card α → i < j →
      recFwd f i ⊥ < recFwd f j ⊥ := by
    intro i j hi hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : recFwd f i ⊥ < recFwd f (i + 1) ⊥ := hlt i hi
    have h2 : recFwd f (i + 1) ⊥ ≤ recFwd f (i + d + 1) ⊥ := hmono (by omega)
    exact lt_of_lt_of_le h1 h2
  -- 单射：Fin (card α + 1) → α
  have hinj : Function.Injective (fun i : Fin (Fintype.card α + 1) => recFwd f (i : ℕ) ⊥) := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hltij | hgtij
    · exact (ne_of_lt (hltj (i : ℕ) (j : ℕ) (by have := i.isLt; omega) hltij)) hij
    · exact (ne_of_lt (hltj (j : ℕ) (i : ℕ) (by have := j.isLt; omega) hgtij)) hij.symm
  have hcard := Fintype.card_le_of_injective
    (fun i : Fin (Fintype.card α + 1) => recFwd f (i : ℕ) ⊥) hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- **有限状态上的最小不动点 = 迭代极限**（Knaster–Tarski 的有限情形）：
单调算子 `f : α → α`（`α` 有限偏序、有底）从 `⊥` 出发的迭代在 `N ≤ card α`
步稳定；稳定值 `B N` 是 `f` 的不动点，且 `≤` 任意不动点（最小性）。
即：迭代极限恰为 `f` 的最小不动点。 -/
theorem least_fixed_point_finite {α : Type*} [Fintype α] [PartialOrder α] [OrderBot α]
    (f : α → α) (hf : Monotone f) :
    ∃ N : ℕ, N ≤ Fintype.card α ∧
      (∀ n : ℕ, N ≤ n → recFwd f n ⊥ = recFwd f N ⊥) ∧
      f (recFwd f N ⊥) = recFwd f N ⊥ ∧
      (∀ y : α, f y = y → recFwd f N ⊥ ≤ y) := by
  obtain ⟨N, hN, hstab⟩ := recFwd_stabilizes_finite f hf
  -- 稳定步是不动点：f (B N) = B (N+1) = B N
  have hfix : f (recFwd f N ⊥) = recFwd f N ⊥ := by
    have h1 : recFwd f (N + 1) ⊥ = f (recFwd f N ⊥) := rfl
    rw [← h1]
    exact hstab.symm
  -- 稳定之后恒为同一值
  have hconst : ∀ k : ℕ, recFwd f (N + k) ⊥ = recFwd f N ⊥ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h1 : recFwd f (N + (k + 1)) ⊥ = f (recFwd f (N + k) ⊥) := rfl
        rw [h1, ih, hfix]
  refine ⟨N, hN, ?_, hfix, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hconst k
  · -- 最小性：⊥ ≤ y 且 f y = y ⟹ B n ≤ y 对所有 n 成立
    intro y hy
    have hbound : ∀ n : ℕ, recFwd f n ⊥ ≤ y := by
      intro n
      induction n with
      | zero => exact bot_le
      | succ n ih =>
          change f (recFwd f n ⊥) ≤ y
          rw [← hy]
          exact hf ih
    exact hbound N

end Lattice
