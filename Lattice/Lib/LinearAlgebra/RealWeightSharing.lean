import Mathlib
import Lattice.Lib.Chain.RealChain
import Lattice.Lib.Architectures.RealBlockLipschitz
import Lattice.Lib.Architectures.RealLoop
/-!
# LATTICE: 跨层参数共享（ALBERT 式）—— 共享权重链的端到端常数与参数量

ALBERT 式**跨层参数共享**：同一层函数在 n 个层位置重复使用（而不是每层
独立权重）。相对于 RealModelChain / RealModelChainHetero 的独立参数链，
共享链的端到端 Lipschitz 常数退化为**幂** `Lⁿ`，且参数量不随层数增长。

定义与定理链（模型无关，任意范数空间 X）：

  1. `sharedChain F n`：把同一层函数 F 重复 n 次的链
     （= `ChainFwd (fun _ => F) n`）——共享链的定义；
  2. `sharedChain_eq_iterate`：共享链 = RealLoop.iterate F n（「共享 = 同一
     映射迭代」，把层间共享与控制流循环统一）；
  3. `shared_chain_error_bound`（核心）：F 是 L-Lipschitz ⟹
     `‖sharedChain F n x − sharedChain F n y‖ ≤ Lⁿ·‖x−y‖`
     （直接实例化 `chainN_identical_blocks_bound` / `chainN_error_bound`）；
  4. `shared_vs_independent`：独立链各层常数 `Ls i ≥ L` 时
     `Lⁿ ≤ ∏ᵢ Ls i`——共享链常数（幂）≤ 独立链常数之积；
  5. `shared_vs_independent_strict` / `shared_vs_independent_eq_iff`：
     等号当且仅当所有层常数都等于 L（正性 `0 < L` 下）——正交性/等号条件；
  6. `shared_parameter_count` / `shared_parameter_count_le`（**工程性质**，
     组合计数）：共享参数张量数不随层数变化，≤ 独立参数数（n ≥ 1）；
  7. `shared_grad_accumulation` / `shared_grad_norm_bound`：
     共享层的梯度是各层梯度贡献之和（累加），其范数被 n·G 界住。

诚实假设（均显式标注）：
  · 定理 1–5 只在 Lipschitz 形式上陈述（`∀x y, ‖F x−F y‖ ≤ L‖x−y‖`），
    是链骨架的直接实例化，不含任何新分析假设；
  · 定理 4/5 的非负/正性假设 `0 ≤ L`、`0 < L` 是常数比较所需
    （Lipschitz 常数通常取非负；`0 < L` 才使等号刻画成立——L = 0 时
    `0ⁿ = 0 = ∏Ls` 可由某个 Ls = 0、其余任意大达成，等号刻画不成立，
    故显式要求 L > 0）；
  · 定理 6 是**工程/组合计数性质**：把「参数张量数」抽象为自然数
    （共享 = p，独立 = p·n），是参数量记账的模型，不含权重结构细节；
  · 定理 7 的梯度是抽象的各层梯度贡献之和（把「共享参数的总梯度 =
    各层反向梯度之和」记为求和），`shared_grad_norm_bound` 是三角不等式
    的直接推论；不含自动微分/反向传播实现细节。
全部证明无 sorry / axiom / admit。

模型无关：任意范数空间 X、任意 Lipschitz 层、任意层数 n。
-/

noncomputable section

namespace Lattice

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 共享链定义：同一层函数重复 n 次 -/

/-- 共享权重链：把同一层函数 `F` 重复 n 次（= `ChainFwd (fun _ => F) n`）。 -/
def sharedChain (F : X → X) (n : ℕ) : X → X :=
  ChainFwd (fun _ : ℕ => F) n

/-! ## 定理一：共享链 = 迭代（衔接 RealLoop.iterate）
「层间共享」与「控制流循环」是同一结构：n 次同一映射。
`RealLoop.iterate` 在 `Type` 层陈述，故本节在 `Type` 层给出该等价。 -/

section IterateLink

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
theorem sharedChain_eq_iterate (F : Y → Y) (n : ℕ) (x : Y) :
    sharedChain F n x = iterate F n x := by
  induction n generalizing x with
  | zero => simp [sharedChain, ChainFwd, iterate]
  | succ n ih =>
      rw [show sharedChain F (n + 1) x = F (sharedChain F n x) from by
            simp [sharedChain, ChainFwd],
          show iterate F (n + 1) x = iterate F n (F x) from rfl,
          iterate_step_swap F n x,
          ih x]

end IterateLink

/-! ## 定理二（核心）：共享权重链的端到端误差 = Lⁿ·‖x−y‖
F 是 L-Lipschitz ⟹ n 层共享链的端到端误差 ≤ Lⁿ·‖x−y‖
（`chainN_identical_blocks_bound` 的直接实例化：∏ 常数 = 幂）。 -/

theorem shared_chain_error_bound (F : X → X) (L : ℝ) (n : ℕ)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) :
    ∀ x y, ‖sharedChain F n x - sharedChain F n y‖ ≤ L ^ n * ‖x - y‖ := by
  intro x y
  simpa [sharedChain] using chainN_identical_blocks_bound F L n hF hL x y

/-! ## 定理三：编辑局部性（共享链版）
第 k 层入口注入扰动 δ，经尾部 n−k 层共享层：变化 ≤ L^(n−k)·‖δ‖
（`chain_edit_locality` 的共享链实例化）。 -/

theorem shared_chain_edit_locality (F : X → X) (L : ℝ) (n k : ℕ) (hk : k < n)
    (hF : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL : 0 ≤ L) (δ x : X) :
    ‖ChainTail (fun _ : ℕ => F) k n (x + δ) - ChainTail (fun _ : ℕ => F) k n x‖
      ≤ L ^ (n - k) * ‖δ‖ := by
  have hb := chain_edit_locality (fun _ : ℕ => F) (fun _ : ℕ => L) n k hk δ
    (by intro i _ x y; exact hF x y) (by intro i _; exact hL) x
  have hprod : (∏ _j in Finset.range (n - k), L) = L ^ (n - k) := by
    rw [Finset.prod_const, Finset.card_range]
  simpa [hprod] using hb

/-! ## 定理四：共享链常数 ≤ 独立链常数之积
独立链各层常数 `Ls i ≥ L`（L ≥ 0）⟹ `Lⁿ ≤ ∏ᵢ<ₙ Ls i`
（共享链的幂常数不大于逐层独立常数之积）。 -/

theorem shared_vs_independent (L : ℝ) (Ls : ℕ → ℝ) (n : ℕ) (hL0 : 0 ≤ L)
    (h : ∀ i, i < n → L ≤ Ls i) :
    L ^ n ≤ ∏ i in Finset.range n, Ls i := by
  have hprod : (∏ _i in Finset.range n, L) = L ^ n := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← hprod]
  apply Finset.prod_le_prod
  · intro i _
    exact hL0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)

/-! ## 定理五：严格不等式（某一层常数严格更大）
若存在某层 `Ls i > L`（其余 ≥ L，且 L > 0），则 `Lⁿ < ∏ᵢ<ₙ Ls i`
（`Finset.prod_lt_prod`：只要一个因子严格更大，乘积严格更大）。 -/

theorem shared_vs_independent_strict (L : ℝ) (Ls : ℕ → ℝ) (n : ℕ) (hL0 : 0 < L)
    (h : ∀ i, i < n → L ≤ Ls i) (hlt : ∃ i, i < n ∧ L < Ls i) :
    L ^ n < ∏ i in Finset.range n, Ls i := by
  have hprod : (∏ _i in Finset.range n, L) = L ^ n := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← hprod]
  apply Finset.prod_lt_prod
  · intro i _
    exact hL0
  · intro i hi
    exact h i (Finset.mem_range.mp hi)
  · rcases hlt with ⟨i, hi, hlti⟩
    exact ⟨i, Finset.mem_range.mpr hi, hlti⟩

/-! ## 定理六：等号条件（正交性）
L > 0 且 `Ls i ≥ L` 时，`∏ᵢ<ₙ Ls i = Lⁿ` 当且仅当所有层常数都等于 L：
共享链常数与独立链常数之积相等 ⟺ 各层无额外放大（等号/正交条件）。 -/

theorem shared_vs_independent_eq_iff (L : ℝ) (Ls : ℕ → ℝ) (n : ℕ) (hL0 : 0 < L)
    (h : ∀ i, i < n → L ≤ Ls i) :
    (∏ i in Finset.range n, Ls i = L ^ n) ↔ (∀ i, i < n → Ls i = L) := by
  constructor
  · intro heq i hi
    by_contra hne
    have hlt : L < Ls i := lt_of_le_of_ne (h i hi) (Ne.symm hne)
    have hstrict := shared_vs_independent_strict L Ls n hL0 h ⟨i, hi, hlt⟩
    rw [heq] at hstrict
    exact lt_irrefl _ hstrict
  · intro hall
    have hcongr : (∏ i in Finset.range n, Ls i) = ∏ _i in Finset.range n, L :=
      Finset.prod_congr rfl (fun i hi => hall i (Finset.mem_range.mp hi))
    rw [hcongr, Finset.prod_const, Finset.card_range]

/-! ## 定理七（工程性质，组合计数）：参数量不随层数增长
把「参数张量数」抽象为自然数：共享 = p（与层数 n 无关），独立 = p·n。
则共享参数量对任意层数相同，且（n ≥ 1 时）不超过独立参数量。 -/

/-- 参数量记账（工程抽象）：共享权重下与层数无关的参数张量数。 -/
def sharedParamCount (p : ℕ) (_n : ℕ) : ℕ := p

/-- 参数量记账（工程抽象）：独立权重下 = 每层 p 个张量 × n 层。 -/
def independentParamCount (p : ℕ) (n : ℕ) : ℕ := p * n

/-- 共享参数量与层数无关（任意两层数下相同）。 -/
theorem shared_parameter_count (p n m : ℕ) :
    sharedParamCount p n = sharedParamCount p m := rfl

/-- 共享参数量 ≤ 独立参数量（n ≥ 1）——共享节省参数（工程记账）。 -/
theorem shared_parameter_count_le (p n : ℕ) (hn : 1 ≤ n) :
    sharedParamCount p n ≤ independentParamCount p n := by
  simp only [sharedParamCount, independentParamCount]
  exact Nat.le_mul_of_pos_right p (by omega)

/-- 共享参数比例：层数越多，共享相对独立的参数节省越大
（`sharedParamCount p n * n ≤ independentParamCount p n` 在 p·n² ≤ p·n 时不真，
故此处置为「独立参数量随 n 线性增长」：n ≥ 1 时 p ≤ p·n）。 -/
theorem independent_param_count_mono (p n m : ℕ) (h : n ≤ m) :
    independentParamCount p n ≤ independentParamCount p m :=
  Nat.mul_le_mul_left p h

/-! ## 定理八：共享层梯度 = 各层梯度之和（累加）
共享参数的总梯度 = 各层位置的反向贡献之和（抽象为向量和）；
范数被层数 × 单层梯度界界住（三角不等式）。 -/

/-- 共享参数的梯度累加：各层贡献之和（`g i` 为第 i 层的反向梯度贡献）。 -/
def sharedGrad (g : ℕ → X) (n : ℕ) : X := ∑ i in Finset.range n, g i

omit [NormedSpace ℝ X] in
/-- 多一层（累加一步）：`sharedGrad g (n+1) = sharedGrad g n + g n`。 -/
theorem shared_grad_accumulation (g : ℕ → X) (n : ℕ) :
    sharedGrad g (n + 1) = sharedGrad g n + g n := by
  simp [sharedGrad, Finset.sum_range_succ]

omit [NormedSpace ℝ X] in
/-- 某层梯度贡献为零不影响累加（链式法则中无贡献的层）。 -/
theorem shared_grad_zero (g : ℕ → X) (n : ℕ) (h : ∀ i, i < n → g i = 0) :
    sharedGrad g n = 0 := by
  simp only [sharedGrad]
  apply Finset.sum_eq_zero
  intro i hi
  exact h i (Finset.mem_range.mp hi)

omit [NormedSpace ℝ X] in
/-- 梯度范数界：各层贡献 ≤ G ⟹ 共享参数梯度范数 ≤ n·G（三角不等式；
层数越多梯度累加越大——共享参数的梯度集中效应）。 -/
theorem shared_grad_norm_bound (g : ℕ → X) (n : ℕ) (G : ℝ)
    (hG : ∀ i, i < n → ‖g i‖ ≤ G) (_hG0 : 0 ≤ G) :
    ‖sharedGrad g n‖ ≤ (n : ℝ) * G := by
  have h1 : ‖sharedGrad g n‖ ≤ ∑ i in Finset.range n, ‖g i‖ := by
    simpa [sharedGrad] using norm_sum_le (Finset.range n) g
  have h2 : (∑ i in Finset.range n, ‖g i‖) ≤ (n : ℝ) * G := by
    calc
      (∑ i in Finset.range n, ‖g i‖) ≤ ∑ _i in Finset.range n, G :=
            Finset.sum_le_sum (fun i hi => hG i (Finset.mem_range.mp hi))
      _ = (n : ℝ) * G := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  linarith

/-! ## 注：共享权重收官闭环
  共享链定义（`ChainFwd` 常数层）⟹ 定理二直接实例化链骨架（∏常数为幂）
  ⟹ 定理三编辑局部性；定理四/五/六给出共享（幂）与独立（逐项积）常数的
  比较与等号刻画——共享在 Lipschitz 意义上永远是独立链的下界（收缩更紧），
  等号仅当各层常数相同；定理七给出参数量的组合记账（工程性质）；
  定理八给出共享参数梯度的累加与界。全部证明无 sorry/axiom/admit。 -/

end Lattice
