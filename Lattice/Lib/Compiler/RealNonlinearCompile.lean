import Mathlib
import Lattice.Runtime.RealLinear
import Lattice.Lift.RealNonlinear
import Lattice.Lib.Optim.RealApprox
/-!
# LATTICE: 非线性约束的编译 —— sign / relu 编码与分段线性保语义

此前的编译链只覆盖**线性子类**（`RealLinear.convertReal`：`a*x+b = 0`）。
本文件把编译推广到**非线性激活编码**，给出五个编译器形式的保语义定理：

  1. `signCompile`：用 `Real.sign (a*x+b)` 编码**等式**约束 ——
     `a*x+b = 0 ⟺ sign(a*x+b) = 0`（`RealNonlinear.sign_preserves` 的编译器形式）；
  2. `reluCompile`：用 `relu (a*x+b)` 编码**不等式**约束 ——
     `a*x+b ≤ 0 ⟺ relu(a*x+b) = 0`（`RealNonlinear.relu_preserves` 的编译器形式）；
  3. `prodZero_compile` / `prodZero_iff`：`a·b = 0` 型**乘积约束**的 sign 编码
     （非线性零因子结构：`a·b = 0 ⟺ a = 0 ∨ b = 0`，编码后零化 ⟺ 约束成立）；
  4. `nonlinear_compile_preserves`（复合）：一个约束同时含「等式部分 ∧ 不等式部分」
     （如 `a·b = 0` 与 `c ≤ d` 的组合），编译器输出 `(sign 分量, relu 分量)`，
     该输出为 `(0,0)` ⟺ 约束满足 —— 由第 1、2 条**逐分量组合**得到；
     `nlCompile_batch` 把它提升到约束列表的合取；
  5. `piecewise_compile`：**分段线性**约束的编译保持 —— 分段函数
     `if x ≤ c then f x else g x` 的零化 ⟺ 两条分支在各自区间上分别成立
     （逐段验证：左段取 `if_pos`、右段取 `if_neg`）；
  6. `nonlinear_soundness_local`：**局部（有界域）**保语义 —— 在有界域 `|t| ≤ R` 上
     用仿射 `L` 近似非线性 `f`（`RealApprox.ApproxOn`，误差 ≤ ε），
     `L t = 0` 只给出 `|f t| ≤ ε`（**诚实降级**：只能得到 ε 界，得不到精确零点）；
     `linearization_global_fails` 给出**全局版不成立**的显式反例
     （存在 `f, L` 使 `L ≡ 0` 而 `∃ t, f t ≠ 0`），因此全局保语义在纯线性化下
     **不可证**，这正是本条必须标注为「局部」的原因。

诚实假设与降级：
- `signCompile` 依赖 `Real.sign`（Mathlib 中为 `noncomputable`），故本文件置于
  `noncomputable section`；这只影响可计算性，不影响定理的语义内容。
- 第 1–5 条是**逐点精确**等价（无近似）；第 6 条是**条件界**，`R`（有界域）与
  `ε`（近似误差）均为显式参数，且已附反例说明全局版不可得。
- 不使用 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

/-! ## 一、sign 编码等式约束 -/

/-- 等式约束 `a*x+b = 0` 的 sign 编码：编译为函数 `x ↦ Real.sign (a*x+b)`。 -/
def signCompile (a b : ℝ) : ℝ → ℝ := fun x => Real.sign (a * x + b)

/-- 符号侧等式约束的满足语义。 -/
def SignSat (a b : ℝ) (x : ℝ) : Prop := a * x + b = 0

/-- **sign 编码保语义**：`a*x+b = 0 ⟺ sign(a*x+b) = 0`。
证明：`Real.sign_eq_zero_iff`（`sign r = 0 ↔ r = 0`）。 -/
theorem signCompile_preserves (a b : ℝ) (x : ℝ) : SignSat a b x ↔ signCompile a b x = 0 := by
  unfold SignSat signCompile
  rw [Real.sign_eq_zero_iff]

/-- sign 编码保解集（集合论表述）。 -/
theorem signCompile_solution_set (a b : ℝ) :
    {x : ℝ | SignSat a b x} = {x : ℝ | signCompile a b x = 0} := by
  ext x
  exact signCompile_preserves a b x

/-! ## 二、relu 编码不等式约束 -/

/-- 不等式约束 `a*x+b ≤ 0` 的 relu 编码：编译为函数 `x ↦ relu (a*x+b)`。 -/
def reluCompile (a b : ℝ) : ℝ → ℝ := fun x => relu (a * x + b)

/-- 符号侧不等式约束的满足语义（`a*x+b ≤ 0`，即 `a*x+b` 被 relu 吸收）。 -/
def ReluConstrSat (a b : ℝ) (x : ℝ) : Prop := a * x + b ≤ 0

/-- **relu 编码保语义**：`a*x+b ≤ 0 ⟺ relu(a*x+b) = 0`。
证明：`RealNonlinear.relu_eq_zero_iff`。 -/
theorem reluCompile_preserves (a b : ℝ) (x : ℝ) :
    ReluConstrSat a b x ↔ reluCompile a b x = 0 := by
  unfold ReluConstrSat reluCompile
  rw [relu_eq_zero_iff]

/-- relu 编码保解集（集合论表述）。 -/
theorem reluCompile_solution_set (a b : ℝ) :
    {x : ℝ | ReluConstrSat a b x} = {x : ℝ | reluCompile a b x = 0} := by
  ext x
  exact reluCompile_preserves a b x

/-! ## 三、`a·b = 0` 型乘积约束 -/

/-- 乘积约束 `a*b = 0` 的 sign 编码（非线性零因子结构的最小编译器形式）。 -/
def prodCompile (a b : ℝ) : ℝ := Real.sign (a * b)

/-- **乘积约束的 sign 编码保语义**：`a*b = 0 ⟺ sign(a*b) = 0`。 -/
theorem prodZero_compile (a b : ℝ) : a * b = 0 ↔ prodCompile a b = 0 := by
  unfold prodCompile
  rw [Real.sign_eq_zero_iff]

/-- **乘积约束的零因子分解**：`a*b = 0 ⟺ a = 0 ∨ b = 0`（ℝ 无零因子）。
这把乘积约束归约到两个等式约束的**析取**（非线性结构的语义基础）。 -/
theorem prodZero_iff (a b : ℝ) : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  mul_eq_zero

/-! ## 四、复合约束的编译（sign ∧ relu 逐分量组合） -/

/-- 复合非线性约束：一个 sign 编码的等式部分 + 一个 relu 编码的不等式部分。
例：`a·b = 0` 型约束（等式部分）与 `c ≤ d` 型约束（不等式部分）的合取。 -/
structure NlConstraint where
  /-- sign（等式）部分的一次系数 -/
  sa : ℝ
  /-- sign（等式）部分的常数项 -/
  sb : ℝ
  /-- relu（不等式）部分的一次系数 -/
  ra : ℝ
  /-- relu（不等式）部分的常数项 -/
  rb : ℝ

/-- 复合约束的满足语义：等式部分为零 **且** 不等式部分非正。 -/
def NlSat (c : NlConstraint) (x : ℝ) : Prop :=
  c.sa * x + c.sb = 0 ∧ c.ra * x + c.rb ≤ 0

/-- 复合约束的**编译器**：把两部分分别交给 sign 与 relu 编码，
输出二元组 `(sign 输出, relu 输出)`。 -/
def nlCompile (c : NlConstraint) (x : ℝ) : ℝ × ℝ :=
  (signCompile c.sa c.sb x, reluCompile c.ra c.rb x)

/-- **复合约束的编译保语义**：编译器输出为 `(0,0)` ⟺ 约束满足
（由 `signCompile_preserves` 与 `reluCompile_preserves` 逐分量组合）。 -/
theorem nonlinear_compile_preserves (c : NlConstraint) (x : ℝ) :
    NlSat c x ↔ nlCompile c x = (0, 0) := by
  unfold NlSat nlCompile
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(signCompile_preserves c.sa c.sb x).mp h1,
      (reluCompile_preserves c.ra c.rb x).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(signCompile_preserves c.sa c.sb x).mpr h1,
      (reluCompile_preserves c.ra c.rb x).mpr h2⟩

/-- **批量复合约束**：约束列表中每一条都满足 ⟺ 每一条的编译器输出都为零对。
（合取语义下的保语义；逐条 iff 直接复合。） -/
theorem nlCompile_batch (cs : List NlConstraint) (x : ℝ) :
    (∀ c ∈ cs, NlSat c x) ↔ ∀ c ∈ cs, nlCompile c x = (0, 0) := by
  constructor
  · intro h c hc
    exact (nonlinear_compile_preserves c x).mp (h c hc)
  · intro h c hc
    exact (nonlinear_compile_preserves c x).mpr (h c hc)

/-! ## 五、分段线性函数的编译保持 -/

/-- 分段线性约束程序：断点 `c`，左段（`x ≤ c`）仿射 `fa*x+fb`，
右段（`c < x`）仿射 `ga*x+gb`。 -/
structure PiecewiseConstraint where
  /-- 断点 -/
  c : ℝ
  /-- 左段一次系数 -/
  fa : ℝ
  /-- 左段常数项 -/
  fb : ℝ
  /-- 右段一次系数 -/
  ga : ℝ
  /-- 右段常数项 -/
  gb : ℝ

/-- 分段约束语义：**逐段**成立 —— 左段（`x ≤ c`）与右段（`c < x`）各自满足。 -/
def PiecewiseSat (p : PiecewiseConstraint) (x : ℝ) : Prop :=
  (x ≤ p.c → p.fa * x + p.fb = 0) ∧ (p.c < x → p.ga * x + p.gb = 0)

/-- 分段线性编译器：按断点选择分支，输出该分支的仿射值。 -/
def piecewiseCompile (p : PiecewiseConstraint) : ℝ → ℝ :=
  fun x => if x ≤ p.c then p.fa * x + p.fb else p.ga * x + p.gb

/-- **分段线性编译保语义**：分段编译输出的零化 ⟺ 两条分支在各自区间上分别成立。
证明逐段进行：`x ≤ c` 时用 `if_pos` 取出左分支，
`c < x` 时用 `if_neg`（配 `not_le.mpr`）取出右分支。 -/
theorem piecewise_compile (p : PiecewiseConstraint) (x : ℝ) :
    PiecewiseSat p x ↔ piecewiseCompile p x = 0 := by
  unfold PiecewiseSat piecewiseCompile
  constructor
  · rintro ⟨hf, hg⟩
    by_cases h : x ≤ p.c
    · rw [if_pos h]
      exact hf h
    · rw [if_neg h]
      exact hg (lt_of_not_ge h)
  · intro hz
    constructor
    · intro h
      have hbranch : (if x ≤ p.c then p.fa * x + p.fb else p.ga * x + p.gb)
          = p.fa * x + p.fb := if_pos h
      rw [hbranch] at hz
      exact hz
    · intro h
      have hnot : ¬ x ≤ p.c := not_le.mpr h
      have hbranch : (if x ≤ p.c then p.fa * x + p.fb else p.ga * x + p.gb)
          = p.ga * x + p.gb := if_neg hnot
      rw [hbranch] at hz
      exact hz

/-- 分段编译保解集。 -/
theorem piecewise_compile_solution_set (p : PiecewiseConstraint) :
    {x : ℝ | PiecewiseSat p x} = {x : ℝ | piecewiseCompile p x = 0} := by
  ext x
  exact piecewise_compile p x

/-! ## 六、局部（有界域）保语义 —— 与全局反例 -/

/-- **局部保语义（有界域上的诚实降级）**：
在有界域 `|t| ≤ R` 上，非线性函数 `f` 被仿射函数 `L` 以误差 `ε` 近似
（`RealApprox.ApproxOn f L R ε`），则编译器（`L`）的零点只保证
`f` 在该点处**落在 ε 带内**：`|f t| ≤ ε`。
这是纯线性化下能得到的**最强**结论——精确零点一般不可得。 -/
theorem nonlinear_soundness_local (f L : ℝ → ℝ) (R ε : ℝ) (h : ApproxOn f L R ε) :
    ∀ t : ℝ, |t| ≤ R → L t = 0 → |f t| ≤ ε := by
  intro t ht hz
  have hd : |f t - L t| ≤ ε := h t ht
  simpa [hz] using hd

/-- 局部保语义的严格情形：若近似误差 `ε = 0`，则编译器零点处 `f` 精确为零。 -/
theorem nonlinear_soundness_local_exact (f L : ℝ → ℝ) (R : ℝ)
    (h : ApproxOn f L R 0) :
    ∀ t : ℝ, |t| ≤ R → L t = 0 → f t = 0 := by
  intro t ht hz
  have hle : |f t| ≤ 0 := nonlinear_soundness_local f L R 0 h t ht hz
  exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

/-- **全局版不成立（显式反例）**：存在非线性 `f` 与仿射 `L`，使 `L ≡ 0`
（编译器在所有输入处都报告"满足"），但 `f` 并非处处为零。
故"线性化编译保全局语义"**不可证**——只能得到上面的有界域版本。
（取 `f t = t²`，`L ≡ 0`，反例点 `t = 1`。） -/
theorem linearization_global_fails :
    ∃ (f L : ℝ → ℝ), (∀ t, L t = 0) ∧ ∃ t, f t ≠ 0 := by
  refine ⟨fun t => t ^ 2, fun _ => 0, fun t => rfl, 1, ?_⟩
  norm_num

end Lattice
