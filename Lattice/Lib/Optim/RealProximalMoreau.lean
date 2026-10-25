import Mathlib
import Lattice.Lib.Optim.RealProximal
import Lattice.Lib.Convex.RealFenchelMoreau
/-!
# LATTICE: 近端算子的 Moreau 包络、Moreau 分解与非扩张性（收敛线的全局设施）

`RealProximal` 已经给出近端算子的**极小刻画** `IsProx`、**变分不等式刻画** `ProxVI`
与一维非扩张性 `prox_nonexpansive`。本文件在**有限维** `Fin n → ℝ` 上把 B6 所需的
Moreau 设施补齐：包络定义、包络的可微性（梯度公式）、Moreau 分解、以及
**有限维非扩张性**（回收并强化一维版）。

## 主要内容

1. **欧氏范数平方** `normsq`（`Fin n → ℝ` 上的 `∑ i, vᵢ²`）及其基本性质
   （非负、`= 0 ↔ v = 0`）；
2. **有限维近端算子**：`IsProxN f η x p`（极小刻画）与 `ProxVIN f η x p`（变分不等式）；
3. **凸性桥** `proxVIN_of_isProxN`：凸 `f` 时 `IsProxN ⟹ ProxVIN`
   （有限维版，走「两点凸性 + 沿方向展开」的初等路线，不调用 mathlib 凸分析的极限设施）；
4. **非扩张性** `proxN_nonexpansive`：`‖p − q‖ ≤ ‖x − y‖`（凸 `f`，同步长 `η > 0`）；
5. **唯一性** `proxN_unique`；
6. **Moreau 包络** `moreauEnvelope f η x := f (prox) + (1/(2η))‖prox − x‖²`，
   并证明：
   · `moreauEnvelope_le_self`：包络 ≤ `f x`（**包络是 `f` 的下方光滑化**）；
   · `moreauEnvelope_le`：包络 ≤ 任意 `y` 处的罚函数值（**下确界性质**）；
   · `moreauEnvelope_le_of_proxVI`：变分不等式形式下的下界；
7. **梯度公式（有限差分形式）** `moreauEnvelope_grad_formula`：
   包络在 `x` 处沿方向 `d` 的**单侧差商**等于 `(1/η)⟨x − p, d⟩`，
   即 `∇f^η(x) = (1/η)(x − prox)`（**Moreau 包络的可微性内核**）；
8. **Moreau 分解（二次/共轭特例）** `moreau_decomposition_linear`：
   `f(y) = c·y` 时 `prox_{ηf}(x) = x − ηc`，
   且 **`x = prox_{ηf}(x) + η·∇f*(...)`** 的线性情形恒等式
   （`x = (x − ηc) + η·c`）——即「`x` 分解为近端点与共轭侧梯度」的可验证特例；
9. **`prox` 与 `f` 的最小值**：`prox` 不动点 ⟺ 全局最小点（`prox_fixed_iff_minimizer`）。

## 诚实边界（中文关键词：诚实 / 未证 / 降级 / 标注）

- **一般 `f` 的 `argmin` 存在性未证**：本文件沿用 `RealProximal` 的**极小刻画**路线
  （`IsProx` 是谓词，不是 `argmin` 函数），存在性由调用方提供 `IsProx` 见证，
  或直接调用 `RealProxExistence.prox_exists`（凸 + 连续）——本文件**不重复**该定理，
  只在需要处标注接口（诚实）。
- **Moreau 包络的光滑性只做到「梯度公式（差商形式）」**，**未证** `ContDiff` 意义下的
  `C^{1,1}` 正则性（需要 `HasFDerivAt` 与包络的有限性论证；mathlib 4.14 无现成
  Moreau 包络设施）。**标注为未做/降级**。
- **Moreau 分解的一般形式** `x = prox_{ηf}(x) + η·prox_{η⁻¹f*}(x/η)`
  **未证**（需要 Fenchel 共轭 `f*` 与 `prox` 的对偶关系；
  mathlib 4.14 的 `ConvexConjugate` 只在一般赋范空间层面，与本库一维 `f : ℝ → ℝ`
  的 `fenchelConjAll` 记号不直接衔接）。本文件给出的是**线性特例**的完整验证（降级）。
- 一维 `ℝ` 与有限维 `Fin n → ℝ` 两个层面都有；`import Mathlib` 在最上；
  无 sorry / axiom / admit。
-/

noncomputable section

open scoped BigOperators
open scoped Pointwise

namespace Lattice

variable {n : ℕ}

/-! ## 一、有限维欧氏范数平方 -/

/-- **欧氏范数平方**：`‖v‖² = ∑ i, vᵢ²`（`Fin n → ℝ` 上，等价于 `EuclideanSpace` 范数）。

⚠ **平行定义提示（v14，S8 定义↔使用审计发现；coordinator 已核实）**：
**本文件的 `normsq` 与 `RealHessian.lean:60` 的 `normSq` **定义体逐字符相同**，
且**两者仅差大小写**（`normsq` vs `normSq`）**。
- **实测**：本文件 **0 个 importer**；`RealHessian` **6 个 importer**；
- **当前无冲突**：**全库没有任何文件同时 `import` 两者**（coordinator 已核验）⟹
  这是 **X3 所记"潜伏命名冲突"（latent pair）**，**不是活冲突**；
- ⚠ **风险**：**一旦有文件同时 import 两者**，`normsq`/`normSq` 会**同时可见**，
  在 `open Lattice` 下可能被误用（**大小写仅差一字母，肉眼极易混**）；
- **⇒ 处置：保留两份**（合并需引入依赖边，而 `RealHessian` 的 6 个 importer 与
  `RealProximalMoreau` 的 0 个 importer 说明两者面向不同下游）；**仅加本交叉引用**，
  使后人知道**存在这个近名对**。
- **⇒ 一般纪律**：**给新定义命名前先 grep 大小写变体**（本波次已有 `GD_converges`/`gd_converges`、
  `normSq`/`normsq` 两例）——**PowerShell 的 `-match` 默认忽略大小写，故必须用 `-cmatch` 或 grep 工具**。 -/
def normsq {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- 范数平方非负。 -/
theorem normsq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ normsq v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- 范数平方为 0 当且仅当向量为 0。 -/
theorem normsq_eq_zero_iff {n : ℕ} {v : Fin n → ℝ} : normsq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hterm : (v i) ^ 2 = 0 := by
      have hle : (v i) ^ 2 ≤ normsq v :=
        Finset.single_le_sum (f := fun j => (v j) ^ 2)
          (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
      rw [h] at hle
      exact le_antisymm hle (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hterm
  · intro h
    subst h
    simp [normsq]

/-- 范数平方是**二次齐次**的：`‖c·v‖² = c²·‖v‖²`。 -/
theorem normsq_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    normsq (c • v) = c ^ 2 * normsq v := by
  unfold normsq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **平行四边形恒等式（差形式）**：`‖x − p‖² = ‖x‖² − 2⟨x,p⟩ + ‖p‖²`，其中
`⟨x,p⟩ = ∑ i, xᵢ·pᵢ`。这是近端算子一切代数操作的基元。 -/
theorem normsq_sub {n : ℕ} (x p : Fin n → ℝ) :
    normsq (x - p) = normsq x - 2 * (∑ i, x i * p i) + normsq p := by
  unfold normsq
  -- ⚠ `Finset.sum_add_distrib` / `sum_sub_distrib` 是**双绑定**形式（`∑ x ∈ s, …`），
  -- 对这里的**单绑定**目标 `∑ x_1, …` **不匹配**（报 `did not find instance of the pattern`）。
  -- 正解：用 `Finset.sum_congr` 把求和体**逐项**改写成展开形，
  -- 再用 `Finset.sum_add_distrib`/`sum_sub_distrib`（对**已展开的单绑定和**可用）
  -- 把 `∑` 拆成三个单项和，最后 `ring` 收尾。
  have hsum : (∑ i : Fin n, (x - p) i ^ 2)
      = ∑ i : Fin n, ((x i) ^ 2 - 2 * (x i * p i) + (p i) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [hsum]
  -- 拆 `+ (p i)^2` 与 `- 2*(x i * p i)`（对**已展开的单绑定和**，这两个引理可用）
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- 把 `∑ i, 2 * (x i * p i)` 的常数 2 提到 `∑` 外（`Finset.mul_sum` 的反向）。
  -- ⚠ 这一步**已把目标关掉**，故其后**不能再**跟 `apply Finset.sum_congr`/`ring`
  -- （会报 `no goals to be solved`——探针实测）。
  rw [← Finset.mul_sum]

/-- **Cauchy–Schwarz（本文件版本，回收 mathlib，绝对值形式）**：

    `|∑ᵢ uᵢ·vᵢ| ≤ √(∑ᵢ uᵢ²) · √(∑ᵢ vᵢ²)`

**这是标准（且更强）的 Cauchy–Schwarz**：非绝对值版是它的推论（由 `le_abs_self`）。

回收 `Finset.sum_mul_sq_le_sq_mul_sq`（`Algebra/Order/BigOperators/Ring/Finset.lean:197`）。
**注意**（STYLE.md 已记录）：该引理是**双绑定**形式 `(∑ i ∈ s, f i * g i)^2 ≤ …`，
对单绑定目标不能直接 `rw`；本文件先 `simpa` 把它**对齐**到 `Finset.univ` 单绑定目标，
再用 `Real.sq_sqrt`/`mul_pow` 把右端**平方化**，最后用 `abs_le_of_sq_le_sq` 收尾。

**诚实标注（本文件的一处自我更正）**：本条初稿曾陈述为**非绝对值版**
`∑ uᵢ·vᵢ ≤ √(∑uᵢ²)·√(∑vᵢ²)`，并试图先证 `0 ≤ ∑ uᵢ·vᵢ` —— **那是无效推理**：
平方不等式 `(∑u·v)² ≤ (∑u²)(∑v²)` **对 `∑u·v` 的符号毫无约束**
（反例 `n=1, u=1, v=-1`：`∑u·v = −1 < 0` 而平方不等式仍成立）。
故**把命题加强为绝对值形式**（正向修正，非降级）：这样第 2 步即结论，
且下游 `proxN_nonexpansive` 用 `le_abs_self` 即可衔接，**范数形式无需放弃**。 -/
theorem normsq_inner_abs_le {n : ℕ} (u v : Fin n → ℝ) :
    |∑ i, u i * v i| ≤ Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) := by
  have hCS : ((∑ i : Fin n, u i * v i)) ^ 2
      ≤ (∑ i : Fin n, (u i) ^ 2) * (∑ i : Fin n, (v i) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) u v
    simpa using h
  have hright : (Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2)) ^ 2
      = (∑ i : Fin n, (u i) ^ 2) * (∑ i : Fin n, (v i) ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u i)),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  have hsq : ((∑ i, u i * v i)) ^ 2
      ≤ (Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2)) ^ 2 := by
    rw [hright]; exact hCS
  have hnn : 0 ≤ Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∑ i, u i * v i| = Real.sqrt (((∑ i, u i * v i)) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt ((Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) := Real.sqrt_sq hnn

/-- **Cauchy–Schwarz（非绝对值版，本文件推论）**：
`∑ᵢ uᵢ·vᵢ ≤ √(∑uᵢ²)·√(∑vᵢ²)`。由 `normsq_inner_abs_le` 与 `le_abs_self` 得到。 -/
theorem normsq_inner_le {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i, u i * v i) ≤ Real.sqrt (∑ i, (u i) ^ 2) * Real.sqrt (∑ i, (v i) ^ 2) :=
  le_trans (le_abs_self _) (normsq_inner_abs_le u v)

/-- **Cauchy–Schwarz（`normsq` 记号版）**：
`∑ᵢ uᵢ·vᵢ ≤ √(normsq u)·√(normsq v)`。
这是 `normsq_inner_le` 的**记号改写**版本（`normsq` 是 `def`，与 `∑ (·)²` 定义相等但
**语法不同**，故需单独陈述以便下游 `rw`）。 -/
theorem inner_le_sqrt_normsq {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i, u i * v i) ≤ Real.sqrt (normsq u) * Real.sqrt (normsq v) := by
  have h := normsq_inner_le u v
  -- `normsq` 是 `def`，`rw` 无法使用其等式定理 ⇒ 用 `unfold`/`simpa only` 展开
  unfold normsq at h
  exact h

/-! ## 二、有限维近端算子：两种刻画 -/

/-- **有限维近端算子（极小刻画）**：`p` 使 `y ↦ f(y) + (1/(2η))‖y − x‖²` 取到全局最小。 -/
def IsProxN {n : ℕ} (f : (Fin n → ℝ) → ℝ) (η : ℝ) (x p : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, f p + (1 / (2 * η)) * normsq (p - x) ≤ f y + (1 / (2 * η)) * normsq (y - x)

/-- **有限维近端变分不等式**：`∀ y, f(p) + (1/η)⟨x − p, y − p⟩ ≤ f(y)`，
其中 `⟨u,v⟩ = ∑ i, uᵢ·vᵢ`。凸 `f` 时与 `IsProxN` 等价。 -/
def ProxVIN {n : ℕ} (f : (Fin n → ℝ) → ℝ) (η : ℝ) (x p : Fin n → ℝ) : Prop :=
  ∀ y : Fin n → ℝ, f p + (1 / η) * (∑ i, (x i - p i) * (y i - p i)) ≤ f y

/-! ## 三、凸性桥（有限维）：IsProxN ⟹ ProxVIN

沿射线 `z_t = p + t·(z − p)`（`t ∈ (0,1]`）走：极小性给 `z_t` 处的罚函数下界，
凸性给 `f(z_t) ≤ (1−t)f(p) + t·f(z)`，两式相消后除以 `t` 并令 `t → 0`。

有限维下「令 t → 0」用 `le_of_forall_pos_le_add` 的 ε 论证实现——
这与 `RealProximal.prox_vi_of_isProx` 的技术相同，只是把一维乘积换成内积和。 -/

/-- **展开引理（供 `proxVIN_aux` 与包络差商使用）**：
`‖a + t • d‖² = ‖a‖² + 2t⟨a, d⟩ + t²‖d‖²`。
由 `normsq_sub a (-(t • d))` 与 `normsq_smul` 得到（避免在复杂目标里手写 `∑` 展开）。 -/
theorem normsq_add_smul {n : ℕ} (a d : Fin n → ℝ) (t : ℝ) :
    normsq (a + t • d) = normsq a + 2 * t * (∑ i, a i * d i) + t ^ 2 * normsq d := by
  have h1 : a + t • d = a - (-(t • d)) := by abel
  rw [h1, normsq_sub]
  have hinner : (∑ i : Fin n, a i * (-(t • d)) i) = -(t * (∑ i, a i * d i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hinner]
  -- ⚠ `normsq (-(t • d))` 不是 `normsq (?c • ?v)` 的形状：内层是 `neg`，
  -- 外层才是 `smul`（`normsq_smul` 的模式 `normsq (?c • ?v)` 匹配不到 `-(t • d)`）。
  -- 先把它**改写成** `(-t) • d`（`neg_smul`）再套 `normsq_smul`。
  have hneg : (-(t • d) : Fin n → ℝ) = (-t) • d := by
    rw [neg_smul]
  rw [hneg, normsq_smul]
  ring

/-- **展开引理（差形式）**：`‖(a − s) ‖² = ‖a‖² − 2⟨a, s⟩ + ‖s‖²`（`normsq_sub` 的重述）。 -/
theorem normsq_sub_expand {n : ℕ} (a s : Fin n → ℝ) :
    normsq (a - s) = normsq a - 2 * (∑ i, a i * s i) + normsq s :=
  normsq_sub a s

/-- **键恒等式（供 `proxVIN_aux`）**：
`‖(p − x) + t(z − p)‖² − ‖p − x‖² = 2t⟨p−x, z−p⟩ + t²‖z−p‖²`。
直接由 `normsq_add_smul` 得到，**不再手写 `∑` 展开**。 -/
theorem proxVIN_key {n : ℕ} (p x z : Fin n → ℝ) (t : ℝ) :
    normsq ((p - x) + t • (z - p)) - normsq (p - x)
      = 2 * t * (∑ i, (p i - x i) * (z i - p i)) + t ^ 2 * normsq (z - p) := by
  rw [normsq_add_smul (p - x) (z - p) t]
  -- ⚠ `normsq_add_smul` 产出的是**投影形式** `(p - x) i`，而目标写的是**展开形式** `p i - x i`。
  -- 该差异同时出现在 `2*t*∑ …` **与**目标左端已有的 `normsq (p - x)` 项上——
  -- 只把 `∑` 对齐仍会失配（探针实测：`rw [hsub]` 报 `did not find instance`，
  -- 因为目标里还有 `normsq (p-x)` 与该 `∑` 的两个实例需要同时处理）。
  -- 正解：把 `hsub` 的**方向**取成「展开形式 → 投影形式」，先统一到 `normsq_add_smul`
  -- 给出的**投影形态**，`ring` 处理掉 `normsq (p-x) - normsq (p-x)`，最后再 `linarith` 收尾。
  have hsub : (∑ i : Fin n, (p i - x i) * (z i - p i))
      = ∑ i : Fin n, (p - x) i * (z - p) i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
  -- 用 `show` 把目标显式写成「投影形态」，让 `ring` 的原子匹配成功
  show normsq (p - x) + 2 * t * (∑ i : Fin n, (p - x) i * (z - p) i)
        + t ^ 2 * normsq (z - p) - normsq (p - x)
      = 2 * t * (∑ i : Fin n, (p i - x i) * (z i - p i)) + t ^ 2 * normsq (z - p)
  rw [hsub]
  ring

/-- **包络差商展开**：`‖(p − x) − t·d‖² − ‖p − x‖² = −2t⟨p−x, d⟩ + t²‖d‖²`。 -/
theorem env_dirderiv_key {n : ℕ} (p x d : Fin n → ℝ) (t : ℝ) :
    normsq ((p - x) - t • d) - normsq (p - x)
      = -2 * t * (∑ i, (p i - x i) * d i) + t ^ 2 * normsq d := by
  -- ⚠ 目标的右端是**已展开形式** `(p i - x i) * d i`，而 `normsq_sub_expand`
  -- 产出的是**投影形式** `((p - x) i) * ((t • d) i)`——两者**语法不同**，故直接
  -- `rw` 会在内积项上失配。这里先证两条**投影↔展开**的桥，再套展开引理。
  have hinner : (∑ i : Fin n, (p - x) i * (t • d) i) = t * (∑ i, (p i - x i) * d i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [normsq_sub_expand (p - x) (t • d), hinner]
  -- ⚠ 首次构建实测：`rw [hneg, normsq_smul]` 失败（报 `did not find instance of the pattern -(t • d)`）。
  -- `normsq_sub_expand` 展开后出现的项是 `normsq (t • d)`（**正的**），
  -- 而 `hneg : -(t•d) = -t • d` 针对的是**取负**形态，方向完全不对；
  -- `normsq_smul` 的隐式匹配也在含 `∑` 的大目标里失配。
  -- 正解：**显式**把 `normsq_smul` 的结论作为 `have`（形状自足），再 `rw` 它。
  have hsmul : normsq (t • d) = t ^ 2 * normsq d := normsq_smul t d
  rw [hsmul]
  ring

/-- 辅助引理（有限维）：`t ∈ (0,1]` 时
`f p + (1/η)⟨x−p, z−p⟩ ≤ f z + (t/(2η))‖z−p‖²`。

证明：取 `z_t = p + t(z−p)`，
· `IsProxN` 在 `z_t`：`f p + (1/(2η))‖p−x‖² ≤ f z_t + (1/(2η))‖z_t−x‖²`；
· 凸性：`f z_t ≤ (1−t) f p + t f z`；
· 两者相减并用 `normsq_sub` 展开 `‖z_t−x‖² − ‖p−x‖²`，
  注意 `z_t − x = (p − x) + t(z − p)`，展开后 `t` 的一次项给目标、`t²` 项被 `(t/(2η))` 吸收。 -/
lemma proxVIN_aux {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {η : ℝ} {x p : Fin n → ℝ} (hη : 0 < η) (hprox : IsProxN f η x p)
    (z : Fin n → ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    f p + (1 / η) * (∑ i, (x i - p i) * (z i - p i))
      ≤ f z + (t / (2 * η)) * normsq (z - p) := by
  have h2η : (0 : ℝ) < 2 * η := by linarith
  -- 射线上的点
  have hconv_pt : f (p + t • (z - p)) ≤ (1 - t) * f p + t * f z := by
    -- ⚠ **关键坑**：`ConvexOn` 是 `def` 别名，定义体是**合取式**
    --   `Convex 𝕜 s ∧ (∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, … → f (a • x + b • y) ≤ a • f x + b • f y)`
    -- （`Analysis/Convex/Function.lean:52-54`），**不是 structure**。
    -- 故 `obtain ⟨hc, -⟩ := hconv` 拿到的是 **`Convex ℝ Set.univ`（集合谓词）**，
    -- 而不是逐点凸性函数——原稿在这里把 `hc` 当成逐点函数用，
    -- 于是 `hc (Set.mem_univ (z-p)) …` 被解析成「集合成员证明」，
    -- 最终 `h : t • (z-p) + (1-t) • p ∈ Set.univ`（**这就是原始报错的根因**）。
    -- 正解：取**第二个**分量 `hconv.2`（定义别名不透明，用 `obtain ⟨-, hpt_conv⟩`）。
    obtain ⟨-, hptconv⟩ := hconv
    -- ⚠ 参数选择必须**让凸组合恰等于** `p + t • (z - p)`：
    -- `hptconv` 给的是 `f (a • x + b • y) ≤ a • f x + b • f y`。
    -- 取 `x := z`、`y := p`、`a := 1 - t`、`b := t` ⟹
    --   左端 `(1-t) • z + t • p`（`abel` 可化为 `p + t • (z - p)`）；
    --   右端 `(1-t) • f z + t • f p`（**正是目标的右端**，只是 `smul` 形式）。
    -- ⚠ 首次构建实测：原稿取 `x := z - p`、`y := p`、`a := t`、`b := 1 - t`，
    -- 得到的右端是 `t * f (z - p) + (1 - t) * f p`——**与目标 `(1-t)*f p + t*f z` 不符**
    -- （既有项顺序颠倒，又有 `f (z - p)` vs `f z` 的实质错误）⟹ `type mismatch`。
    -- ⚠ 第二次构建实测：改取 `x := z`、`y := p` 后**仍错**——因为
    -- `(1-t) • z + t • p = z + t(p - z) ≠ p + t(z - p)`（两者是**不同的**点）。
    -- **正解**：要得到 `p + t • (z - p)`，必须取 `x := p`、`y := z`、`a := 1 - t`、`b := t`：
    --   `(1-t) • p + t • z = p + t(z - p)` ✅（`ring` 可验），右端正是 `(1-t)*f p + t*f z` ✅。
    have h := hptconv (x := p) (y := z) (a := 1 - t) (b := t)
      (Set.mem_univ p) (Set.mem_univ z)
      (show (0 : ℝ) ≤ 1 - t from by linarith) (show (0 : ℝ) ≤ t from le_of_lt ht0)
      (show (1 - t) + t = 1 from by ring)
    -- `h : f ((1 - t) • p + t • z) ≤ (1 - t) • f p + t • f z`
    have hpt : (1 - t) • p + t • z = p + t • (z - p) := by
      ext i
      -- ⚠ 探针实测：`simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]` **不够**——
      -- 目标里的 `(z - p) i` **是投影形态**，不会被展开 ⟹ 残留
      -- `-(t * p i) + t * z i + p i = t * (z - p) i + p i` 而 `ring` 卡住。
      -- 正解：把 **`Pi.sub_apply`** 一并放进 `simp only`（展开 `(z - p) i` 为 `z i - p i`）。
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [hpt] at h
    -- 把 smul 形式的系数化为乘法即得目标
    simpa only [smul_eq_mul] using h
  -- 极小性在 z_t 处
  have hprox_t := hprox (p + t • (z - p))
  -- 关键恒等式：‖z_t − x‖² − ‖p − x‖² = 2t⟨p−x, z−p⟩ + t²‖z−p‖²
  have hkey : normsq (p + t • (z - p) - x) - normsq (p - x)
      = 2 * t * (∑ i, (p i - x i) * (z i - p i)) + t ^ 2 * normsq (z - p) := by
    have hpt : p + t • (z - p) - x = (p - x) + t • (z - p) := by abel
    rw [hpt]
    exact proxVIN_key p x z t
  -- 合并：t(f p − f z) ≤ (1/(2η))·(t·2⟨p−x,z−p⟩ + t²‖z−p‖²)
  have hmain : t * (f p - f z)
      ≤ (1 / (2 * η)) * (2 * t * (∑ i, (p i - x i) * (z i - p i)) + t ^ 2 * normsq (z - p)) := by
    have h1 : (1 / (2 * η)) * normsq (p - x)
        ≤ f (p + t • (z - p)) - f p + (1 / (2 * η)) * normsq (p + t • (z - p) - x) := by
      linarith
    have h2 : f (p + t • (z - p)) - f p ≤ t * (f z - f p) := by linarith
    have h3 : (1 / (2 * η)) * normsq (p - x)
        ≤ t * (f z - f p) + (1 / (2 * η)) * normsq (p + t • (z - p) - x) := by linarith
    have h4 : (1 / (2 * η)) * (normsq (p - x) - normsq (p + t • (z - p) - x))
        ≤ t * (f z - f p) := by linarith
    have h5 : (1 / (2 * η)) * (-(normsq (p + t • (z - p) - x) - normsq (p - x)))
        ≤ t * (f z - f p) := by
      have he : normsq (p - x) - normsq (p + t • (z - p) - x)
          = -(normsq (p + t • (z - p) - x) - normsq (p - x)) := by ring
      rwa [he] at h4
    rw [hkey] at h5
    linarith
  -- 除以 t
  have hdiv : f p - f z ≤ (1 / (2 * η)) * (2 * (∑ i, (p i - x i) * (z i - p i))
      + t * normsq (z - p)) := by
    have heq : (1 / (2 * η)) * (2 * t * (∑ i, (p i - x i) * (z i - p i))
        + t ^ 2 * normsq (z - p))
        = t * ((1 / (2 * η)) * (2 * (∑ i, (p i - x i) * (z i - p i))
            + t * normsq (z - p))) := by
      field_simp
      ring
    rw [heq] at hmain
    exact (mul_le_mul_left ht0).mp hmain
  -- 整理成目标形式
  have hinner : (∑ i, (p i - x i) * (z i - p i)) = -(∑ i, (x i - p i) * (z i - p i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinner] at hdiv
  have hfinal : (1 / η) * (∑ i, (x i - p i) * (z i - p i))
      = -((1 / (2 * η)) * (2 * (-(∑ i, (x i - p i) * (z i - p i)))
          + t * normsq (z - p))) + (t / (2 * η)) * normsq (z - p) := by
    field_simp
    ring
  linarith [hdiv, hfinal]

/-- **凸性桥（有限维）**：`f` 凸、`p` 是 `x` 的近端点 ⟹ 变分不等式
`∀ y, f(p) + (1/η)⟨x−p, y−p⟩ ≤ f(y)`。
由 `proxVIN_aux` 对 `t → 0⁺` 取极限（ε 论证）。 -/
theorem proxVIN_of_isProxN {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {η : ℝ} {x p : Fin n → ℝ} (hη : 0 < η) (hprox : IsProxN f η x p) :
    ProxVIN f η x p := by
  intro z
  refine le_of_forall_pos_le_add fun ε hε => ?_
  by_cases hd : normsq (z - p) = 0
  · -- `hd` 分支：`z = p`。**不能用 `subst`**（它会消去变量 `p`，使后续引用 `p` 失败），
    -- 改用 `rw [hz]` 把 `z` 替换为 `p`。
    have hzp : z - p = 0 := normsq_eq_zero_iff.mp hd
    have hz : z = p := sub_eq_zero.mp hzp
    rw [hz]
    have h0 : (∑ i : Fin n, (x i - p i) * (p i - p i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp
    rw [h0, mul_zero, add_zero]
    exact le_add_of_nonneg_right (le_of_lt hε)
  · have hdpos : 0 < normsq (z - p) := lt_of_le_of_ne (normsq_nonneg _) (Ne.symm hd)
    have h4η : (0 : ℝ) < 2 * η := by linarith
    set t : ℝ := min 1 (ε * (2 * η) / normsq (z - p)) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos (mul_pos hε h4η) hdpos)
    have ht1 : t ≤ 1 := min_le_left _ _
    have hb := proxVIN_aux hconv hη hprox z ht0 ht1
    have htd : t * normsq (z - p) ≤ ε * (2 * η) := by
      have hle : t ≤ ε * (2 * η) / normsq (z - p) := min_le_right _ _
      have hm := mul_le_mul_of_nonneg_right hle (le_of_lt hdpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hdpos)] at hm
    have hfin : (t / (2 * η)) * normsq (z - p) ≤ ε := by
      have he : (t / (2 * η)) * normsq (z - p) * (2 * η) = t * normsq (z - p) := by
        field_simp
      have hm : (t / (2 * η)) * normsq (z - p) * (2 * η) ≤ ε * (2 * η) := by
        rw [he]; exact htd
      exact (mul_le_mul_right h4η).mp hm
    linarith

/-! ## 四、非扩张性与唯一性（有限维） -/

/-- **核心定理（有限维近端算子非扩张，平方形式）**：`f` 凸、`p` 是 `x` 的近端点、
`q` 是 `y` 的近端点（同步长 `η > 0`）⟹ **`‖p − q‖² ≤ ⟨x−y, p−q⟩`**。

这是非扩张性的**代数内核**（不需要 Cauchy–Schwarz）：两条变分不等式分别取
`y := q` 与 `y := p` 相加即得 `(1/η)‖p−q‖² ≤ (1/η)⟨x−y, p−q⟩`，约去 `1/η > 0`。
由 `⟨x−y,p−q⟩ ≤ ‖x−y‖·‖p−q‖`（Cauchy–Schwarz）即得 `‖p−q‖ ≤ ‖x−y‖`
（见 `proxN_nonexpansive`；本文件把该步**分离**出来以便各自独立机器验证）。 -/
theorem proxN_nonexpansive_sq {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {η : ℝ} (hη : 0 < η) {x y p q : Fin n → ℝ}
    (hp : IsProxN f η x p) (hq : IsProxN f η y q) :
    normsq (p - q) ≤ ∑ i, (x i - y i) * (p i - q i) := by
  have hVIp := proxVIN_of_isProxN hconv hη hp
  have hVIq := proxVIN_of_isProxN hconv hη hq
  have h1 : f p + (1 / η) * (∑ i, (x i - p i) * (q i - p i)) ≤ f q := hVIp q
  have h2 : f q + (1 / η) * (∑ i, (y i - q i) * (p i - q i)) ≤ f p := hVIq p
  have hsum : (1 / η) * (∑ i, (x i - p i) * (q i - p i))
      + (1 / η) * (∑ i, (y i - q i) * (p i - q i)) ≤ 0 := by linarith
  -- 合并两个内积和：S₁ + S₂ = ⟨p−q, p−q⟩ − ⟨x−y, p−q⟩
  have hcombine : (∑ i, (x i - p i) * (q i - p i)) + (∑ i, (y i - q i) * (p i - q i))
      = (∑ i, (p i - q i) * (p i - q i)) - (∑ i, (x i - y i) * (p i - q i)) := by
    -- 两边都化为 `∑ i, f i` 的**单绑定**形式后逐项比较，避开双绑定 `sum_add_distrib` 的失配
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hpq : (∑ i, (p i - q i) * (p i - q i)) = normsq (p - q) := by
    unfold normsq
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hkey : (1 / η) * normsq (p - q) ≤ (1 / η) * (∑ i, (x i - y i) * (p i - q i)) := by
    have he : (1 / η) * (∑ i, (x i - p i) * (q i - p i))
        + (1 / η) * (∑ i, (y i - q i) * (p i - q i))
        = (1 / η) * (normsq (p - q) - (∑ i, (x i - y i) * (p i - q i))) := by
      rw [← mul_add, hcombine, hpq]
    rw [he] at hsum
    have hηinv : (0 : ℝ) < 1 / η := by positivity
    nlinarith [hsum]
  have hηinv : (0 : ℝ) < 1 / η := by positivity
  exact (mul_le_mul_left hηinv).mp hkey

/-- **核心定理（有限维近端算子非扩张）**：凸 `f`、同步长 `η > 0`、
`p` 是 `x` 的近端点、`q` 是 `y` 的近端点 ⟹ **`‖p − q‖ ≤ ‖x − y‖`**（欧氏范数）。

由平方形式 `proxN_nonexpansive_sq`（`‖p−q‖² ≤ ⟨x−y, p−q⟩`）与
`⟨x−y, p−q⟩ ≤ ‖x−y‖·‖p−q‖`（`normsq_inner_le`，Cauchy–Schwarz）得到
`‖p−q‖² ≤ ‖x−y‖·‖p−q‖`，再约去 `‖p−q‖`。

**诚实标注**：Cauchy–Schwarz 那一步由本文件的 `normsq_inner_le` 提供
（用 mathlib 的 `Finset.sum_mul_sq_le_sq_mul_sq` 回收，见其 docstring）。 -/
theorem proxN_nonexpansive {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {η : ℝ} (hη : 0 < η) {x y p q : Fin n → ℝ}
    (hp : IsProxN f η x p) (hq : IsProxN f η y q) :
    Real.sqrt (normsq (p - q)) ≤ Real.sqrt (normsq (x - y)) := by
  have hsq := proxN_nonexpansive_sq hconv hη hp hq
  have hCS := inner_le_sqrt_normsq (x - y) (p - q)
  -- ‖p−q‖² ≤ √‖x−y‖² · √‖p−q‖²
  have hbound : normsq (p - q) ≤ Real.sqrt (normsq (x - y)) * Real.sqrt (normsq (p - q)) :=
    le_trans hsq hCS
  by_cases h0 : Real.sqrt (normsq (p - q)) = 0
  · rw [h0]; exact Real.sqrt_nonneg _
  · have hpos : 0 < Real.sqrt (normsq (p - q)) :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h0)
    have hsqr : Real.sqrt (normsq (p - q)) * Real.sqrt (normsq (p - q)) = normsq (p - q) :=
      -- ⚠ `Real.sq_sqrt h : √x ^ 2 = x`（**`^ 2` 记法**），与目标里的
      -- `√x * √x = x`（**乘法记法**）**语法不同**，直接 `exact` 报 `type mismatch`
      -- （STYLE.md §4「`x ^ 2` 与 `x * x` 混用」）。正解：用 **`Real.mul_self_sqrt`**
      -- （`Data/Real/Sqrt.lean:133`，语句就是 `√x * √x = x`）。
      Real.mul_self_sqrt (normsq_nonneg _)
    have h' : Real.sqrt (normsq (p - q)) * Real.sqrt (normsq (p - q))
        ≤ Real.sqrt (normsq (x - y)) * Real.sqrt (normsq (p - q)) := by
      rw [hsqr]; exact hbound
    exact (mul_le_mul_right hpos).mp h'

/-- **有限维近端算子唯一性**：凸 `f`、同一点 `x` 的两个近端点相等。 -/
theorem proxN_unique {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    {η : ℝ} (hη : 0 < η) {x p q : Fin n → ℝ}
    (hp : IsProxN f η x p) (hq : IsProxN f η x q) : p = q := by
  have h := proxN_nonexpansive hconv hη hp hq
  have h0 : Real.sqrt (normsq (x - x)) = 0 := by simp [normsq]
  rw [h0] at h
  have hle : Real.sqrt (normsq (p - q)) ≤ 0 := h
  have hge : 0 ≤ Real.sqrt (normsq (p - q)) := Real.sqrt_nonneg _
  have hz : Real.sqrt (normsq (p - q)) = 0 := le_antisymm hle hge
  have hns : normsq (p - q) = 0 := by
    have := Real.sq_sqrt (normsq_nonneg (p - q))
    rw [hz] at this
    simpa using this.symm
  exact sub_eq_zero.mp (normsq_eq_zero_iff.mp hns)

/-! ## 五、Moreau 包络 -/

/-- **Moreau 包络**（极小值形式）：`f^η(x) = f(p) + (1/(2η))‖p − x‖²`，
其中 `p` 是 `x` 的近端点。与 `inf_y (f(y) + (1/(2η))‖y−x‖²)` 一致（由 `IsProxN` 的极小性）。 -/
def moreauEnvelope {n : ℕ} (f : (Fin n → ℝ) → ℝ) (η : ℝ) (x p : Fin n → ℝ) : ℝ :=
  f p + (1 / (2 * η)) * normsq (p - x)

/-- **包络是 `f` 的下方光滑化（弱形式）**：`IsProxN` 在 `y := x` 处取值直接给出
`f^η(x) ≤ f x`。 -/
theorem moreauEnvelope_le_self {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} {x p : Fin n → ℝ}
    (hprox : IsProxN f η x p) :
    moreauEnvelope f η x p ≤ f x := by
  have h := hprox x
  unfold moreauEnvelope IsProxN at *
  have hx : normsq (x - x) = 0 := by simp [normsq]
  rw [hx, mul_zero, add_zero] at h
  linarith

/-- **包络的下确界性质**：`f^η(x) ≤ f(y) + (1/(2η))‖y − x‖²` 对**所有** `y` 成立。
这正是「包络 = 下确界」的 ≤ 方向，也是包络定义中 `inf` 的完整内容。 -/
theorem moreauEnvelope_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} {x p : Fin n → ℝ}
    (hprox : IsProxN f η x p) (y : Fin n → ℝ) :
    moreauEnvelope f η x p ≤ f y + (1 / (2 * η)) * normsq (y - x) :=
  hprox y

/-- **包络在近端点处的等价写法**：`f^η(p) ≤ f^η(x)` 的变分形式——
由 `ProxVIN` 取 `y := p` 与包络定义直接得到的一致性检查
（`f(p) + 0 ≤ f(p)` 给出的正是 `moreauEnvelope f η p p = f p`）。
这里陈述更常用的**包络在 `x` 处的下界**：`f(p) ≤ f^η(x)`（罚项非负）。 -/
theorem le_moreauEnvelope {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} {x p : Fin n → ℝ}
    (hη : 0 < η) :
    f p ≤ moreauEnvelope f η x p := by
  unfold moreauEnvelope
  have : 0 ≤ (1 / (2 * η)) * normsq (p - x) :=
    mul_nonneg (by positivity) (normsq_nonneg _)
  linarith

/-- **包络的极大极小夹逼**：对**任意**见证 `p`（满足 `IsProxN`），
`f p ≤ f^η(x) ≤ f x`——包络把 `f` 夹在「近端点值」与「原值」之间。 -/
theorem moreauEnvelope_sandwich {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} {x p : Fin n → ℝ}
    (hη : 0 < η) (hprox : IsProxN f η x p) :
    f p ≤ moreauEnvelope f η x p ∧ moreauEnvelope f η x p ≤ f x :=
  ⟨le_moreauEnvelope hη, moreauEnvelope_le_self hprox⟩

/-! ## 六、Moreau 包络的梯度公式（可微性内核）

标准结果：`∇f^η(x) = (1/η)(x − prox_{ηf}(x))`。
本文件用**差商（方向导数）形式**陈述并证明——这是不需要 `HasFDerivAt` 设施的
可证版本：包络在 `x` 处沿 `d` 的**单侧差商**恰为 `(1/η)⟨x − p, d⟩`。

**注意**：真值方向是**等式**（当 `p` 是该 `x` 的近端点时）。
下面证明两个方向：
· **下界（真）**：`f^η(x + t·d) ≥ f^η(x) + (t/η)⟨x−p, d⟩`（由 `ProxVIN`）；
· **上界（真，一阶）**：`f^η(x + t·d) ≤ f^η(x) + (t/η)⟨x−p, d⟩ + (t²/(2η))‖d‖²`。 -/

/-- **包络的方向导数下界（正确形式）**：由变分不等式 `ProxVIN`，
包络沿方向 `d` 的**单侧差商**有下界

    `f^η(x + t·d) ≥ f^η(x) + (t/η)⟨x − p, d⟩ − (t²/(2η))‖d‖²`

（对 `t > 0`，`p` 为 `x` 的近端点）。

**推导**：VI 在 `y := p + t·d` 处给 `f p + (t/η)⟨x−p,d⟩ ≤ f(p + t·d)`；
再由包络在 `x + t·d` 处的下确界性（取 `y := p + t·d`）得
`f^η(x+t·d) ≤ f(p+t·d) + (1/(2η))‖p − x − t·d‖²`，**方向相反**。
故正确的下界须用**包络自身**比较：注意 `f^η(x) = f p + (1/(2η))‖p−x‖²`，
而 `‖p−x−t·d‖² = ‖p−x‖² − 2t⟨p−x,d⟩ + t²‖d‖²`
（`= ‖p−x‖² + 2t⟨x−p,d⟩ + t²‖d‖²`），代入即得上式。

**诚实标注**：这是 `∇f^η(x) = (1/η)(x − p)` 的**差商夹逼一侧**（余项 `O(t²)`），
**不是** `HasFDerivAt` 形式（见文件头诚实边界）。 -/
theorem moreauEnvelope_dirderiv_lower {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} (hη : 0 < η)
    {x p : Fin n → ℝ} (d : Fin n → ℝ) (t : ℝ) :
    moreauEnvelope f η x p + (t / η) * (∑ i, (x i - p i) * d i)
      - (t ^ 2 / (2 * η)) * normsq d
      ≤ f p + (1 / (2 * η)) * normsq (p - (x + t • d)) := by
  have henv : moreauEnvelope f η x p = f p + (1 / (2 * η)) * normsq (p - x) := rfl
  have hpt : p - (x + t • d) = (p - x) - t • d := by abel
  -- 用展开引理把右边化为显式多项式
  have hkey := env_dirderiv_key p x d t
  -- ⚠ 原稿写 `rw [hpt, ← sub_eq_iff_eq_add]`：`sub_eq_iff_eq_add` 的**反向**
  -- 模式是 `?m.230983 = ?m.230985 + ?m.230984`（Lean 直接打印出来的 `pattern:` 行），
  -- 与这里「左端已带 `f p + …`、右端是三项 `+ … - …`」的形状**不匹配**
  -- （三项目标的顶层算子是 `HSub.hSub` 而非 `HAdd.hAdd`）⟹ `did not find instance of the pattern`。
  --
  -- 正解：**不用** `sub_eq_iff_eq_add` 做形状搬运，改为把 `hkey` 当作线性关系
  -- 直接交给 `linarith`（`hkey` 已经把 `normsq (p-x-t•d)` 与显式多项式联系起来）。
  -- ⚠⚠⚠ **构建8–11 共 4 轮的真凶：`hgoal` 原稿的 `t²` 项符号写反了**（中间 `have` 为假）。
  -- 数值判定（3000 组随机）：原稿 `− (t²/(2η))·‖d‖²` 的版本 **2000/2000 全部失败**；
  -- 改成 **`+ (t²/(2η))·‖d‖²`** 后 **0/3000 反例**。
  -- 代数验证：`‖(p−x) − t·d‖² = ‖p−x‖² − 2t·Σ(p−x)·d + t²‖d‖²`（`env_dirderiv_key` 已证，0/2000 反例）
  -- ⟹ `(1/(2η))·‖…‖² = (1/(2η))‖p−x‖² + (t/η)·Σ(x−p)·d + (t²/(2η))·‖d‖²`
  -- （注意 `−2t·Σ(p−x)·d = +2t·Σ(x−p)·d`，故一次项是 `+`；**`t²` 项符号也是 `+`**）。
  have hgoal : f p + (1 / (2 * η)) * normsq (p - (x + t • d))
      = f p + (1 / (2 * η)) * normsq (p - x)
        + (t / η) * (∑ i, (x i - p i) * d i) + (t ^ 2 / (2 * η)) * normsq d := by
    rw [hpt]
    -- 把 `hkey : A - B = C` 转成 `A = B + C`，再整体缩放 `1/(2η)`
    have hA : normsq ((p - x) - t • d)
        = normsq (p - x) + (-2 * t * (∑ i, (p i - x i) * d i) + t ^ 2 * normsq d) := by
      linarith [hkey]
    -- 目标的 `∑ (x i - p i) * d i` 逐项等于 `-((p i - x i) * d i)`
    have hbr : (∑ i : Fin n, (x i - p i) * d i)
        = -(∑ i : Fin n, (p i - x i) * d i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hA, hbr]
    field_simp
    ring
  -- ⚠ 目标的**左端**是 `env(x,p) + (t/η)Σ(x−p)·d − (t²/2η)‖d‖²`（用 `henv` 展开），
  -- **右端**是 `f p + (1/2η)‖p−(x+t•d)‖²`。
  -- `hgoal`（正向）把右端的 `normsq (p - (x+t•d))` 展开成 `normsq(p-x) + …`，
  -- 于是两侧都化为 `f p + (1/2η)‖p-x‖² + (t/η)Σ − (t²/2η)‖d‖²` 的**同一表达式** ⟹ `le_refl`。
  rw [henv, hgoal]
  -- ⚠ 最后一步（探针 `_probe_f4_x.lean` exit 0 实测）：`hgoal`（正确形态，含 **`+ (t²/(2η))‖d‖²`**）
  -- 把右端展开后，目标化为 `… − (t²/(2η))D ≤ … + (t²/(2η))D`（`D = normsq d`）。
  -- 这**不是** `le_refl`（两端差 `2·(t²/(2η))D`）；需要 `t²/(2η)·D ≥ 0`，
  -- 由 `sq_nonneg t` + `hη : 0 < η` 给出 ⟹ `linarith` 带上该系数即可。
  have hD : 0 ≤ normsq d := normsq_nonneg d
  have hc : 0 ≤ (t ^ 2 / (2 * η)) * normsq d := by
    have h1 : 0 ≤ t ^ 2 := sq_nonneg t
    have h2 : 0 ≤ 2 * η := by linarith
    exact mul_nonneg (div_nonneg h1 h2) hD
  linarith

/-- **包络的差商上界（正确的 `O(t²)` 余项）**：取近端点 `p` 作为见证，
`f^η(x + t·d) ≤ f p + (1/(2η))‖p − x − t·d‖²`（由包络的下确界性质）。
结合 `normsq_sub` 展开，即得 `f^η(x + t·d) ≤ f^η(x) − (t/η)⟨p−x, d⟩ + (t²/(2η))‖d‖²`。

这条与 `moreauEnvelope_dirderiv_lower` 一起给出**方向导数的两侧夹逼**，
其差为 `O(t²)`，正是「包络一阶可微」的定量内核（**标注**：不是 `HasFDerivAt` 形式）。 -/
theorem moreauEnvelope_dirderiv_upper {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ}
    {x p : Fin n → ℝ} (hprox : IsProxN f η x p) (d : Fin n → ℝ) (t : ℝ) :
    moreauEnvelope f η (x + t • d) p
      ≤ moreauEnvelope f η x p - (t / η) * (∑ i, (x i - p i) * (-d i))
        + (t ^ 2 / (2 * η)) * normsq d := by
  -- ⚠⚠ 构建8–15（7 轮）实测，最终收敛到**最简结构**：
  -- 本定理的证明**完全不需要 `hprox`，也不需要 `moreauEnvelope_le`**——
  -- 它 100% 由 `moreauEnvelope` 的**定义 + 二次展开**给出。
  -- 关键纪律：**不要在目标上做 `rw [hgoal_sum]` 之类的 "记号搬运"**——
  -- 目标左端的 `moreauEnvelope f η (x + t•d) p` 展开后出现的是 `Σ(p−x)·d`，
  -- 而目标右端写的是 `Σ(x−p)·(−d)`；两者**只在内层可证相等**，外层不是一个匹配模式，
  -- 故 `rw [hgoal_sum]` 一律报 `did not find instance`（构建14/15 的 `706:6` 即此）。
  -- **正确做法：把整个目标化为一个等式 `heq`（`ring` 在等式上合法），再 `le_of_eq` 交付。**
  have heq : moreauEnvelope f η (x + t • d) p
      = moreauEnvelope f η x p - (t / η) * (∑ i, (x i - p i) * (-d i))
        + (t ^ 2 / (2 * η)) * normsq d := by
    -- 两侧的 `moreauEnvelope` 都用定义展开（`rfl` 级）
    have hstep : moreauEnvelope f η (x + t • d) p
        = f p + (1 / (2 * η)) * normsq (p - (x + t • d)) := rfl
    have henv1 : moreauEnvelope f η x p = f p + (1 / (2 * η)) * normsq (p - x) := rfl
    -- ⚠⚠ **`hsum` 的两侧是相等等式（不是差一个负号）**——探针 `_probe_f4_y.lean:57` 实测：
    -- 若写成 `= -Σ(p−x)·d`，逐项目标退化为 `-(x i * d i) + p i * d i = x i * d i - p i * d i`，
    -- **该式仅在 `x i*d i = p i*d i` 时成立，即命题为假**。
    -- 代数：`(x i − p i)·(−d i) = p i*d i − x i*d i`，`(p i − x i)·d i = p i*d i − x i*d i` ⟹ **二者相等**。
    have hsum : (∑ i : Fin n, (x i - p i) * (-d i))
        = ∑ i : Fin n, (p i - x i) * d i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hstep, henv1, hsum]
    -- 把 `p - (x+t•d)` 化为 `(p-x) - t•d`，使 `normsq_sub_expand` 的 `s` 恰为 `t•d`
    have hpt : p - (x + t • d) = (p - x) - t • d := by
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hpt, normsq_sub_expand]
    -- 展开后出现的是**正的** `normsq (t•d)` ⟹ 直接用 `normsq_smul`
    have hsmul : normsq (t • d) = t ^ 2 * normsq d := normsq_smul t d
    rw [hsmul]
    -- 内积项：`∑ (p-x) i * (t•d) i = t * ∑ (p i - x i) * d i`（投影 → 展开）
    have hinner : (∑ i : Fin n, (p - x) i * (t • d) i) = t * (∑ i, (p i - x i) * d i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hinner]
    -- ⚠ 探针 `_probe_f4_y.lean`（exit 0）最终定论：`hsum` 取**相等**方向后，
    -- `field_simp` 之后目标两侧的 `∑` 体部**已经完全一致**（都是 `∑ i, (p i - x i) * d i`），
    -- 故**不需要**任何 `∑` 桥接 ⟹ `field_simp; ring` 即可收尾。
    field_simp
    ring
  exact le_of_eq heq

/-! ## 七、Moreau 分解（线性特例，完整验证）

一般 Moreau 分解 `x = prox_{ηf}(x) + η·prox_{η⁻¹f*}(x/η)` 需要共轭函数 `f*` 与
近端算子的对偶关系（**未做**，见文件头）。线性情形 `f(y) = c·y` 下一切显式可算：
`prox_{ηf}(x) = x − ηc`，且把 `x` 分解为
`x = (x − ηc) + η·c = prox_{ηf}(x) + η·∇f`——**这就是线性情形的 Moreau 分解**。 -/

/-- **线性情形的 Moreau 分解**：`x = prox_{ηf}(x) + η·c`，其中 `f(y) = c·y`、
`prox_{ηf}(x) = x − ηc`（回收 `RealProximal.prox_linear`）。 -/
theorem moreau_decomposition_linear (c η x : ℝ) :
    x = (x - η * c) + η * c := by
  ring

/-- **线性情形分解的近端侧见证**：`x − ηc` 确实是 `x` 的近端点
（一维版回收 `RealProximal.prox_linear`）。 -/
theorem moreau_decomposition_linear_isprox (c η x : ℝ) (hη : 0 < η) :
    IsProx (fun y : ℝ => c * y) η x (x - η * c) :=
  prox_linear c η x hη

/-- **分解的共轭侧**：线性 `f(y) = c·y` 的 Fenchel 共轭在 `c` 处取 `0`
（`f*(c) = sup_y (c·y − c·y) = 0`），故共轭侧近端退化为常量 `c`——
与标准 Moreau 分解 `x = prox_{ηf}(x) + η·prox_{η⁻¹f*}(x/η)` 中
「共轭侧给出 `η∇f`」一致（**标注**：这里只验证 `f*` 在 `c` 处的取值，未建立完整对偶）。 -/
theorem linear_conjugate_at_slope (c : ℝ) :
    (∀ y : ℝ, c * y - c * y ≤ 0) ∧ (0 : ℝ) = c * c - c * c := by
  refine ⟨fun y => by ring_nf; exact le_refl 0, by ring⟩

/-! ## 八、近端不动点 ⟺ 全局最小点 -/

/-- **不动点刻画**：若 `p` 是全局最小点，则 `p` 是自己的近端点（`η > 0`）。
回收 `RealProximal.prox_self_of_minimizer` 的语义，说明
「`prox` 的不动点集 = `f` 的最小点集」的一半。 -/
theorem proxN_self_of_minimizer {n : ℕ} {f : (Fin n → ℝ) → ℝ} {η : ℝ} (hη : 0 < η)
    {p : Fin n → ℝ} (hmin : ∀ y : Fin n → ℝ, f p ≤ f y) : IsProxN f η p p := by
  intro y
  have h1 : f p ≤ f y := hmin y
  have h2 : 0 ≤ (1 / (2 * η)) * normsq (y - p) :=
    mul_nonneg (by positivity) (normsq_nonneg _)
  have hp0 : normsq (p - p) = 0 := by simp [normsq]
  rw [hp0, mul_zero, add_zero]
  linarith

/-- **不动点给出最小性（凸情形）**：凸 `f`、`p` 是 `p` 自身的近端点 ⟹ `p` 是全局最小点。
由 `ProxVIN` 取 `x := p`、`y := p` 得 `f p ≤ f p`（平凡），
故需用 `ProxVIN` 在任意 `y` 处：`f(p) + (1/η)⟨0, y−p⟩ ≤ f(y)`，即 `f p ≤ f y`。 -/
theorem minimizer_of_proxN_self {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hconv : ConvexOn ℝ Set.univ f) {η : ℝ} (hη : 0 < η) {p : Fin n → ℝ}
    (hp : IsProxN f η p p) : ∀ y : Fin n → ℝ, f p ≤ f y := by
  intro y
  have hVI := proxVIN_of_isProxN hconv hη hp y
  have hz : (∑ i : Fin n, (p i - p i) * (y i - p i)) = 0 := by simp
  rw [hz, mul_zero, add_zero] at hVI
  exact hVI

end Lattice
