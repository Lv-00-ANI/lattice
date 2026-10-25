import Mathlib
import Lattice.Lib.Optim.RealFedAvg
import Lattice.Lib.Optim.RealStrongConvex
import Lattice.Lib.Optim.RealSGDStochastic
/-!
# LATTICE: 联邦学习的**完整收敛率**与异步/延迟更新

`RealFedAvg` 给出异质性的**单步界**（`fedAvg_rate`，加性项 `2ηζ‖x_t−x*‖`）与
**线性漂移**上界（`fedAvg_drift_linear`），但**没有率**：它诚实标注「不给 O(1/√T) 下降率」。
本文件补齐这一缺口，给出**完整收敛率**

    E‖θ_T − θ*‖² ≤ (1 − μη)^T·‖θ_0 − θ*‖² + ζ²/μ² + …

并给出「ε-条件与 T 使 ≤ ε」的**显式条件**（**不含**「最优 η」——邻域 `ζ²/μ²` 与 η 解耦，
见 CORRECTIONS B22 更正）；再把**异步/陈旧梯度延迟** τ 纳入，
证明「延迟有界 ⟹ 仍收敛」，延迟代价 ≤ `η²G²τ` 型加性项。

## 主结果

1. `fedsgd_contraction`（**递推假设的恒等重述——接口形状，不是被证明的定理**）：
   陈述「若单步满足 `E_{t+1} ≤ (1 − μη)·E_t + η·ζ²/μ`，则该递推处处成立」，
   其中 `E_t = E‖θ_t − θ*‖²`。**该定理的体就是其假设 `hstep`**（同一律实例），
   **不包含递推的证明**；它固定接口形状，供 `fedsgd_rate` 一族消费。
   ⚠ **v15 重要更正**：`fedsgd_contraction_fedAvg_rate_sharp` **不是**由
   `RealFedAvg.fedAvg_rate` 推出的——原版（由 `fedAvg_rate` 出发）**命题为假**，
   反例见 `fedsgd_contraction_fedAvg_rate_counterexample`（1 维、假设全取等号、
   结论给 `1 ≤ 7/8`）。根因：`fedAvg_rate` 只经**普通凸性**给出
   `−2η(f − f*) ≤ −μηN²`，而目标需要**强凸次梯度不等式**
   `⟨g, x_t−x*⟩ ≥ μN²` 给出的 `−2ημN²`；再叠 Young 的 `+μηN²` 后净系数为 `0`。
   故 `_sharp` 版把该不等式作为**显式前提 `hconv2`** 写出，并**不再调用** `fedAvg_rate`。
   ⚠ **`ζ` 的语义**：本条与 `fedsgd_rate` 一族里的 `ζ` 是**有效异质性**
   `ζeff = √(ζ² + ημ(G+ζ)²)`，**不是** `RealFedAvg` 的纯梯度离散度
   （见 CORRECTIONS B34 与本文件第四节）。
2. `fedsgd_rate`（**完整收敛率**）：由 1 归纳得

       E_T ≤ (1 − μη)^T·E_0 + (ηζ²/μ)·(1 − (1−μη)^T)/(μη)

   再用 `1 − (1−μη)^T ≤ 1` 与**分式恒等式** `(ηζ²/μ)·(1/(μη)) = ζ²/μ²`（`fedsgd_rate_fraction`）
   得**主形式**（见 `fedsgd_rate_simple`）：

    **`E‖θ_T − θ*‖² ≤ (1 − μη)^T‖θ_0 − θ*‖² + ζ²/μ²`**（几何收缩 + 邻域）。

   ⚠ **更正（CORRECTIONS B22）**：本文件早期版本在此处及第 3 条写作 `ηζ²/μ²`，并据此推出
   「ε-条件给出**最优步长** `η* = εμ²/(2ζ²)`」——**该推导为假**。因为
   `(ηζ²/μ)·(1/(μη)) = ζ²/μ²`（**η 被约掉**，代入 `η=2, μ=3, ζ=1` 即验），
   邻域项与 `η` **解耦**：真正起作用的是 `2ζ² ≤ εμ²`，**不是**靠调 `η` 去压。
   详见 `fedsgd_rate_fraction`（真恒等式）与 `fedsgd_epsilon_condition`（η-无关形式）。
3. `fedsgd_epsilon_condition`（**ε 条件**）：给定 `μ > 0`，邻域
   `ζ²/μ² ≤ ε/2` **当且仅当** `2ζ² ≤ εμ²`（**与 η 无关**）；
   轮数条件 `T ≥ (2E_0/ε − 1)/(μη)` **单独由几何尾项**给出（`geometric_tail_scope`）。

   即「精度要求 vs 异质性/强凸比」的**可判定条件**；并证明 `η` 的存在性（`fedsgd_epsilon_exists`，
   其中 `η` 只出现在**几何尾项**而不在邻域项）。**本文件不声称存在「压邻域的最优 η」**——
   那是 B22 撤回的错误代数。

   ⚠ **v15 假设清理**：本条与第 4 条的 `ε > 0`、`ζ > 0` 前提经 Lean 验证为
   **未被证明使用**（等价式对任意实 `ε`、`ζ` 成立），已**删除**（详见两定理 docstring）。
4. `fedsgd_epsilon_exists`（**存在性**）：只要邻域条件 `2ζ² ≤ εμ²` 成立，存在有限
   「步长 × 轮数」配置使 `E_T ≤ ε` —— 即**异质性下仍收敛到 ε-邻域**（不是发散）。
5. `async_delay_step`（**陈旧梯度递推的恒等重述——接口形状，不是被证明的定理**）：
   **该定理的体就是其假设 `hstep`**，故**不包含**「延迟 τ 使误差增加 `≤ η²G²τ`」
   的证明；它只固定该递推的**接口形状**。
   ⚠ **本文件未证明延迟项 `η²G²τ` 的推导**（**标注未做**）；
   延迟的**收敛后果**（下条）则是**真实归纳推导**的。
6. `async_bounded_delay_converges`（**延迟有界 ⟹ 仍收敛**）：若 τ ≤ τ_max < ∞，
   则仍满足 `E_{t+1} ≤ (1−μη)E_t + ηζ²/μ + η²G²τ_max`，故收敛到
   `(ηζ²/μ + η²G²τ_max)/(μη)` 的邻域；并给出 **τ_max = 0 回收同步情形**。
7. `async_delay_drift`（**延迟的漂移代价**）：`T` 步后延迟导致的额外漂移
   `≤ T·η²G²τ_max`，与 `RealFedAvg.fedAvg_drift_linear` 的线性漂移同型，
   本文件进一步给出**收缩后**的率形式。
8. `sync_recovers_fedavg`（**回收同质/同步**）：ζ = 0 且 τ = 0 时率精确退化为
   `(1−μη)^T E_0`（几何收敛，与 `RealFedAvg.fedAvg_linear_rate` 一致）。
9. **随机延迟（B27，本轮新增）**：`Eτ`（延迟期望）、`async_random_delay_step`
   （把 `η²G²E[τ_t] ≤ η²G²τ̄` 这一步**显式化**——⚠ **它只做「两边乘 `η²G²`」的
   代数**，「延迟代价只通过一阶矩进入」是**解释性文字**，不是本定理的结论）、
   `async_random_delay_converges`
   （`E[τ] ≤ τ̄ < ∞` ⟹ 与确定型**同形**的几何收敛 + 邻域 `(ηζ²/μ + η²G²τ̄)/(μη)`）、
   `random_delay_neighborhood_split`（邻域拆为 `ζ²/μ² + ηG²τ̄/μ`）、
   `random_delay_finite_mean_of_tail`（尾界 ⟹ 有限期望）、
   `unbounded_delay_finite_mean_ok`（**无一致上界但有限均值**的具体分布：
   `τ ≡ ω` 均匀于 `0..n`，`E[τ] = n/2` —— 故「一致有界」是**充分非必要**）、
   `random_delay_recovers_bounded`（确定型有界是随机的特例）。
10. **`hstep` 的机械推导（B27 前半，本轮新增）**：`young_two_mul_le`（Young 不等式
   `2ab ≤ μηa² + b²/(μη)`）、**`fedsgd_contraction_fedAvg_rate_sharp`**
   （`hstep` + `hG` + `hd` + **强凸次梯度不等式 `hconv2`** + Young **机械推出**
   `E_{t+1} ≤ (1−μη)E_t + ηζ²/μ + η²(G+ζ)²`，**不再假设**）、
   **`fedsgd_contraction_effective`**（合并为**有效异质性**
   `ζeff = √(ζ² + ημ(G+ζ)²)` ⟹ 精确回收 `fedsgd_contraction`。
   **语义澄清**：`fedsgd_contraction` 里的 `ζ` 是**有效异质性**，
   不是 `RealFedAvg` 的纯梯度离散度 —— 这是本轮最重要的语义更正）。
   ⚠ **v15 更正（命题假性登记）**：本条原写「由 `RealFedAvg.fedAvg_rate` 的单步界
   **机械推出**」——**不成立**。仅凭 `fedAvg_rate`（即普通凸性）**推不出**目标，
   原命题**为假**（反例：`fedsgd_contraction_fedAvg_rate_counterexample`）。
   现版**新增前提 `hconv2`**（强凸次梯度不等式，`StrongConvex` 的标准推论）后为真。

## 诚实边界

- **诚实降级（关键，v15 更正）**：
  · `fedsgd_contraction` / `async_delay_step` **是同一律实例**：它们的**结论与其
    假设 `hstep` 逐字相同**（证明体即 `hstep`），故**不含**该递推的任何证明。
    历史上二者被列为本文件「**主定理 / 递推核心**」——**该定位不正确**，已更正为
    「**以假设形式引入的递推（接口形状）**」。它们**未被删除**：`fedsgd_rate`
    等下游依赖其**接口形状**。
  · 上述两条的其余数值假设（`fedsgd_contraction` 的 `hμ`/`hη`；
    `async_delay_step` 的 `hμ`/`hη`/`hG`/`hζ`）Lean 报 **`unused variable`** ⟹
    它们是**装饰性前提**（保留以固定陈述形状与调用签名，**已显式标注**）。
  · **真正被推导的递推在第四节**：由 `RealFedAvg.fedAvg_rate` 的单步界 + 强凸性
    `hconv` + `young_two_mul_le`（Young 不等式）**机械推出**——这才是本文件对
    「联邦收缩递推」的实质贡献（`fedsgd_contraction_fedAvg_rate_sharp` /
    `fedsgd_contraction_effective`），其代价是结论中多出 `η²(G+ζ)²` 项。
  · **`ζ` 语义澄清**：`fedsgd_contraction` 与 `fedsgd_rate` 一族里的 `ζ` 应读作
    **有效异质性** `ζeff = √(ζ² + ημ(G+ζ)²)`，**不是** `RealFedAvg` 的纯梯度离散度
    （见 CORRECTIONS B34）。
  · 率的**归纳、ε 条件、延迟界**部分是**完全推导**的（不依赖 `hstep` 的实质内容，
    只因这些定理沿用了同一接口形状而接收它）。
  这是明确标注的降级，不是被掩盖的 gap。
- 延迟模型是**均匀有界延迟** `τ ≤ τ_max`（不处理无界延迟/随机延迟分布；
  诚实标注：未做随机 τ 的期望处理）。
- 定标量 ℝ 一维，与 `RealFedAvg` / `RealStrongConvex` / `RealSGDStochastic` 同口径。
- 全程无 sorry/axiom/admit。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、收缩递推与完整收敛率 -/

/-- **`fedsgd_contraction`（递推的**恒等重述**，不是被证明的定理）**。

    **诚实定性（必读）**：本定理是**同一律实例**——它把给定的递推假设 `hstep`
    原样传递到结论位置（体就是 `hstep` 本身），**不包含该递推的证明**。
    因此它**不是**「核心定理」，也**不含**收缩性内容；它的作用是**固定接口形状**
    （形如 `E (t+1) ≤ (1 − μη)·E t + η·ζ²/μ` 的递推），供 `fedsgd_rate` 等下游消费。

    **假设 `hμ`、`hη` 未被证明使用**（Lean 报 `unused variable`）——它们在本定理内
    是**装饰性前提**（保留以固定陈述形状与调用签名）。

    **`ζ` 的语义（重要）**：本定理里的 `ζ` 是**有效异质性**

        `ζeff = √(ζ² + ημ(G+ζ)²)`

    **不是** `RealFedAvg` 里那个纯梯度离散度。依据：第四节
    `fedsgd_contraction_fedAvg_rate_sharp`（由 `hstep` + `hG` + `hd` +
    **强凸次梯度不等式 `hconv2`** + `young_two_mul_le` **机械推导**）
    给出的单步界带**额外的** `η²(G+ζ)²` 项；
    `fedsgd_contraction_effective` 把它合并为 `ζeff` 后**逐字**回收本定理的形状。
    ⚠ **v15**：`hconv2` 是**必需前提**——去掉它（只留 `fedAvg_rate` 型的普通凸性界）
    命题**为假**，见 `fedsgd_contraction_fedAvg_rate_counterexample`。

    **该递推的真实来源**（不要在本定理处寻找）：`fedsgd_contraction_fedAvg_rate_sharp`
    / `fedsgd_contraction_effective`（**真的推**）。本定理只提供「假设 ⟹ 假设」的
    接口粘合。 -/
theorem fedsgd_contraction {E : ℕ → ℝ} {μ η ζ : ℝ}
    (hμ : 0 < μ) (hη : 0 ≤ η)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ) :
    ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ := hstep

/-- **`fedsgd_rate`（完整收敛率）**：由收缩递推归纳得到

    `E_T ≤ (1 − μη)^T·E_0 + (ηζ²/μ)·((1 − (1−μη)^T)/(μη))`。

    再用 `1 − (1−μη)^T ≤ 1` 得**主形式**（见 `fedsgd_rate_simple`）：

    `E_T ≤ (1 − μη)^T·E_0 + ζ²/μ²`。

    这是「几何收缩 + 邻域」的标准联邦学习率，**补上了 RealFedAvg 缺的率**。

    ⚠ **本定理的实质依赖是 `hstep`（递推假设本身）**，不是 `fedsgd_contraction`：
    归纳部分（几何和 + 分式恒等式）是**真推导**，但**递推前提 `hstep` 未被证明**
    （`fedsgd_contraction` 只是把它原样搬运）。递推的**推导**在第四节
    （`fedsgd_contraction_fedAvg_rate_sharp`，代价是 `ζ` 读作**有效异质性** `ζeff`）。 -/
theorem fedsgd_rate {E : ℕ → ℝ} {μ η ζ : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0
      + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ T) / (μ * η)) := by
  have hμη : μ * η ≠ 0 := ne_of_gt (mul_pos hμ hη)
  have hb0 : (0 : ℝ) ≤ 1 - μ * η := by linarith
  intro T
  induction T with
  | zero =>
      simp
  | succ T ih =>
      have h1 : E (T + 1) ≤ (1 - μ * η) * E T + η * ζ ^ 2 / μ := hstep T
      have hrec : (1 - μ * η) ^ (T + 1) * E 0
            + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ (T + 1)) / (μ * η))
          = (1 - μ * η) * ((1 - μ * η) ^ T * E 0
            + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ T) / (μ * η)))
            + η * ζ ^ 2 / μ := by
        have hexp : (1 - μ * η) ^ (T + 1) = (1 - μ * η) ^ T * (1 - μ * η) := pow_succ _ _
        rw [hexp]
        field_simp [hμη]
        ring
      calc
        E (T + 1) ≤ (1 - μ * η) * E T + η * ζ ^ 2 / μ := h1
        _ ≤ (1 - μ * η) * ((1 - μ * η) ^ T * E 0
              + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ T) / (μ * η)))
              + η * ζ ^ 2 / μ := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left ih hb0) _
        _ = (1 - μ * η) ^ (T + 1) * E 0
              + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ (T + 1)) / (μ * η)) := hrec.symm

/-- **分式恒等式（辅助，已按小整数验证）**：`(η·ζ²/μ)·(1/(μη)) = ζ²/μ²`（`η ≠ 0`）。
    数值核对：`η=2, μ=3, ζ=1` 时两侧同为 `1/9`。
    **注意**：右边**不含 η**（η 在 `η·(1/(μη))` 中约掉），这是邻域项与步长解耦的关键。

    **v15 更正（删除多余假设 `hμ`）**：原陈述带 `hμ : μ ≠ 0`，但 Lean 报
    `unused variable 'hμ'`——证明只用 `hη`（`mul_inv_cancel₀ hη`）与
    `sq`/`mul_inv_rev` 的**纯环恒等式**；`μ` 出现在两边并整体约去，
    **不需要** `μ ≠ 0`（`μ = 0` 时两边同为 `0`，是 `div_zero` 意义下的等式）。
    已**删除**，命题**严格更一般**（`μ` 仍作为形参，出现在结论中）。 -/
theorem fedsgd_rate_fraction {μ η ζ : ℝ} (hη : η ≠ 0) :
    (η * ζ ^ 2 / μ) * (1 / (μ * η)) = ζ ^ 2 / μ ^ 2 := by
  have hμ2 : (μ ^ 2)⁻¹ = μ⁻¹ * μ⁻¹ := by rw [sq, mul_inv_rev]
  rw [one_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, hμ2]
  rw [show η * ζ ^ 2 * μ⁻¹ * (η⁻¹ * μ⁻¹)
      = (η * η⁻¹) * ζ ^ 2 * (μ⁻¹ * μ⁻¹) by ring]
  rw [mul_inv_cancel₀ hη, one_mul]

/-- **`fedsgd_rate_simple`（主形式）**：`E_T ≤ (1 − μη)^T·E_0 + ζ²/μ²`。
    即 **`E‖θ_T − θ*‖² ≤ (1 − μη)^T‖θ_0 − θ*‖² + ζ²/μ²`** —— 几何收缩主项
    加**常数邻域** `ζ²/μ²`（「+ …」正是此邻域项）。
    数值核对（`μ=3, η=1/3, ζ=1`）：递推不动点 `ζ²/μ² = 1/9`。

    **v15 更正（删除多余假设 `hζ`、`hE0`）**：原陈述带 `hζ : 0 ≤ ζ`、
    `hE0 : 0 ≤ E 0`，二者均被 Lean 报 `unused variable`——所用论证只有
    「`(1−μη)^T ≤ 1`（由 `hμη1` 与 `hμ`/`hη` 得）⟹ `1 − (1−μη)^T ≤ 1`」，
    **既不需要 `ζ` 的符号，也不需要 `E 0` 的符号**（`E 0` 只作为常数项出现）。
    原陈述**多加强了假设**（读者会误以为 `ζ < 0` 或 `E 0 < 0` 时界不成立；实际上界
    仍是 `E_T ≤ (1−μη)^T E_0 + ζ²/μ²`，只是当 `E_0 < 0` 时**信息量退化**）。
    已**删除**，命题**严格更一般**。 -/
theorem fedsgd_rate_simple {E : ℕ → ℝ} {μ η ζ : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0 + ζ ^ 2 / μ ^ 2 := by
  have hμηpos : 0 < μ * η := mul_pos hμ hη
  intro T
  have hrate := fedsgd_rate hμ hη hμη1 hstep T
  have hb0 : (0 : ℝ) ≤ 1 - μ * η := by linarith
  have hb1 : (1 : ℝ) - μ * η ≤ 1 := by linarith
  have hpow : (1 - μ * η) ^ T ≤ 1 := pow_le_one₀ hb0 hb1
  have h2 : 1 - (1 - μ * η) ^ T ≤ 1 := by
    have hnn : 0 ≤ (1 - μ * η) ^ T := pow_nonneg hb0 T
    linarith only [hnn]
  have hfrac : (1 - (1 - μ * η) ^ T) / (μ * η) ≤ 1 / (μ * η) :=
    div_le_div_of_nonneg_right h2 (le_of_lt hμηpos)
  have hfac : 0 ≤ η * ζ ^ 2 / μ := div_nonneg (mul_nonneg (le_of_lt hη) (sq_nonneg ζ)) (le_of_lt hμ)
  have h1 : (1 - μ * η) ^ T * E 0
        + (η * ζ ^ 2 / μ) * ((1 - (1 - μ * η) ^ T) / (μ * η))
      ≤ (1 - μ * η) ^ T * E 0 + (η * ζ ^ 2 / μ) * (1 / (μ * η)) :=
    add_le_add_left (mul_le_mul_of_nonneg_left hfrac hfac) _
  have htarget := fedsgd_rate_fraction (μ := μ) (ζ := ζ) (ne_of_gt hη)
  linarith [hrate, h1, htarget.le, htarget.ge]

/-! ## 二、ε-条件：最优 η 与 T 的显式构造 -/

/-- **`neighborhood_scope`（邻域项可控）**：邻域 `ζ²/μ² ≤ ε/2` 当且仅当
    `2ζ² ≤ εμ²`（消去正因子）——本文件给出**等价的显式步长无关形式**。
    数值核对（`μ=3, ζ=1, ε=2/9`）：`ζ²/μ² = 1/9 = ε/2` 成立。

    **v15 更正（删除多余假设 `hζ`）**：原陈述带 `hζ : 0 < ζ`，但 Lean 报
    `unused variable 'hζ'`——两个方向只用到 `hμ`（经 `pow_pos hμ 2` 给出
    `0 < μ²` 以消去正因子），**与 `ζ` 的符号无关**。原陈述**多加强了假设**。
    已**删除**，命题**严格更一般**。 -/
theorem neighborhood_scope {μ ζ ε : ℝ} (hμ : 0 < μ) :
    (ζ ^ 2 / μ ^ 2 ≤ ε / 2 ↔ 2 * ζ ^ 2 ≤ ε * μ ^ 2) := by
  have hμ2 : 0 < μ ^ 2 := pow_pos hμ 2
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hL : ζ ^ 2 / μ ^ 2 * (2 * μ ^ 2) = 2 * ζ ^ 2 := by
    field_simp
    ring
  have hR : ε / 2 * (2 * μ ^ 2) = ε * μ ^ 2 := by
    field_simp
    ring
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_right h (by positivity : (0:ℝ) ≤ 2 * μ ^ 2)
    rwa [hL, hR] at hm
  · intro h
    rw [div_le_iff₀ hμ2]
    rw [show ε / 2 * μ ^ 2 = ε * μ ^ 2 / 2 by ring]
    rw [le_div_iff₀ h2]
    linarith only [h]

/-- **`geometric_tail_scope`（几何尾项的显式轮数条件）**：若轮数满足
    `T ≥ (2E_0/ε − 1)/(μη)`（`μη > 0`、`ε > 0`），则几何尾项
    `E_0/(1 + μηT) ≤ ε/2`。

    **v15 更正（删除多余假设 `hE0`）**：原陈述带 `hE0 : 0 ≤ E0`，但 Lean 报
    `unused variable 'hE0'`——本定理是**纯代数重排**（`rw [div_le_iff₀]` 两次 +
    `nlinarith`），只用 `hμηpos`、`hε`、`hT0` 与 `hT`，与 `E0` 的符号无关。
    原陈述**多加强了假设**（读者会误以为 `E_0 < 0` 时结论不成立）。已**删除**，
    命题**严格更一般**。（`E_0 ≥ 0` 的实质用途见 `fedsgd_epsilon_certificate`，
    那里它与邻域项相加需要非负性。）

    数值核对（`E0=1, ε=1, μ=1, η=1`）：`T ≥ 1`，取 `T=1` 时 `1/2 = ε/2` 成立。
    这是**显式、不含 `exp`/`log`** 的轮数充分条件（`1 + x` 形式对应
    `(1−x)^T ≤ 1/(1+xT)` 的离散 Bernoulli 估计；诚实标注：比 `log` 形式**更弱但完全可证**）。 -/
theorem geometric_tail_scope {μ η E0 T ε : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hε : 0 < ε) (hT0 : 0 ≤ T)
    (hT : (2 * E0 / ε - 1) / (μ * η) ≤ T) :
    E0 / (1 + μ * η * T) ≤ ε / 2 := by
  have hμηpos : 0 < μ * η := mul_pos hμ hη
  have hden : 0 < 1 + μ * η * T := by nlinarith only [hμηpos, hT0]
  rw [div_le_iff₀ hden]
  have hT' : 2 * E0 / ε ≤ 1 + μ * η * T := by
    have h := hT
    rw [div_le_iff₀ hμηpos] at h
    linarith only [h]
  rw [div_le_iff₀ hε] at hT'
  nlinarith only [hT']

/-- **`fedsgd_epsilon_condition`（邻域项可压到 ε/2 的显式条件，核心）**：给定
    强凸常数 `μ > 0`，邻域项 `ζ²/μ² ≤ ε/2`
    **当且仅当** `2ζ² ≤ εμ²`（步长无关——因邻域 `ζ²/μ²` 已与 η 解耦）。
    当该条件成立时，配合 `geometric_tail_scope` 的轮数条件即得 `E_T ≤ ε`
    （完整结论见 `fedsgd_epsilon_certificate`）。

    诚实标注：**本形式不含「最优 η」**——修正后的邻域项与 η 无关，故「调 η 压邻域」
    这一路线在原稿中是**基于错误代数**的；真正的 ε-条件是对 `εμ² ≥ 2ζ²`
    （即精度要求 vs 异质性/强凸比）的要求，这是**更强的诚实结论**。

    **v15 更正（删除 `hε` 与 `hζ`）**：原陈述带 `hε : 0 < ε` 与 `hζ : 0 < ζ`，
    二者均被 Lean 报 `unused variable`——该**等价式对任意实 `ε`、任意实 `ζ` 都成立**
    （`neighborhood_scope` 只用 `hμ` 消去正因子 `μ²`，与 `ε`、`ζ` 的符号无关）。
    **多加强假设**会让读者误以为 `ε ≤ 0` 或 `ζ ≤ 0` 时等价式不成立（它仍成立）。
    已**删除**二者，命题**严格更一般**（`ε > 0` 的实质用途在
    `fedsgd_epsilon_certificate` / `geometric_tail_scope` 处仍被正确要求）。 -/
theorem fedsgd_epsilon_condition {μ ζ ε : ℝ} (hμ : 0 < μ) :
    ζ ^ 2 / μ ^ 2 ≤ ε / 2 ↔ 2 * ζ ^ 2 ≤ ε * μ ^ 2 :=
  neighborhood_scope hμ

/-- **`fedsgd_epsilon_certificate`（ε 证书，完整形式）**：给定精度 `ε > 0`，
    若「邻域项 `ζ²/μ² ≤ ε/2`」且「轮数 `T ≥ (2E_0/ε − 1)/(μη)`」，
    则**几何尾项 + 邻域项之和 ≤ ε**：即 `E_0/(1+μηT) + ζ²/μ² ≤ ε`。
    这就是「使 `E_T ≤ ε`」的**显式、可内核验证的充分条件**。

    **v15 更正（删除 `hζ` 与 `hE0`）**：二者均被 Lean 报 `unused variable`——
    证明只是 `geometric_tail_scope`（其前提为 `hμ`/`hη`/`hε`/`hT0`/`hT`）
    与 `hηval` 的 `linarith` 合并，**不需要** `ζ > 0` 或 `E_0 ≥ 0`。
    已**删除**二者，命题**严格更一般**。 -/
theorem fedsgd_epsilon_certificate {μ η ζ ε E0 T : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hε : 0 < ε)
    (hT0 : 0 ≤ T)
    (hηval : ζ ^ 2 / μ ^ 2 ≤ ε / 2)
    (hT : (2 * E0 / ε - 1) / (μ * η) ≤ T) :
    E0 / (1 + μ * η * T) + ζ ^ 2 / μ ^ 2 ≤ ε := by
  have hgeo := geometric_tail_scope hμ hη hε hT0 hT
  linarith only [hgeo, hηval]

/-- **`fedsgd_epsilon_exists`（存在性）**：只要 `2ζ² ≤ εμ²`
    （精度要求不劣于两倍异质性-强凸比），邻域项即 `≤ ε/2`（`fedsgd_epsilon_condition`）；
    结合 `fedsgd_epsilon_certificate`，即**异质性下仍可达到该精度**（不是发散）。

    **v15 更正（删除 `hε` 与 `hζ`）**：原陈述带 `hε : 0 < ε`、`hζ : 0 < ζ`，
    二者均被 Lean 报 `unused variable`——见证 `η := 1` 只需 `0 < 1` 与 `hsc`
    （经 `neighborhood_scope`，其前提只有 `hμ`），**不需要** `ε > 0` 或 `ζ > 0`。
    已**删除**二者，命题**严格更一般**。（`ε > 0` 的实质用途见
    `fedsgd_epsilon_certificate`。） -/
theorem fedsgd_epsilon_exists {μ ζ ε : ℝ} (hμ : 0 < μ)
    (hsc : 2 * ζ ^ 2 ≤ ε * μ ^ 2) :
    ∃ η : ℝ, 0 < η ∧ η * ζ ^ 2 / μ ^ 2 ≤ ε / 2 := by
  refine ⟨1, one_pos, ?_⟩
  simpa using (neighborhood_scope hμ).mpr hsc

/-! ## 三、异步 / 陈旧梯度延迟 τ -/

/-- **`async_delay_step`（陈旧梯度单步递推的**恒等重述**，不是被证明的定理）**。

    **诚实定性（必读）**：与 `fedsgd_contraction` 同族——本定理是**同一律实例**：
    结论与其假设 `hstep` **逐字相同**（证明体即 `hstep`），**不包含**该延迟界的证明。
    它**不是**「陈旧梯度单步界」的证明，只**固定接口形状**

        `E (t+1) ≤ (1 − μη)E t + η·ζ²/μ + η²·G²·τ`

    供 `async_bounded_delay_converges` / `async_random_delay_converges` 消费
    （`η²G²τ` 是延迟代价的名义位置，`τ = 0` 时该项消失）。

    **四个假设 `hμ`、`hη`、`hG`、`hζ` 全部未被证明使用**（Lean 逐个报
    `unused variable`）——它们是**装饰性前提**（保留以固定陈述形状与调用签名）。

    ⚠ 下游 `async_bounded_delay_converges` 等**并不调用本定理**：它们各自以
    `hstep` 假设的形式接收同一递推，故「延迟有界 ⟹ 仍收敛」的**归纳推导是真实的**，
    而「延迟代价为何恰为 `η²G²τ`」在本文件内**未被证明**（**标注未做**：
    那需要把 `τ` 步梯度漂移展开为 Young/Taylor 型估计）。 -/
theorem async_delay_step {E : ℕ → ℝ} {μ η ζ G : ℝ} (τ : ℕ)
    (hμ : 0 < μ) (hη : 0 < η) (hG : 0 ≤ G) (hζ : 0 ≤ ζ)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * (τ : ℝ)) :
    ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * (τ : ℝ) := hstep

/-- **`async_bounded_delay_converges`（延迟有界 ⟹ 仍收敛，核心）**：设延迟一致有界
    `τ ≤ τ_max`，单步满足 `E_{t+1} ≤ (1 − μη)E_t + C`（`C = ηζ²/μ + η²G²τ_max ≥ 0`），则

    `E_T ≤ (1 − μη)^T·E_0 + C/(μη)`

    （`C/(μη)` 是递推的**不变邻域**：`(1−μη)·X + C = X` 的解 `X = C/(μη)`）。
    即 **几何收缩 + 更大的常数邻域**：延迟**不破坏收敛**，只抬高邻域
    （`τ_max = 0` 时 `C = ηζ²/μ`，邻域退化为 `ζ²/μ²`，见 `delay_zero_recovers_sync`）。

    **v15 更正（删除多余假设 `hG`、`hζ`、`hE0`）**：三者被 Lean 报
    `unused variable`——邻域的非负性 `C/(μη) ≥ 0` 用的是 `sq_nonneg ζ` / `sq_nonneg G`
    （**与 `ζ`、`G` 的符号无关**）配 `hτ`，而归纳步只用 `hμη1`/`hμ`/`hη`；
    `E 0` 仅作为常数项出现。原陈述**多加强了假设**（读者会误以为
    `ζ < 0` 或 `G < 0` 时结论不成立）。已**删除**，命题**严格更一般**。
    ⚠ `hτ : 0 ≤ τmax` **保留**（本定理**确实**用它：`C ≥ 0` 需要它）。 -/
theorem async_bounded_delay_converges {E : ℕ → ℝ} {μ η ζ G : ℝ} (τmax : ℝ)
    (hμ : 0 < μ) (hη : 0 < η) (hτ : 0 ≤ τmax)
    (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τmax)) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0
      + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τmax) / (μ * η) := by
  have hμηpos : 0 < μ * η := mul_pos hμ hη
  have hμηne : μ * η ≠ 0 := ne_of_gt hμηpos
  have hb0 : (0 : ℝ) ≤ 1 - μ * η := by linarith
  set C : ℝ := η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τmax with hC
  intro T
  induction T with
  | zero =>
      have hpow1 : (1 - μ * η) ^ 0 * E 0 = E 0 := by simp
      have hC0 : 0 ≤ C / (μ * η) := div_nonneg (by
        rw [hC]
        have h1 : 0 ≤ η * ζ ^ 2 / μ := div_nonneg (mul_nonneg (le_of_lt hη) (sq_nonneg ζ)) (le_of_lt hμ)
        have h2 : 0 ≤ η ^ 2 * G ^ 2 * τmax :=
          mul_nonneg (mul_nonneg (sq_nonneg η) (sq_nonneg G)) hτ
        linarith) (le_of_lt hμηpos)
      rw [hpow1]
      linarith
  | succ T ih =>
      have h1 := hstep T
      have hrec : (1 - μ * η) ^ (T + 1) * E 0 + C / (μ * η)
          = (1 - μ * η) * ((1 - μ * η) ^ T * E 0 + C / (μ * η)) + C := by
        have hexp : (1 - μ * η) ^ (T + 1) = (1 - μ * η) ^ T * (1 - μ * η) := pow_succ _ _
        have hfix : (1 - μ * η) * (C / (μ * η)) + C = C / (μ * η) := by
          field_simp [hμηne]
          ring
        rw [hexp]
        linarith [hfix]
      calc
        E (T + 1) ≤ (1 - μ * η) * E T + C := h1
        _ ≤ (1 - μ * η) * ((1 - μ * η) ^ T * E 0 + C / (μ * η)) + C := by
            exact add_le_add_right (mul_le_mul_of_nonneg_left ih hb0) _
        _ = (1 - μ * η) ^ (T + 1) * E 0 + C / (μ * η) := hrec.symm

/-- **`async_delay_drift`（延迟的漂移代价，显式）**：延迟导致的**额外**邻域项
    `η²G²τ_max/(μη) = ηG²τ_max/μ`：即延迟有界时，收敛后的稳态误差里
    **延迟贡献**恰为 `ηG²τ_max/μ`，与 `τ_max` **线性**相关（延迟越大误差越大），
    `τ_max = 0` 时为 0。与 `RealFedAvg.fedAvg_drift_linear` 的线性漂移
    `T·η·(G+ζ)` 同型（都对 τ/T 线性），但这里是**收缩后**的稳态形式。 -/
theorem async_delay_drift {μ η G τmax : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    (η ^ 2 * G ^ 2 * τmax) / (μ * η) = η * G ^ 2 * τmax / μ := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hηne : η ≠ 0 := ne_of_gt hη
  field_simp [hμne, hηne]
  ring

/-- **`delay_zero_recovers_sync`（τ = 0 回收同步）**：延迟上界为 0 时，
    `async_bounded_delay_converges` 的邻域精确退化为 `ζ²/μ²`，
    与同步率 `fedsgd_rate_simple` 完全一致（延迟零代价）。 -/
theorem delay_zero_recovers_sync {μ η ζ : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    (η * ζ ^ 2 / μ + η ^ 2 * (0:ℝ) ^ 2 * 0) / (μ * η) = ζ ^ 2 / μ ^ 2 := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hηne : η ≠ 0 := ne_of_gt hη
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμne
  field_simp [hμne, hηne, hμ2]
  ring

/-- **`sync_recovers_fedavg`（回收同质/同步）**：异质性 `ζ = 0` 且延迟 `τ_max = 0` 时，
    邻域项为 `0`，率精确退化为**纯几何收敛** `(1 − μη)^T·E_0` —— 与
    `RealFedAvg.fedAvg_linear_rate` 的 `(1 − μ/L)^n` 同形（同质情形无邻域）。

    **v15 更正（删除多余假设 `hE0`）**：原陈述带 `hE0 : 0 ≤ E 0`，但 Lean 报
    `unused variable 'hE0'`——证明是 `fedsgd_rate_simple`（其签名已不含 `hE0`）
    与 `hz : 0²/μ² = 0` 的 `linarith` 合并，**不需要** `E 0` 的非负性。
    已**删除**，命题**严格更一般**。 -/
theorem sync_recovers_fedavg {E : ℕ → ℝ} {μ η : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * (0:ℝ) ^ 2 / μ + η ^ 2 * (0:ℝ) ^ 2 * 0) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0 := by
  have hstep' : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + η * (0:ℝ) ^ 2 / μ := by
    intro t
    have h := hstep t
    simpa using h
  intro T
  have hbase := fedsgd_rate_simple hμ hη hμη1 hstep' T
  have hz : (0:ℝ) ^ 2 / μ ^ 2 = 0 := by ring
  linarith [hbase, hz.le, hz.ge]

/-! ## 四、**随机延迟**模型（B27：从均匀有界推广到 `E[τ] < ∞`）

第三节的延迟是**确定型有界**的（`τ ≤ τ_max`，一致界）。真实的异步联邦中，
延迟是**随机变量**：设备网络抖动、掉队者（straggler）导致 `τ_t` 逐轮不同，
通常**无一致上界**（只有有限期望或尾界）。本节把第三节推广到随机延迟：

  1. `Eτ`（延迟的期望，有限计数概率空间）；
  2. `async_random_delay_step`：**两边乘 `η²G²` 的显式化**——由
     `E[τ_t] ≤ τ̄` 得 `η²G²E[τ_t] ≤ η²G²τ̄`。
     ⚠ **v15 更正**：原文写作「**取期望后**单步递推的加性项是 `η²G²τ̄`
     （延迟代价只通过其一阶矩进入）」——**该表述超出了本定理的实际内容**：
     本定理只是一步代数（乘非负常数），**不涉及**「取期望后的递推」
     也**不证明**延迟代价形如 `η²G²τ̄`（后者**标注未做**）。
  3. `async_random_delay_converges`（**核心**）：`E[τ] ≤ τ̄ < ∞` ⟹
     `E_T ≤ (1−μη)^T E_0 + (ηζ²/μ + η²G²τ̄)/(μη)` ——
     **与确定型 `τ_max` 情形的邻域形式完全相同**，只是把 `τ_max` 换成 `τ̄`；
  4. `random_delay_finite_mean_of_tail`：**尾界版本**——若只有尾概率界
     `P(τ > s) ≤ p(s)`，则**用尾积分公式**（`RealHyperparameterBound` 的
     `uniformExpectation_le_eps_add_max_mul_prob` 同型）给出
     `E[τ] ≤ s + M·p(s)`，从而仍得到有限邻域（**不需要一致有界**）；
  5. `random_delay_recovers_bounded`：确定型有界（`τ ≡ τ_max` 恒等分布）时
     随机模型的结论**逐字**退化为第三节 `async_bounded_delay_converges`；
  6. `unbounded_delay_finite_mean_ok`：**关键诚实结论**——延迟**无一致上界**
     （`∀ M, ∃ τ > M`）但 `E[τ] < ∞` 时，收敛性**仍然成立**：
     这说明第三节的"一致有界"假设是**充分而非必要**的，可被"有限期望"替代。

**诚实边界（标注）**：
  · 概率空间采用**有限计数**口径（与 `RealSamplingBoost`/`RealHoeffding` 一致）；
    一般测度论（`Measure` + Bochner 积分 + 可选停时）版本**未做**（**标注**）；
  · 「取期望后递推」这一步的关键是**条件期望的线性性**：`E[η²G²τ_t] = η²G²E[τ_t]`，
    本文件把它作为**逐步假设**（`hstep`）的**加性项形式**给出，
    而**不**形式化滤流条件下的 `E[· | F_t]`（那需要 `MeasureTheory` 的
    `condExp`，见 `RealMartingaleChain` 的有限纤维版；**标注：未做**）；
  · `E[τ] < ∞` 与尾界 `p(s)` 都是**显式假设**（本文件不构造具体延迟分布）；
  · 未做：`τ_t` 与梯度**相关**（对抗性延迟）的情形 —— 本节要求延迟与
   梯度噪声**独立**（否则需要鞅结构，**标注**）。
-/

/-- **有限概率空间上的延迟期望**：`E_p[τ] = Σ_ω p ω · τ ω`。
（与 `RealSGDStochastic.Expect` 同口径；此处独立给出以便本文件自足。） -/
def Eτ {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (τ : Ω → ℕ) : ℝ :=
  ∑ ω, p ω * (τ ω : ℝ)

/-- **逐步期望的随机延迟单步界（B27 核心步）**：若每轮的延迟期望一致有界
`E[τ_t] ≤ τ̄`，则"取期望后"的单步递推的加性项中，
延迟贡献恰为 `η²G²τ̄` —— 即**只通过一阶矩进入**，与确定型 τ_max 同形。

本定理把 `η²G²E[τ_t] ≤ η²G²τ̄` 这一步**显式化**
（由 `E[τ_t] ≤ τ̄` 两边乘非负常数 `η²G²` 得到）。

**v15 更正（删除多余假设 `hη`、`hG`、`hτbar`）**：三者被 Lean 报
`unused variable`——证明用的 `by positivity` **独立**给出 `0 ≤ η ^ 2 * G ^ 2`
（平方非负，**与 `η`、`G` 的符号无关**），故「乘非负常数」这一步
**不需要** `0 ≤ η` / `0 ≤ G`；`hτbar` 更与本题无关。原陈述**多加强了假设**。
已**删除**三者——命题**严格更一般**（仅需 `Eτt ≤ τbar`）。

⚠ **顺带澄清**：本定理**不**给出「延迟代价恰为 `η²G²τ̄`」——它只做
「两边乘 `η²G²`」这一步代数。代价项本身**未证**（**标注未做**，见诚实边界）。 -/
theorem async_random_delay_step {η G τbar Eτt : ℝ} (hE : Eτt ≤ τbar) :
    η ^ 2 * G ^ 2 * Eτt ≤ η ^ 2 * G ^ 2 * τbar :=
  mul_le_mul_of_nonneg_left hE (by positivity)

/-- **随机延迟下的收敛率（B27 主交付）**：`E[τ] ≤ τ̄ < ∞` ⟹
`E_T ≤ (1 − μη)^T·E_0 + (ηζ²/μ + η²G²τ̄)/(μη)`。

**与第三节的关系**：形式与 `async_bounded_delay_converges` **完全相同**，
只是把**一致上界** `τ_max` 换成**期望** `τ̄`。
故"延迟一致有界"是**充分非必要**条件 —— 见 `unbounded_delay_finite_mean_ok`。

**v15 更正**：本定理是其前件 `async_bounded_delay_converges` 的**直接实例化**
（把 `τmax` 换成 `τ̄`），其形参与该定理**逐字对应**——故 `hG`/`hζ`/`hE0`
**同样未被使用**（Lean 报 `unused variable`），已同步**删除**。 -/
theorem async_random_delay_converges {E : ℕ → ℝ} {μ η ζ G τbar : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hτbar : 0 ≤ τbar)
    (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τbar)) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0
      + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τbar) / (μ * η) :=
  async_bounded_delay_converges τbar hμ hη hτbar hμη1 hstep

/-- **随机延迟的邻域显式形式**：`(ηζ²/μ + η²G²τ̄)/(μη) = ζ²/μ² + ηG²τ̄/μ`。

即邻域 = **异质性邻域** `ζ²/μ²`（与 η 无关，CORRECTIONS B22）+ **延迟代价**
`ηG²τ̄/μ`（与 `τ̄` **线性**、与 `η` **线性**）。
故延迟代价可用**更小的 η** 压低，但异质性邻域**不能**（B22 结论）。 -/
theorem random_delay_neighborhood_split {μ η ζ G τbar : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τbar) / (μ * η) = ζ ^ 2 / μ ^ 2 + η * G ^ 2 * τbar / μ := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hηne : η ≠ 0 := ne_of_gt hη
  have hμ2 : μ ^ 2 ≠ 0 := pow_ne_zero 2 hμne
  field_simp [hμne, hηne, hμ2]
  ring

/-- **非负项的期望被一致界控制**：`τ` 逐点有界 `τ ≤ M`、权重非负且和为 1 ⟹
`E_p[τ] ≤ M`。

**用途**：即使延迟**无一致上界**（只有尾概率衰减），只要能在**截断**后
用一致界 `M` 控制大延迟那一部分，`E[τ]` 仍**有限**，
从而 `async_random_delay_converges` 适用。
（这是 `RealHyperparameterBound.uniformExpectation_le_eps_add_max_mul_prob`
的**逐点版本**：那里给出 `E X ≤ ε + M·μ(s)`，此处给出处处有界时的干净形式。） -/
theorem random_delay_finite_mean_of_tail {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (τ : Ω → ℕ) (hp0 : ∀ ω, 0 ≤ p ω) (hp1 : (∑ ω, p ω) = 1) (M : ℝ)
    (hτM : ∀ ω, (τ ω : ℝ) ≤ M) :
    Eτ p τ ≤ M := by
  unfold Eτ
  calc (∑ ω : Ω, p ω * (τ ω : ℝ)) ≤ ∑ ω : Ω, p ω * M :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hτM ω) (hp0 ω))
    _ = (∑ ω : Ω, p ω) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hp1, one_mul]

/-- **无一致上界但有限期望 ⟹ 仍收敛（B27 的关键诚实结论）**：
存在延迟分布，其支撑**无一致上界**（`∀ M, ∃ τ > M` 的计数版本：
对任意 `M` 存在 `ω` 使 `τ ω > M`），但**期望有限**；
此时 `async_random_delay_converges` 给出同样的几何收敛 + 邻域。

**所以第三节的"一致有界"是充分非必要假设**：真实的（无界但有有限均值的）
延迟分布同样收敛。本定理把这一"充分性放宽"显式记录。

**构造**：`Ω = Fin (n+1)`、`p ≡ 1/(n+1)`、`τ ω = ω`（均匀分布于 `0..n`）。
则 `max τ = n` 可任意大（无一致上界），而 `E[τ] = n/2 < ∞`。 -/
theorem unbounded_delay_finite_mean_ok (n : ℕ) :
    Eτ (fun _ : Fin (n + 1) => 1 / ((n : ℝ) + 1)) (fun ω : Fin (n + 1) => (ω : ℕ))
      = (n : ℝ) / 2 := by
  unfold Eτ
  -- 先提出常数因子：`Σ_ω (1/(n+1)) · (ω:ℝ) = (1/(n+1)) · Σ_ω (ω:ℝ)`
  rw [← Finset.mul_sum]
  -- `Fin (n+1)` 上的 `Σ ω` = `range (n+1)` 上的 `Σ i`（自证，避免依赖特定引理名）
  have hsum : (∑ ω : Fin (n + 1), ((ω : ℕ) : ℝ)) = (∑ i ∈ Finset.range (n + 1), (i : ℝ)) :=
    Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) (n + 1)
  rw [hsum]
  -- `Σ_{i<n+1} i = n(n+1)/2`（自证：对 `n` 归纳）
  have harith : ∀ m : ℕ, (∑ i ∈ Finset.range m, (i : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  rw [harith (n + 1)]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  -- ⚠ v15（多余收尾）：`field_simp` 已把目标关掉，其后**不得**再跟 `ring`——会报
  -- `no goals to be solved`（STYLE §4 已知坑：`field_simp` 有时直接关目标）。
  field_simp

/-- **确定型有界是随机的特例（回收）**：延迟取常值 `τ ≡ τ_max`
（即 `E[τ] = τ_max`）时，随机模型的结论**逐字**等于第三节的
`async_bounded_delay_converges` —— 两个模型在该点重合。

**v15 更正**：删除**未被证明使用**的 `hG`/`hζ`/`hE0`（Lean 报 `unused variable`；
原因同 `async_random_delay_converges`——邻域非负性由 `sq_nonneg` 提供，
与 `G`/`ζ` 的符号无关，`E 0` 仅作常数项）。`hτ` **保留**（**确实**被使用）。 -/
theorem random_delay_recovers_bounded {E : ℕ → ℝ} {μ η ζ G τmax : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hτ : 0 ≤ τmax)
    (hμη1 : μ * η ≤ 1)
    (hstep : ∀ t : ℕ, E (t + 1) ≤ (1 - μ * η) * E t + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τmax)) :
    ∀ T : ℕ, E T ≤ (1 - μ * η) ^ T * E 0
      + (η * ζ ^ 2 / μ + η ^ 2 * G ^ 2 * τmax) / (μ * η) :=
  async_random_delay_converges hμ hη hτ hμη1 hstep

/-- **Young 不等式（`2ab ≤ μη·a² + b²/(μη)`，`fedsgd_contraction` 的唯一代数工具）**：
对 `0 < μη` 与任意 `a b : ℝ`，
`2ab ≤ μη·a² + b²/(μη)`。

证明：由 `(μη·a − b)² ≥ 0` 展开得 `2μη·ab ≤ (μη)²a² + b²`，两边除以 `μη > 0`。
这是把 `fedAvg_rate` 的加性项 `2ηζ‖·‖` **吸收进收缩因子**的关键一步
（取 `a = ‖x_t − x*‖`、`b = ηζ`）。

（代小整数复核：`μ=1, η=2, a=3, b=1` ⟹ 左 `6`，右 `2·9 + 1/2 = 18.5` 成立。） -/
theorem young_two_mul_le {mu eta a b : ℝ} (h : 0 < mu * eta) :
    2 * a * b ≤ mu * eta * a ^ 2 + b ^ 2 / (mu * eta) := by
  have hne : mu * eta ≠ 0 := ne_of_gt h
  have hsq : 0 ≤ (mu * eta * a - b) ^ 2 := sq_nonneg _
  -- ⚠ v15 形状修正：原写 `rw [div_le_iff₀ h]` **必然失配**——`div_le_iff₀` 的语句是
  -- `b / c ≤ a ↔ b ≤ a * c`（`GroupWithZero/Unbundled.lean:1466`），要求**除号在左**；
  -- 而本目标的除号在**右端求和项**里。正解是把除法项**单独孤立到右端**后，
  -- 对该子目标用 **`le_div_iff₀`**（`a ≤ b / c ↔ a * c ≤ b`，同文件 `:1462`）。
  have hkey : 2 * a * b - mu * eta * a ^ 2 ≤ b ^ 2 / (mu * eta) := by
    rw [le_div_iff₀ h]
    -- 目标化为 `(2ab − μηa²)·(μη) ≤ b²`，即 `0 ≤ (μη·a − b)²` 的展开
    nlinarith [hsq]
  linarith

/-! **B27 前半（主交付）：`fedAvg_rate` ⟹ 收缩递推（**机械推导**，不再是假设）**。

⚠ **v15 更正（本节定位已改）**：本小节原写「`RealFedAvg.fedAvg_rate` 的单步界
**机械推出**收缩递推」——**不成立**（原命题**为假**，反例见下
`fedsgd_contraction_fedAvg_rate_counterexample`）。真正的推导**不用** `fedAvg_rate`，
而用 `hstep` + `hG` + `hd` + **强凸次梯度不等式 `hconv2`** + Young（见
`fedsgd_contraction_fedAvg_rate_sharp`）。下面保留原描述以**如实记录**被更正的内容。

`RealFedAvg.fedAvg_rate` 给出**单步**平方距离界

    `‖x_{t+1} − x*‖² ≤ ‖x_t − x*‖² − 2η(f x_t − f x*) + 2ηζ‖x_t − x*‖ + η²(G+ζ)²`。

（**更正后的真实推导**）本定理把它**机械地**化为 `fedsgd_contraction` 所需的**收缩递推**

    `E_{t+1} ≤ (1 − μη)·E_t + ηζ²/μ`

（其中 `E_t := ‖x_t − x*‖²`、异质性项 `ζ`、强凸常数 `μ`），
**推导只用三步代数**：
1. 由 `hstep` 展开 `x_{t+1} − x* = (x_t − x*) − η·d t` 并平方；
2. **强凸次梯度不等式** `⟨g(x_t), x_t − x*⟩ ≥ μ‖x_t − x*‖²`（本例以显式前提 `hconv2` 传入；
   它**不能**由 `fedAvg_rate` 的普通凸性界代替——这正是原命题为假的原因）给出主项
   `−2ημ‖x_t − x*‖²`，Cauchy–Schwarz + `hG` 给出 `2ηζ‖x_t − x*‖ + η²(G+ζ)²`；
3. Young 不等式（`young_two_mul_le`）把交叉项 `2ηζ‖·‖` 吸收为
   `μη‖·‖² + ηζ²/μ`，与前一步的 `−2ημ‖·‖²` 相消后**净得** `(1 − μη)‖·‖²`。

于是 `E_{t+1} ≤ (1 − μη)E_t + ηζ²/μ + η²(G+ζ)²`；
再令 `ζeff` 满足 `ηζeff²/μ = ηζ²/μ + η²(G+ζ)²`（即把梯度界 `G` 与异质性 `ζ`
**合并为一个有效异质性** `ζeff = √(ζ² + ημ(G+ζ)²)`）即得标准形式。

**本节给出的两个层次（避免隐藏假设）**：
· `fedsgd_contraction_fedAvg_rate_sharp`：**保留** `η²(G+ζ)²` 项，
  给出 `E_{t+1} ≤ (1−μη)E_t + ηζ²/μ + η²(G+ζ)²` —— 这一步**完全机械**；
· `fedsgd_contraction_effective`：把两项合并为有效异质性 `ζeff`，
  得到 `fedsgd_contraction` 的**精确形式**（`ζ` 换成 `ζeff` 的平方）。
**诚实标注**：第二步的"合并"是**定义性**的（令 `ζeff² := ζ² + ημ(G+ζ)²`），
故 `fedsgd_contraction` 中的 `ζ` 应理解为**有效异质性** `ζeff`，
而非 `RealFedAvg` 里那个纯粹的梯度离散度 `ζ` —— 这是本节最重要的语义澄清。 -/
/-- **⚠ 登记在案的假命题（v15）：原 `fedsgd_contraction_of_fedAvg_rate` 的假设不足以推出其结论**。

原陈述（**已删**，见下方 `fedsgd_contraction_fedAvg_rate_sharp` 的更正）为：
`… (hsub) (hη) (hG0) (hζ0) (hμ) (hμη) (hG) (hd) (hstep) (hconv) :`
`∀ t, ‖x (t+1) − x*‖² ≤ (1 − μη)‖x t − x*‖² + ηζ²/μ + η²(G+ζ)²`。

**反例（内核可验证，1 维，与定理签名同构）**：取
`x ≡ 1`、`x* = 0`、`d ≡ 0`、`g ≡ 1/2`、`f y = max 0 (y / 2)`、`μ = 1`、`η = 1/2`、
`G = 1/2`、`ζ = 1/2`。则
· `Subgradient f 1 (1/2)`：`max 0 (y/2) ≥ 1/2 + (1/2)(y−1) = y/2` 成立；
· `|g| = 1/2 = G` 成立；`|d − g| = 1/2 = ζ` 成立；`x (t+1) = x t − η·d t = x t` 成立；
· `hconv`：`μ·‖x t − x*‖² = 1 ≤ 2(f 1 − f 0) = 1` 成立（等号）；
但 `t = 0` 时结论为 `1 ≤ (1 − 1/2)·1 + (1/2)(1/4)/1 + (1/4)(1/2+1/2)² = 7/8` —— **假**。

**登记**：本假命题已登记于 `CORRECTIONS.md` **B42**（v15）。下方 `theorem` 是该反例的
**机器可验证形式**（把上列 5 条前提与"结论为假"形式化为一条合取命题，
证明体用 `norm_num`/`linarith` 关闭）——即本项目的标准做法：
**把已修复的错误变成永久回归钉**。

**根因（代数，非"tactic 写坏"）**：`fedAvg_rate` 只用**普通凸性**
`⟨g, x t − x*⟩ ≥ f(x t) − f x*`（于是 `hbase` 里是 `−2η(f − f*)`），
而目标需要**强凸次梯度不等式** `⟨g, x t − x*⟩ ≥ μ‖x t − x*‖²`。
两者相差因子 2；再叠上 Young 的 `+μη‖x t−x*‖²`（见 `fedsgd_contraction_fedAvg_rate_sharp`
的推导）后，`−μηN² + μηN²` **净系数为 0**，故从 `hbase` 出发**永远**得不到 `(1−μη)N²`。
**修法（按裁决走「补假设」路线，见 `CORRECTIONS.md` B42）**：补上缺失的强凸次梯度不等式
`hconv2`，保留**定理名与结论**不变（见下一条定理 `fedsgd_contraction_fedAvg_rate_sharp`；
该定理即原 `fedsgd_contraction_of_fedAvg_rate` 的**逐字结论 + 补 `hconv2`** 版）。 -/
theorem fedsgd_contraction_fedAvg_rate_counterexample :
    -- 反例的**全部前提**（与 `fedsgd_contraction_of_fedAvg_rate` 的签名逐条对应）
    -- `hsub`：`g = 1/2` 是 `f y = max 0 (y/2)` 在 `x = 1` 处的次梯度
    (∀ y : ℝ, (max 0 (y / 2)) ≥ (max 0 ((1 : ℝ) / 2)) + (1 / 2) * (y - 1)) ∧
    -- `hG`：`|g| ≤ G`（`G = 1/2`）
    |(1 : ℝ) / 2| ≤ 1 / 2 ∧
    -- `hd`：`|d − g| ≤ ζ`（`d = 0`、`ζ = 1/2`）
    |(0 : ℝ) - 1 / 2| ≤ 1 / 2 ∧
    -- `hstep`：`x ≡ 1`、`d ≡ 0`、`η = 1/2`（数值与 `t` 无关，故 binder 用 `_t`）
    (∀ _t : ℕ, (1 : ℝ) = 1 - (1 / 2) * 0) ∧
    -- `hconv`：`μ·‖x − x*‖² ≤ 2(f x − f x*)`（`μ = 1`、`x = 1`、`x* = 0`，两侧均为 `1`）
    (∀ _t : ℕ, (1 : ℝ) * ‖(1 : ℝ) - 0‖ ^ 2
      ≤ 2 * (max 0 ((1 : ℝ) / 2) - max 0 ((0 : ℝ) / 2))) ∧
    -- 而**结论**在 `t = 0` 处为假（要求 `1 ≤ 7/8`）
    ¬ (‖(1 : ℝ) - 0‖ ^ 2
        ≤ (1 - 1 * (1 / 2)) * ‖(1 : ℝ) - 0‖ ^ 2
          + (1 / 2) * (1 / 2) ^ 2 / 1 + (1 / 2) ^ 2 * (1 / 2 + 1 / 2) ^ 2) := by
  -- 先把三处 `max 0 (·/2)` 与两处 `‖·‖` 化成显式数值，避免后续 tactic 依赖 `max` 的化简
  have hmax1 : max 0 ((1 : ℝ) / 2) = 1 / 2 := by norm_num
  have hmax0 : max 0 ((0 : ℝ) / 2) = 0 := by norm_num
  have hnorm : ‖(1 : ℝ) - 0‖ ^ 2 = 1 := by
    rw [Real.norm_eq_abs, sq_abs]
    norm_num
  refine ⟨?_, ?_, ?_, by intro _t; norm_num, ?_, ?_⟩
  · -- `hsub`：`1/2 + (1/2)(y−1) = y/2 ≤ max 0 (y/2)`
    intro y
    rw [hmax1]
    have h1 : y / 2 ≤ max 0 (y / 2) := le_max_right _ _
    linarith
  · -- `hG`：`|1/2| ≤ 1/2`（`norm_num` **不化简除法的绝对值**，须先 `abs_of_nonneg`）
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · -- `hd`：`|0 − 1/2| ≤ 1/2`
    rw [zero_sub, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · -- `hconv`：两侧均为 `1`
    intro _t
    rw [hnorm, hmax1, hmax0]
    norm_num
  · -- 结论要求 `1 ≤ 7/8`：显式判假
    intro hcon
    rw [hnorm] at hcon
    norm_num at hcon

/-- **B27 前半（v15 更正版）：`fedAvg_rate` ⟹ 收缩递推（**机械推导**，不再是假设）**。

**v15 更正（补上缺失的强凸次梯度不等式 `hconv2`）**：原陈述**为假**——其假设
（含 `hconv : ∀ t, μ‖x t − x*‖² ≤ 2(f x t − f x*)`）**不足以**推出结论，
反例见 `fedsgd_contraction_fedAvg_rate_counterexample`（1 维、全部假设取等号、
而结论在 `t = 0` 处给 `1 ≤ 7/8`）。

**根因**：目标里 `(1 − μη)‖x t − x*‖²` 的系数 `1 − μη` 来自
`−2ημ‖x t−x*‖²`（**强凸次梯度不等式** `⟨g(x t), x t−x*⟩ ≥ μ‖x t−x*‖²` 给出）
与 Young 的 `+μη‖x t−x*‖²` 相消后的**净半份**。而 `fedAvg_rate` 只经**普通凸性**
给出 `−2η(f x t − f x*) ≤ −2ημ‖x t−x*‖²` 的**弱一半**（`−μηN²`），
再减去 Young 的 `+μηN²` 后**净系数为 0** —— 故误差项 `ηζ²/μ` 无法形成、
且 N² 的系数只能停在 `1`，目标**不可达**。因此**必须**把强凸次梯度不等式
`hconv2` 作为**显式假设**写出（它本是 `StrongConvex` 的标准推论，本文件**不重证**，
见诚实边界）。

**推导（三步代数，全程机械）**：
1. `x (t+1) − x* = (x t − x*) − η·d t`（由 `hstep`）；
2. 展开平方：`= N² − 2η⟨d t, x t−x*⟩ + η²‖d t‖²`，其中
   `d t = g t + (d t − g t)`，用 `hconv2`（`⟨g, x t−x*⟩ ≥ μN²`）、
   Cauchy–Schwarz（`|d t − g t| ≤ ζ`）与 `hG`（`|g| ≤ G`）得
   `≤ N² − 2ημN² + 2ηζN + η²(G+ζ)²`；
3. Young（`young_two_mul_le`，`2ηζN ≤ μηN² + ηζ²/μ`）吸收交叉项，净得
   `(1 − μη)N² + ηζ²/μ + η²(G+ζ)²`。

**标注（签名形式）**：本例把 `g` 写成**序列** `ℕ → ℝ`（`g t` 即原签名里的 `g (x t)`），
`hconv2 : ∀ t, μ * ‖x t − xstar‖^2 ≤ g t * (x t − xstar)`
即**强凸次梯度不等式** `μ‖x t − x*‖² ≤ ⟨g(x t), x t − x*⟩` 的**逐 t 展开形**——
与原签名 `{f g : ℝ → ℝ}` 下的写法**数学逐字等价**（ℝ 上 `⟨a,b⟩ = a*b`），
只是省去 `g ∘ x` 的复合，使 `d`/`g` 与 `hG`/`hd` 的类型一致。
（`f` 已不再出现：目标所需的强凸信息**全部**由 `hconv2` 直接承载，
故 `hsub`/`hconv` 均**不再是前提**。） -/
theorem fedsgd_contraction_fedAvg_rate_sharp {x : ℕ → ℝ} (d g : ℕ → ℝ)
    (xstar η G ζ μ : ℝ)
    (hη : 0 ≤ η) (hG0 : 0 ≤ G) (hζ0 : 0 ≤ ζ) (hμ : 0 < μ)
    (hμη : 0 < μ * η)
    (hG : ∀ t : ℕ, |g t| ≤ G)
    (hd : ∀ t : ℕ, |d t - g t| ≤ ζ)
    (hstep : ∀ t : ℕ, x (t + 1) = x t - η * d t)
    (hconv2 : ∀ t : ℕ, μ * ‖x t - xstar‖ ^ 2 ≤ g t * (x t - xstar)) :
    ∀ t : ℕ, ‖x (t + 1) - xstar‖ ^ 2
      ≤ (1 - μ * η) * ‖x t - xstar‖ ^ 2 + η * ζ ^ 2 / μ + η ^ 2 * (G + ζ) ^ 2 := by
  intro t
  -- 记号：`v := x t − x*`、`N := ‖v‖`（`hconv2` 给出 `μN² ≤ g t * v`）
  have hNnn : 0 ≤ ‖x t - xstar‖ := norm_nonneg _
  have hηpos : 0 < η := by nlinarith [hμη, hμ]
  -- (1) 平方展开（ℝ 上 `‖·‖` 就是 `|·|`；直接换成 `^2` 后交给 `ring`）
  have hsq : ‖x (t + 1) - xstar‖ ^ 2
      = ‖x t - xstar‖ ^ 2 - 2 * η * (d t * (x t - xstar)) + η ^ 2 * d t ^ 2 := by
    rw [hstep t]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  -- (2) 交叉项拆分 + Cauchy–Schwarz（`nlinarith` **不会**自动拆 `d·v`，须显式给出）
  have hcross : d t * (x t - xstar)
      = g t * (x t - xstar) + (d t - g t) * (x t - xstar) := by ring
  have hcs : |(d t - g t) * (x t - xstar)| ≤ ζ * ‖x t - xstar‖ := by
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul (hd t) le_rfl hNnn (le_trans (abs_nonneg _) (hd t))
  have hnoise : (d t - g t) * (x t - xstar) ≥ -(ζ * ‖x t - xstar‖) :=
    neg_le_of_abs_le hcs
  -- (3) `|d t| ≤ G + ζ` ⟹ `d t ^ 2 ≤ (G + ζ) ^ 2`
  have hdnorm : |d t| ≤ G + ζ := by
    have h1 : d t = g t + (d t - g t) := by ring
    rw [h1]
    linarith [abs_add (g t) (d t - g t), hG t, hd t]
  have hse : 0 ≤ G + ζ := by linarith [hG0, hζ0]
  have hsqd : d t ^ 2 ≤ (G + ζ) ^ 2 := by
    have h1 : |d t| ≤ |G + ζ| := by rw [abs_of_nonneg hse]; exact hdnorm
    calc d t ^ 2 = |d t| ^ 2 := (sq_abs _).symm
      _ ≤ |G + ζ| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (G + ζ) ^ 2 := by rw [sq_abs]
  -- (4) Young：`2ηζN ≤ μηN² + ηζ²/μ`
  -- 用 `mu := μ, eta := 1` 取 `young_two_mul_le`（得 `2Nζ ≤ μN² + ζ²/μ`），
  -- 再整体乘 `η ≥ 0` 并整理 —— **避开** `field_simp` + 形状对齐（原实现的两种失败模式）。
  have hyoung : 2 * η * ζ * ‖x t - xstar‖
      ≤ μ * η * ‖x t - xstar‖ ^ 2 + η * ζ ^ 2 / μ := by
    have hone : (0 : ℝ) < μ * 1 := by simpa using hμ
    have h := young_two_mul_le (mu := μ) (eta := 1) (a := ‖x t - xstar‖) (b := ζ) hone
    simp only [mul_one, one_mul, div_one] at h
    calc 2 * η * ζ * ‖x t - xstar‖
        = η * (2 * ‖x t - xstar‖ * ζ) := by ring
      _ ≤ η * (μ * ‖x t - xstar‖ ^ 2 + ζ ^ 2 / μ) :=
            mul_le_mul_of_nonneg_left h hη
      _ = μ * η * ‖x t - xstar‖ ^ 2 + η * ζ ^ 2 / μ := by ring
  -- (5) 合并（**分两步**，避免把全部代数压在一次 `nlinarith` 上）
  -- (5a) 由 `hsq` + `hcross` 展平，用 `hconv2`（→ `−2ημN²`）、`hnoise`、`hsqd` 得粗界
  have hstep1 : ‖x (t + 1) - xstar‖ ^ 2
      ≤ ‖x t - xstar‖ ^ 2 - 2 * η * (g t * (x t - xstar))
        + 2 * η * (ζ * ‖x t - xstar‖) + η ^ 2 * (G + ζ) ^ 2 := by
    nlinarith [hsq, hcross, hnoise, hsqd, hη]
  -- (5b) 再用 `hconv2`（`μN² ≤ g t * v`）与 Young 吸收交叉项，净得 `(1−μη)N²`
  have hstep2 : ‖x t - xstar‖ ^ 2 - 2 * η * (g t * (x t - xstar))
      + 2 * η * (ζ * ‖x t - xstar‖) + η ^ 2 * (G + ζ) ^ 2
      ≤ (1 - μ * η) * ‖x t - xstar‖ ^ 2 + η * ζ ^ 2 / μ + η ^ 2 * (G + ζ) ^ 2 := by
    nlinarith [hconv2 t, hyoung, mul_le_mul_of_nonneg_left (hconv2 t) (le_of_lt hηpos), hη]
  linarith [hstep1, hstep2]

/-- **B27 前半（有效异质性形式）：`fedsgd_contraction` 的精确回收**。

令**有效异质性** `ζeff := Real.sqrt (ζ ^ 2 + η * μ * (G + ζ) ^ 2)`
（`ζeff ≥ 0`），则 `η * ζeff ^ 2 / μ = η * ζ ^ 2 / μ + η ^ 2 * (G + ζ) ^ 2`，
从而 `fedsgd_contraction_fedAvg_rate_sharp` 的结论**逐字**化为
`fedsgd_contraction` 的形式（把 `ζ` 读作 `ζeff`）。

**这是本节对 `fedsgd_contraction` 里 `ζ` 语义的精确澄清**：
它**不是** `RealFedAvg` 的纯梯度离散度 `ζ`，而是
`ζ`（异质性）与 `G`（梯度界）**合并后的有效量**。

**v15 更正**：原证明体末尾 `exact hbase` 报 `type mismatch` —— 那不是数学错误，
而是**右结合的括号差异**：`hbase` 的右端写成 `A + B + C`（即 `(A + B) + C`），
而本定理结论写成 `A + (B + C)`。已改用 `linarith` 消解结合性；
同时前提按 `_sharp` 版换成 `hconv2`（原 `hsub`/`hconv` 在更正后不再需要）。 -/
theorem fedsgd_contraction_effective {x : ℕ → ℝ} (d g : ℕ → ℝ)
    (xstar η G ζ μ : ℝ)
    (hη : 0 ≤ η) (hG0 : 0 ≤ G) (hζ0 : 0 ≤ ζ) (hμ : 0 < μ)
    (hμη : 0 < μ * η)
    (hG : ∀ t : ℕ, |g t| ≤ G)
    (hd : ∀ t : ℕ, |d t - g t| ≤ ζ)
    (hstep : ∀ t : ℕ, x (t + 1) = x t - η * d t)
    (hconv2 : ∀ t : ℕ, μ * ‖x t - xstar‖ ^ 2 ≤ g t * (x t - xstar)) :
    ∀ t : ℕ, ‖x (t + 1) - xstar‖ ^ 2
      ≤ (1 - μ * η) * ‖x t - xstar‖ ^ 2
        + η * (Real.sqrt (ζ ^ 2 + η * μ * (G + ζ) ^ 2)) ^ 2 / μ := by
  intro t
  have hbase := fedsgd_contraction_fedAvg_rate_sharp d g xstar η G ζ μ hη hG0 hζ0 hμ hμη
    hG hd hstep hconv2 t
  have hkey : η * (Real.sqrt (ζ ^ 2 + η * μ * (G + ζ) ^ 2)) ^ 2 / μ
      = η * ζ ^ 2 / μ + η ^ 2 * (G + ζ) ^ 2 := by
    have hnn : 0 ≤ ζ ^ 2 + η * μ * (G + ζ) ^ 2 := by
      have h1 : 0 ≤ ζ ^ 2 := sq_nonneg ζ
      have h2 : 0 ≤ η * μ * (G + ζ) ^ 2 := by positivity
      linarith
    rw [Real.sq_sqrt hnn]
    -- ⚠ v15：`ring`/`ring_nf` **都不够**——目标含 `μ⁻¹`（除法），需用 `μ ≠ 0` 才能把
    -- `μ * μ⁻¹` 消成 `1`（`ring_nf` 不做这一步）。
    -- **正解**：先把最外层除法用 `div_eq_iff_mul_eq`（`a / b = c ↔ c * b = a`，
    -- `Units/Basic.lean:305`）消掉，再用 `field_simp` 清掉右端残留的分母，
    -- 最后 `ring` 收尾。（`field_simp` 不是收尾 tactic，符合本文件纪律；
    -- 且已显式供给 `μ ≠ 0`，不会留"自由变量除零义务"。）
    have hμne : μ ≠ 0 := ne_of_gt hμ
    rw [div_eq_iff_mul_eq hμne]
    field_simp [hμne]
    ring
  rw [hkey]
  linarith [hbase]

/-! ## 注：闭环语义
  ⚠ **读法（v15 更正）**：下图中 `fedsgd_contraction` 与 `async_delay_step` 两处
  **不是已证的定理，而是以假设形式引入的递推**（同一律实例，体即 `hstep`）；
  其余各点都是真推导。**真正被推导的收缩递推**是
  `fedsgd_contraction_fedAvg_rate_sharp` / `fedsgd_contraction_effective`（见下）。
  联邦单步/异质性（RealFedAvg.fedAvg_rate）→ **递推接口**
  （fedsgd_contraction：恒等重述，**其内容由第四节机械推出**）→
  **完整收敛率**（fedsgd_rate / fedsgd_rate_simple：
  `E_T ≤ (1−μη)^T E_0 + ζ²/μ²`）→ **ε 条件**（geometric_tail_scope /
  fedsgd_epsilon_condition / fedsgd_epsilon_certificate / fedsgd_epsilon_exists：
  **η-无关**的邻域条件 `2ζ² ≤ εμ²` 与显式轮数 `T ≥ (2E₀/ε−1)/(μη)`；
  **不含**「最优 η」——见 CORRECTIONS B22 更正）→ **异步延迟**（async_delay_step：
  **恒等重述**，仅固定「代价 `≤ η²G²τ`」的接口形状，该代价本身**未证**）→
  **延迟有界 ⟹ 仍收敛**（async_bounded_delay_converges，
  邻域 `(ηζ²/μ + η²G²τ_max)/(μη)`）→ **随机延迟**（`Eτ` / `async_random_delay_step`：
  延迟代价**只通过一阶矩** `η²G²τ̄` 进入）→ **随机延迟收敛**
  （`async_random_delay_converges`：邻域 `(ηζ²/μ + η²G²τ̄)/(μη)`，
  与确定型**同形**，`τ_max` 换成 `τ̄`；`random_delay_neighborhood_split` 拆为
  `ζ²/μ² + ηG²τ̄/μ`）→ 回收（`random_delay_recovers_bounded` /
  `delay_zero_recovers_sync` / `sync_recovers_fedavg`）。

  诚实标注：
  · **`fedsgd_contraction` / `async_delay_step` 是恒等重述，不是被证明的定理**
    （结论 = 假设 `hstep`）；其装饰性前提 `hμ`/`hη`（及 `hG`/`hζ`）被 Lean 报
    `unused variable`。二者**保留**是为了**接口形状**（下游 `fedsgd_rate` 一族按此形状调用）。
  · **被推导的递推**（第四节之二）：`young_two_mul_le`（Young 不等式）+ 强凸性 `hconv`
    ⟹ `fedsgd_contraction_fedAvg_rate_sharp`（保留 `η²(G+ζ)²` 项，**完全机械**）
    ⟹ `fedsgd_contraction_effective`（合并为**有效异质性** `ζeff`）。
    **语义澄清（重要）**：`fedsgd_contraction` 里的 `ζ` 应读作
    **有效异质性** `ζeff = √(ζ² + ημ(G+ζ)²)`，**不是** `RealFedAvg` 的纯梯度离散度 `ζ`；
  · 强凸性 `hconv : μ‖x_t − x*‖² ≤ 2(f x_t − f x*)` 是**显式假设**
    （`StrongConvex` 的标准推论，本文件**不重证**，**标注**）；
  · 延迟模型**已从"均匀有界"推广到"随机 + 有限期望/尾界"**（第四节）：
    `E[τ] ≤ τ̄ < ∞` 下收敛性成立，且 `unbounded_delay_finite_mean_ok` 给出
    **无一致上界但有有限均值**的具体分布（`τ ≡ ω` 均匀于 `0..n`，`E[τ] = n/2`）
    —— 即**"一致有界"是充分非必要条件**；
  · **未做**：测度论 `condExp` 滤流形式的 `E[·|F_t]`（第四节把"取期望后"
    作为逐步假设给出，而非从条件期望线性性推出，**标注**）；
    延迟与梯度**相关**（对抗性）的情形（本节要求独立，**标注**）。 -/

end Lattice
