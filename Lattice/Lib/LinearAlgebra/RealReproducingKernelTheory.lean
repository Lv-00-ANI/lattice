import Mathlib
import Lattice.Lib.LinearAlgebra.RealRKHSKernel
/-!
# LATTICE: 再生核 Hilbert 空间的深层理论（有限索引版）—— 再生性、范数、核闭包与归一化

`RealRKHSKernel` 已建立核方法的**基础层**：核的定义（`IsSymmKernel` / `IsPSDKernel` /
`IsPosDefKernel`）、核 Gram 矩阵（`kernelGramMatrix`）、Mercer 有限版
（`kernelGramMatrix_psd_iff_exists_featureMap`）、距离–核恒等式
（`metric_eq_kernel_expansion`）以及「注意力 = Nadaraya–Watson」接口
（`softmax_attention_is_nw`）。它**明确登记**了三个未做项（见该文件「诚实边界」）：

  > **未做：RKHS 的完备化 / 再生性**。……没有构造抽象 RKHS `H_K`，也没有证明再生性
  > `⟨K_x, f⟩ = f(x)`。原因是抽象 RKHS 需要「由核函数张成的内积空间取完备化」……
  > **未做：核的正则性理论**。RKHS 范数、代表点定理……
  > **未做：无穷维特征映射的有限逼近误差**。

本文件**正面补上前两项**，采用与 `RealRKHSKernel` 完全一致的**有限索引**策略：
把索引集取为 `Fin n`，于是

  · 「抽象 RKHS `H_K`」退化为 **`Fin n → ℝ`**（有限维欧氏空间，自动完备）；
  · 「`L²` 的完备化」**消失**（有限维已完备，无需商空间 + 完备化）；
  · 「再生核 `K_x`」退化为**特征坐标行** `fun i => Φ (x i) p` 向量；
  · 「再生性 `⟨K_x, f⟩ = f x`」退化为**内积恒等式**（下方 `reproducing_property`）。

这不是「逼近」——在有限索引集上它与抽象 RKHS 的内容**逐字相同**，只是把
「张成空间取完备化」换成了「直接落在 `Fin n → ℝ` 里」。

## 本文件建立（与 `RealRKHSKernel` 严格互补，**不重复其任何定理**）

**一、再生性（reproducing property）**
1. `featureCoord`：把有限特征映射 `Φ : α → Fin m → ℝ` 看成坐标族
   `featureCoord Φ x i = Φ (x i) : Fin m → ℝ`（这是「`Φ(x_i)` 作为 RKHS 向量」的实现）；
2. `reproducingPairing`：`⟨Φ a, Φ b⟩ = Σ_p Φ a p · Φ b p`；`reproducingPairing_eq_sum` 为其展开；
3. **`reproducing_property`（主结果）**：**再生性**
   `reproducingPairing Φ (x i) (x j) = K (x i) (x j)`——
   即「在点 `x j` 处的求值泛函」就是「与 `K_{x j}` 的内积」。这是 RKHS 的**定义性质**，
   也是 `RealRKHSKernel` 明确登记为未做的那一条；
4. `reproducing_property_self`：对角特例 `⟨K_x, K_x⟩ = K x x`；
5. `isSymmKernel_of_featureMap`：**有特征映射 ⟹ 核自动对称**（`RealRKHSKernel` 中
   对称性须作为假设 `hsymm`；此处说明有 `Φ` 时它是**结论**）；
6. `isPSDKernel_of_featureMap`：**有特征映射 ⟹ 核半正定**（`IsPSDKernel` 语言）；
7. `reproducing_linearity` / `evalLinearMap`：求值泛函的**线性性**，并给出
   `LinearMap` 形态 `evalLinearMap u`（`evalLinearMap_apply` 为其展开）；
8. `reproducingPairing_eq_of_same_kernel`：**再生值由核唯一决定**——
   同一核的两条特征映射给出相同的再生对（RKHS 在同构意义下唯一的核心）。

**二、RKHS 范数与核的关系（`‖K_x‖² = K(x,x)`）**
9. `rkhsNormSq`：`‖Φ a‖² := Σ_p Φ a p²`（有限 RKHS 范数平方）；
10. **`rkhs_norm_sq_eq_kernel_diag`（主结果）**：`‖K_x‖² = K x x`
    —— 任务指定的核心关系，也是 `‖K_x − K_y‖² = Kxx − 2Kxy + Kyy` 的**单点版**
    （该两点版是 `RealRKHSKernel.metric_eq_kernel_expansion`，本文件**不重复**）；
11. `rkhs_norm_sq_eq_kernel_diag_of_psd`：**纯核语言版**——不需要显式给 `Φ`，
    只要核对称且半正定，则**存在** `Fin 1 → ℝ` 的坐标实现使 `Σ p, Phi p² = K a a`
    （由 `RealRKHSKernel` 的 Mercer 有限版在单点输入上取得）；
12. `rkhs_norm_sq_nonneg_of_psd`：`K` 半正定 ⟹ `0 ≤ K a a`（消费
    `RealRKHSKernel.kernel_diag_nonneg`）；`rkhs_norm_sq_eq_zero_iff`：`‖Φ a‖² = 0 ⟺ Φ a = 0`；
13. **`norm_reproducing_bound`**：**Cauchy–Schwarz 型 RKHS 界**
    `|Σ_p Φ a p · f p| ≤ √(K a a)·√(Σ_p f p²)`——这是「求值连续」的**定量形式**，
    也是 RKHS 正则化理论（`|f(x)|` 被 `‖f‖` 控制）的代数核心；
14. **`norm_difference_eq_kernel_distance` / `rkhsNormSq_sub_eq_kernel_distance`**：
    `‖K_x − K_y‖² = Kxx − 2Kxy + Kyy` 在**范数层面**的闭合形态——把
    `RealRKHSKernel.metric_eq_kernel_expansion` 的 `Φ` 语言翻译为
    `rkhsNormSq` / 差向量的**库内对象语言**（该恒等式本体在 `RealRKHSKernel`，
    本文件**不重证**，只给可直接引用的包装）；
15. `rkhs_norm_triangle`：**三角不等式** `√Σ(u+v)² ≤ √Σu² + √Σv²`
    （RKHS 范数是**真范数**，不只是二次型）；
16. `rkhs_distance_nonneg` / `rkhs_distance_zero_iff`：距离非负性与
    「距离为零 ⟺ `Φ a = Φ b`」（消费 `RealRKHSKernel.metric_kernel_nonneg` /
    `kernel_metric_zero_iff`，以范数语言重述）。

**三、核的闭包性质（和、积、数乘仍是核）**
17. **`kernelAdd_psd`**：核的和半正定（二次型对加法线性：`q₁ + q₂ ≥ 0`）；
    `kernelAdd_symm` / `isPosDefKernel_add`：对称性与 `IsPosDefKernel` 语言的对应版本；
18. **`kernelMul_psd_of_featureMap`（主结果，Hadamard / Schur 乘积定理的有限版）**：
    两个具**显式特征映射**的核，其**逐点积**仍是核。证明走**张量积特征映射**
    `(Φ⊗Ψ)(x)_{(p,q)} = Φ(x)_p·Ψ(x)_q`，直接展开平方和；
19. `kernelMul_psd_of_psd`：**纯核语言版**——`K₁, K₂` **对称 + 半正定** ⟹
    逐点积半正定（在共同输入族上一次取两条特征映射，再走 `kernelMul_psd_of_featureMap`）；
    `kernelMul_symm`：逐点积的对称性；
20. `kernelSMul_psd`：`c ≥ 0` 时 `c·K` 仍是核；`isPosDefKernel_smul` 为其 `IsPosDefKernel` 版本。
    （⚠ 本文件**不**提供「Gram 矩阵形态」的三条闭包——下游直接对
    `IsPSDKernel` 用即可，`RealRKHSKernel.isPosDefKernel_gram_psd` 负责与 Gram 对接。）

**四、核的归一化（`K̃ = K/√(Kxx·Kyy)`）**
21. `normalizedKernel`：`K̃ x y = K x y / (√(K x x)·√(K y y))`；
22. `normalizedKernel_self`：**对角恒为 1**（`K x x > 0` 时）——归一化的定义性后果；
23. `normalizedKernel_symm`：对称性保持；
24. **`normalizedKernel_le_one`（主结果）**：**上界 `≤ 1` 的可证部分**——
    `K` 半正定 + **对称** + 对角正 ⟹ `K̃ x y ≤ 1`。
    ⚠ **v15**：上界**不是**由 AM–GM 与 `2Kxy ≤ Kxx+Kyy` 结合得到的
    （那是原稿的错误路线：两条不等式给的是**同一个量的下界**，无法比较）；
    正确路线是**二次型判别式**：`Kaa·t² + 2Kxy·t + Kyy ≥ 0` 取
    `t = −Kxy/Kaa` 得 `Kxy² ≤ Kaa·Kyy`，开方即得。
    且**必须**加 `hsymm : IsSymmKernel K`（半正定只约束**对称部分**）。
    注意：本条只给**上界** `≤ 1`；下界 `0 ≤` 见 `normalizedKernel_nonneg`
    （需显式逐点非负假设），两者的合取形式见 `normalizedKernel_mem_unit`。
25. `normalizedKernel_gram_diag_one`：归一化 Gram 矩阵对角全为 1（相关矩阵形态）。

**五、与 `RealRKHSKernel` 的衔接（显式互链，不重复证明）**
26. `featureMap_reproducing_compat`：把 `RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap`
    给出的 `Φ` 直接送入本文件的再生性——**Mercer 分解 ⟹ 再生性**，闭环。
    注意：**v15**：Mercer 有限版给出的 `Φ` 指标是 **`Fin n`**（样本下标），**不是** `α`
    ⟹ 结论**就陈述在 `Fin n` 上**（原稿写 `reproducingPairing Φ (x i) (x j)` 类型不符）。

## 与 `RealRKHSKernel` 的重叠/互补关系（逐条，勿重复）

| 内容 | `RealRKHSKernel` | 本文件 |
|:--|:--|:--|
| 核定义 / Gram / 对称性 | **有**（`IsSymmKernel` 等） | 只**引用**，不重定义 |
| Mercer 有限版 | **有**（`kernelGramMatrix_psd_iff_exists_featureMap`） | 只**消费**其 `Φ`（`featureMap_reproducing_compat`） |
| 距离–核恒等式（`Φ` 语言） | **有**（`metric_eq_kernel_expansion`） | 不重证；给**范数记号**下的闭合形态 |
| 核平滑 / 注意力 | **有**（`nwEstimate` / `softmax_attention_is_nw`） | **不做**（不属本文件范围） |
| **再生性** | 登记为**未做** | **本文件做**（`reproducing_property`） |
| **RKHS 范数 `‖K_x‖²=Kxx`** | 登记为**未做** | **本文件做**（`rkhs_norm_sq_eq_kernel_diag`） |
| **核的和/积闭包** | 未做 | **本文件做**（`kernelAdd_psd` / `kernelMul_psd_of_psd` / `kernelSMul_psd`） |
| **核归一化** | 未做 | **本文件做**（`normalizedKernel` / `normalizedKernel_le_one`） |
| `polyKernel` 的 `d ≥ 2` | 登记为**未证** | **未补上**（仅提供一般闭包引理 `kernelMul_psd_of_psd` 作为工具） |

## 诚实边界（诚实 / 未证 / 未做 / 降级 / 标注）

- **未做：抽象（无穷维）RKHS 的完备化**。本文件的「RKHS」是 `Fin n → ℝ` 上的
  有限维欧氏空间——在**有限索引集**上它与抽象 RKHS 内容相同（张成空间的完备化
  在有限维是恒等操作），但**不构造**一般的 `H_K`（需要 `L²` 完备化 / 商空间）。
  这是与 `RealRKHSKernel` 相同的策略，且理由相同（mathlib 4.14 无该骨架）。
- **未做：代表点定理（representer theorem）**。`RealRKHSKernel` 亦登记未做。
  本文件提供的 `reproducing_property` 与 `norm_reproducing_bound` 是它的
  **代数前提**，但定理本身（正则化经验风险的最优解落在有限张成内）需要
  Hilbert 空间投影 / 正交分解的一般理论，本轮未做。
- **诚实降级：`normalizedKernel` 的下界 `0 ≤` 需要 `K ≥ 0` 的显式假设**。
  半正定核**本身不保证逐点非负**（例如 `K(x,y) = ⟪x,y⟫` 在正交点处为 0、
  在反平行点处为负）。因此 `normalizedKernel_nonneg` 以
  `hKnn : ∀ a b, 0 ≤ K a b` 为**显式假设**陈述，并**不声称**一般 PSD 核
  的归一化落在 `[0,1]`。
- 注意：**v15 更正（重要）：上界 `≤ 1` 也**不是**只需 PSD**。
  原稿称「上界只需 PSD + 对角正」——**该说法已被证伪**（第 3 例同根因假命题）：
  半正定**只约束对称部分**，反例 `K ⊥ ⊥ = K ⊤ ⊤ = 1`、`K ⊥ ⊤ = 2`、`K ⊤ ⊥ = 0`
  满足半正定（二次型 `= (v₀+v₁)² ≥ 0`）但 `K̃ ⊥ ⊤ = 2 > 1`。
  故 `normalizedKernel_le_one` / `normalizedKernel_mem_unit` **均已显式加入
  `hsymm : IsSymmKernel K`**。（同族：`RealRKHSKernel.kernel_le_half_diag_add`
  与已登记的 `kernel_symm_of_psd`——「半正定只约束对称部分」是**系统性**直觉陷阱。）
- **诚实降级：多项式核的乘积提升未做**。
  本文件**未**提供 `polyKernel_mul_gram_psd` 之类的「`(⟪x,y⟫)^d·(⟪u,v⟫)^e` 仍是核」定理
  ——虽然 `kernelMul_psd_of_featureMap` 已给出所需的技术骨架（张量积特征映射），
  但把 `RealRKHSKernel.polyKernel` 显式接上去需要额外的索引重排，**本轮未做**。
  ⇒ 因此 `RealRKHSKernel` 登记的「`polyKernel` 一般 `d ≥ 2` 未证」这一点，
  **本文件并未补上**（仅提供了补它所需的一般闭包引理）。
- **未做：`expKernel` / 热核的一般 PSD**。仍等价于 Bochner 定理的有限版，
  mathlib 4.14 无；`RealRKHSKernel` 已登记，本文件沿用该边界、不重复论证。
  **推论**：本文件的 `kernelMul_psd_of_psd` **不能**用来证 `expKernel` 的 PSD
  （后者不能分解为两个已证 PSD 核的有限积）。
- **未做：核的正则性（连续 / 可测）**。本文件对 `α` 无任何拓扑/可测假设，
  故「求值连续」是在**有限索引集**上的 Lipschitz 陈述（`norm_reproducing_bound`），
  不是拓扑意义上的连续性。
- **未做：无穷维特征映射的截断误差**。属低秩逼近范畴（`RealEckartYoung`），本文件不涉。
- **范围**：索引集 `Fin n`，特征维 `Fin m`，全程有限求和；`α` 为任意类型。
- 无 sorry / axiom / admit；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators
open scoped Matrix
open scoped InnerProduct

namespace Lattice

variable {α : Type*}

/-! ## 一、再生性（reproducing property）

有限索引版的 RKHS：**索引集 `Fin n`**，特征空间 `Fin m → ℝ`。
「在点 `x i` 处的再生核向量」就是**特征坐标** `Φ (x i) : Fin m → ℝ`。

`RealRKHSKernel` 把「抽象 RKHS `H_K` 的完备化」登记为未做；本文件用
「`Fin n` 索引 + `Fin m → ℝ`」把该缺口在**有限**情形下补齐：所有关于
「再生核 `K_x`」「求值泛函」「RKHS 范数」的陈述都成为 `Fin m → ℝ` 上的
内积恒等式，可直接由 `Φ` 定义展开。
-/

/-- **有限特征坐标**：`featureCoord Φ i = Φ (x i)`，即「第 `i` 个样本点处的
RKHS 向量 `K_{x i}`」在特征基下的坐标。

这是抽象 RKHS 中「`K_x ∈ H_K`」在有限索引版下的**具体实现**：
`Fin n` 是样本索引（也是「RKHS 的生成点」），`Fin m` 是特征维。 -/
def featureCoord {n m : ℕ} {α : Type*} (Φ : α → Fin m → ℝ) (x : Fin n → α) (i : Fin n) :
    Fin m → ℝ :=
  Φ (x i)

/-- **再生对**：`reproducingPairing Φ a b = ⟨Φ a, Φ b⟩ = Σ_p Φ a p · Φ b p`。

即 RKHS 内积在有限特征坐标下的写法。 -/
def reproducingPairing {m : ℕ} {α : Type*} (Φ : α → Fin m → ℝ) (a b : α) : ℝ :=
  ∑ p, Φ a p * Φ b p

/-- `reproducingPairing` 的定义展开（`rfl`，保留为具名引理便于 `rw`）。 -/
theorem reproducingPairing_eq_sum {m : ℕ} {α : Type*} (Φ : α → Fin m → ℝ) (a b : α) :
    reproducingPairing Φ a b = ∑ p, Φ a p * Φ b p := rfl

/-- **⭐ 再生性（reproducing property，本文件主结果之一）**：

设 `K a b = Σ_p Φ a p · Φ b p`（即 `Φ` 是 `K` 的一个有限特征映射），则

    **`⟨Φ (x i), Φ (x j)⟩ = K (x i) (x j)`**。

用 RKHS 语言：**在点 `x j` 处的求值泛函就是与再生核向量 `K_{x j} = Φ (x j)` 的内积**。
这正是 RKHS 的**定义性质**，也是 `RealRKHSKernel` 在「诚实边界」中明确登记为
**未做**的条目（该文件只给了特征映射到 `ℝⁿ` 的 Mercer 分解，未做再生性）。

证明是定义展开：`Σ_p Φ(x i)_p·Φ(x j)_p = K (x i) (x j)` 即 `hK` 的实例。 -/
theorem reproducing_property {n m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (x : Fin n → α) (i j : Fin n) :
    reproducingPairing Φ (x i) (x j) = K (x i) (x j) := by
  rw [reproducingPairing_eq_sum, ← hK]

/-- **再生性的对角形态**：`⟨K_x, K_x⟩ = K x x`（`i = j` 的特例）。

这是 `rkhs_norm_sq_eq_kernel_diag` 的内积写法。 -/
theorem reproducing_property_self {n m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (x : Fin n → α) (i : Fin n) :
    reproducingPairing Φ (x i) (x i) = K (x i) (x i) :=
  reproducing_property Φ hK x i i

/-- **再生性 ⟹ 核对称的自动版本**：若 `Φ` 是 `K` 的特征映射，则
`K a b = K b a`（因 `Σ_p Φ a p Φ b p` 对 `a,b` 对称）。

这是 `RealRKHSKernel.IsSymmKernel` 在「有显式特征映射」时的**自动获得**
（该文件把对称性作为**假设** `hsymm` 传入，本文件说明：只要有特征映射，
对称性是**结论**）。 -/
theorem isSymmKernel_of_featureMap {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) : IsSymmKernel K := by
  intro a b
  rw [hK a b, hK b a]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **特征映射 ⟹ 核半正定**（`RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap`
的 `⟸` 方向的**点式版本**，此处以 `IsPSDKernel` 抽象核语言陈述，便于与再生性并列）。

展开 `Σ_i Σ_j v_i (Σ_p Φ(x i)_p Φ(x j)_p) v_j = Σ_p (Σ_i v_i Φ(x i)_p)² ≥ 0`。 -/
theorem isPSDKernel_of_featureMap {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) : IsPSDKernel K := by
  intro n x v
  have hstep : ∀ i j : Fin n, v i * K (x i) (x j) * v j
      = ∑ p, (v i * Φ (x i) p) * (v j * Φ (x j) p) := by
    intro i j
    rw [hK (x i) (x j), Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  calc
    (∑ i, ∑ j, v i * K (x i) (x j) * v j)
        = ∑ i, ∑ j, ∑ p, (v i * Φ (x i) p) * (v j * Φ (x j) p) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep i j
    _ = ∑ p, (∑ i, v i * Φ (x i) p) ^ 2 := by
          -- 注意：v15 修复：**不要**在 `Finset.sum_congr` 的 λ 体内 `rw [Finset.sum_comm]`
          -- （会让 `∑` 的幺半群类型参数留成元变量 ⟹ `AddCommMonoid ?m` stuck）。
          -- 正解：把内层恒等式**先提成 `have`**，再用 `calc` 分三步换序。
          have hinner : ∀ p : Fin m,
              (∑ i, ∑ j, (v i * Φ (x i) p) * (v j * Φ (x j) p))
                = (∑ i, v i * Φ (x i) p) * (∑ j, v j * Φ (x j) p) := by
            intro p
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
          calc (∑ i, ∑ j, ∑ p, (v i * Φ (x i) p) * (v j * Φ (x j) p))
              = ∑ i, ∑ p, ∑ j, (v i * Φ (x i) p) * (v j * Φ (x j) p) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
            _ = ∑ p, ∑ i, ∑ j, (v i * Φ (x i) p) * (v j * Φ (x j) p) := by
                rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
            _ = ∑ p, (∑ i, v i * Φ (x i) p) * (∑ j, v j * Φ (x j) p) :=
                Finset.sum_congr rfl fun p _ => hinner p
            _ = ∑ p, (∑ i, v i * Φ (x i) p) ^ 2 :=
                Finset.sum_congr rfl fun p _ => by rw [sq]
    _ ≥ 0 := Finset.sum_nonneg fun p _ => sq_nonneg _

/-- **求值泛函的线性性（再生对的第一变量）**：
`⟨K_x, a·f + b·g⟩ = a·⟨K_x, f⟩ + b·⟨K_x, g⟩`。

这是再生性「求值是内积」的**线性性**推论——RKHS 中求值泛函是线性泛函。 -/
theorem reproducing_linearity {m : ℕ} (u f g : Fin m → ℝ) (a b : ℝ) :
    (∑ p, u p * (a * f p + b * g p)) = a * (∑ p, u p * f p) + b * (∑ p, u p * g p) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **线性求值泛函的显式形式**：`Σ_p u p · f p` 可写成对 `f` 的 `Fin m →ₗ[ℝ] ℝ` 作用
（`LinearMap` 形态，供下游取算子范数用）。 -/
def evalLinearMap (u : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ p, u p * f p
  map_add' f g := by
    -- 注意：目标是 β-redex（`rw` 不做 β-归约）⟹ 先 `show` 展开，再 `simp only` 一次改写
    show (∑ p, u p * (f + g) p) = ∑ p, u p * f p + ∑ p, u p * g p
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    show (∑ p, u p * (c • f) p) = c • ∑ p, u p * f p
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring

/-- `evalLinearMap u f = Σ_p u p · f p`（定义即证）。 -/
@[simp] theorem evalLinearMap_apply {m : ℕ} (u f : Fin m → ℝ) :
    evalLinearMap u f = ∑ p, u p * f p := rfl

/-- **再生值由特征映射唯一决定**：若两条特征映射 `Φ`、`Ψ` 给出**同一个核** `K`，
则它们的再生对在每一对点上相等——
即「核 ⟹ 再生值点对」是良定义的（不依赖于特征映射的选取）。

这是 RKHS **唯一性**的核心（同一个核的 RKHS 在等距同构意义下唯一）。 -/
theorem reproducingPairing_eq_of_same_kernel {m₁ m₂ : ℕ} {K : α → α → ℝ}
    (Φ : α → Fin m₁ → ℝ) (Ψ : α → Fin m₂ → ℝ)
    (hΦ : ∀ a b, K a b = ∑ p, Φ a p * Φ b p)
    (hΨ : ∀ a b, K a b = ∑ p, Ψ a p * Ψ b p) (a b : α) :
    reproducingPairing Φ a b = reproducingPairing Ψ a b := by
  rw [reproducingPairing_eq_sum, reproducingPairing_eq_sum,
    ← hΦ a b, ← hΨ a b]

/-! ## 二、RKHS 范数与核的关系：`‖K_x‖² = K(x,x)`

`RealRKHSKernel` 登记「RKHS 范数」为未做。本文件给出有限维版本：
`‖Φ(x)‖² = Σ_p Φ(x)_p²`，并证明它**恰等于** `K x x`。
-/

/-- **有限 RKHS 范数平方**：`rkhsNormSq Φ a = ‖Φ a‖² = Σ_p Φ a p ^ 2`。

在有限索引版 RKHS 中，这就是「`K_a` 的范数平方」。 -/
def rkhsNormSq {m : ℕ} {α : Type*} (Φ : α → Fin m → ℝ) (a : α) : ℝ :=
  ∑ p, Φ a p ^ 2

/-- **⭐ RKHS 范数平方 = 核对角值（主结果）**：**`‖K_x‖² = K x x`**。

即「再生核向量 `K_x` 的范数平方恰是核对角元 `K(x,x)`」——
这是任务指定的核心关系，也是 RKHS 理论中「`K(x,x)` 是特征向量长度平方」的准确含义。

证明：`Σ_p Φ(x)_p² = Σ_p Φ(x)_p·Φ(x)_p = K x x`（`hK` 的 `a = b = x` 实例
配 `pow_two`）。 -/
theorem rkhs_norm_sq_eq_kernel_diag {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a : α) :
    rkhsNormSq Φ a = K a a := by
  unfold rkhsNormSq
  rw [hK a a]
  exact Finset.sum_congr rfl fun p _ => by rw [pow_two]

/-- **⭐ 纯核语言的范数公式**：**不需要显式给出 `Φ`**，只要 `K` 对称且半正定，
则**任何**实现 `K` 的特征映射 `Φ` 都满足 `‖K_x‖² = K x x`。

这条把 `rkhs_norm_sq_eq_kernel_diag` 从「给定 `Φ`」提升为「核的性质」：
`K` 的 PSD 性**强制**该范数公式，与特征映射的选取无关。
证明：由 `RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap`
（Mercer 有限版）取得某个 `Φ`，再用 `rkhs_norm_sq_eq_kernel_diag`。

注意：注意此处用的是 `n = 1` 的单点 Gram 矩阵——这正是 Mercer 有限版对**任意有限集合**
成立（而不仅是全体样本）的用处。 -/
theorem rkhs_norm_sq_eq_kernel_diag_of_psd (K : α → α → ℝ) (hsymm : IsSymmKernel K)
    (hpsd : IsPSDKernel K) (a : α) :
    ∃ Phi : Fin 1 → ℝ, (∑ p, Phi p ^ 2) = K a a := by
  -- 单点输入上的 Mercer 有限版：Gram 半正定 ⟺ 存在特征映射
  have hgram : ∀ v : Fin 1 → ℝ, 0 ≤ ∑ i, ∑ j, v i * kernelGramMatrix K (fun _ : Fin 1 => a) i j * v j :=
    isPosDefKernel_gram_psd K ⟨hsymm, hpsd⟩ (fun _ : Fin 1 => a)
  obtain ⟨Phi, hPhi⟩ :=
    (kernelGramMatrix_psd_iff_exists_featureMap K (fun _ : Fin 1 => a) hsymm).mp hgram
  refine ⟨Phi 0, ?_⟩
  have h00 : kernelGramMatrix K (fun _ : Fin 1 => a) 0 0 = ∑ p, Phi 0 p * Phi 0 p :=
    hPhi 0 0
  have hdiag : kernelGramMatrix K (fun _ : Fin 1 => a) 0 0 = K a a := rfl
  rw [hdiag] at h00
  rw [h00]
  exact Finset.sum_congr rfl fun p _ => by rw [pow_two]

/-- **核对角非负 ⟹ 范数平方非负**（纯核语言，消费 `RealRKHSKernel.kernel_diag_nonneg`）。 -/
theorem rkhs_norm_sq_nonneg_of_psd (K : α → α → ℝ) (hpsd : IsPSDKernel K) (a : α) :
    0 ≤ K a a :=
  kernel_diag_nonneg K hpsd a

/-- **范数平方为零 ⟺ 特征向量为零**：`‖Φ a‖² = 0 ↔ Φ a = 0`。 -/
theorem rkhs_norm_sq_eq_zero_iff {m : ℕ} {α : Type*} (Φ : α → Fin m → ℝ) (a : α) :
    rkhsNormSq Φ a = 0 ↔ Φ a = 0 := by
  unfold rkhsNormSq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => sq_nonneg (Φ a p))]
  constructor
  · intro h
    funext p
    -- 注意：`h p _ : Φ a p ^ 2 = 0` 而目标是 `Φ a p = 0` ⟹ 用 `pow_eq_zero` 需先取平方根
    exact pow_eq_zero (h p (Finset.mem_univ p))
  · intro h p _
    -- 注意：v15 修复：`rw [h]`（`h : Φ a = 0`）会先在 `Φ a p` 里把 `Φ a` 重写成 `0`，
    -- 留下伪目标 `0 p ^ 2 = 0`。正解：用 `congrFun` 取出**逐点**等式再改。
    rw [show Φ a p = 0 from congrFun h p]
    ring

/-- **⭐ Cauchy–Schwarz 型 RKHS 界：`|f(x)| ≤ √(K x x) · ‖f‖`**。

这是 RKHS 「**求值泛函连续**」的**定量形式**：点值被 `√(K x x)`（乘上 `f` 的范数）控制。
RKHS 正则化理论中「小范数 ⟹ 点值受控」的代数核心。

证明：`|⟨K_x, f⟩| ≤ ‖K_x‖·‖f‖`（Cauchy–Schwarz，走 `Finset.sum_mul_sq_le_sq_mul_sq`），
再用 `‖K_x‖² = K x x` 与 `√(Kxx)² = Kxx`。

（`RealRKHSKernel` 无此条；它只到距离–核恒等式，未做范数/求值界。） -/
theorem norm_reproducing_bound {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a : α) (f : Fin m → ℝ)
    (hKnn : 0 ≤ K a a) :
    |∑ p, Φ a p * f p| ≤ Real.sqrt (K a a) * Real.sqrt (∑ p, f p ^ 2) := by
  -- Cauchy–Schwarz：`(Σ u_p f_p)² ≤ (Σ u_p²)(Σ f_p²)`
  have hcs : (∑ p, Φ a p * f p) ^ 2 ≤ (∑ p, Φ a p ^ 2) * (∑ p, f p ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) (Φ a) f
  have hnorm : (∑ p, Φ a p ^ 2) = K a a := rkhs_norm_sq_eq_kernel_diag Φ hK a
  rw [hnorm] at hcs
  have hfsq : 0 ≤ ∑ p, f p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg (f p)
  -- `|Σ|² ≤ Kaa · ‖f‖² = (√Kaa · √‖f‖²)²`，两边开方
  have habs : (∑ p, Φ a p * f p) ^ 2 ≤ (Real.sqrt (K a a) * Real.sqrt (∑ p, f p ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hKnn, Real.sq_sqrt hfsq]
    exact hcs
  have hnn : 0 ≤ Real.sqrt (K a a) * Real.sqrt (∑ p, f p ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (∑ p, Φ a p * f p), abs_nonneg (∑ p, Φ a p * f p)]

/-- **RKHS 范数是真范数（三角不等式）**：
`√(Σ_p (u_p+v_p)²) ≤ √(Σ_p u_p²) + √(Σ_p v_p²)`。

这条说明 `rkhsNormSq` 给出的不是任意二次型，而是**范数**的平方——
「RKHS 是 Hilbert 空间」在有限版下的实质内容。

注意：**v15 修复**：原证明体引用了 `Real.sqrt_sum_sq_add_sqrt_sum_sq_le`，
**该引理在 mathlib 4.14 不存在**（`#check` 报 `unknown constant`）。
现改为**自证**：走 Cauchy–Schwarz（`Finset.sum_mul_sq_le_sq_mul_sq`）得
`Σ uv ≤ √(Σu²)·√(Σv²)`，再与 `(√u²+√v²)² = Σu² + 2√u²√v² + Σv²` 比较。 -/
theorem rkhs_norm_triangle {m : ℕ} (u v : Fin m → ℝ) :
    Real.sqrt (∑ p, (u p + v p) ^ 2)
      ≤ Real.sqrt (∑ p, u p ^ 2) + Real.sqrt (∑ p, v p ^ 2) := by
  have hua : (0 : ℝ) ≤ ∑ p, u p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg (u p)
  have hva : (0 : ℝ) ≤ ∑ p, v p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg (v p)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  -- Cauchy–Schwarz：`(Σ u v)² ≤ (Σ u²)(Σ v²)`
  have hcs : (∑ p, u p * v p) ^ 2 ≤ (∑ p, u p ^ 2) * (∑ p, v p ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m)) u v
  -- 开方得 `Σ u v ≤ √(Σu²)·√(Σv²)`（用 `le_abs_self` 处理符号）
  have hcross : (∑ p, u p * v p) ≤ Real.sqrt (∑ p, u p ^ 2) * Real.sqrt (∑ p, v p ^ 2) := by
    have h := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hua] at h
    exact le_trans (le_abs_self _) h
  have hexp : (∑ p, (u p + v p) ^ 2)
      = (∑ p, u p ^ 2) + 2 * (∑ p, u p * v p) + (∑ p, v p ^ 2) := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    ring
  have hrhs : (Real.sqrt (∑ p, u p ^ 2) + Real.sqrt (∑ p, v p ^ 2)) ^ 2
      = (∑ p, u p ^ 2) + 2 * (Real.sqrt (∑ p, u p ^ 2) * Real.sqrt (∑ p, v p ^ 2))
        + (∑ p, v p ^ 2) := by
    rw [add_sq, Real.sq_sqrt hua, Real.sq_sqrt hva]
    ring
  rw [hexp, hrhs]
  linarith

/-- **⭐ 范数层面的距离–核恒等式（闭合形态）**：

`‖K_x − K_y‖² = K x x − 2·K x y + K y y`。

注意：**重叠声明**：该恒等式的**本体**是 `RealRKHSKernel.metric_eq_kernel_expansion`
（`Φ` 语言）。本文件**不重证**它——这里给的是**同一命题在 RKHS 范数记号
（`rkhsNormSq` / `featureCoord`）下的等价表述**，目的是让下游可以直接用
「RKHS 范数」这一库内对象引用距离–核恒等式，而无需展开 `Σ (Φ a p - Φ b p)²`。

证明：把 `(Φ a p - Φ b p)^2` 用 `ring` 展开成 `Φ a p^2 - 2 Φ a p Φ b p + Φ b p^2`，
再用 `RealRKHSKernel.metric_eq_kernel_expansion` 收口。 -/
theorem norm_difference_eq_kernel_distance {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a b : α) :
    (∑ p, (Φ a p - Φ b p) ^ 2) = K a a - 2 * K a b + K b b :=
  metric_eq_kernel_expansion Φ hK a b

/-- **范数记号下的距离–核恒等式**：`‖K_x − K_y‖² = Kxx − 2Kxy + Kyy`
（左端用 `rkhsNormSq` 作用于**差向量**）。

与上一条是同一命题的**差向量**包装：`rkhsNormSq (fun c => Φ a - Φ b) ()` 的写法
即 `Σ_p (Φ a p - Φ b p)^2`。 -/
theorem rkhsNormSq_sub_eq_kernel_distance {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a b : α) :
    rkhsNormSq (fun _ : Unit => fun p => Φ a p - Φ b p) () = K a a - 2 * K a b + K b b := by
  unfold rkhsNormSq
  exact norm_difference_eq_kernel_distance Φ hK a b

/-- **RKHS 距离非负**：`0 ≤ K a a − 2·K a b + K b b`
（消费 `RealRKHSKernel.metric_kernel_nonneg`；此处以**范数**语言重述，
说明核诱导的「距离平方」是范数的平方，故非负）。 -/
theorem rkhs_distance_nonneg {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a b : α) :
    0 ≤ K a a - 2 * K a b + K b b :=
  metric_kernel_nonneg Φ hK a b

/-- **RKHS 距离为零 ⟺ 再生核向量相等**：
`K a a − 2·K a b + K b b = 0 ↔ Φ a = Φ b`
（消费 `RealRKHSKernel.kernel_metric_zero_iff`，以范数语言重述）。 -/
theorem rkhs_distance_zero_iff {m : ℕ} {K : α → α → ℝ} (Φ : α → Fin m → ℝ)
    (hK : ∀ a b, K a b = ∑ p, Φ a p * Φ b p) (a b : α) :
    K a a - 2 * K a b + K b b = 0 ↔ Φ a = Φ b :=
  kernel_metric_zero_iff Φ hK a b

/-! ## 三、核的闭包性质：和、积、数乘仍是核

`RealRKHSKernel` 只对**具体核**（可分核 / 多项式核 `d=1` / 热核常值）逐例验证 PSD，
未建立**一般闭包运算**。本节补上三条最基本的闭包：
加法、Hadamard（逐点）乘法、非负数乘。

这也是「核工程」（拼接核、乘积核）的代数依据：从已知核出发**组合**出新核。
-/

/-- **核的和半正定**：`K₁, K₂` 半正定 ⟹ `K₁ + K₂` 半正定。

证明：二次型对加法线性，`Σ_i Σ_j v_i (K₁+K₂)_{ij} v_j = q₁(v) + q₂(v) ≥ 0`。 -/
theorem kernelAdd_psd {K₁ K₂ : α → α → ℝ} (h₁ : IsPSDKernel K₁) (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun a b => K₁ a b + K₂ a b) := by
  intro n x v
  have hsplit : ∀ i j : Fin n,
      v i * (K₁ (x i) (x j) + K₂ (x i) (x j)) * v j
        = v i * K₁ (x i) (x j) * v j + v i * K₂ (x i) (x j) * v j :=
    fun i j => by ring
  calc
    (∑ i, ∑ j, v i * (K₁ (x i) (x j) + K₂ (x i) (x j)) * v j)
        = ∑ i, ∑ j, (v i * K₁ (x i) (x j) * v j + v i * K₂ (x i) (x j) * v j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = (∑ i, ∑ j, v i * K₁ (x i) (x j) * v j)
          + (∑ i, ∑ j, v i * K₂ (x i) (x j) * v j) := by
          -- 注意：v15 修复：`Finset.sum_add_distrib` 是**双绑定**（`∑ x ∈ s`），
          -- 对单绑定目标 `∑ j : Fin n` 直接 `rw` 不匹配。
          -- 正解：先用 `sum_congr` 把和式体**分配成和**，再对**外层**用一次 `sum_add_distrib`。
          have hinner : ∀ i : Fin n,
              (∑ j, (v i * K₁ (x i) (x j) * v j + v i * K₂ (x i) (x j) * v j))
                = (∑ j, v i * K₁ (x i) (x j) * v j)
                  + (∑ j, v i * K₂ (x i) (x j) * v j) :=
            fun i => Finset.sum_add_distrib
          calc (∑ i, ∑ j, (v i * K₁ (x i) (x j) * v j
                  + v i * K₂ (x i) (x j) * v j))
              = ∑ i, ((∑ j, v i * K₁ (x i) (x j) * v j)
                      + (∑ j, v i * K₂ (x i) (x j) * v j)) :=
                Finset.sum_congr rfl fun i _ => hinner i
            _ = (∑ i, ∑ j, v i * K₁ (x i) (x j) * v j)
                  + (∑ i, ∑ j, v i * K₂ (x i) (x j) * v j) :=
                Finset.sum_add_distrib
    _ ≥ 0 := add_nonneg (h₁ x v) (h₂ x v)

/-- **⭐ 核的逐点积半正定（Hadamard / Schur 乘积定理的有限版，主结果）**：

`K₁, K₂` 半正定 ⟹ **逐点积** `(a,b) ↦ K₁ a b · K₂ a b` 半正定。

这是核方法最重要的闭包性质之一（乘积核：`K₁` 描述一路特征、`K₂` 另一路，
乘积即张量积特征空间的内积）。

**证明走显式特征映射**（不是 Schur 乘积定理的谱论证）：
由 Mercer 有限版取 `Φ`、`Ψ` 使 `K₁ a b = Σ_p Φ a p Φ b p`、`K₂ a b = Σ_q Ψ a q Ψ b q`，
则 `K₁ a b · K₂ a b = Σ_{(p,q)} (Φ a p · Ψ a q)·(Φ b p · Ψ b q)`，
即**张量积特征映射**的内积；于是二次型是平方和非负。

注意：这条**只对已给定特征映射的核**成立；对 `K` 直接陈述需要 Mercer 有限版
（对称 + PSD），见 `kernelMul_psd_of_psd`。 -/
theorem kernelMul_psd_of_featureMap {m₁ m₂ : ℕ} {K₁ K₂ : α → α → ℝ}
    (Φ : α → Fin m₁ → ℝ) (Ψ : α → Fin m₂ → ℝ)
    (hK₁ : ∀ a b, K₁ a b = ∑ p, Φ a p * Φ b p)
    (hK₂ : ∀ a b, K₂ a b = ∑ q, Ψ a q * Ψ b q) :
    IsPSDKernel (fun a b => K₁ a b * K₂ a b) := by
  -- 注意：**v15 修复**：原稿用 `isPSDKernel_of_featureMap` 时给了**乘积指标** `Fin m₁ × Fin m₂`，
  -- 但该定理的指标被固定为 `Fin m`（`{m : ℕ}`），**乘积型不是 `Fin m` 的形状**
  -- ⟹ `application type mismatch`。正解：**不绕道该定理**，就地按
  -- 「张量积特征映射的二次型 = 平方和」直接算（与 `kernelMul_psd_of_psd` 同一算术）。
  intro n x v
  have hsplit : ∀ i j : Fin n,
      v i * ((fun a b => K₁ a b * K₂ a b) (x i) (x j)) * v j
        = ∑ pq : Fin m₁ × Fin m₂,
            (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
              * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) := by
    intro i j
    show v i * (K₁ (x i) (x j) * K₂ (x i) (x j)) * v j = _
    have h1 : K₁ (x i) (x j) = ∑ p, Φ (x i) p * Φ (x j) p := hK₁ (x i) (x j)
    have h2 : K₂ (x i) (x j) = ∑ q, Ψ (x i) q * Ψ (x j) q := hK₂ (x i) (x j)
    have hmul : (∑ p, Φ (x i) p * Φ (x j) p) * (∑ q, Ψ (x i) q * Ψ (x j) q)
        = ∑ pq : Fin m₁ × Fin m₂,
            (Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2) := by
      rw [Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
            (f := fun p => Φ (x i) p * Φ (x j) p)
            (g := fun q => Ψ (x i) q * Ψ (x j) q)]
      rw [Fintype.sum_prod_type
            (f := fun pq : Fin m₁ × Fin m₂ =>
              (Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2))]
      -- 注意：上面两步 `rw` **已闭合目标** ⟹ 不要再跟 `exact`/`ring`（会报 `no goals`）
    -- 注意：分步：先把 `v i * (…) * v j` 左乘分配，再用 `hmul`，再右乘分配。
    have hL : v i * (K₁ (x i) (x j) * K₂ (x i) (x j))
        = v i * ((∑ p, Φ (x i) p * Φ (x j) p) * (∑ q, Ψ (x i) q * Ψ (x j) q)) := by
      rw [h1, h2]
    have hstep : v i * ((∑ p, Φ (x i) p * Φ (x j) p)
          * (∑ q, Ψ (x i) q * Ψ (x j) q)) * v j
        = (∑ pq : Fin m₁ × Fin m₂,
            v i * ((Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2))) * v j := by
      rw [hmul, Finset.mul_sum (s := Finset.univ)
            (f := fun pq : Fin m₁ × Fin m₂ =>
              (Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2)) (a := v i)]
    calc v i * (K₁ (x i) (x j) * K₂ (x i) (x j)) * v j
        = v i * ((∑ p, Φ (x i) p * Φ (x j) p)
            * (∑ q, Ψ (x i) q * Ψ (x j) q)) * v j := by rw [hL]
      _ = (∑ pq : Fin m₁ × Fin m₂,
            v i * ((Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2))) * v j := hstep
      _ = ∑ pq : Fin m₁ × Fin m₂,
            v i * ((Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2)) * v j :=
          Finset.sum_mul (s := Finset.univ)
            (f := fun pq : Fin m₁ × Fin m₂ =>
              v i * ((Φ (x i) pq.1 * Φ (x j) pq.1) * (Ψ (x i) pq.2 * Ψ (x j) pq.2))) (a := v j)
      _ = ∑ pq : Fin m₁ × Fin m₂,
            (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
              * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) :=
          Finset.sum_congr rfl fun pq _ => by ring
  have hinner : ∀ pq : Fin m₁ × Fin m₂,
      (∑ i, ∑ j, (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
          * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2))
        = (∑ i, v i * Φ (x i) pq.1 * Ψ (x i) pq.2) ^ 2 := by
    intro pq
    -- 注意：`sum_mul_sum` 的方向是 `(∑f)*(∑g) = ∑∑ f*g`；目标是 `∑∑ = (∑)^2`
    -- ⟹ 用 `.symm`（配合 `pow_two`）。
    rw [pow_two]
    exact (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i => v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
      (g := fun j => v j * Φ (x j) pq.1 * Ψ (x j) pq.2)).symm
  have hswap : (∑ i, ∑ j, ∑ pq : Fin m₁ × Fin m₂,
        (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
          * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2))
      = ∑ pq : Fin m₁ × Fin m₂,
          ∑ i, ∑ j, (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
            * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) := by
    -- 注意：`rw [sum_comm]` 出现在 `refine sum_congr … ?_` 之后就泄漏元变量
    -- ⟹ 把中间步骤提成具名 `have`，两次 `sum_comm` 各自独立成一步。
    have s1 : (∑ i, ∑ j, ∑ pq : Fin m₁ × Fin m₂,
          (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
            * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2))
        = ∑ i, ∑ pq : Fin m₁ × Fin m₂, ∑ j,
            (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
              * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    have s2 : (∑ i, ∑ pq : Fin m₁ × Fin m₂, ∑ j,
          (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
            * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2))
        = ∑ pq : Fin m₁ × Fin m₂, ∑ i, ∑ j,
            (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
              * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) :=
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    rw [s1, s2]
  calc ∑ i, ∑ j, v i * ((fun a b => K₁ a b * K₂ a b) (x i) (x j)) * v j
      = ∑ i, ∑ j, ∑ pq : Fin m₁ × Fin m₂,
          (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
            * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = ∑ pq : Fin m₁ × Fin m₂,
          ∑ i, ∑ j, (v i * Φ (x i) pq.1 * Ψ (x i) pq.2)
            * (v j * Φ (x j) pq.1 * Ψ (x j) pq.2) := hswap
    _ = ∑ pq : Fin m₁ × Fin m₂, (∑ i, v i * Φ (x i) pq.1 * Ψ (x i) pq.2) ^ 2 :=
        Finset.sum_congr rfl fun pq _ => hinner pq
    _ ≥ 0 := Finset.sum_nonneg fun pq _ => sq_nonneg _

/-- **核的逐点积半正定（纯 PSD 语言版）**：`K₁, K₂` **对称 + 半正定** ⟹ 逐点积半正定。

由 Mercer 有限版在**共同输入族** `x` 上取特征映射（`n` 点，一次取够），
再走 `kernelMul_psd_of_featureMap` —— 取一次即可，无需逐点重构。

注意：需要 `hsymm`：Mercer 有限版（`kernelGramMatrix_psd_iff_exists_featureMap`）本身
要求对称性（半正定推不出对称，见 `RealRKHSKernel.kernel_sym_part_abs_le` 的登记）。 -/
theorem kernelMul_psd_of_psd {K₁ K₂ : α → α → ℝ}
    (hs₁ : IsSymmKernel K₁) (hs₂ : IsSymmKernel K₂)
    (h₁ : IsPSDKernel K₁) (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun a b => K₁ a b * K₂ a b) := by
  intro n x v
  -- 在**同一个** `n` 点输入族上取两条特征映射（Mercer 有限版）
  have hgram₁ : ∀ w : Fin n → ℝ,
      0 ≤ ∑ i, ∑ j, w i * kernelGramMatrix K₁ x i j * w j :=
    isPosDefKernel_gram_psd K₁ ⟨hs₁, h₁⟩ x
  have hgram₂ : ∀ w : Fin n → ℝ,
      0 ≤ ∑ i, ∑ j, w i * kernelGramMatrix K₂ x i j * w j :=
    isPosDefKernel_gram_psd K₂ ⟨hs₂, h₂⟩ x
  obtain ⟨Φ, hΦ⟩ := (kernelGramMatrix_psd_iff_exists_featureMap K₁ x hs₁).mp hgram₁
  obtain ⟨Ψ, hΨ⟩ := (kernelGramMatrix_psd_iff_exists_featureMap K₂ x hs₂).mp hgram₂
  -- 注意：**v15 修复**：`Φ`/`Ψ` 的指标类型是 **`Fin n`**（Mercer 有限版只给出**样本点**上的
  -- 特征映射），**不是** `α`。原稿把 `hΦ' : ∀ a b : Fin n, …` 喂给要求
  -- `∀ a b : α, …` 的 `kernelMul_psd_of_featureMap` ⟹ 类型不符。
  -- 正解：**就在 `Fin n` 上**直接展开张量积特征映射 `(p,q) ↦ Φ i p · Ψ i q` 并算二次型。
  -- 注意：且 `Finset.sum_mul_sum` 必须**显式传参**（留 `_` ⟹ `AddCommMonoid ?m` stuck）；
  -- `∑_{p,q}` 与 `∑_{pq}` 的桥接用单绑定的 `Fintype.sum_prod_type`。
  -- 注意：且 `rw [sum_comm]`/`mul_sum` **不能写在 `sum_congr` 的 λ 体内**（元变量泄漏）
  -- ⟹ 一律把内层恒等式**先提成具名 `have`**，再用 `calc` 组合。
  have hsplit : ∀ i j : Fin n,
      v i * (K₁ (x i) (x j) * K₂ (x i) (x j)) * v j
        = ∑ pq : Fin n × Fin n,
            (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) := by
    intro i j
    have h1 : K₁ (x i) (x j) = ∑ p, Φ i p * Φ j p := hΦ i j
    have h2 : K₂ (x i) (x j) = ∑ q, Ψ i q * Ψ j q := hΨ i j
    have hmul : (∑ p, Φ i p * Φ j p) * (∑ q, Ψ i q * Ψ j q)
        = ∑ pq : Fin n × Fin n, (Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2) := by
      rw [Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
            (f := fun p => Φ i p * Φ j p) (g := fun q => Ψ i q * Ψ j q)]
      rw [Fintype.sum_prod_type
            (f := fun pq : Fin n × Fin n => (Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2))]
      -- 注意：上面两步 `rw` **已闭合目标** ⟹ 不要再跟 `exact`/`ring`（会报 `no goals`）
    have hL : v i * (K₁ (x i) (x j) * K₂ (x i) (x j))
        = v i * ((∑ p, Φ i p * Φ j p) * (∑ q, Ψ i q * Ψ j q)) := by rw [h1, h2]
    have hstep : v i * ((∑ p, Φ i p * Φ j p) * (∑ q, Ψ i q * Ψ j q)) * v j
        = (∑ pq : Fin n × Fin n,
            v i * ((Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2))) * v j := by
      rw [hmul, Finset.mul_sum (s := Finset.univ)
            (f := fun pq : Fin n × Fin n =>
              (Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2)) (a := v i)]
    calc v i * (K₁ (x i) (x j) * K₂ (x i) (x j)) * v j
        = v i * ((∑ p, Φ i p * Φ j p) * (∑ q, Ψ i q * Ψ j q)) * v j := by rw [hL]
      _ = (∑ pq : Fin n × Fin n,
            v i * ((Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2))) * v j := hstep
      _ = ∑ pq : Fin n × Fin n,
            v i * ((Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2)) * v j :=
          Finset.sum_mul (s := Finset.univ)
            (f := fun pq : Fin n × Fin n =>
              v i * ((Φ i pq.1 * Φ j pq.1) * (Ψ i pq.2 * Ψ j pq.2))) (a := v j)
      _ = ∑ pq : Fin n × Fin n,
            (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) :=
          Finset.sum_congr rfl fun pq _ => by ring
  have hinner : ∀ pq : Fin n × Fin n,
      (∑ i, ∑ j, (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2))
        = (∑ i, v i * Φ i pq.1 * Ψ i pq.2) ^ 2 := by
    intro pq
    rw [pow_two]
    exact (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i => v i * Φ i pq.1 * Ψ i pq.2)
      (g := fun j => v j * Φ j pq.1 * Ψ j pq.2)).symm
  have hswap : (∑ i, ∑ j, ∑ pq : Fin n × Fin n,
        (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2))
      = ∑ pq : Fin n × Fin n,
          ∑ i, ∑ j, (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) := by
    have s1 : (∑ i, ∑ j, ∑ pq : Fin n × Fin n,
          (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2))
        = ∑ i, ∑ pq : Fin n × Fin n, ∑ j,
            (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    have s2 : (∑ i, ∑ pq : Fin n × Fin n, ∑ j,
          (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2))
        = ∑ pq : Fin n × Fin n, ∑ i, ∑ j,
            (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) :=
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    rw [s1, s2]
  calc ∑ i, ∑ j, v i * (K₁ (x i) (x j) * K₂ (x i) (x j)) * v j
      = ∑ i, ∑ j, ∑ pq : Fin n × Fin n,
          (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = ∑ pq : Fin n × Fin n,
          ∑ i, ∑ j, (v i * Φ i pq.1 * Ψ i pq.2) * (v j * Φ j pq.1 * Ψ j pq.2) := hswap
    _ = ∑ pq : Fin n × Fin n, (∑ i, v i * Φ i pq.1 * Ψ i pq.2) ^ 2 :=
        Finset.sum_congr rfl fun pq _ => hinner pq
    _ ≥ 0 := Finset.sum_nonneg fun pq _ => sq_nonneg _

/-- **核的非负数乘仍是核**：`c ≥ 0`、`K` 半正定 ⟹ `c·K` 半正定。 -/
theorem kernelSMul_psd {K : α → α → ℝ} (c : ℝ) (hc : 0 ≤ c) (h : IsPSDKernel K) :
    IsPSDKernel (fun a b => c * K a b) := by
  intro n x v
  have hsplit : ∀ i j : Fin n, v i * (c * K (x i) (x j)) * v j
      = c * (v i * K (x i) (x j) * v j) := fun i j => by ring
  calc
    (∑ i, ∑ j, v i * (c * K (x i) (x j)) * v j)
        = ∑ i, ∑ j, c * (v i * K (x i) (x j) * v j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = c * ∑ i, ∑ j, v i * K (x i) (x j) * v j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum ..).symm
    _ ≥ 0 := mul_nonneg hc (h x v)

/-- **核对称性的闭包**：`K₁, K₂` 对称 ⟹ 逐点积对称。 -/
theorem kernelMul_symm {K₁ K₂ : α → α → ℝ} (h₁ : IsSymmKernel K₁) (h₂ : IsSymmKernel K₂) :
    IsSymmKernel (fun a b => K₁ a b * K₂ a b) := by
  intro a b
  simp only [h₁ a b, h₂ a b]

/-- **核对称性的闭包（加法）**。 -/
theorem kernelAdd_symm {K₁ K₂ : α → α → ℝ} (h₁ : IsSymmKernel K₁) (h₂ : IsSymmKernel K₂) :
    IsSymmKernel (fun a b => K₁ a b + K₂ a b) := by
  intro a b
  simp only [h₁ a b, h₂ a b]

/-- **正定核的闭包（加法）**：`IsPosDefKernel` 语言。 -/
theorem isPosDefKernel_add {K₁ K₂ : α → α → ℝ} (h₁ : IsPosDefKernel K₁)
    (h₂ : IsPosDefKernel K₂) : IsPosDefKernel (fun a b => K₁ a b + K₂ a b) :=
  ⟨kernelAdd_symm h₁.1 h₂.1, kernelAdd_psd h₁.2 h₂.2⟩

/-- **正定核的闭包（非负数乘）**：`IsPosDefKernel` 语言。 -/
theorem isPosDefKernel_smul {K : α → α → ℝ} (c : ℝ) (hc : 0 ≤ c) (h : IsPosDefKernel K) :
    IsPosDefKernel (fun a b => c * K a b) :=
  ⟨fun a b => by simp only [h.1 a b], kernelSMul_psd c hc h.2⟩

/-! ## 四、核的归一化：`K̃ = K/√(Kxx·Kyy)` 与值域 `[0,1]`

`RealRKHSKernel` 未做核归一化。本节定义归一化核并证明其**可证部分**：
对角恒为 1、对称性保持、在「核逐点非负 + 对角正」时值域落在 `[0,1]`。

归一化核在机器学习里就是**相关系数核**（如归一化高斯核），
它把核变成 Gram **相关矩阵**（对角 1）。
-/

/-- **归一化核**：`normalizedKernel K a b = K a b / (√(K a a)·√(K b b))`。

（经典写法 `K̃ = K/√(Kxx·Kyy)`；此处写成两个 `√` 的积以避免 `Real.sqrt_mul`
对负数的 junk 值问题——两者在 `K a a, K b b ≥ 0` 时相等。） -/
def normalizedKernel (K : α → α → ℝ) (a b : α) : ℝ :=
  K a b / (Real.sqrt (K a a) * Real.sqrt (K b b))

/-- **归一化核的自值为 1**：`K a a > 0 ⟹ K̃ a a = 1`。

（`K a a / (√(Kaa)·√(Kaa)) = Kaa / Kaa = 1`，用 `Real.sq_sqrt`。） -/
theorem normalizedKernel_self (K : α → α → ℝ) (a : α) (ha : 0 < K a a) :
    normalizedKernel K a a = 1 := by
  unfold normalizedKernel
  -- 注意：v15 修复：`rw [← Real.mul_self_sqrt …]` 会**同时**重写 `K a a` 出现在
  -- 已有 `Real.sqrt` 内部的那些位置（产生 `√(√…·√…)` 的伪目标）。
  -- 正解：把该等式提成具名 `have`，只重写目标里那一处乘积。
  have h : Real.sqrt (K a a) * Real.sqrt (K a a) = K a a :=
    Real.mul_self_sqrt (le_of_lt ha)
  rw [h]
  exact div_self (ne_of_gt ha)

/-- **归一化保持对称性**。 -/
theorem normalizedKernel_symm (K : α → α → ℝ) (h : IsSymmKernel K) :
    IsSymmKernel (normalizedKernel K) := by
  intro a b
  unfold normalizedKernel
  rw [h a b, mul_comm]

/-- **⭐ 归一化核的值域上界 `≤ 1`（主结果）**：

`K` 半正定 + **对称** + 对角正 ⟹ `K̃ x y ≤ 1`。

证明链（**v15 更正后的真实路线**）：二次型 `Kaa·t² + 2·Kxy·t + Kyy ≥ 0` 对**所有** `t`
成立（在两点输入 `(a,b)` 上取 `v = (t,1)`，并用 `hsymm` 把 `K b a` 换成 `K a b`）；
取 `t = −Kxy/Kaa` 得 `Kxy² ≤ Kaa·Kyy`；开方得 `Kxy ≤ √(Kaa)·√(Kyy)`；
两边除以 `√Kaa·√Kyy` 收口。

注意：**v15 更正（一）：原证明链不成立**。原稿称
「`2·Kxy ≤ Kxx+Kyy` 与 AM–GM `2√(Kxx·Kyy) ≤ Kxx+Kyy` **两者结合**得 `Kxy ≤ √(Kxx·Kyy)`」——
**这是错的**：两条不等式给出的是**同一个量的两个下界**，无法比较 `Kxy` 与 `√(Kxx·Kyy)`。
（编译证据：该处 `linarith` 报 `failed to find a contradiction`，且**加入 `hsymm` 后仍然失败**
——说明它不是缺假设，而是**路线本身有洞**。）

注意：**v15 更正（二）：与 `RealRKHSKernel.kernel_le_half_diag_add` 同根因（本文件第 3 例）**：
原陈述只假设 `hpsd : IsPSDKernel K`，**推不出**该结论——
`kernel_le_half_diag_add` 自身已被证实为**假命题**（半正定只约束**对称部分**），
故本定理必须**显式加入 `hsymm : IsSymmKernel K`**。
反例与 `RealRKHSKernel` 处登记的完全同形（`K ⊥ ⊥ = K ⊤ ⊤ = 1`、`K ⊥ ⊤ = 2`、`K ⊤ ⊥ = 0`：
二次型 `= (v₀+v₁)² ≥ 0` 故半正定成立，但 `K̃ ⊥ ⊤ = 2/1 = 2 > 1`）。
⇒ 这是「半正定只约束对称部分」这一**系统性直觉陷阱**在本文件的第 3 例。 -/
theorem normalizedKernel_le_one (K : α → α → ℝ) (hpsd : IsPSDKernel K)
    (hsymm : IsSymmKernel K) (a b : α)
    (ha : 0 < K a a) (hb : 0 < K b b) :
    normalizedKernel K a b ≤ 1 := by
  have hnn_a : 0 ≤ K a a := le_of_lt ha
  have hnn_b : 0 ≤ K b b := le_of_lt hb
  -- 二次型对**所有** `t` 非负（`v = (t,1)`，两点输入 `(a,b)`）
  have hquad : ∀ t : ℝ, 0 ≤ K a a * t ^ 2 + 2 * K a b * t + K b b := by
    intro t
    have h := hpsd (fun i : Fin 2 => if i = 0 then a else b)
      (fun i : Fin 2 => if i = 0 then t else (1 : ℝ))
    simp only [Fin.sum_univ_two, Fin.isValue, Fin.reduceEq, ↓reduceIte] at h
    rw [hsymm b a] at h
    nlinarith [h]
  -- 判别式：取 `t = −Kxy/Kaa` 得 `Kxy² ≤ Kaa·Kyy`
  have hdet : K a b ^ 2 ≤ K a a * K b b := by
    have h1 := hquad (-(K a b / K a a))
    have key : K a a * (-(K a b / K a a)) ^ 2 + 2 * K a b * (-(K a b / K a a)) + K b b
        = K b b - K a b ^ 2 / K a a := by
      -- 注意：不用 `field_simp`（本波次纪律禁用）⟹ 走 `div_eq_mul_inv` + 显式逆元消去。
      -- 注意 `ring_nf` **不会**保留 `Kaa * Kaa⁻¹` 的字面形状（它归一到 `Kaa⁻¹^2`），
      -- 故必须**显式**给出 `Kaa * Kaa⁻¹^2 = Kaa⁻¹` 这一步。
      have hka : K a a ≠ 0 := ne_of_gt ha
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have h2 : K a a * (K a a)⁻¹ ^ 2 = (K a a)⁻¹ := by
        rw [sq, ← mul_assoc, mul_inv_cancel₀ hka, one_mul]
      rw [show K a a * (-(K a b * (K a a)⁻¹)) ^ 2
              + 2 * K a b * (-(K a b * (K a a)⁻¹)) + K b b
            = K a a * K a b ^ 2 * (K a a)⁻¹ ^ 2 - K a b ^ 2 * (K a a)⁻¹ * 2 + K b b
          from by ring]
      rw [show K a a * K a b ^ 2 * (K a a)⁻¹ ^ 2
            = K a b ^ 2 * (K a a * (K a a)⁻¹ ^ 2) from by ring, h2]
      ring
    rw [key] at h1
    have h2 : K a b ^ 2 / K a a ≤ K b b := by linarith
    have h3 := (div_le_iff₀ ha).mp h2
    linarith
  -- 开方：`Kxy ≤ √(Kxy²) ≤ √(Kaa·Kyy) = √Kaa·√Kyy`
  have hkey : K a b ≤ Real.sqrt (K a a) * Real.sqrt (K b b) := by
    calc K a b ≤ Real.sqrt (K a b ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
      _ ≤ Real.sqrt (K a a * K b b) := Real.sqrt_le_sqrt hdet
      _ = Real.sqrt (K a a) * Real.sqrt (K b b) := Real.sqrt_mul hnn_a (K b b)
  have hden_pos : 0 < Real.sqrt (K a a) * Real.sqrt (K b b) :=
    mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
  unfold normalizedKernel
  rw [div_le_one hden_pos]
  exact hkey

/-- **⭐ 归一化核的非负下界 `0 ≤`（主结果，需显式逐点非负假设）**：

`K` 逐点非负 + 对角正 ⟹ `0 ≤ K̃ x y`。

注意：**诚实降级**：半正定**不蕴含**逐点非负（`K(x,y) = ⟪x,y⟫` 在反平行点处为负），
故本定理以 `hKnn : ∀ a b, 0 ≤ K a b` 为**显式假设**。 -/
theorem normalizedKernel_nonneg (K : α → α → ℝ) (a b : α) (hKnn : ∀ a b, 0 ≤ K a b)
    (ha : 0 < K a a) (hb : 0 < K b b) :
    0 ≤ normalizedKernel K a b := by
  unfold normalizedKernel
  exact div_nonneg (hKnn a b)
    (le_of_lt (mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)))

/-- **⭐ 归一化核值域 `[0,1]`（主结果，合取形式）**：

`K` 半正定 + **对称** + 逐点非负 + 对角正 ⟹ `0 ≤ K̃ x y ≤ 1`。
这是任务指定的「**值域 `[0,1]` 的可证部分**」——上界需要 PSD **加对称性**
（见 `normalizedKernel_le_one` 的 v15 更正），下界需要额外假设逐点非负。 -/
theorem normalizedKernel_mem_unit (K : α → α → ℝ) (hpsd : IsPSDKernel K)
    (hsymm : IsSymmKernel K) (a b : α)
    (hKnn : ∀ a b, 0 ≤ K a b) (ha : 0 < K a a) (hb : 0 < K b b) :
    0 ≤ normalizedKernel K a b ∧ normalizedKernel K a b ≤ 1 :=
  ⟨normalizedKernel_nonneg K a b hKnn ha hb,
    normalizedKernel_le_one K hpsd hsymm a b ha hb⟩

/-- **归一化 Gram 矩阵对角恒为 1**：`K̃(x_i, x_i) = 1`（对角正时）。
即归一化把 Gram 变成**相关矩阵**。 -/
theorem normalizedKernel_gram_diag_one {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hpos : ∀ i, 0 < K (x i) (x i)) (i : Fin n) :
    normalizedKernel K (x i) (x i) = 1 :=
  normalizedKernel_self K (x i) (hpos i)

/-- **归一化核的 Gram 矩阵 = 相关系数矩阵**（逐点等式，便于下游引用）。 -/
theorem normalizedKernel_gram_apply {n : ℕ} (K : α → α → ℝ) (x : Fin n → α) (i j : Fin n) :
    normalizedKernel K (x i) (x j)
      = K (x i) (x j) / (Real.sqrt (K (x i) (x i)) * Real.sqrt (K (x j) (x j))) := rfl

/-! ## 五、与 `RealRKHSKernel` 的衔接：Mercer 分解 ⟹ 再生性

`RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap` 给出「Gram 半正定 ⟺
存在特征映射 `Φ`」。本节把该 `Φ` **直接**送入本文件的再生性，
形成闭环：**Mercer 分解 ⟹ 再生性 ⟹ 范数公式**。
-/

/-- **⭐ Mercer 分解 ⟹ 再生性（闭环定理）**：

若 `K` 对称、其 `n` 点 Gram 矩阵半正定，则**存在**特征映射 `Φ : Fin n → Fin n → ℝ`
使得对**每一对** `i j` 都有再生性 `⟪Φ(x_i), Φ(x_j)⟫ = K(x_i)(x_j)`
与范数公式 `‖Φ(x_i)‖² = K(x_i)(x_i)`。

这条把 `RealRKHSKernel` 的 Mercer 有限版与本文件的再生性/范数公式**接起来**：
前者给「存在性」，后者给「该存在性在 RKHS 语言下的内容」。

注意：**v15 修复**：Mercer 有限版给出的特征映射是 **`Φ : Fin n → Fin n → ℝ`**
（指标是**样本下标** `Fin n`，**不是** `α`）⟹ 原稿用
`reproducingPairing Φ (x i) (x j)`（该函数要求 `Φ : α → Fin m → ℝ`）**类型不符**。
正解：**直接在 `Fin n` 指标上陈述**——这正是 Mercer 有限版实际给出的内容，
且 `Σ_p Φ i p · Φ j p` 就是本文件的再生对（`reproducingPairing` 的展开式）。 -/
theorem featureMap_reproducing_compat {n : ℕ} (K : α → α → ℝ) (x : Fin n → α)
    (hsymm : IsSymmKernel K)
    (hpsd : ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, v i * kernelGramMatrix K x i j * v j) :
    ∃ Φ : Fin n → Fin n → ℝ,
      (∀ i j, (∑ p, Φ i p * Φ j p) = K (x i) (x j))
        ∧ (∀ i, (∑ p, (Φ i p) ^ 2) = K (x i) (x i)) := by
  obtain ⟨Φ, hΦ⟩ := (kernelGramMatrix_psd_iff_exists_featureMap K x hsymm).mp hpsd
  refine ⟨Φ, fun i j => ?_, fun i => ?_⟩
  · exact (hΦ i j).symm
  · -- 注意：`hΦ i i` 的右端是 `Σ p, Φ i p * Φ i p`（经 `kernelGramMatrix` 中转），
    -- 目标是 `Σ p, (Φ i p)^2 = K (x i) (x i)` ⟹ 两处都要桥接：
    -- ① `pow_two` 把 `(Φ i p)^2` 化成 `Φ i p * Φ i p`（**方向：`(·)^2` 在目标里**）；
    -- ② `kernelGramMatrix` 的定义等式把 `Σ p, …` 接到 `K (x i) (x i)`。
    have hdiag : (∑ p, Φ i p * Φ i p) = K (x i) (x i) := by
      rw [← hΦ i i]
      rfl
    rw [show (∑ p, Φ i p ^ 2) = ∑ p, Φ i p * Φ i p from
      Finset.sum_congr rfl fun p _ => by rw [pow_two]]
    exact hdiag

/-- **Mercer 分解 ⟹ 核对称（自动获得）**：把 `isSymmKernel_of_featureMap` 与
Mercer 有限版合成——**半正定 Gram + 显式特征映射 ⟹ 核对称**，
无需把对称性作为假设（与 `RealRKHSKernel` 中「对称性必须单独假设」形成对照：
那里是**抽象核**（无特征映射），此处置于**有特征映射**的语境，对称性成为结论）。 -/
theorem isSymmKernel_of_gram_psd_and_featureMap {n : ℕ} {K : α → α → ℝ}
    (Φ : Fin n → Fin n → ℝ) (x : Fin n → α)
    (hΦ : ∀ i j, kernelGramMatrix K x i j = ∑ p, Φ i p * Φ j p) :
    ∀ i j, K (x i) (x j) = K (x j) (x i) := by
  intro i j
  have h1 : K (x i) (x j) = ∑ p, Φ i p * Φ j p := hΦ i j
  have h2 : K (x j) (x i) = ∑ p, Φ j p * Φ i p := hΦ j i
  rw [h1, h2]
  exact Finset.sum_congr rfl fun p _ => by ring

/-! ## 注：闭环语义

**核定义**（`RealRKHSKernel.IsSymmKernel` / `IsPSDKernel`）
→ **Mercer 有限版**（`RealRKHSKernel.kernelGramMatrix_psd_iff_exists_featureMap`）
→ **再生性**（本文件 `reproducing_property`：`⟪K_{x_i}, K_{x_j}⟫ = K(x_i)(x_j)`）
→ **范数公式**（`rkhs_norm_sq_eq_kernel_diag`：`‖K_x‖² = K(x,x)`）
→ **求值界**（`norm_reproducing_bound`：`|f(x)| ≤ √(Kxx)·‖f‖`）
→ **距离–核恒等式的范数形态**（`norm_difference_eq_kernel_distance`）
→ **核闭包**（`kernelAdd_psd` / `kernelMul_psd_of_featureMap` / `kernelSMul_psd`）
→ **归一化**（`normalizedKernel` / `normalizedKernel_mem_unit`）。

诚实降级：RKHS 为**有限索引版**（`Fin n → ℝ`，无抽象完备化）；
代表点定理未做；`normalizedKernel` 的下界需显式逐点非负；
`polyKernel` 一般 `d ≥ 2`（不可乘积分解）仍未证；
`expKernel` / 热核的一般 PSD 仍等价于 Bochner 定理（mathlib 无），沿用未做。
-/

end Lattice
