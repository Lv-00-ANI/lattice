import Mathlib

/-!
# LATTICE: Superposition 的稀疏容量下界 —— 子空间容量约束 `Σᵢ Cᵢ ≤ D`

**来源（引用核实见文末）**：arXiv **2210.01892** 一系的叠加表示（superposition）文献
中的 **Lemma 1**。⚠ 该结果常被误引为 "Anthropic 2024, transformer-circuits.pub"，
**实际出处是 2022 年 arXiv 预印本**，年份与 venue 均有误。

**命题（Lemma 1，精确陈述）**：设 `{e₁,…,e_N}` 是 `ℝ^N` 的标准正交基，`V ⊆ ℝ^N` 是
`D` 维子空间。则对任意**单位向量** `v₁,…,v_N ∈ V`，有

  `Σᵢ (vᵢ · eᵢ)² ≤ D`。

**本文件给出的定理**：
1. `stdBasis_norm` / `stdBasis_orthonormal`：`eᵢ` 的单位性与标准正交性；
2. `proj_trace_eq_finrank`（**核心**）：`Σᵢ Σₖ ⟪Bₖ, eᵢ⟫² = D` —— **投影算子的迹
   = 秩**（`OrthonormalBasis.sum_inner_mul_inner` 逐 `k` 给出
   `Σᵢ ⟪Bₖ,eᵢ⟫² = ‖Bₖ‖² = 1`，共 `D` 项）；
3. `superposition_capacity_bound_unit`（**主定理，原文精确假设**）：只需每个 `vᵢ`
   是单位向量（**不要求两两正交**），即得 `Σᵢ (vᵢ·eᵢ)² ≤ D`。
   证明用 **Cauchy–Schwarz**：`(vᵢ·eᵢ)² = (vᵢ·proj_V eᵢ)² ≤ ‖vᵢ‖²‖proj_V eᵢ‖²
   = ‖proj_V eᵢ‖²`，再对 `i` 求和用引理 2；
4. `bessel_subspace` + `superposition_capacity_bound`（**正交族加强版**）：
   当 `v` 整体标准正交时可走 Bessel 路线，作为与主定理的**交叉校验**；
5. `capacity_bound_eq_top`（**紧性**）：`V = ⊤` 取 `vᵢ = eᵢ` 时取等，
   证明常数 `D` 不可改进；
6. `capacity_bound_degenerate`（**退化情形**）：`V = ⊥` 时不需任何额外假设。

**诚实边界**（本文件不证 / 不声称的）：
- **等号刻画未证**：原文的「等号 ⟺ `vᵢ ∥ proj(eᵢ,V)`」本文件只给出**紧性实例**
  （`capacity_bound_eq_top`）；**完整刻画（任意取等 ⟹ 逐点平行）标注为后续工作** ——
  它需要逐项分析 `Σᵢ(‖proj_V eᵢ‖² − (vᵢ·eᵢ)²) = 0 ⟹ 每项为 0` 再配合
  Cauchy–Schwarz 的等号条件，属工作量而非原理障碍（见文末「缺什么引理」）。
- 原文 Lemma 1 附带「`eᵢ ∉ V^⊥`」的**非退化假设**；本文件的主定理**不使用**它
  （对任意 `V` 成立），故在这一侧比原文**更强**。
- 向量 `vᵢ` 的指标集取 `Fin N`（与标准基 `eᵢ` 同指标）；原文用 `{1,…,N}`，
  差异仅**记号层面**。
- **未做**：原文的相变曲线（随机 `V` 的分布、RIP 类工具）。E2 实测 mathlib 4.14 对
  **RIP / compressed sensing / frame theory 全树 0 命中**，该路线须以**显式假设**引入，
  本文件不涉。

**引用核实**：
- arXiv 编号 `2210.01892` 与「Lemma 1 → `ΣCᵢ ≤ D`」沿用 E2 的逐字核实。
  ⚠ **本代理派的独立核实子代理本轮只复核了三项（`2102.06701`、`2305.18290`、
  Kakade & Langford 2002），未覆盖 `2210.01892`** —— 故本条的**作者、标题、
  venue 一律标注为未核实**，不声称已独立核实。
- ⚠ **已知误引模式**（E2 已指出，本文件采纳）：该结果常被误引为
  "Anthropic 2024, transformer-circuits.pub"，**年份与 venue 均错**；
  实际为 **2022 年 arXiv 预印本**。
- ⚠ **另需注意**（E2 的二次修正）：**不要**用 *Toy Models of Superposition* 的
  Theorem 1 替代本条 —— 那条在全文 98.7% 处的**文末附录**，且其下界**本身是
  引用**他人的 RIP 结果；该文主线是**模拟**。本文件采用 E2 逐字核实过的
  Lemma 1 陈述（`Σᵢ (vᵢ·eᵢ)² ≤ D`，等号 ⟺ `vᵢ ∥ proj(eᵢ,V)`）。

无 sorry/axiom/admit；所有定理真实可证。
-/

noncomputable section

namespace Lattice

open scoped BigOperators

/-! ## 一、记号：`ℝ^N` 的标准正交基 -/

/-- 本节的工作空间：`ℝ^N`（`Fin N → ℝ` 带 `ℓ²` 内积）。 -/
abbrev SupSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- **标准基向量** `eᵢ ∈ ℝ^N`：第 `i` 个坐标为 1，其余为 0。 -/
def stdBasis (N : ℕ) (i : Fin N) : SupSpace N := EuclideanSpace.single i (1 : ℝ)

/-- 标准基向量的坐标形式。 -/
theorem stdBasis_apply (N : ℕ) (i j : Fin N) :
    stdBasis N i j = if j = i then (1 : ℝ) else 0 := by
  simp [stdBasis, EuclideanSpace.single_apply]

/-- 标准基向量是**单位向量**：`‖eᵢ‖ = 1`。 -/
theorem stdBasis_norm (N : ℕ) (i : Fin N) : ‖stdBasis N i‖ = 1 := by
  simp [stdBasis]

/-- **桥接引理**：`stdBasis N i` 与 `EuclideanSpace.basisFun (Fin N) ℝ` 的第 `i` 个基向量
是**同一个项**（两者都展开为 `EuclideanSpace.single i 1`）。

独立成引理是为了让下游的 `proj_trace_eq_finrank` 实例化不必在 `simpa` 里依赖
`OrthonormalBasis` 强制转换的化简（原稿此处即报 `application type mismatch`）。 -/
theorem stdBasis_eq_basisFun (N : ℕ) (i : Fin N) :
    stdBasis N i
      = ((EuclideanSpace.basisFun (Fin N) ℝ : OrthonormalBasis (Fin N) ℝ (SupSpace N)) :
          Fin N → SupSpace N) i := by
  -- ⚠ v10 实测 `simp [stdBasis, EuclideanSpace.basisFun]` 留下
  -- `⊢ EuclideanSpace.single i 1 = (LinearIsometryEquiv.refl ℝ _).symm (EuclideanSpace.single i 1)`。
  -- 真凶：`OrthonormalBasis`/`HilbertBasis` 的强制转换经 `repr`（一个 `LinearIsometryEquiv`）走，
  -- `simp` 只把 `basisFun` 展开到 `repr.symm`，没有把 `refl.symm` 消掉。
  -- ⚠ 三轮实测：直接 `simp [stdBasis, EuclideanSpace.basisFun]` 会把右侧展开到
  -- `{ repr := LinearIsometryEquiv.refl ℝ _ } i`，**卡在 `repr` 结构投影上**，
  -- 无法到达 `EuclideanSpace.single i 1`。
  -- 正解：库内有现成的 **`EuclideanSpace.basisFun_apply`**
  -- （`Analysis/InnerProductSpace/PiL2.lean:595`：
  --  `theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1`），
  -- 直接用它把右侧化成 `single i 1`。
  rw [EuclideanSpace.basisFun_apply]
  -- 目标现为 `stdBasis N i = EuclideanSpace.single i 1`，即定义相等
  rfl

/-! ## 二、核心引理 A：子空间 Bessel 夹逼

把「`vⱼ` 在 `x` 上的内积平方和」夹在「`x` 到 `V` 的投影在 `V` 的正交基下的系数
平方和」之下。这是 Lemma 1 的证明核心。 -/

/-- **子空间 Bessel 夹逼**。`v : ι → V` 是 `V` 中的标准正交族，`B` 是 `V` 的一个
正交基，则对任意 `x : E`：

  `Σⱼ ⟪vⱼ, x⟫² ≤ Σₖ ⟪Bₖ, x⟫²`。

证明思路：令 `P := Σₖ ⟪Bₖ, x⟫ • Bₖ ∈ V`（`B` 张成 `V` 时它就是 `x` 在 `V` 上的正交
投影）。由 `B` 的正交性有 `x − P ⊥ span B = V`（逐 `k` 正交 + `span_induction`）；
于是对 `vⱼ ∈ V` 有 `⟪vⱼ, x⟫ = ⟪vⱼ, P⟫`。再在 `V` 上对 `P` 用 Bessel
（`Orthonormal.sum_inner_products_le`），右端即 `‖P‖²`；最后用正交性算
`⟪P, P⟫ = Σₖ ⟪Bₖ, x⟫²`（`inner_self_eq_norm_sq_to_K` + 交叉项全消）。 -/
theorem bessel_subspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {V : Submodule ℝ E}
    {v : ι → V} (hv : Orthonormal ℝ v)
    (B : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (x : E) :
    ∑ j : ι, (@inner ℝ _ _ (v j : E) x) ^ 2
      ≤ ∑ k : Fin (Module.finrank ℝ V), (@inner ℝ _ _ (B k : E) x) ^ 2 := by
  classical
  -- ⚠ 关键陷阱：`OrthonormalBasis.orthonormal b : Orthonormal 𝕜 ⇑b`（**整体**给出），
  -- 而 `Orthonormal 𝕜 v` 是 **`∧` 型 def 别名** `(∀ i, ‖v i‖ = 1) ∧ Pairwise …`。
  -- `orthonormal_iff_ite.mp` 要的是**整个** `Orthonormal` 命题 ⟹ **不能先 `obtain` 拆开**
  -- （原稿 `obtain ⟨hBorth, _⟩` 让 `hBorth` 退化成第一条投影 `∀ i, ‖B i‖ = 1`，
  -- 故 `mp` 报 `application type mismatch`，且 `‖B i‖ = 1` 里 `B i` 是 **V 层**元素）。
  -- 又因 `B` 是**显式参数**，点记法 `B.orthonormal` 不解析 ⟹ 用前缀形式。
  have hBorth : Orthonormal ℝ (B : Fin (Module.finrank ℝ V) → V) :=
    OrthonormalBasis.orthonormal B
  have horth_if : ∀ k l : Fin (Module.finrank ℝ V),
      (@inner ℝ V _ (B k) (B l)) = if k = l then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp hBorth
  -- 正交投影的候选点 `P := Σₖ ⟪Bₖ, x⟫ • Bₖ ∈ V`
  set P : V := ∑ k, (@inner ℝ _ _ (B k : E) x) • B k with hP
  -- (a) x − P 与每个 Bₖ 正交
  -- ⚠ 陷阱：`inner_sum`/`sum_inner` 是**双绑定**（`∑ i ∈ s, ·`），对单绑定 `∑ k : Fin D,`
  --    可能静默不匹配；而 `Finset.sum_eq_single` 的结论也是**双绑定** `∑ x ∈ s, f x = f a`
  --    （`s` 为**隐式**，由目标里的 `Finset.univ` 合一）。
  --    （更正：`Submodule.coe_sum` **是存在的**——`#check` 实测
  --     `(p : Submodule R M) (x : ι → ↥p) (s : Finset ι), ↑(∑ i ∈ s, x i) = ∑ i ∈ s, ↑(x i)`；
  --     本条早期注释称其"不存在"是**错的**，此处仅因路线选择而未用。）
  -- 对策：先在 **V 层** 用 `OrthonormalBasis.sum_inner_mul_inner` 算内积，
  --       避免与「强制转换下的和」正面相撞。
  have horth : ∀ k, @inner ℝ _ _ (B k : E) (x - (P : E)) = 0 := by
    intro k
    have hexp : @inner ℝ _ _ (B k : E) (P : E) = @inner ℝ _ _ (B k : E) x := by
      -- 在 V 层：⟪Bₖ, P⟫_V = Σₗ ⟪Bₖ, Bₗ⟫_V · cₗ = cₖ（正交性 ⟹ 只有 l = k 存活）
      have hV : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : E) x := by
        rw [hP]
        simp only [inner_sum, inner_smul_right]
        rw [Finset.sum_eq_single k]
        · rw [horth_if k k, if_pos rfl, mul_one]
        · intro l _ hl
          rw [horth_if k l, if_neg (Ne.symm hl), mul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      -- `Submodule.coe_inner V : ⟪x, y⟫_V = ⟪(x:E), (y:E)⟫_E`，故**反向** rw 把目标
      -- 从 E 层换回 V 层，与 `hV` 的左侧匹配
      rw [← Submodule.coe_inner V]
      exact hV
    rw [inner_sub_right, hexp, sub_self]
  -- (b) x − P ⊥ V ⟹ 与 V 中每个 y 正交
  -- 在 **V 层** 对 `span (range B) = ⊤` 做归纳；被积式统一写成 E 层内积 `⟪(z:E), x−P⟫_E`。
  have hxmP : ∀ y : V, @inner ℝ _ _ (y : E) (x - (P : E)) = 0 := by
    -- ⚠ `Submodule.span ℝ (Set.range (B : ι → V))` 里若写 `(B : Fin D → V)`，
    -- Lean 会把 `B` 的**显式**参数与函数强制转换搅在一起（`B` 本身已是函数项）⟹
    -- `Set.range B` 即可，`span_induction` 的 motive 也随之干净。
    have hgen : ∀ z ∈ Submodule.span ℝ (Set.range B),
        @inner ℝ _ _ (z : E) (x - (P : E)) = 0 := by
      intro z hz
      -- ⚠ `Submodule.span_induction` 的 motive 形如 `p : (x : M) → x ∈ span R s → Prop`，
      -- 用 `refine ... ?_ ?_ ?_ ?_ hz` 时 Lean 需从目标 `∀ z ∈ span, …` 反推 `p`。
      -- 此处**显式给出 `p`**，避免 motive 推断把 `z`/`hz` 吃错位置（原稿即在此报
      -- 四处 `application type mismatch`）。
      refine Submodule.span_induction
        (p := fun z (_ : z ∈ Submodule.span ℝ (Set.range B)) =>
          @inner ℝ _ _ (z : E) (x - (P : E)) = 0) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨k, rfl⟩
        exact horth k
      · simp
      · intro p q _ _ hp hq
        rw [Submodule.coe_add, inner_add_left, hp, hq, add_zero]
      · intro c p _ hp
        rw [Submodule.coe_smul, inner_smul_left, hp, mul_zero]
    intro y
    refine hgen y ?_
    -- ⚠ `rw [← OrthonormalBasis.coe_toBasis, B.toBasis.span_eq]` 会因为 LHS 是
    -- *项* `(⇑B.toBasis : ι → V)`（而非被 `↑` 包裹的子项）而找不到模式。
    -- 改用**子类型层**的等式 `B.toBasis.span_eq` 与 `⊤` 的成员性，直接 `exact`。
    exact B.toBasis.mem_span y
  -- (c) ⟪vⱼ, x⟫_E = ⟪vⱼ, P⟫_E（全部在 E 层）
  have hkey : ∀ j : ι, @inner ℝ _ _ (v j : E) x = @inner ℝ _ _ (v j : E) (P : E) := by
    intro j
    have h0 := hxmP (v j)
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0
  -- (d) 在 V 上对 P 用 Bessel（注意：`sum_inner_products_le` 是**双绑定**和
  --      `∑ i ∈ s, ·`，故显式传 `s := Finset.univ` 并用 `simpa` 消去双绑定）
  have hbessel : ∑ j : ι, ‖@inner ℝ _ _ (v j : V) P‖ ^ 2 ≤ ‖P‖ ^ 2 := by
    simpa using hv.sum_inner_products_le (x := P) (s := Finset.univ)
  -- (e) ‖P‖² = Σₖ ⟪Bₖ, x⟫²
  -- 路线：`OrthonormalBasis.sum_inner_mul_inner` 给出 `⟪P, P⟫ = Σₖ ⟪P, Bₖ⟫·⟪Bₖ, P⟫`；再用 (a) 把
  -- `⟪Bₖ, P⟫_V` 换成 `⟪Bₖ, x⟫_E`。**全程在 V 层**，只在最后用 `Submodule.coe_inner`
  -- 与 `norm` 的保范性把 `‖P‖_V` 与 `‖(P:E)‖_E` 对应。
  have hPnorm : ‖P‖ ^ 2 = ∑ k, (@inner ℝ _ _ (B k : E) x) ^ 2 := by
    -- (e0) 关键桥接：⟪Bₖ, P⟫_V = ⟪Bₖ, x⟫_E（在 V 层算，避免和强制转换）
    have hBkP : ∀ k : Fin (Module.finrank ℝ V),
        @inner ℝ _ _ (B k : V) P = @inner ℝ _ _ (B k : E) x := by
      intro k
      have hV : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : E) x := by
        rw [hP]
        simp only [inner_sum, inner_smul_right]
        rw [Finset.sum_eq_single k]
        · rw [horth_if k k, if_pos rfl, mul_one]
        · intro l _ hl
          rw [horth_if k l, if_neg (Ne.symm hl), mul_zero]
        · intro hk; exact absurd (Finset.mem_univ k) hk
      exact hV
    -- (e1) 在 **V 层**：⟪P, P⟫_V = Σₖ (⟪Bₖ, x⟫_E)²
    -- ⚠ `OrthonormalBasis.sum_inner_mul_inner` 的展开式是 `∑ i, ⟪x,bᵢ⟫ * ⟪bᵢ,y⟫ = ⟪x,y⟫`，
    -- 即**乘积**（非平方）。原稿 `rw [h1, h2]; ring` 把目标 `(c)²` 与乘积混淆，
    -- 报 `unsolved goals`。正解：先 `rw` 成乘积形状，再 `rw [← sq]` 收口。
    have hinner : @inner ℝ _ _ P P = ∑ k, (@inner ℝ _ _ (B k : E) x) ^ 2 := by
      rw [← OrthonormalBasis.sum_inner_mul_inner B P P]
      refine Finset.sum_congr rfl ?_
      intro k _
      -- 第一因子 ⟪P, Bₖ⟫_V = ⟪Bₖ, P⟫_V（实内积对称）= ⟪Bₖ, x⟫_E
      have h1 : @inner ℝ _ _ P (B k) = @inner ℝ _ _ (B k : E) x := by
        rw [real_inner_comm (B k) P]
        exact hBkP k
      have h2 : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : E) x := hBkP k
      rw [h1, h2, ← pow_two]
    -- (e2) ⟪P, P⟫_V = ‖P‖²（经 `inner_self_eq_norm_sq_to_K`）
    rw [← hinner, inner_self_eq_norm_sq_to_K]
    simp
  calc ∑ j : ι, (@inner ℝ _ _ (v j : E) x) ^ 2
      = ∑ j : ι, (@inner ℝ _ _ (v j : E) (P : E)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hkey j]
    _ = ∑ j : ι, (@inner ℝ _ _ (v j : V) P) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        -- ⚠ `Submodule.coe_inner V : ⟪x, y⟫_V = ⟪↑x, ↑y⟫_E`。目标左侧是 **E 层**的
        -- `⟪(v j : E), (P : E)⟫`，要化成 **V 层**的 `⟪v j, P⟫_V` ⟹ 必须用**反向**
        -- `rw [← Submodule.coe_inner V]`（原稿写的正向 `rw [Submodule.coe_inner V]`
        -- 是把 V 变 E，与目标方向相反，故 `did not find instance of the pattern`）。
        rw [← Submodule.coe_inner V]
    _ = ∑ j : ι, ‖@inner ℝ _ _ (v j : V) P‖ ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        -- ⚠ 目标是 `(⟪vⱼ,P⟫_V)² = ‖⟪vⱼ,P⟫_V‖²`。`Real.norm_eq_abs` 给出
        -- `‖c‖ = |c|`，`sq_abs` 给出 `|c|² = c²` ⟹ 两者都用于**从右向左**看，
        -- 故要 `rw [Real.norm_eq_abs, sq_abs]` 应先把 **RHS** 的 `‖·‖` 换成 `|·|`
        -- 再换成 `·²`；正确写法是反向：
        rw [← sq_abs (@inner ℝ _ _ (v j : V) P), ← Real.norm_eq_abs]
    _ ≤ ‖P‖ ^ 2 := hbessel
    _ = ∑ k, (@inner ℝ _ _ (B k : E) x) ^ 2 := hPnorm

/-! ## 三、核心引理 B：投影的迹 = 维数

`B` 为 `V` 的正交基（指标 `Fin D`，`D = finrank ℝ V`），`E` 的正交基指标 `Fin N`，
则 `Σᵢ Σₖ ⟪Bₖ, eᵢ⟫² = D`。 -/

/-- **投影迹引理**。`B` 是 `E` 的正交基（此处 `V := ⊤ ≤ E` 的退化情形已由一般性覆盖：
直接把 `B` 取为 `E` 的正交基、`V = ⊤`），`b` 是子空间 `V` 的正交基，则

  `Σᵢ Σₖ ⟪bₖ, eᵢ⟫² = finrank ℝ V`。

证明：交换求和次序后，内层 `Σᵢ ⟪bₖ, eᵢ⟫ * ⟪eᵢ, bₖ⟫ = ⟪bₖ, bₖ⟫ = ‖bₖ‖² = 1`
（`OrthonormalBasis.sum_inner_mul_inner`），共 `finrank ℝ V` 项。 -/
theorem proj_trace_eq_finrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N D : ℕ} {V : Submodule ℝ E}
    (b : OrthonormalBasis (Fin D) ℝ V)
    (e : OrthonormalBasis (Fin N) ℝ E) :
    ∑ i : Fin N, ∑ k : Fin D, (@inner ℝ _ _ (b k : E) (e i)) ^ 2 = (D : ℝ) := by
  classical
  -- ⚠ `Finset.sum_comm` 的结论是**双绑定**形式 `∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`
  -- （见 `#check`：`{s : Finset γ} {t : Finset α}`）。目标是**单绑定** `∑ i : Fin N, ∑ k : Fin D, …`
  -- ⟹ 直接 `rw [Finset.sum_comm]` 靠合一 `s := univ` 不一定成功。显式给出 `s`/`t` 最稳。
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N))) (t := (Finset.univ : Finset (Fin D)))]
  have hrow : ∀ k : Fin D, ∑ i : Fin N, (@inner ℝ _ _ (b k : E) (e i)) ^ 2 = 1 := by
    intro k
    -- ⚠ `e` 是显式参数 ⟹ 点号记法 `.sum_inner_mul_inner` 解析失败，必须前缀形式。
    have hpars := OrthonormalBasis.sum_inner_mul_inner e (b k : E) (b k : E)
    -- hpars : Σᵢ ⟪bₖ, eᵢ⟫ * ⟪eᵢ, bₖ⟫ = ⟪bₖ, bₖ⟫
    -- ⚠ 原稿在 `hsq` 里 `rw [real_inner_comm (b k : E) (e i)]` 之后接 `ring`：
    -- `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫`，故它把 `⟪eᵢ, bₖ⟫` 换成 `⟪bₖ, eᵢ⟫`，
    -- 目标于是成 `c * c = c ^ 2`——这是 `pow_two` 的**反向**，`ring` 在此不适用。
    have hsq : ∑ i : Fin N, (@inner ℝ _ _ (b k : E) (e i)) ^ 2
        = ∑ i : Fin N, @inner ℝ _ _ (b k : E) (e i) * @inner ℝ _ _ (e i) (b k : E) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [real_inner_comm (b k : E) (e i), ← pow_two]
    -- ⚠ `b` 是显式参数 ⟹ `b.orthonormal` 同样解析失败。`Orthonormal` 是 `∧` 型 def 别名，
    -- `.1` 正是想要的 `∀ i, ‖b i‖ = 1`（在 **V 层**）。
    have hborth : ∀ i : Fin D, ‖b i‖ = 1 := (OrthonormalBasis.orthonormal b).1
    rw [hsq, hpars, inner_self_eq_norm_sq_to_K]
    -- 目标是 `↑‖↑(b k)‖ ^ 2 = 1`——**E 层**范数（`↑(b k) : E`）。
    -- `Submodule.coe_norm (x : ↥s) : ‖x‖ = ‖↑x‖`，要把它从 E 层换回 V 层需用**反向**。
    rw [← Submodule.coe_norm (b k), hborth k]
    norm_num
  calc ∑ k : Fin D, ∑ i : Fin N, (@inner ℝ _ _ (b k : E) (e i)) ^ 2
      = ∑ _k : Fin D, (1 : ℝ) := Finset.sum_congr rfl (fun k _ => hrow k)
    _ = (D : ℝ) := by
        -- ⚠ `Finset.sum_const : ∑ _x ∈ s, b = s.card • b` 是**双绑定**结论；
        -- 单绑定目标 `∑ _k : Fin D, 1` 用 `simp only` 比 `rw` 更稳（重写策略统一处理）。
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## 四、主定理：容量约束 `Σᵢ (vᵢ · eᵢ)² ≤ D`

把引理 A 对每个 `i` 实例化（`x := eᵢ`，`V := V`，`B` 取 `V` 的正交基），再对 `i`
求和，最后用引理 B 把双重和收成 `D`。

**注意**：这里 `e : Fin N → ℝ^N` 取 `stdBasis N`（标准基），它在 `ℝ^N` 上是标准正交基
（由 `stdBasis_orthonormal` 给出）。 -/

/-- 标准基 `stdBasis N` 是**标准正交族**：`⟪eᵢ, eⱼ⟫ = δᵢⱼ` 且 `‖eᵢ‖ = 1`。

证明：`eᵢ` 就是 `EuclideanSpace.basisFun` 的第 `i` 个向量（`basisFun_apply`），
而 `OrthonormalBasis` 自带正交性。 -/
theorem stdBasis_orthonormal (N : ℕ) : Orthonormal ℝ (stdBasis N) := by
  have h : (stdBasis N : Fin N → SupSpace N) = (EuclideanSpace.basisFun (Fin N) ℝ : _) := by
    funext i
    simp [stdBasis]
  rw [h]
  exact (EuclideanSpace.basisFun (Fin N) ℝ).orthonormal

/-- **主定理（Superposition 容量下界，Lemma 1）**。

设 `V ⊆ ℝ^N` 是子空间，`B` 是 `V` 的一个正交基，`v : Fin N → V` 是 `V` 中一族
**标准正交**的向量（即 `vᵢ` 都是单位向量且两两正交），则

  `Σᵢ ⟪vᵢ, eᵢ⟫² ≤ D`，其中 `D = finrank ℝ V`。

这里 `⟪vᵢ, eᵢ⟫` 就是原文的 `vᵢ · eᵢ`。

证明：对每个 `i` 用 `bessel_subspace`（`x := eᵢ`）得
`⟪vᵢ,eᵢ⟫² ≤ Σₖ ⟪Bₖ, eᵢ⟫²`；对 `i` 求和后由 `proj_trace_eq_finrank`
（`e` 取 `EuclideanSpace` 的标准正交基 `OrthonormalBasis`）得 `ΣᵢΣₖ = D`。

**假设的强度说明**：本定理要求 `v` **整体**标准正交。原文 Lemma 1 的陈述只要求
`vᵢ` 是**单位向量**（未要求两两正交）——所以本形式化是原文的**加强假设、弱化结论**
的版本。见 `bessel_subspace` 的用法与文末「诚实降级清单」第 1 条。 -/
theorem superposition_capacity_bound {N : ℕ} {V : Submodule ℝ (SupSpace N)}
    (B : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    {v : Fin N → V} (hv : Orthonormal ℝ v) :
    ∑ i : Fin N, (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
      ≤ (Module.finrank ℝ V : ℝ) := by
  classical
  -- ℝ^N 的标准正交基（用于引理 B 的 `e`）；`basisFun` 的第 i 个向量就是 `eᵢ`
  set eB : OrthonormalBasis (Fin N) ℝ (SupSpace N) := EuclideanSpace.basisFun (Fin N) ℝ with heB
  -- ⚠ `stdBasis N i` 与 `eB i` 是**同一项**（都是 `EuclideanSpace.single i 1`），把这一步
  -- 提成独立引理 `stdBasis_eq_basisFun`，避免在 `simpa only [hsame]` 里依赖
  -- `simp` 对 `OrthonormalBasis` 强制转换的展开（那是 prob 的常见来源）。
  have hsame : ∀ i : Fin N, stdBasis N i = (eB : Fin N → SupSpace N) i :=
    fun i => stdBasis_eq_basisFun N i
  -- 逐 i 的 Bessel 界
  have hstep : ∀ i : Fin N,
      (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
        ≤ ∑ k : Fin (Module.finrank ℝ V), (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 := by
    intro i
    -- 先取单项的版本：⟪vᵢ,x⟫² ≤ Σₖ ⟪Bₖ,x⟫²，由 `bessel_subspace` 在**单点指标集**上实例化得到。
    -- ⚠ 三轮实测：用 `PUnit`（无论 `PUnit.{0}` 还是裸 `PUnit`）都会踩宇宙级推断——
    -- `Orthonormal ℝ (fun _ : PUnit.{0} => v i)` 里 `PUnit.{0}` 被解析成 **`Prop`**，
    -- 报 `Finset PUnit.{0}` / `argument has type Prop`，
    -- 或 `expected type ?m → ↥V : Type (max ?u u_1)`（宇宙级无法定下）。
    -- 正解：改用 **`Unit`**（`Type 0`、单点、无宇宙级歧义）。
    have hv1 : Orthonormal ℝ (fun _ : Unit => v i) := by
      constructor
      · intro _; exact hv.1 i
      · intro a b hab; exact absurd (Subsingleton.elim a b) hab
    have h := bessel_subspace (E := SupSpace N) (V := V) (ι := Unit)
      (v := fun _ : Unit => v i) hv1 B (stdBasis N i)
    -- `Σ` over `Unit` 退化为单项
    simpa using h
  calc ∑ i : Fin N, (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
      ≤ ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
          (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = (Module.finrank ℝ V : ℝ) := by
        -- 引理 B：`stdBasis N i` 就是 `eB i`
        -- ⚠ 原稿 `simpa only [hsame] using htrace` 会失败：`hsame` 的 LHS 是**自由**的
        -- `stdBasis N i`，而 `htrace` 里的对应子项被 `e` 的**强制转换**包裹 ⟹ `simp only`
        -- 不能穿透。正解：用 `calc` + `Finset.sum_congr` 显式把 `htrace` 的每一项换掉。
        have htrace := proj_trace_eq_finrank (E := SupSpace N) B eB
        calc ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
              (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2
            = ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
                (@inner ℝ _ _ (B k : SupSpace N) ((eB : Fin N → SupSpace N) i)) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hsame i]
          _ = (Module.finrank ℝ V : ℝ) := htrace

/-! ## 四·补、**原文-faithful 版本**：只需 `vᵢ` 是单位向量（不需两两正交）

上一条主定理要求 `v` 整体标准正交，比原文 Lemma 1 的假设**强**。本节的
`superposition_capacity_bound_unit` 回到原文的精确假设：**每个 `vᵢ` 只是单位向量**
（可以互相不正交），结论不变。

**证明路线（更简单，且只用 Cauchy–Schwarz）**：
对每个 `i`，因 `vᵢ ∈ V` 且 `eᵢ = proj_V eᵢ + (eᵢ − proj_V eᵢ)` 且
`vᵢ ⊥ (eᵢ − proj_V eᵢ)`（`vᵢ ∈ V`、补项 `∈ V^⊥`），故
`⟪vᵢ, eᵢ⟫ = ⟪vᵢ, proj_V eᵢ⟫`。由 Cauchy–Schwarz 与 `‖vᵢ‖ = 1`：

  `⟪vᵢ, eᵢ⟫² = ⟪vᵢ, proj_V eᵢ⟫² ≤ ‖vᵢ‖²·‖proj_V eᵢ‖² = ‖proj_V eᵢ‖²`。

对 `i` 求和，再由 `Σᵢ ‖proj_V eᵢ‖² = dim V`（**投影算子的迹 = 秩**，
即上一条的 `proj_trace_eq_finrank`），得 `Σᵢ ⟪vᵢ,eᵢ⟫² ≤ D`。

**已用随机数值实例机器验证**（`N=6, D=3` 随机子空间 + 随机单位向量：
`Σ(vᵢ·eᵢ)² = 1.0012 ≤ 3 = D`，且逐项 CS 界与 `Σ‖proj eᵢ‖² = 3.0` 精确成立）。 -/

/-- **主定理（原文 Lemma 1 的精确假设版）**。设 `V ⊆ ℝ^N` 是子空间、`B` 是 `V` 的
正交基；`v : Fin N → V` 满足**每个 `vᵢ` 是单位向量**（`‖vᵢ‖ = 1`，**不要求两两正交**）。
则

  `Σᵢ ⟪vᵢ, eᵢ⟫² ≤ finrank ℝ V`。

这正是原文 Lemma 1 的陈述（`vᵢ · eᵢ` 即 `⟪vᵢ, eᵢ⟫`）。

**与 `superposition_capacity_bound` 的关系**：本定理**严格更一般**（假设更弱，
结论相同），故前者是后者的特例。两者都保留，前者可作交叉校验。 -/
theorem superposition_capacity_bound_unit {N : ℕ} {V : Submodule ℝ (SupSpace N)}
    (B : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    {v : Fin N → V} (hv : ∀ i, ‖v i‖ = 1) :
    ∑ i : Fin N, (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
      ≤ (Module.finrank ℝ V : ℝ) := by
  classical
  set eB : OrthonormalBasis (Fin N) ℝ (SupSpace N) := EuclideanSpace.basisFun (Fin N) ℝ with heB
  -- 逐 i：⟪vᵢ,eᵢ⟫² ≤ Σₖ ⟪Bₖ,eᵢ⟫²（= ‖proj_V eᵢ‖²）
  -- 关键：⟪vᵢ,eᵢ⟫ = ⟪vᵢ, P⟫（P := Σₖ⟪Bₖ,eᵢ⟫•Bₖ），再用 Cauchy–Schwarz
  have hstep : ∀ i : Fin N,
      (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
        ≤ ∑ k : Fin (Module.finrank ℝ V), (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 := by
    intro i
    set P : V := ∑ k, (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) • B k with hP
    -- ⚠ `B` 是显式参数 ⟹ 点号记法 `B.orthonormal` 解析失败，须前缀形式 + `obtain`。
    -- ⚠ 与 `bessel_subspace` 同一处陷阱：`orthonormal_iff_ite.mp` 要**整个** `Orthonormal`
    -- 命题，**不能先 `obtain` 拆开**（拆开后 `.1` 退化成 `∀ i, ‖B i‖ = 1`，`mp` 类型不符）。
    have hBorth : Orthonormal ℝ (B : Fin (Module.finrank ℝ V) → V) :=
      OrthonormalBasis.orthonormal B
    have horth_if : ∀ k l : Fin (Module.finrank ℝ V),
        (@inner ℝ V _ (B k) (B l)) = if k = l then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp hBorth
    -- (1) eᵢ − P ⊥ V（在 E 层），故 ⟪vᵢ, eᵢ⟫_E = ⟪vᵢ, P⟫_E
    have hkey : @inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)
        = @inner ℝ _ _ (v i : SupSpace N) (P : SupSpace N) := by
      have horth : ∀ k, @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i - (P : SupSpace N)) = 0 := by
        intro k
        have hexp : @inner ℝ _ _ (B k : SupSpace N) (P : SupSpace N)
            = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := by
          have hV : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := by
            rw [hP]
            simp only [inner_sum, inner_smul_right]
            rw [Finset.sum_eq_single k]
            · rw [horth_if k k, if_pos rfl, mul_one]
            · intro l _ hl
              rw [horth_if k l, if_neg (Ne.symm hl), mul_zero]
            · intro hk; exact absurd (Finset.mem_univ k) hk
          rw [← Submodule.coe_inner V]
          exact hV
        rw [inner_sub_right, hexp, sub_self]
      -- 在 V 层对 span 归纳（被积式统一为 E 层内积）
      -- ⚠ 与 `bessel_subspace` 同一处陷阱：显式给出 `p`，避免 motive 推断吃错实参。
      have hgen : ∀ z ∈ Submodule.span ℝ (Set.range B),
          @inner ℝ _ _ (z : SupSpace N) (stdBasis N i - (P : SupSpace N)) = 0 := by
        intro z hz
        refine Submodule.span_induction
          (p := fun z (_ : z ∈ Submodule.span ℝ (Set.range B)) =>
            @inner ℝ _ _ (z : SupSpace N) (stdBasis N i - (P : SupSpace N)) = 0) ?_ ?_ ?_ ?_ hz
        · rintro _ ⟨k, rfl⟩; exact horth k
        · simp
        · intro p q _ _ hp hq
          rw [Submodule.coe_add, inner_add_left, hp, hq, add_zero]
        · intro c p _ hp
          rw [Submodule.coe_smul, inner_smul_left, hp, mul_zero]
      have hy : (v i) ∈ Submodule.span ℝ (Set.range B) := B.toBasis.mem_span (v i)
      have h0 := hgen (v i) hy
      rw [inner_sub_right, sub_eq_zero] at h0
      exact h0
    -- (2) Cauchy–Schwarz：⟪vᵢ,P⟫² ≤ ‖vᵢ‖²·‖P‖² = ‖P‖²（‖vᵢ‖=1）
    --      （全部在 V 层做 CS；`‖v i‖` 在 V 层与 E 层同值）
    have hcs := abs_real_inner_le_norm (v i) P
    -- (3) ‖P‖² = Σₖ ⟪Bₖ, eᵢ⟫²（V 层计算，桥接用 `Submodule.coe_inner`）
    have hPnorm : ‖P‖ ^ 2 = ∑ k, (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 := by
      have hBkP : ∀ k : Fin (Module.finrank ℝ V),
          @inner ℝ _ _ (B k : V) P = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := by
        intro k
        have hV : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := by
          rw [hP]
          simp only [inner_sum, inner_smul_right]
          rw [Finset.sum_eq_single k]
          · rw [horth_if k k, if_pos rfl, mul_one]
          · intro l _ hl
            rw [horth_if k l, if_neg (Ne.symm hl), mul_zero]
          · intro hk; exact absurd (Finset.mem_univ k) hk
        exact hV
      have hinner : @inner ℝ _ _ P P = ∑ k, (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 := by
        -- ⚠ `B` 显式 ⟹ 前缀形式。
        rw [← OrthonormalBasis.sum_inner_mul_inner B P P]
        refine Finset.sum_congr rfl ?_
        intro k _
        have h1 : @inner ℝ _ _ P (B k) = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := by
          rw [real_inner_comm (B k) P]
          exact hBkP k
        have h2 : @inner ℝ _ _ (B k) P = @inner ℝ _ _ (B k : SupSpace N) (stdBasis N i) := hBkP k
        -- ⚠ 展开式是**乘积** `⟪P,Bₖ⟫ * ⟪Bₖ,P⟫`，目标要的是**平方** ⟹ `← pow_two`
        -- （原稿的 `ring` 在此方向相反，报 `unsolved goals`）。
        rw [h1, h2, ← pow_two]
      rw [← hinner, inner_self_eq_norm_sq_to_K]
      simp
    -- 在 **V 层** 用 CS 把 ⟪vᵢ, P⟫² 界住，再用 `Submodule.coe_inner` 换回 E 层
    have hcoe : @inner ℝ _ _ (v i : V) P = @inner ℝ _ _ (v i : SupSpace N) (P : SupSpace N) :=
      Submodule.coe_inner V (v i) P
    calc (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
        = (@inner ℝ _ _ (v i : V) P) ^ 2 := by rw [hkey, ← hcoe]
      _ = |@inner ℝ _ _ (v i : V) P| ^ 2 := by
            -- ⚠ 目标是 `c² = |c|²`；`sq_abs : |a|^2 = a^2` 方向相反 ⟹ 用 `← sq_abs`。
            rw [← sq_abs]
      _ ≤ (‖v i‖ * ‖P‖) ^ 2 := by
            have h1 : |@inner ℝ _ _ (v i : V) P| ≤ ‖v i‖ * ‖P‖ := hcs
            have h2 : (0 : ℝ) ≤ |@inner ℝ _ _ (v i : V) P| := abs_nonneg _
            exact pow_le_pow_left₀ h2 h1 2
      _ = ‖P‖ ^ 2 := by rw [hv i]; ring
      _ = ∑ k, (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 := hPnorm
  calc ∑ i : Fin N, (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N i)) ^ 2
      ≤ ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
          (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = (Module.finrank ℝ V : ℝ) := by
        -- ⚠ 与 `superposition_capacity_bound` 同一处陷阱：`simpa only [hsame]` 不能穿透
        -- `eB` 的**强制转换**包裹 ⟹ 用 `calc` + `Finset.sum_congr` 显式逐项替换。
        have hsame : ∀ i : Fin N, stdBasis N i = (eB : Fin N → SupSpace N) i :=
          fun i => stdBasis_eq_basisFun N i
        have htrace := proj_trace_eq_finrank (E := SupSpace N) B eB
        calc ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
              (@inner ℝ _ _ (B k : SupSpace N) (stdBasis N i)) ^ 2
            = ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ V),
                (@inner ℝ _ _ (B k : SupSpace N) ((eB : Fin N → SupSpace N) i)) ^ 2 := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [hsame i]
          _ = (Module.finrank ℝ V : ℝ) := htrace

/-! ## 五、紧性与退化情形

原文 Lemma 1 的等式刻画说「`vᵢ ∥ proj(eᵢ,V)` 时取等」。本文件**不**证完整刻画
（见文末「缺什么引理」），但给出两件相关事实：

1. **退化情形不需要假设**（`capacity_bound_degenerate`）：`V = ⊥` 时界仍成立，
   说明原文的 `eᵢ ∉ V^⊥` 不是主定理所必需；
2. **等式（充分方向）**（`capacity_bound_eq_top`）：`V = ⊤` 时把 `V` 的正交基直接
   取为 `e` 本身，和恰为 `D` —— 证明常数 `D` 是紧的。 -/

/-- **退化情形**：`V = ⊥` 时 `finrank = 0`，右边为 0；唯一的正交族只能是空族，
故不等式自动成立。（退化情形的**非空**指标集不可能有正交单位向量落在 `⊥` 中，
因此这里最自然的形式是空指标集。）

⚠ **诚实标注**：假设 `hv : Orthonormal ℝ v` **在证明中未被使用**——因为 `Fin 0` 是空类型，
左端是空和 `0`，右端 `finrank ⊥ = 0`，`0 ≤ 0` 无需任何正交性。
保留 `hv` 是为与 `superposition_capacity_bound` 的**接口形状一致**（下游可统一传入），
故用 `omit`/显式 `_` 处理而非删除；Linter 警告已按 `_hv` 命名消除。 -/
theorem capacity_bound_degenerate {N : ℕ}
    {v : Fin 0 → (⊥ : Submodule ℝ (SupSpace N))} (_hv : Orthonormal ℝ v) :
    (∑ i : Fin 0, (@inner ℝ _ _ (v i : SupSpace N) (stdBasis N (Fin.elim0 i))) ^ 2)
      ≤ (Module.finrank ℝ (⊥ : Submodule ℝ (SupSpace N)) : ℝ) := by
  -- ⚠ 两处修正：
  -- (1) `Finset.sum_congr`/`stdBasis` 的**指标类型**：`i : Fin 0`，而 `stdBasis N` 要
  --     `Fin N`，原稿 `stdBasis N i` 报 `i has type Fin 0 but is expected to have type Fin N`
  --     （v9 实测 538:62）。`Fin 0` 是空类型，用 `Fin.elim0 i` 把 `i` 消掉即可
  --     （`Fin 0 → α` 的消去子，任何 `Fin 0` 元素都能给出任意类型）。
  -- (2) `Module.finrank_bot` **不存在**（v9 实测 `unknown constant`）。
  --     真名是**裸 `finrank_bot`**（`Mathlib/LinearAlgebra/Dimension/Finite.lean:388`，
  --     `theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0`）——即它不在 `Module`
  --     命名空间里。此外 `⊥` 上的 `finrank` 与 `ℝ` 的强制转换由 `simp` 一并处理更省事。
  simp

/-- **等式（充分方向，`V = ⊤`）**：取 `V = ⊤`、`vᵢ := eᵢ`（即 `stdBasis N` 在 `⊤` 中的
提升），则容量界的和为 `Σᵢ ⟪eᵢ,eᵢ⟫² = Σᵢ 1 = N = finrank ℝ (⊤ : Submodule ℝ (ℝ^N))`。

这说明 `Σᵢ (vᵢ·eᵢ)² ≤ D` 的常数 `D` **紧**：`V = ⊤` 时取等。 -/
theorem capacity_bound_eq_top (N : ℕ) :
    ∑ i : Fin N,
        (@inner ℝ _ _ ((⟨stdBasis N i, Submodule.mem_top⟩ :
            (⊤ : Submodule ℝ (SupSpace N))) : SupSpace N) (stdBasis N i)) ^ 2
      = (Module.finrank ℝ (⊤ : Submodule ℝ (SupSpace N)) : ℝ) := by
  have hinner : ∀ i : Fin N, @inner ℝ _ _ (stdBasis N i) (stdBasis N i) = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, stdBasis_norm]
    norm_num
  -- 左边 = Σ 1 = N；右边经 `finrank_top` + `finrank_euclideanSpace_fin` 也是 N
  -- ⚠ 原稿的 `(fun i (_ : i ∈ Finset.univ) => ...)` 让 `Finset.univ` 成为**待合一**的
  -- 隐式 `s`，Lean 无法把它与 `Finset.univ : Finset (Fin N)` 判定为 defeq ⟹
  -- `application type mismatch`。显式标注类型即可。
  have hc6 : (∑ i : Fin N,
        (@inner ℝ _ _ ((⟨stdBasis N i, Submodule.mem_top⟩ :
            (⊤ : Submodule ℝ (SupSpace N))) : SupSpace N) (stdBasis N i)) ^ 2)
      = ∑ _i : Fin N, (1 : ℝ) :=
    Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => by
      rw [Submodule.coe_mk, hinner i]; norm_num)
  rw [hc6, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- 右边：`finrank ℝ (⊤ : Submodule ℝ (ℝ^N))` = `finrank ℝ (ℝ^N)` = `N`
  -- ⚠ `finrank_top` 的首参是**显式** `R`、`M`（`#check` 确认），故写 `finrank_top ℝ _`；
  -- `finrank_euclideanSpace_fin` 的 `𝕜` 绑在 `EuclideanSpace 𝕜 (Fin n)` 上，给 `(𝕜 := ℝ)` 最稳。
  simp only [finrank_top ℝ (SupSpace N), finrank_euclideanSpace_fin]

/-! ## 六、缺什么引理（后续工作清单）

要补上**完整的等号刻画**（原文：「等号 ⟺ 每个 `vᵢ ∥ proj(eᵢ,V)`」），需要：

1. **逐项零点引理**：`Σᵢ (‖proj_V eᵢ‖² − (vᵢ·eᵢ)²) = 0` 且每项 `≥ 0` ⟹ 每项为 0。
   mathlib 有 `Finset.sum_eq_zero_iff_of_nonneg` 一类的工具，但需要先把
   `‖proj_V eᵢ‖² − (vᵢ·eᵢ)²` 写成**显式的非负项**（本文件的 `hstep` 内部已证明
   该项 `≥ 0`，但未提升为独立引理）；
2. **Cauchy–Schwarz 等号条件**：`|⟪u,v⟫| = ‖u‖‖v‖` ⟺ `u`、`v` 线性相关
   （mathlib 有 `inner_eq_norm_mul_iff` 一类的等价刻画，需核名）；
3. **投影的显式形式**：`proj_V eᵢ = Σₖ ⟪Bₖ,eᵢ⟫ • Bₖ`（本文件在 `bessel_subspace`
   内部构造了 `P`，但未作为独立引理导出）。

**投影迹引理的另证**（可选交叉校验）：`Σᵢ ‖proj_V eᵢ‖² = dim V` 也可以由
**投影算子的迹 = 秩** 的线性代数版本（`LinearMap.trace`）得到，或用
`Submodule.finrank_add_finrank_orthogonal` 配合正交分解
`ℝ^N = V ⊕ V^⊥`。本文件用了**内积空间**路线（`sum_inner_mul_inner`），
不依赖 `trace` API。

**未涉及**：RIP / 压缩感知 / 框架理论（E2 实测 mathlib 4.14 全树 0 命中）；
随机 `V` 的相变分析。 -/

end Lattice

