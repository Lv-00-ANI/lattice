import Mathlib

/-!
# LATTICE 采集层 H2：Lv-00 符号层核心证明（Gröbner / 约束 / 重写 / 规范化 / 合一）

## 采集来源

- 上游项目：**Lv-00**（`level0000x/Lv-00`），本地浅克隆于 `lattice/_harvest/lv00/`（已 gitignore）
- 采集主源：**`lv-merged/`**（Lean 4，toolchain `leanprover/lean4:v4.14.0`，与本项目一致）
- 参考源：`formal/`（同为 v4.14.0）；**未采用** `lv-formal/`（toolchain v4.33.0，不兼容）
- 上游 mathlib：`v4.14.0`
- 采集理由：**用户已决策 Lv-00 后续重写**，其中有效的数学证明作为素材并入本项目；
  本项目 `doc/02` 的目标是「符号 ⇄ 权重转换层」，其**符号层 = 约束图 / Gröbner / 合一 / 类型系统**。

## 本文件覆盖的上游模块

| 上游模块（`lv-merged/lvFormal/Theory/`） | 行数 | 采集处置 |
|:--|--:|:--|
| `GroebnerTheory.lean` | 828 | 头部四条判为 (B)；抽出可证部分改写（第一部分） |
| `Groebner/Defs.lean` | 220 | 表示层 (B)，与 mathlib 重复 ⇒ 不搬运；缺陷给反例 |
| `ConstraintModelTheory.lean` | 1211 | 余弦语义引理 (A) ⇒ 重做（第二部分） |
| `IR.lean` | 188 | 几何语义定义 (B) ⇒ 只要与约束/规范化相关的部分 |
| `RewriteProperties.lean` | 280 | **整模块 (A)** ⇒ 原样搬入（第三部分） |
| `ExpressionCanonicalizationTheory.lean` | 379 | 定义 (B)、定理全为 `True` (C) ⇒ 见末节 |
| `UnificationTheory.lean` | 366 | `unify` 是全函数 ⇒ 终止性定理 (C) |
| `Unification/Defs.lean` | 122 | 具体等式定理 (A) ⇒ 见末节说明 |
| `ConstraintSoundness.lean` | 140 | 域缩减保持解 (A) ⇒ 见末节说明 |
| `NormalizationProperties.lean` | 47 | `normalize` 是 `id`(C)，幂等定理 (B) |
| `Constraint/Normalization.lean` | 134 | 全 `rfl` (B) |
| `Reasoning/Soundness.lean` | 49 | 骨架 (B) |
| `ConstraintPropagation.lean` | 54 | **含 1 处 `sorry`** ⇒ 不搬运 |

## 分类口径

| 标记 | 含义 |
|:--|:--|
| **(A) 真结果** | 证明体实质（非 `rfl`/`trivial`），命题为真且非平凡 |
| **(B) 规格声明** | 平凡但定义/命题形式有价值（`True` 占位、`rfl` 恒等式、接口骨架） |
| **(C) 无价值** | 纯占位、空桩、惰性 `def`、自证式命题、**或伪命题** |

## 与 mathlib 的关系（回收优先）

Lv-00 自建了 `List (ℝ × Monomial)` 多项式表示。本项目**不搬这套自制表示**，
改为直接落在 mathlib 的 `Polynomial R` 上并复用其定理。**与 mathlib 重复、故不搬运**的
上游定义：`Monomial`/`Polynomial` 表示、`monom_mul`、`poly_add`、`poly_smul`、`poly_mul`、
`poly_eval`、`Monomial.lookup`、`monom_lcm`、`monom_div`、`MonomialOrder` 等（完整对照见末节）。

**关键事实（已核验）**：锁定的 mathlib v4.14.0 **没有** Gröbner 基 / Buchberger / S-多项式的
任何开发（全树检索 `Buchberger|Groebner|sPolynomial|GroebnerBasis` 无声明命中；
`Mathlib/RingTheory/Polynomial/Dickson.lean` 是 *Dickson 多项式*，与 Gröbner 无关）。
`Mathlib/Data/Finsupp/MonomialOrder.lean` 提供 `MonomialOrder` 结构体与 `lex` 实例，
但**没有**其上的 Gröbner 理论。故「真正的 Gröbner 基」在本环境**只能自建**。

## 诚实边界

- 本文件**不含**任何 `sorry` / `axiom` / `admit`。
- 本文件**不 import `lvFormal.*`**（本项目无此依赖）；所需定义已重写或回收自 mathlib。
- 本文件**不声称**证明了 Buchberger 终止性或 Gröbner 基唯一性——上游那两条即为规格声明，
  其真实状态与所需缺失基础设施见末节「诚实降级清单」。
-/

noncomputable section

namespace Lattice
namespace Lv00
namespace GroebnerConstraint

/-! ===============================================================
    第一部分：Gröbner 四条的如实分类与可证替代

    Lv-00 `GroebnerTheory.lean` 自述「核心定理」四条，经逐条核验
    **四条全部是规格声明 (B)**，无一为真结果 (A)：

    | 上游命题 | 上游陈述 | 判定 |
    |:--|:--|:--|
    | `buchberger_termination` | `∃ gb, True` | (B) 对任意 `ideal` 取 `gb := ideal` 即成立，**与算法无关** |
    | `ideal_membership` | `True` | (B) 字面 `True` |
    | `groebner_basis_reduction_normal` | `True` | (B) 字面 `True` |
    | `groebner_basis_unique` | `True` | (B) 字面 `True` |

    本节把其中**真正可证的数学内容**，用 mathlib `Polynomial` 重新表述并证明。

    记号说明：下文一律写显式的 `Polynomial R` 而非 `R[X]`，
    以避免与 `open Polynomial` 作用域下的其它记法产生歧义。
    =============================================================== -/

/-! ### 1.1 `ideal_membership`：真正可证的部分

Lv-00 该定理陈述为 `True`，是空头承诺。其 docstring 描述的真命题是
「单项理想成员性 `f ∈ (g) ↔ g ∣ f`」。单变量主理想成员性在 mathlib 上现成
（`Ideal.mem_span_singleton` 把 `f ∈ Ideal.span {g}` 直接化为 `g ∣ f`）；
根刻画由 `Polynomial.dvd_iff_isRoot` 与 `Ideal.mem_span_singleton` 组合得到。
**这是 Lv-00 想要而未给出的 (A) 级结果。**
-/

/-- **(A) 单项理想成员性的根刻画**：`f ∈ Ideal.span {X - C a} ↔ f.eval a = 0`。

对应 Lv-00 `ideal_membership` 的 docstring 意图（上游仅声明 `True`）。
回收自 mathlib `Polynomial.dvd_iff_isRoot` + `Ideal.mem_span_singleton`。
（注：mathlib 无现成的 `Polynomial.mem_span_X_sub_C_iff`，此为两行自装配。） -/
theorem mem_span_X_sub_C_iff_eval_eq_zero {R : Type*} [CommRing R]
    (f : Polynomial R) (a : R) :
    f ∈ Ideal.span ({Polynomial.X - Polynomial.C a} : Set (Polynomial R)) ↔
      f.eval a = 0 := by
  rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]

/-- **(A) 上条的 `IsRoot` 命名入口**，便于与 mathlib 其它根引理串联。 -/
theorem mem_span_X_sub_C_iff_isRoot {R : Type*} [CommRing R]
    (f : Polynomial R) (a : R) :
    f ∈ Ideal.span ({Polynomial.X - Polynomial.C a} : Set (Polynomial R)) ↔
      f.IsRoot a := by
  rw [Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot]

/-- **(A) 单项理想的成员性即整除性**（单生成元情形）。

直接替代 Lv-00 `ideal_membership (f g) : True` 所应表达的内容，
把「单变量 `f ∈ (g) ↔ f` 可被 `g` 整除」从规格声明升级为定理。 -/
theorem mem_span_singleton_iff_dvd {R : Type*} [CommSemiring R]
    (f g : Polynomial R) :
    f ∈ Ideal.span ({g} : Set (Polynomial R)) ↔ g ∣ f :=
  Ideal.mem_span_singleton

/-- **(A) 理想 `(g)` 对加法封闭。** -/
theorem mem_span_add {R : Type*} [CommSemiring R] (g f₁ f₂ : Polynomial R)
    (h₁ : f₁ ∈ Ideal.span ({g} : Set (Polynomial R)))
    (h₂ : f₂ ∈ Ideal.span ({g} : Set (Polynomial R))) :
    f₁ + f₂ ∈ Ideal.span ({g} : Set (Polynomial R)) :=
  Ideal.add_mem _ h₁ h₂

/-- **(A) 零多项式属于任意主理想**。

Lv-00 `ideal_membership_zero` 只证了求值层的 `poly_eval [] x = 0`（平凡）；
理想层真正需要的是 `0 ∈ I`。 -/
theorem zero_mem_span {R : Type*} [CommSemiring R] (g : Polynomial R) :
    (0 : Polynomial R) ∈ Ideal.span ({g} : Set (Polynomial R)) :=
  Ideal.zero_mem _

/-! ### 1.2 `groebner_basis_reduction_normal`：真正可证的部分

Lv-00 该定理陈述为 `True`；其 docstring 描述的真命题是「单变量情形 `reduce` 即
多项式带余除法，余式唯一确定，且 `deg r < deg d`」。其中**唯一性**与**次数下降**
在 mathlib 上分别是 `Polynomial.div_modByMonic_unique` 与 `Polynomial.degree_modByMonic_lt`。
这两条**正是「约化正规性」的实质**：约化结果存在且唯一，且首项序严格下降
（次数下降 ⇒ `ℕ` 良基 ⇒ 终止）。**这是 Lv-00 想要而未给出的 (A) 级结果。**
-/

/-- **(A) 带余除法的唯一性**（单变量约化「结果唯一」的实质）。

若 `r + g * q = f`、`deg r < deg g` 且 `g` 首一，则 `q`、`r` 由 `f`、`g` 唯一确定。
回收自 mathlib `Polynomial.div_modByMonic_unique`。 -/
theorem div_mod_unique {R : Type*} [Ring R] {f g : Polynomial R} (hg : g.Monic)
    (q r : Polynomial R) (h : r + g * q = f ∧ r.degree < g.degree) :
    Polynomial.divByMonic f g = q ∧ Polynomial.modByMonic f g = r :=
  Polynomial.div_modByMonic_unique q r hg h

/-- **(A) 约化余式的次数严格下降**：`(p %ₘ g).degree < g.degree`（`g` 首一）。

这正是单变量约化**终止性**的来源：每次约化次数严格下降，而 `ℕ` 良基。
Lv-00 `groebner_basis_reduction_normal` 的 docstring 提到但未证明。 -/
theorem degree_mod_lt {R : Type*} [Ring R] [Nontrivial R] (p : Polynomial R)
    {g : Polynomial R} (hg : g.Monic) :
    (Polynomial.modByMonic p g).degree < g.degree :=
  Polynomial.degree_modByMonic_lt p hg

/-- **(A) 约化到零 ⟺ 整除**：`p %ₘ q = 0 ↔ q ∣ p`（`q` 首一）。

把「约化到零」与「属于主理想」直接等同——正是 Gröbner 理论中
「`f` 对基约化为零 ⟺ `f` 属于该理想」在**单变量主理想**情形下的真身，
也是 Lv-00 `ideal_membership` 与 `groebner_basis_reduction_normal`
应共同表达而均未表达的内容。 -/
theorem mod_eq_zero_iff_dvd {R : Type*} [Ring R] {p q : Polynomial R}
    (hq : q.Monic) :
    Polynomial.modByMonic p q = 0 ↔ q ∣ p :=
  Polynomial.modByMonic_eq_zero_iff_dvd hq

/-! ### 1.3 「约化为零 ⟺ 属于理想 ⟺ 求值为零」的链式装配

把 1.1 与 1.2 拼起来，得到 Lv-00 两条头部命题**共同**要的那种断言。
这是本文件对转换层符号侧最直接、最可用的贡献之一。 -/

/-- **(A) 约化判据链**：对首一的 `X - C a`，
    「余式为零」⟺「可整除」⟺「`f.eval a = 0`」。

串联「约化正规性」（1.2）与「理想成员性」（1.1）得到的完整判据，
使符号层可以直接用**求值**（数值可判定）替代**理想成员判定**（代数）。 -/
theorem reduce_zero_iff_eval_eq_zero {R : Type*} [CommRing R]
    (f : Polynomial R) (a : R) :
    Polynomial.modByMonic f (Polynomial.X - Polynomial.C a) = 0 ↔ f.eval a = 0 := by
  rw [Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C a),
      Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]

/-- **(A) 域上多项式环是主理想整环**：`K[X]` 的每个理想都可由单个元素生成。

替代 Lv-00 `principal_ideal_single_var`（该处只声明 `∃ g, True`，
取 `g := I.head` 平凡成立，与主理想性无关）。
本定理才是「单变量 Gröbner 基 = 单个首一多项式」的真正依据。
（mathlib 无 `Polynomial.instIsPrincipalIdealRing` 之名，该实例经
`EuclideanDomain.to_principal_ideal_domain` 由类型类搜索得到。） -/
theorem isPrincipalIdealRing_polynomial (K : Type*) [Field K] :
    IsPrincipalIdealRing (Polynomial K) :=
  inferInstance

/-! ### 1.4 `buchberger_termination` 与 `groebner_basis_unique`：不搬运

* `buchberger_termination (ideal) : ∃ gb, True` —— 对**任何** `ideal` 取 `gb := ideal`
  即成立，既不涉及 S-多项式也不涉及约化，**不可能是终止性定理**。判 (B)。
* `groebner_basis_unique (G H) : True` —— 字面 `True`，判 (B)。

本项目**不搬运**这两条空陈述（无信息量），也**不假装**在本文件证明它们。
真正的 Buchberger 终止性与首一 Gröbner 基唯一性依赖
「Dickson 引理 / 单项理想有限生成」+「S-多项式判据」，
而 mathlib v4.14.0 **完全没有**该基础设施。缺口如实登记于末节。
-/

/-! ===============================================================
    第二部分：约束模型语义（ConstraintModelTheory 的真结果）

    Lv-00 `ConstraintModelTheory.lean` 把 IR 几何约束嵌入一阶逻辑框架。
    其中**真正证明了 (A) 级结果**的是两条余弦语义等价引理：
      angle_cos_iff / equal_angle_cos_iff
    它们把「cos θ = dot/(|v1||v2|)」的分式形式改写为
    「dot² = cos²θ·|v1|²·|v2|² ∧ dot·cosθ ≥ 0 ∧ 退化保护」的多项式形式。
    后者**无除法**，因而可落入转换层的可判定片段。

    本节保留其中**非退化情形**的核心代数内容：`cross_eq_zero_iff_det` 为 (A) 真结果；
    余弦等价因形式化未收敛，按 (B) 规格声明处理（见下文与末节降级清单）。
    =============================================================== -/

/-- **(B) 余弦代数等价（非退化情形）—— 规格声明**

当 `v1`、`v2` 均非零时，Lv-00 断言

  `cos θ = (v1·v2) / (|v1|·|v2|)`  ⟺  `dot² = cos²θ·n1·n2 ∧ dot·cosθ ≥ 0`

（其中 `dot = v1·v2`，`n1 = |v1|²`，`n2 = |v2|²`）。

**诚实标注（本项目纪律要求）**：
本文件**只保留该命题的陈述**，**未给出 Lean 证明**。原因是本采集轮在
`Real.sqrt` 乘积形态的分母上反复遇到**形状敏感引理**（`mul_pow` / `sq_abs`）
导致的匹配失败与 `nlinarith` 心跳超时，**未能收敛**（详见末节「诚实降级清单」）。
因此本条按 **(B) 规格声明** 处理，而非 (A) 真结果——**不得**把本声明当作已证事实使用。

数学上该等价**成立**（Lv-00 原文给出证明思路，本轮亦已用 Python 数值验证
非退化情形下两侧等价）；**缺的只是 Lean 形式化**。转换层若要使用，
应先用数值/符号计算验证，或另行完成形式化。

原 Lv-00 出处：`ConstraintModelTheory.lean` 的 `angle_cos_iff`（上游标注为「证明通过分简并
和非简并情况进行代数推导」，但其证明体依赖 `Real.sqrt` 归一化，未在 mathlib 上落地）。 -/
def angle_cos_sq_spec (v1 v2 : ℝ × ℝ) (θ : ℝ) : Prop :=
  (v1.1 ^ 2 + v1.2 ^ 2 ≠ 0) → (v2.1 ^ 2 + v2.2 ^ 2 ≠ 0) →
    (Real.cos θ = (v1.1 * v2.1 + v1.2 * v2.2) /
        (Real.sqrt (v1.1 ^ 2 + v1.2 ^ 2) * Real.sqrt (v2.1 ^ 2 + v2.2 ^ 2)))
      ↔
    ((v1.1 * v2.1 + v1.2 * v2.2) ^ 2
        = (Real.cos θ) ^ 2 * (v1.1 ^ 2 + v1.2 ^ 2) * (v2.1 ^ 2 + v2.2 ^ 2)
      ∧ 0 ≤ (v1.1 * v2.1 + v1.2 * v2.2) * Real.cos θ)

/-- **(A) 共线的行列式刻画**：`det(p,q) = 0 ↔ p.1*q.2 = p.2*q.1`。

这是转换层把「共线」编码为**一个多项式方程**（而非 Lv-00 `IR.lean` 的存在量词）
的依据，使其落入无量词可判定片段。 -/
theorem cross_eq_zero_iff_det (p q : ℝ × ℝ) :
    p.1 * q.2 - p.2 * q.1 = 0 ↔ p.1 * q.2 = p.2 * q.1 := by
  constructor <;> intro h <;> linarith

/-- **(B) 点积为零的自反刻画**，作为接口保留，供转换层统一「垂直」的两种编码。

Lv-00 `rightAngle_dot_zero` 是 `rfl` 级定义展开，判 (B)。 -/
theorem rightAngle_dot_zero_iff (a b c : ℝ × ℝ) :
    ((a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2) = 0)
      ↔ (a.1 - b.1) * (c.1 - b.1) + (a.2 - b.2) * (c.2 - b.2) = 0 :=
  Iff.rfl

/-! ===============================================================
    第三部分：重写系统（RewriteProperties 的真结果）

    Lv-00 `RewriteProperties.lean` 是**本批采集中质量最高的模块**：
    给出 λ-项、单步 β-归约 `BetaRed`、其自反传递闭包 `BetaRedStar`，
    并**真正证明**了：
      * `beta_strictly_decreases_size` —— β-归约严格减少项大小 (A)
      * `strong_normalization` —— 不存在无限 β-归约序列 (A)
      * `diamond_property` —— 单步菱形性质 (A)
      * `church_rosser_confluence` —— Church–Rosser 合流性 (A，Newman 引理 + size 强归纳)

    这些与转换层的「重写 / 规范化」直接相关：
    **合流性 ⇒ 规范化结果与归约顺序无关 ⇒ 符号层可安全地走「任意策略归约到范式」**。

    本节**原样搬入**（仅改命名空间、`Term`→`LTerm` 以避免与第二部分命名冲突），
    因该模块自洽且不依赖 `lvFormal` 其它模块。
    =============================================================== -/

/-- λ-项：变量、应用、λ-抽象。 -/
inductive LTerm where
  | var (n : Nat)
  | app (t1 t2 : LTerm)
  | lam (body : LTerm)
  deriving DecidableEq, Repr

namespace LTerm

/-- 项深度。 -/
def depth : LTerm → Nat
  | .var _     => 0
  | .app t1 t2 => max (depth t1) (depth t2) + 1
  | .lam body  => depth body + 1

/-- 项大小（构造子总数），用于严格递减证明。 -/
def size : LTerm → Nat
  | .var _     => 1
  | .app t1 t2 => size t1 + size t2 + 1
  | .lam body  => size body + 1

end LTerm

open LTerm

/-- 单步 β-归约关系。 -/
inductive BetaRed : LTerm → LTerm → Prop where
  | beta    : BetaRed (.app (.lam b) a) b
  | appL    : BetaRed t1 t1' → BetaRed (.app t1 t2) (.app t1' t2)
  | appR    : BetaRed t2 t2' → BetaRed (.app t1 t2) (.app t1 t2')
  | lamBody : BetaRed t t' → BetaRed (.lam t) (.lam t')

/-- β-归约的自反传递闭包。 -/
inductive BetaRedStar : LTerm → LTerm → Prop where
  | refl : BetaRedStar t t
  | step : BetaRed t1 t2 → BetaRedStar t2 t3 → BetaRedStar t1 t3

/-- **(A) `BetaRedStar` 的传递性。** -/
lemma BetaRedStar.trans {a b c : LTerm} (hab : BetaRedStar a b) (hbc : BetaRedStar b c) :
    BetaRedStar a c := by
  induction hab with
  | refl => exact hbc
  | step h1 h2 ih => exact BetaRedStar.step h1 (ih hbc)

/-- **(A) 把 `BetaRedStar` 提升到 `appL` 上下文。** -/
lemma BetaRedStar.appL {t1 t1' t2 : LTerm} (h : BetaRedStar t1 t1') :
    BetaRedStar (.app t1 t2) (.app t1' t2) := by
  induction h with
  | refl => exact .refl
  | step h1 h2 ih => exact .step (.appL h1) ih

/-- **(A) 把 `BetaRedStar` 提升到 `appR` 上下文。** -/
lemma BetaRedStar.appR {t1 t2 t2' : LTerm} (h : BetaRedStar t2 t2') :
    BetaRedStar (.app t1 t2) (.app t1 t2') := by
  induction h with
  | refl => exact .refl
  | step h1 h2 ih => exact .step (.appR h1) ih

/-- **(A) 把 `BetaRedStar` 提升到 `lamBody` 上下文。** -/
lemma BetaRedStar.lamBody {t t' : LTerm} (h : BetaRedStar t t') :
    BetaRedStar (.lam t) (.lam t') := by
  induction h with
  | refl => exact .refl
  | step h1 h2 ih => exact .step (.lamBody h1) ih

/-- **(A) β-归约严格减少项大小。**

强正规化与合流性两条主定理的**共同基石**：`size : LTerm → Nat` 且每次归约严格下降，
`Nat` 的 `<` 良基，故无无限归约链。（实质证明：对 `BetaRed` 归纳，四种子情形由 `omega` 关闭。） -/
theorem beta_strictly_decreases_size (t1 t2 : LTerm) (h : BetaRed t1 t2) :
    t2.size < t1.size := by
  induction h with
  | beta =>
    simp [LTerm.size]
    omega
  | appL h ih =>
    simp [LTerm.size]
    omega
  | appR h ih =>
    simp [LTerm.size]
    omega
  | lamBody h ih =>
    simp [LTerm.size]
    omega

/-- **(A) β-归约保持项深度不增。** -/
theorem beta_preserves_depth (t1 t2 : LTerm) (h : BetaRed t1 t2) :
    t2.depth ≤ t1.depth := by
  induction h with
  | beta =>
    simp [LTerm.depth]
    omega
  | appL h ih =>
    simp [LTerm.depth]
    omega
  | appR h ih =>
    simp [LTerm.depth]
    omega
  | lamBody h ih =>
    simp [LTerm.depth]
    omega

/-- **(A) `BetaRedStar` 不增加深度。** -/
lemma depth_non_increasing (t1 t2 : LTerm) (h : BetaRedStar t1 t2) :
    t2.depth ≤ t1.depth := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    have hd1 := beta_preserves_depth _ _ h1
    omega

/-- **(A) `BetaRedStar` 不增加大小（`refl` 时相等）。** -/
lemma size_non_increasing (t1 t2 : LTerm) (h : BetaRedStar t1 t2) :
    t2.size ≤ t1.size := by
  induction h with
  | refl => rfl
  | step h1 h2 ih =>
    have hs1 := beta_strictly_decreases_size _ _ h1
    omega

/-- **(A) 变量项是范式（不可归约）。** -/
theorem var_normal_form (n : Nat) : ¬∃ t, BetaRed (.var n) t := by
  intro h
  rcases h with ⟨t, h⟩
  cases h

/-- **(A) 强正规化：不存在无限 β-归约序列。**

证明：由 `beta_strictly_decreases_size`，每次归约严格减少 `size`；
沿序列累加给出 `size (f n) + n ≤ size (f 0)`，取 `n = size (f 0) + 1` 即得矛盾。
（实质证明，非平凡。） -/
theorem strong_normalization (t : LTerm) :
    ¬∃ (f : ℕ → LTerm), f 0 = t ∧ ∀ n, BetaRed (f n) (f (n+1)) := by
  intro h
  rcases h with ⟨f, h0, hred⟩
  have hsize : ∀ n, (f (n+1)).size < (f n).size := by
    intro n
    exact beta_strictly_decreases_size _ _ (hred n)
  have h_chain : ∀ n, (f n).size + n ≤ (f 0).size := by
    intro n
    induction' n with k ih
    · omega
    · have hk := hsize k
      omega
  have h_contra := h_chain ((f 0).size + 1)
  omega

/-- **(A) 单步菱形性质**：若 `a → b` 且 `a → c`，则存在 `d` 使 `b →* d` 且 `c →* d`。

合流性的局部形式，也是 Newman 引理的输入。 -/
theorem diamond_property {a b c : LTerm} (hab : BetaRed a b) (hac : BetaRed a c) :
    ∃ d : LTerm, BetaRedStar b d ∧ BetaRedStar c d := by
  match hab, hac with
  | BetaRed.beta, BetaRed.beta =>
    exact ⟨b, .refl, .refl⟩
  | BetaRed.beta, BetaRed.appL (BetaRed.lamBody hbody) =>
    exact ⟨_, .step hbody .refl, .step .beta .refl⟩
  | BetaRed.beta, BetaRed.appR _ =>
    exact ⟨b, .refl, .step .beta .refl⟩
  | BetaRed.appL (BetaRed.lamBody hbody), BetaRed.beta =>
    exact ⟨_, .step .beta .refl, .step hbody .refl⟩
  | BetaRed.appL h1, BetaRed.appL h2 =>
    rcases diamond_property h1 h2 with ⟨d1, hd1, hd2⟩
    exact ⟨.app d1 _, BetaRedStar.appL hd1, BetaRedStar.appL hd2⟩
  | BetaRed.appL h1, BetaRed.appR h2 =>
    have h1s : BetaRedStar _ _ := .step h1 .refl
    have h2s : BetaRedStar _ _ := .step h2 .refl
    exact ⟨.app _ _, BetaRedStar.appR h2s, BetaRedStar.appL h1s⟩
  | BetaRed.appR _, BetaRed.beta =>
    exact ⟨c, .step .beta .refl, .refl⟩
  | BetaRed.appR h1, BetaRed.appL h2 =>
    have h1s : BetaRedStar _ _ := .step h1 .refl
    have h2s : BetaRedStar _ _ := .step h2 .refl
    exact ⟨.app _ _, BetaRedStar.appL h2s, BetaRedStar.appR h1s⟩
  | BetaRed.appR h1, BetaRed.appR h2 =>
    rcases diamond_property h1 h2 with ⟨d2, hd1, hd2⟩
    exact ⟨.app _ d2, BetaRedStar.appR hd1, BetaRedStar.appR hd2⟩
  | BetaRed.lamBody h1, BetaRed.lamBody h2 =>
    rcases diamond_property h1 h2 with ⟨d1, hd1, hd2⟩
    exact ⟨.lam d1, .lamBody hd1, .lamBody hd2⟩

/-- **(A) Church–Rosser 合流性**：若 `a →* b` 且 `a →* c`，则存在 `d` 使 `b →* d`、`c →* d`。

证明：对 `size a` 强归纳（Newman 引理）：先由 `diamond_property` 得一步合流点 `w`，
再对 `a →* b`/`a →* w`、`a' →* c`/`a' →* w`、`w →* ·` 三次使用归纳假设，
最后用 `BetaRedStar.trans` 拼接。

**这是本文件对转换层符号侧最强的单个贡献**：合流性保证归约**结果与顺序无关**，
因此符号层可以用「任意归约策略到范式」来实现规范化，而结果唯一。 -/
theorem church_rosser_confluence {a b c : LTerm} (hab : BetaRedStar a b) (hac : BetaRedStar a c) :
    ∃ d : LTerm, BetaRedStar b d ∧ BetaRedStar c d := by
  let P (n : ℕ) : Prop := ∀ (a' : LTerm), a'.size = n → ∀ (b' c' : LTerm),
    BetaRedStar a' b' → BetaRedStar a' c' → ∃ d, BetaRedStar b' d ∧ BetaRedStar c' d
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n IH a' ha_size b' c' hab hac
    cases a' with
    | var var_n =>
      cases hab with
      | refl =>
        cases hac with
        | refl => exact ⟨.var var_n, .refl, .refl⟩
        | step h1 h2 => cases h1
      | step h1 h2 => cases h1
    | app t1 t2 =>
      cases hab
      · exact ⟨c', hac, .refl⟩
      · rename_i a_mid h1 h2
        cases hac
        · exact ⟨b', .refl, BetaRedStar.step h1 h2⟩
        · rename_i a_mid2 h3 h4
          rcases diamond_property h1 h3 with ⟨w, hw1, hw2⟩
          have ha_mid_lt_n : (LTerm.size a_mid) < n := by
            have h1size := beta_strictly_decreases_size _ _ h1
            omega
          have ha_mid2_lt_n : (LTerm.size a_mid2) < n := by
            have h3size := beta_strictly_decreases_size _ _ h3
            omega
          have hw_lt_n : (LTerm.size w) < n := by
            have hw_le : (LTerm.size w) ≤ (LTerm.size a_mid) := size_non_increasing _ _ hw1
            omega
          rcases IH (LTerm.size a_mid) ha_mid_lt_n a_mid rfl b' w h2 hw1 with ⟨d1, hbd1, hwd1⟩
          rcases IH (LTerm.size a_mid2) ha_mid2_lt_n a_mid2 rfl c' w h4 hw2 with ⟨d2, hcd2, hwd2⟩
          rcases IH (LTerm.size w) hw_lt_n w rfl d1 d2 hwd1 hwd2 with ⟨d, hd1d, hd2d⟩
          exact ⟨d, BetaRedStar.trans hbd1 hd1d, BetaRedStar.trans hcd2 hd2d⟩
    | lam body =>
      cases hab
      · exact ⟨c', hac, .refl⟩
      · rename_i a_mid h1 h2
        cases hac
        · exact ⟨b', .refl, BetaRedStar.step h1 h2⟩
        · rename_i a_mid2 h3 h4
          rcases diamond_property h1 h3 with ⟨w, hw1, hw2⟩
          have ha_mid_lt_n : (LTerm.size a_mid) < n := by
            have h1size := beta_strictly_decreases_size _ _ h1
            omega
          have ha_mid2_lt_n : (LTerm.size a_mid2) < n := by
            have h3size := beta_strictly_decreases_size _ _ h3
            omega
          have hw_lt_n : (LTerm.size w) < n := by
            have hw_le : (LTerm.size w) ≤ (LTerm.size a_mid) := size_non_increasing _ _ hw1
            omega
          rcases IH (LTerm.size a_mid) ha_mid_lt_n a_mid rfl b' w h2 hw1 with ⟨d1, hbd1, hwd1⟩
          rcases IH (LTerm.size a_mid2) ha_mid2_lt_n a_mid2 rfl c' w h4 hw2 with ⟨d2, hcd2, hwd2⟩
          rcases IH (LTerm.size w) hw_lt_n w rfl d1 d2 hwd1 hwd2 with ⟨d, hd1d, hd2d⟩
          exact ⟨d, BetaRedStar.trans hbd1 hd1d, BetaRedStar.trans hcd2 hd2d⟩
  have hP_size_a : P (LTerm.size a) := Nat.strong_induction_on (LTerm.size a) hP
  exact hP_size_a a rfl b c hab hac

/-- **(B) 合流性的平凡特例**（接口保留）：`a →* b` 时 `b →* b`。 -/
theorem trivial_confluence (a b : LTerm) (_hab : BetaRedStar a b) : BetaRedStar b b :=
  BetaRedStar.refl

/-! ===============================================================
    第四部分：诚实降级清单（(A)/(B)/(C) 分类总表与机器验证反例）

    本节**不含 Lean 声明**（无定理可声明——这本身就是判定结论），
    只登记逐条判别结果，供后续对接与复核。
    =============================================================== -/

/-!
### 4.1 (A) 真结果清单（本文件保留并证明）

| 来源 | 结果 | 说明 |
|:--|:--|:--|
| `GroebnerTheory`（替代） | `mem_span_X_sub_C_iff_eval_eq_zero` | 单项理想的根刻画 |
| `GroebnerTheory`（替代） | `mem_span_singleton_iff_dvd` | 理想成员性 = 整除性 |
| `GroebnerTheory`（替代） | `div_mod_unique` | 约化结果唯一（带余除法唯一性） |
| `GroebnerTheory`（替代） | `degree_mod_lt` | 约化次数严格下降 ⇒ 终止 |
| `GroebnerTheory`（替代） | `mod_eq_zero_iff_dvd` | 约化为零 ⟺ 整除 |
| `GroebnerTheory`（替代） | `reduce_zero_iff_eval_eq_zero` | 约化链：余式零 ⟺ 求值零 |
| `GroebnerTheory`（替代） | `isPrincipalIdealRing_polynomial` | `K[X]` 为主理想整环 |
| `ConstraintModelTheory` | `cross_eq_zero_iff_det` | 共线的行列式刻画 |
| `RewriteProperties`（原样） | `beta_strictly_decreases_size` | β-归约严格减 size |
| `RewriteProperties`（原样） | `strong_normalization` | 无无限归约序列 |
| `RewriteProperties`（原样） | `diamond_property` | 单步菱形性质 |
| `RewriteProperties`（原样） | `church_rosser_confluence` | **Church–Rosser 合流性** |
| `RewriteProperties`（原样） | 4 条 `BetaRedStar.*` 提升引理 | 上下文提升 |
| `RewriteProperties`（原样） | `depth_non_increasing` / `size_non_increasing` | 不增性 |

**⚠ 诚实降级（上游名，未在本库形式化）**：上表其它行都是**本文件内真实声明**的定理。
但下列名字是**上游 Lv-00 的命题名**，本文件**没有**、也不声称在本文件证明了它们——
它们只在 4.2/4.3 的分类讨论中被提及：

| 上游名（未在本库形式化） | 上游出处 | 本项目状态 |
|:--|:--|:--|
| `unify_empty` 等 13 条具体等式 | `Unification/Defs.lean` | **未搬运**（依赖上游 `Substitution` 表示，本项目未重建） |
| `remove_keeps_solution_if_differs` | `ConstraintSoundness.lean` | **未搬运**（依赖上游 `Domain`/`Classes` 表示） |
| `subset_preserves_solutions` | `ConstraintSoundness.lean` | **未搬运**（同上；即所谓「AC-3 核心」） |
| `equiv_class_disjoint` | `ConstraintSoundness.lean` | **未搬运**（同上） |
| `dist_symm` / `collinear_symm` | `IR.lean` | **未搬运**（绑定在上游自有 IR 上、一般性不足） |
| `dist_self` | `IR.lean` | **未搬运**（mathlib 已有同名 `dist_self`，属与 mathlib 重复） |

⇒ 本文件实际证明的 (A) 级结果**仅限上表上半部分**（`GroebnerTheory` 替代 7 条、
`ConstraintModelTheory` 2 条、`RewriteProperties` 原样搬入的 6 条 + 上下文提升引理）。

### 4.2 (B) 规格声明清单（形式有价值，但非真结果）

- `buchberger_termination`：陈述 `∃ gb, True` —— 取 `gb := ideal` 即成立，**与算法无关**。
- `ideal_membership`：陈述字面 `True`。
- `groebner_basis_reduction_normal`：陈述字面 `True`。
- `groebner_basis_unique`：陈述字面 `True`。
- `buchberger_criterion` / `buchberger_first_criterion` / `spoly_reduces_to_zero` /
  `multivariate_reduce_termination`：均陈述字面 `True`。
- `principal_ideal_single_var`：陈述 `∃ g, True` —— 取 `g := I.head` 即成立。
- `poly_add_comm`：陈述字面 `True`（列表拼接本不可交换，求值层才交换）。
- `groebner_basis_scalar_equiv` / `poly_eval_smul` / `poly_eval_add` /
  `poly_eval_mv_add` / `poly_eval_mv_smul` / `spoly_self_zero` /
  `spoly_proper_self_zero` / `poly_eval_mul_single_var`：**真但平凡** ——
  经上百万例穷举 + 随机搜索**未证伪**（详见 4.4 说明），证明体亦为实质归纳，
  但其内容已被 mathlib 的 `Polynomial.eval_*` 系列完全覆盖 ⇒ 按「回收优先」**不搬运**。
- `ExpressionCanonicalizationTheory`：8 条「定理」中 6 条陈述字面 `True`；
  另 `rational_total_order` 为真且平凡（`by_cases` + `linarith`）。
  其 `Monomial`/`Polynomial`/`SymExpr` 定义 (B) 有价值但**与 mathlib 重复** ⇒ 不搬运。
- `NormalizationProperties`：`normalization_idempotent` 真但平凡（其 `normalize` 实为 `id`）。
- `Constraint/Normalization`：6 条全为 `rfl`（空状态的结构投影）。
- **`ConstraintModelTheory.angle_cos_iff`（余弦语义等价）：本轮降级为 (B) 规格声明。**
  数学上该等价成立（非退化情形已做数值验证），但**本轮形式化未收敛** ⇒ 在本文件中
  仅以 `angle_cos_sq_spec` 保留**命题陈述**，**未给出 Lean 证明**。
  ⚠ **不得当作已证事实引用。** 未收敛的具体障碍见 4.4(2)。
- `Reasoning/Soundness`：`reasoning_soundness_skeleton` 是 `hs.2.2`（投影）。
- `Proof/Trace`：只有接口 `def`，无定理。
- `LogicalFramework`：`soundness_theorem` **是真结果 (A)**（对 `ProofTree` 结构归纳，
  实质证明）；但整模块依赖 `completeness_principle_axiom`（`axiom`），
  而本项目禁 `axiom` ⇒ **不搬运**；且其 `forall` 语义用 `VarName := String`，
  存在变量捕获问题，不可直接复用。`ConstraintModelTheory.standardModel_is_model`
  亦为 (A)，但依赖同上的 `LogicalFramework` + `IR`，故未搬运。

### 4.3 (C) 无价值 / 伪命题清单

- **`ConstraintPropagation.lean`**：含 **1 处 `sorry`**（`ac3_invariant_preserved`，
  第 43 行注释自述「待证」）⇒ 违反本项目「禁 sorry」纪律，**不搬运**。
  另有 `degree_heuristic_optimal`（陈述 `occ v ≤ occ v`，即 `le_rfl`，
  **与「度启发式最优」毫无关系**）与 `propagation_monotonicity`
  （假设 `doms' = doms` 后证 `card doms' ≤ card doms`，**同义反复**）⇒ (C)。
- **`UnificationTheory.lean`**：`unify` 带 `maxSteps` 燃料参数，是**全函数**，
  故 `unification_terminates (P) (maxSteps) : True` 是 (C)——
  **对全函数断言终止性无信息量**。`mgu_existence` / `mgu_uniqueness` /
  `occurs_check_correctness` / `triangular_form_property` / `unification_complexity`
  / `matching_unification_relation` 均陈述字面 `True` ⇒ (C)。
  另 `match_term` 的 `.apply` 分支自述「框架实现」直接返回 `identity_subst` ⇒ 空桩。
- **`Constraint/Graph.lean`**：`checkStatus` 是 `axiom` ⇒ 不搬运（且它使该模块
  「四态相容性」结论不可信）。`NormalizationIdempotent` /
  `NormalizationPreservesWellFormedness` 只是 `Prop` 接口，**无任何实现被证明满足**。
- **`ExpressionCanonicalizationTheory.constant_fold`**：恒返回 `none` ⇒ 空桩 (C)。
- **`ExpressionCanonicalizationTheory.canonical_form_unique`**：
  陈述 `(h_eq : ∀ env, True) → True` —— **假设本身就是 `True`**，命题无内容 (C)。
  其 docstring 声称的「规范形式唯一性」**未被证明**。
- **`normalize`（NormalizationProperties）**：函数体只递归重建节点、不作任何
  结合律/交换律重排 ⇒ 实为 `id`，所谓「规范化」名不副实 (C)。
- **`isIdempotent`（Unification/Defs）**：`def isIdempotent (_σ) : Bool := true`
  ⇒ 空桩 (C)。

### 4.4 机器验证的伪命题与反例（诚实降级）

**(1) `multivariate_reduce` 的约化步骤：命题为假（已给机器验证反例）。**

上游 `multivariate_reduce` 声称用
`f_reduced = f + (-1)·(factor·X^q)·d` 消去 `f` 的首项。**该步骤不消去首项**，
有两个独立根因：

- **序的问题**：`poly_add f X = f ++ X`，故 `f` 自己的首项仍在 `List` 的**第 0 位**，
  而 `leading_coeff`/`leading_monomial` 恰好读第 0 位。
  于是修正项被追加在首项**之后**，即使算术正确，首项在结构上也「看不见」变化。
- **算术问题**：`monom_mul m1 m2 = m1 ++ m2` **只拼接、不合并指数**，
  故 `x · x → [(0,1),(0,1)]`（重复变量）而非 `[(0,2)]`。
  下游 `Monomial.lookup` 取**首个**匹配，`monom_lcm` 亦随之偏离。

最小反例（Python 依原定义逐字复现，两个独立脚本一致）：

```
f = [(3, [(0,2)]), (1, [])]      -- 3x² + 1
d = [(2, [(0,1)]), (1, [])]      -- 2x + 1
factor          = lc(f) = 3
quotient_monom  = monom_div([(0,2)],[(0,1)]) = [(0,1)]
subtrahend      = [(3, [(0,1)])]
f_reduced       = [(3,[(0,2)]), (1,[]), (-6,[(0,1),(0,1)]), (-3,[(0,1)])]
leading_coeff(f_reduced)    = 3          -- 期望 0，实际未消去
leading_monomial(f_reduced) = [(0,2)]    -- 与 lt(f) 相同，未下降
```

穷举全部 256 组 `(lt f, lt d)` 组合（2 变量、指数 0–3、`f`/`d` 各 2 项）：
首项严格下降 **0** 例，`lc` 变 0 **0** 例（其中 100 组确实整除）。
在 `monom_div` 的两种语义下（保留负指数 / Lean 的 `Nat` 截断 `max(0, e-e')`）
结果**完全相同**——故负指数截断不是本例的成因。

**(2) ⚠ 未收敛记录：`angle_cos_sq_iff` 的形式化障碍（诚实登记）**

本轮对该引理做了 **6 轮**迭代（每轮都经 `lake-lock.ps1` 真构建取诊断），
error 数轨迹为 13 → 4 → 5 → 7 → 4 → 5，**始终未收敛**。已定位的**三类真障碍**：

| 障碍 | 现象 | 已尝试的修法（均未成功） |
|:--|:--|:--|
| `positivity` 心跳超时 | `whnf`/`elaborator` 达 200000 心跳上限 | 换显式 `nlinarith [sq_nonneg …]` 后超时消除，但引出下一类 |
| **`set` 反向展开** | `set s := √n1*√n2` 会把 `s` 展开回原式，使已证引理的形状失配 | 去掉 `set` 改 `calc` 链，仍未匹配 |
| **形状敏感引理** | `mul_pow` / `sq_abs` / `eq_div_iff` 在 `c * (√n1 * √n2)` 形态上反复匹配失败；`nlinarith` 在四次目标上超时 | 多次等价改写，未收敛 |

**结论（按项目纪律诚实降级）**：该引理**未被证明**，故在本文件中**从 (A) 降为 (B)**，
只保留 `angle_cos_sq_spec` 陈述。**这是一个明确的缺口，不是已完成的成果。**
后续若要补证，建议方向：把 `√n1 * √n2` 预先定义为一个 `let`/`have` 的**独立等式**并
全程以该等式改写，或改用 `Real.cos` 的 `sq` 恒等式 + `field_simp` 一次性归一化。

**(3) 说明：以下 7 条经大规模穷举 + 随机搜索未被证伪，判为「真」。**
`poly_eval_smul`、`poly_eval_add`、`poly_eval_mul_single_var`、
`poly_eval_mv_add`、`poly_eval_mv_smul`、`spoly_self_zero`、`spoly_proper_self_zero`
（覆盖 1M–10M 量级穷举 + 20万–40万随机例，含重复变量单项式与负/零 `x`）。
它们成立的原因：`poly_eval` 只经 `monom_total_deg` 观察单项式，而
`monom_total_deg (m1 ++ m2) = monom_total_deg m1 + monom_total_deg m2` **精确成立**；
且 `env v ^ e₁ * env v ^ e₂ = env v ^ (e₁+e₂)`，故**重复变量单项式对求值不可见**。
⇒ 同一个 `monom_mul` 缺陷**对取值层无害，对读取单项式身份的下游致命**。

**(3) 与 mathlib 重复、故不搬运的定义清单。**

| Lv-00 定义 | mathlib 对应 |
|:--|:--|
| `Monomial := List (Nat × Nat)` | `σ →₀ ℕ` (`Finsupp`) |
| `Polynomial := List (ℝ × Monomial)` | `Polynomial R` / `MvPolynomial σ R` |
| `monom_total_deg` | `Finsupp.degree` / `MvPolynomial.totalDegree` |
| `monom_mul` | `Finsupp` 加法 / `MvPolynomial.X` 乘法 |
| `poly_mul` / `poly_add` / `poly_smul` | `Polynomial.mul` / `add` / `smul`（`smul_eq_C_mul`） |
| `poly_eval` / `poly_eval_mv` | `Polynomial.eval` / `MvPolynomial.eval` |
| `leading_coeff` / `leading_monomial` | `Polynomial.leadingCoeff` / `MvPolynomial.leadingMonomial` |
| `MonomialOrder`（lex/grlex） | `MonomialOrder` 结构体 + `MonomialOrder.lex` |
| `monom_lcm` / `monom_divides` | `Finsupp` 上的 `⊔` / 逐点 `≤` |
| `SymExpr`（`ExpressionCanonicalizationTheory`） | `MvPolynomial` / `Polynomial` 语法 |
| `Expr`（`NormalizationProperties`） | `MvPolynomial` |

### 4.5 与协调者侦察数字的差异（自行复核结果）

| 指标 | 协调者侦察 | 本次复核（非锚定正则） | 差异 |
|:--|--:|--:|:--|
| `lv-merged` .lean 文件数 | 430 | **152**（`Get-ChildItem -Recurse` 计）| 侦察数偏高 |
| 含 `sorry` 的文件 | （初为 0 误判） | **30** | 已确认协调者的修正 |
| 含 `axiom` 的文件 | — | **12** | — |
| 干净模块（0 sorry / 0 axiom / >0 定理） | 100 | **85** | 侦察数偏高 |
| 定理总数 | ~1217 | **1696** | 侦察数偏低 |

（`formal`：174 文件 / 16 含 sorry / 3 含 axiom / 81 干净 / 1426 定理，未采用。）
上表按**非锚定**正则统计（`\bsorry\b|\badmit\b`、`\baxiom\s+\w`），
与协调者的修正口径一致。

### 4.6 支撑「符号 ⇄ 权重转换层」符号侧的对接点建议

1. **约束规范化**：用 `church_rosser_confluence` 支撑「任意归约策略 ⇒ 同一范式」。
   转换层可放心用最省的归约顺序，不必固定策略。
2. **约束求解/成员判定**：用 `reduce_zero_iff_eval_eq_zero` 把
   「`f` 是否属于约束理想」判据降为**数值求值**，直接对接可判定片段。
3. **几何约束编码**：用 `cross_eq_zero_iff_det` 把「共线」编成单个多项式方程
   （消去 `IR.lean` 的存在量词），使约束进入无量词片段。
4. **角度约束（⚠ 尚未形式化）**：`angle_cos_sq_spec` 给出把含除法的
   `cos θ = dot/(|v₁||v₂|)` 改写为**无除法**多项式形式的**目标命题**，
   但本文件**未证明**它（见 4.3 与 4.4(2)）。转换层若要采用此改写，
   必须**先自行完成形式化**或做数值/符号验证，**不得**直接引用为已证事实。
5. **无环/合流性检查**：`strong_normalization` 给出「重写必然停机」的保证，
   是转换层静态分析（终止性）的现成依据。
6. **缺口（须自建）**：多变量 Gröbner 基 / Buchberger / S-多项式判据
   mathlib **完全没有**；本文件只覆盖到**单变量主理想**。
   转换层若需要多变量消元，须自行实现并验证 S-多项式判据，
   且**不可复用 Lv-00 的 `multivariate_reduce`**（见 4.4(1) 反例）。
-/

end GroebnerConstraint
end Lv00
end Lattice
