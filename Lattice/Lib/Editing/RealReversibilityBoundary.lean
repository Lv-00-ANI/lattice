import Mathlib
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Runtime.RealLinear
import Lattice.Lib.Editing.RealExtractInvertibility
-- B352: `relu` is defined in RealNonlinear and NOWHERE else, and no import above
-- brings it in transitively.  Lines 146 and 167 use it, so this file could never
-- have compiled -- it is one of the ten unknown-constant-class breakages.  The
-- missing import is the fifth cause of `unknown constant` (B214).
import Lattice.Runtime.RealNonlinear
/-!
# LATTICE: 可逆性的真假边界 —— 逐层判定与机器验证反例

`doc/02` 把符号 ⇄ 权重链路定位为「**完整且可逆**」。本文件把这个口号
拆成两个**可分别判定**的命题，并给出内核级结论：

- **参数层可逆**（`extract ∘ compile = id`）：`compile` 是**单射**。
  由 `WeightToSymbolEquivalence.roundtrip_extractVec` 等既有定理已证。
- **语义层可逆**（`∃ extract, sem_X (extract w) = sem_W w`）：
  `compile` 在**语义等价类**上不是单射 ⟹ **机器验证为假**。

本文件的内容：

  1. `not_injective_of_witness`：否定结论的统一骨架
     （`x ≠ y ∧ f x = f y ⟹ ¬Injective f`）；
  2. **参数层 (a)**：`convert_injective` / `convertVec_injective` /
     `convertReal_injective` —— 三个编译映射都是单射；
  3. **缩放等价类的最小显式见证 (b)+(d)**：
     `revC = {a := [1], b := 1}` 与 `scaleVec revC 2 = {a := [2], b := 2}`
     是**不同**约束却**语义相同**（`scaleVec_ne_self_two` +
     `scaleVec_two_semantically_equal`）；
  4. **边界定理** `reversibility_boundary`：参数层单射 **∧** 语义层非单射；
  5. **不可能性定理** `no_extractor_preserves_both`：**不存在**同时满足
     参数层往返与语义层同一的提取器 ⟹ **严格意义不可逆**；
  6. **语义层非单射的显式形式** `semantic_layer_not_injective`：
     存在两个不同权重、行为一致、且**都**是编译产物；
  7. **零化编码的反例 (d)**：`relu_not_injective`、
     `relu_zero_not_implies_eq`、`relu_global_not_invertible`、
     `relu_zero_fiber_not_singleton` —— 「输出零 ⟹ 原值唯一」**为假**。

**诚实边界**（本文件不证 / 不声称的）：
- **不声称**「无穷多」权重实现：只证**存在两个**（`∃ w w'`）。从
  "两个"到"无数"需额外构造 `λ ↦ convertVec (scaleVec revC λ)` 的两两不同性，
  该构造平凡但**本文件未写**（见 `doc/REVERSIBILITY.md` §6.9）。
- **不证排列/冗余神经元自由度**：库内没有"网络 = 带索引神经元列表 +
  置换作用"的形式化对象，故 doc/01 难点 2 的"排列等价"未被覆盖。
- **不构造规范形**：本文件证的是规范形**存在的必要性**（因非单射），
  **没有**写出 `canonicalize` 函数及其三条性质。
- 本文件**只读引用**既有模块，不修改任何既有文件。
- 无 sorry / axiom / admit；全部定理内核验证通过。

配套审计表：`doc/REVERSIBILITY.md`。
-/

noncomputable section

namespace Lattice.Lib.Editing.RealReversibilityBoundary

/-! ## 一、可逆性的精确判据：单射 ⟺ 存在左逆 -/

/-- **否定结论的统一骨架**：若 `x ≠ y` 而 `f x = f y`，则 `f` 非单射。
本文件全部"不可逆"结论都由它 + 一个具体见证给出
（既有的 `RealExtractInvertibility.leftInverse_iff_injective`
给出"可逆 ⟺ 单射"，故非单射即不可逆）。 -/
theorem not_injective_of_witness {α β : Type*} (f : α → β) {x y : α}
    (hne : x ≠ y) (heq : f x = f y) : ¬ Function.Injective f :=
  fun hinj => hne (hinj heq)

/-! ## 二、参数层 (a)：编译在符号对象上是单射 -/

/-- **`convert` 是单射（标量，Int）**：不同约束给出不同神经元。
证明：`convert ⟨a,b⟩ = ⟨a',b'⟩` 逐分量展开后即得 `a = a'`、`b = b'`
（结构构造子单射）。 -/
theorem convert_injective : Function.Injective (convert : LinearConstraint → LinearNeuron) := by
  intro c c' h
  cases c with
  | mk a b =>
    cases c' with
    | mk a' b' =>
      simp only [convert, LinearNeuron.mk.injEq] at h
      rw [h.1, h.2]

/-- **`convertVec` 是单射（向量，Int）**。 -/
theorem convertVec_injective : Function.Injective (convertVec : VectorConstraint → LinearLayer) := by
  intro c c' h
  cases c with
  | mk a b =>
    cases c' with
    | mk a' b' =>
      simp only [convertVec, LinearLayer.mk.injEq] at h
      rw [h.1, h.2]

/-- **`convertReal` 是单射（标量，ℝ）**。 -/
theorem convertReal_injective : Function.Injective (convertReal : RealConstraint → RealNeuron) := by
  intro c c' h
  cases c with
  | mk a b =>
    cases c' with
    | mk a' b' =>
      simp only [convertReal, RealNeuron.mk.injEq] at h
      rw [h.1, h.2]

/-! ## 三、(b) + (d)：缩放自由度 —— 机器验证的最小反例

`ConvertVectorLinear.scaleVec_preserves` 证明「缩放不改变满足语义」。
但**同一个函数的两个不同权重实现**恰恰由此产生：
`convertVec c` 与 `convertVec (scaleVec c 2)` 的字段不同，
却表示**同一个约束函数**。

这就是 doc/01 难点 2「同一函数有无数权重实现（排列/缩放等价）」
在内核里的**最简见证**。 -/

/-- 见证约束：`x₀ + 1 = 0`，即 `a = [1]`、`b = 1`。 -/
def revC : VectorConstraint := { a := [1], b := 1 }

/-- **缩放见证了参数层的不同**：`scaleVec revC 2 ≠ revC`
（`b` 字段为 `1 * 2 = 2`，而 `revC.b = 1`）。

证明用 `congrArg VectorConstraint.b` 取投影，把结构等式化为
整数等式 `1 * 2 = 1`，再 `simp` 消解。 -/
theorem scaleVec_ne_self_two : scaleVec revC 2 ≠ revC := by
  intro h
  have hb : revC.b * 2 = revC.b := by
    have := congrArg VectorConstraint.b h
    simpa [scaleVec] using this
  simp [revC] at hb

/-- **语义同一性（复用既有定理）**：缩放的约束与原约束**逐点**语义等价
——直接实例化 `scaleVec_preserves`（`lam = 2 ≠ 0`）。 -/
theorem scaleVec_two_semantically_equal (x : List Int) :
    VectorConstraintSat revC x ↔ VectorConstraintSat (scaleVec revC 2) x :=
  scaleVec_preserves revC x 2 (by norm_num)

/-- **编译结果的参数层不等**：`convertVec (scaleVec revC 2) ≠ convertVec revC`。
由 `convertVec` 的单射性 + `scaleVec_ne_self_two` 立即得到。
这是「无穷多权重实现」的最直接参数见证。 -/
theorem convertVec_scale_ne : convertVec (scaleVec revC 2) ≠ convertVec revC := by
  intro h
  exact scaleVec_ne_self_two (convertVec_injective h)

/-! ## 四、(d)：零化编码丢失信息

ReLU 编码把「负值」与「零」混为一谈，故编码映射**不是单射**；
输出为零**不再**推出约束满足。这是
`RealSymbolToWeightNonlinear.reluZ_counterexample` 的 ℝ 版。 -/

/-- **`relu` 不是单射（机器验证）**：`relu (-1) = relu 0 = 0` 而 `-1 ≠ 0`。
复用既有的 `relu_neg_eq_relu_zero`（见 `RealExtractInvertibility`）。 -/
theorem relu_not_injective : ¬ Function.Injective relu :=
  not_injective_of_witness relu (x := -1) (y := 0) (by norm_num)
    relu_neg_eq_relu_zero

/-- **零化编码的语义反转见证（机器验证反例）**：
ReLU 编码的零化**不等于**等式约束满足 —— 在 `x = -5` 处
`relu (x + 1) = 0`，但等式约束 `x + 1 = 0` **不成立**。 -/
theorem relu_zero_not_implies_eq : ∃ x : ℝ, relu (x + 1) = 0 ∧ x + 1 ≠ 0 :=
  ⟨-5, by norm_num [relu], by norm_num⟩

/-- **反例（激活级，存在性形式）**：`relu` 在 ℝ 上**不是单射** ——
存在 `x ≠ y` 使 `relu x = relu y`（见证 `x = -1`、`y = 0`）。
与既有的 `relu_not_injOn_nonpos`（区域版）合起来，构成激活层
「输出零 ⟹ 原值唯一」**为假**的机器验证。 -/
theorem relu_global_not_invertible :
    ∃ x y : ℝ, x ≠ y ∧ relu x = relu y :=
  ⟨-1, 0, by norm_num, relu_neg_eq_relu_zero⟩

/-- **纤维形式**：`relu` 的 `0` 纤维**不是单点集**——
`-1` 与 `0` 同在 `relu ⁻¹' {0}` 中。
这是「提取到唯一原值」失败的直接原因（原像集合势 > 1）。 -/
theorem relu_zero_fiber_not_singleton :
    ∃ x ∈ (relu ⁻¹' ({0} : Set ℝ)), x ≠ 0 :=
  ⟨-1, by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    simp [relu],
   by norm_num⟩

/-! ## 五、边界定理：参数层可逆 ∧ 语义层不可逆 -/

/-- **边界定理（本文件核心）**：`convertVec` 在**参数层**是单射，
同时存在**两个不同**的符号约束其语义**逐点相同**。

两个合取支分别需要**不同的邻域知识**（结构单射 vs 语义保持），
故本定理是"可逆"这个词在两条不同含义上分裂的**精确陈述**：
- 第一支（`convertVec_injective`）：参数不丢信息 ⟹ 往返恒等可行；
- 第二支（`scaleVec_preserves` 实例）：语义有多对一 ⟹ 严格不可逆。 -/
theorem reversibility_boundary :
    Function.Injective (convertVec : VectorConstraint → LinearLayer) ∧
    (∃ c c' : VectorConstraint, c ≠ c' ∧
      ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x) := by
  refine ⟨convertVec_injective, revC, scaleVec revC 2, scaleVec_ne_self_two.symm, ?_⟩
  intro x
  exact scaleVec_two_semantically_equal x

/-! ## 六、不可能性定理：不存在兼顾两层的提取器 -/

/-- **核心不可能性（机器验证）**：不存在既在参数层往返恒等、
又把**语义相同**的权重映到**相同**符号的提取器。

由参数层往返（`roundtrip_extractVec` 的内容）得
`extract (convertVec revC) = revC` 与
`extract (convertVec (scaleVec revC 2)) = scaleVec revC 2`；
而这两个符号约束**不同**（`scaleVec_ne_self_two`），
其对应权重却**表示同一个函数**（`scaleVec_two_semantically_equal`）。

**结论**：语义层的"可逆"（同函数 ↦ 同符号）与参数层的"可逆"（往返恒等）
**不可兼得** ⟹ **严格意义不可逆**。

⚠️ **与 `RealCompileExtractClosed` 的关系（不矛盾，问题不同）**：
该文件证明 `compileToLayer : ConstraintSet → Layer` 是**双射**
（`compileToLayer_bijective`），即**对象层**的映射可逆——
这与本定理**完全一致**：本定理说的正是"两个**不同**的约束对象
（`revC` 与 `scaleVec revC 2`）映到**不同**的层对象"，
但这两个层**表示同一个函数**。故：
- **对象层**可逆（双射，C1 已证）；
- **语义层**不可逆（本定理）。
把「可逆」不加限定地写成"链路完整且可逆"，抹掉的正是这个区分。 -/
theorem no_extractor_preserves_both :
    ¬ ∃ extract : LinearLayer → VectorConstraint,
        (∀ c : VectorConstraint, extract (convertVec c) = c) ∧
        (extract (convertVec revC) = extract (convertVec (scaleVec revC 2))) := by
  rintro ⟨extract, hround, hsame⟩
  have h1 : extract (convertVec revC) = revC := hround revC
  have h2 : extract (convertVec (scaleVec revC 2)) = scaleVec revC 2 :=
    hround (scaleVec revC 2)
  rw [h1, h2] at hsame
  exact scaleVec_ne_self_two hsame.symm

/-- **语义层非单射的显式形式**：存在两个**不同**的权重 `w ≠ w'`，它们
① 表示**同一个函数**（`LayerOut` 零化判定逐点等价），
② **都**是某个符号约束的编译结果。

这正是 doc/01 难点 2「同一函数有无穷多权重实现」的**存在性内核证明**
（"无穷"部分见文件头诚实边界）。 -/
theorem semantic_layer_not_injective :
    ∃ w w' : LinearLayer, w ≠ w' ∧
      (∀ x : List Int, LayerOut w x = 0 ↔ LayerOut w' x = 0) ∧
      (∃ c : VectorConstraint, w = convertVec c) ∧
      (∃ c : VectorConstraint, w' = convertVec c) := by
  refine ⟨convertVec revC, convertVec (scaleVec revC 2), ?_, ?_, ?_, ?_⟩
  · exact convertVec_scale_ne.symm
  · intro x
    exact (convertVec_preserves_semantics revC x).symm.trans
      ((scaleVec_two_semantically_equal x).trans
        (convertVec_preserves_semantics (scaleVec revC 2) x))
  · exact ⟨revC, rfl⟩
  · exact ⟨scaleVec revC 2, rfl⟩

end Lattice.Lib.Editing.RealReversibilityBoundary
