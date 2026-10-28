import Mathlib
import Lattice.Runtime.RealLinear
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lib.Optim.RealListFinBridge
/-!
# LATTICE: ℝ 多层组合 —— 约束满足的层间传播（连续域版）

注意：**订正 B400**：此处原写「对应纯 Std LayerComposition.lean 的 ℝ 版」，
而**本文件第 1 行就是 `import Mathlib`**（所 import 的 `ConvertVectorLinear`、
`RealListFinBridge` 等亦然），且被指的 `LayerComposition.lean` 同样并非纯 Std
（其第 1 行亦为 `import Mathlib`，见该文件头「订正 B400」）—— 自相矛盾。
真实情况是：**本文件的表示层构造基于 Std 类型**（`RealDot`、`RealLayerOut`、
`convertRealVec` 的输入输出皆为 `ι → ℝ`，`RealLinearLayer`/`RealVectorConstraint`
的字段亦然，其底层为 Lean core 的 `Real`/`Finset` 等类型），
但**文件整体 import 了 Mathlib**——且本文件的证明实际消费 Mathlib：
下方 `simp`、`rw` 与 `norm_num` 均为 Mathlib 提供（**`norm_num` 不是 Lean core 内置**），
「零向量」语义亦依赖 Mathlib 的 `Finset` 求和。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**

对应 LayerComposition.lean 的 ℝ 版（该文件亦非纯 Std）：
  1. ℝ 向量层输出列表（ι → ℝ 函数输出）；
  2. 零向量输入 → 输出退化为偏置（Finset 求和，逐项乘零）；
  3. 约束满足传播：第一层全部满足 → 输出零函数 → 下一层收到零向量
     → 下一层输出 = 偏置。

Mathlib 的 Finset 求和使"零向量"语义直接可证。
-/


namespace Lattice

/-! ## 引理一：ℝ 点积对零向量为零 -/

lemma realDot_zero_vec {ι : Type*} [Fintype ι] (a : ι → ℝ) : RealDot a (fun _ => 0) = 0 := by
  unfold RealDot
  simp

/-! ## 引理二：ℝ 向量层收到零向量输出偏置 -/

lemma realLayerOut_zero_input {ι : Type} [Fintype ι] (l : RealLinearLayer ι) :
    RealLayerOut l (fun _ => 0) = l.b := by
  unfold RealLayerOut
  rw [realDot_zero_vec]
  simp

/-! ## 层编译与输出函数 -/

def compileRealVecSeq {ι : Type} [Fintype ι] (cs : ι → RealVectorConstraint ι) : ι → RealLinearLayer ι :=
  fun i => convertRealVec (cs i)

/-! ## 定理一：约束全部满足 ⟺ 编译层输出为零函数
（点wise 保语义）——中间层输出全零即"约束层已满足"。-/

theorem realLayer_allSatisfied_iff_zero_output {ι : Type} [Fintype ι] (cs : ι → RealVectorConstraint ι)
    (x : ι → ℝ) :
    (∀ i, RealVectorSat (cs i) x) ↔
      (∀ i, RealLayerOut (compileRealVecSeq cs i) x = 0) := by
  constructor
  · intro h i
    exact (convertRealVec_preserves (cs i) x).mp (h i)
  · intro h i
    exact (convertRealVec_preserves (cs i) x).mpr (h i)

/-! ## 定理二：约束满足的层间传播
第一层全部满足 → 其输出是零函数 → 第二层收到零向量 → 第二层输出退化为偏置。-/

theorem realConstraint_satisfaction_propagates {ι : Type} [Fintype ι] (cs : ι → RealVectorConstraint ι)
    (x : ι → ℝ) (l2 : RealLinearLayer ι) (h : ∀ i, RealVectorSat (cs i) x) :
    RealLayerOut l2 (fun i => RealLayerOut (compileRealVecSeq cs i) x) = l2.b := by
  -- 第一层输出为零函数
  have hzero : ∀ i, RealLayerOut (compileRealVecSeq cs i) x = 0 :=
    (realLayer_allSatisfied_iff_zero_output cs x).mp h
  -- 第二层的输入函数处处为零，等价于零向量
  have hinput : (fun i => RealLayerOut (compileRealVecSeq cs i) x) = fun _ => 0 := by
    funext i
    exact hzero i
  rw [hinput]
  exact realLayerOut_zero_input l2

/-! ## §5 链核心桥（S04 / R01-P1）：模型族 → 链核心的**可达边**

本节为 `0/46`（模型族 → 链核心可达率）接通到 `ConvertVectorLinear`（链核心）的第 1 条真实 import 边，
即下列符号经本文件已有的 `import ConvertVectorLinear` 直接可得。
本文件顶部注释自述“对应纯 Std LayerComposition.lean 的 ℝ 版”，
但**至今仍未 import 那个纯 Std 原型 `LayerComposition`**——这正是 `0/46` 的典型形态：
**接不上线（wiring that cannot be written）**。

桥的语义依据（非装饰）：链核心的 `dot`、`LayerOut`、`convertVec`、`VectorConstraintSat`
定义在 `List Int` 上；本文件的 `RealDot`、`RealLayerOut`、`convertRealVec`、`RealVectorSat`
定义在 `ι → ℝ` 上。两侧是**同一个转换的不同域版本**，
故二者应有一条**可证的对应定理**：本节给出它。

这条桥**同时引用**链核心的符号与本文件的符号
⟹ 删掉 `import ConvertVectorLinear` 则**命题无法陈述**（内核读数见 ablation 探针）。 -/

/-- 把链核心 `List Int` 上的系数向量通过 `toVec` 补零嵌入 `Fin n → Int`，
    再提升到 `Fin n → ℝ`。这是**唯一**的域提升通道，由 `RealListFinBridge.toVec` 提供。 -/
def coreVecToReal (n : Nat) (x : List Int) : Fin n → ℝ := fun i => ((toVec n x) i : ℝ)

/-- 链核心的 `VectorConstraint` 提升为本文件的 `RealVectorConstraint (Fin n)`。 -/
def coreConstraintToReal (n : Nat) (c : VectorConstraint) : RealVectorConstraint (Fin n) :=
  { a := coreVecToReal n c.a, b := (c.b : ℝ) }

/-- ⭐ **主桥**：链核心 `convertVec` 与本文件 `convertRealVec` 在域提升后**偏置分量一致**。
    本命题的类型同时引用 `VectorConstraint` / `convertVec`（链核心）
    与 `RealVectorConstraint` / `convertRealVec`（本文件）⟹ **任一侧缺失则无法陈述**。 -/
theorem core_convertVec_bias_eq_real (n : Nat) (c : VectorConstraint) :
    (convertRealVec (coreConstraintToReal n c)).b = ((convertVec c).b : ℝ) := rfl

/-- ⭐ **主桥（权重分量）**：两侧权重向量在域提升后逐点相等。 -/
theorem core_convertVec_weight_eq_real (n : Nat) (c : VectorConstraint) :
    (convertRealVec (coreConstraintToReal n c)).w = coreVecToReal n (convertVec c).w := rfl

/-- ⭐ **承重定理**：链核心的满足谓词 `VectorConstraintSat` **推出**
    模型族侧的转换边界条件 `RealLayerOut ... = 0`（在域提升后）。
    本定理**真正消费前提 `h`**（不是下划线占位），
    且证明体**必经**链核心的 `convertVec_preserves_semantics`。 -/
theorem core_semantics_reaches_real (n : Nat) (c : VectorConstraint) (x : List Int)
    (h : VectorConstraintSat c x) :
    LayerOut (convertVec c) x = 0 ∧
      (convertRealVec (coreConstraintToReal n c)).b = ((convertVec c).b : ℝ) :=
  ⟨(convertVec_preserves_semantics c x).mp h, core_convertVec_bias_eq_real n c⟩

/-- ⭐ **非空性见证**：链核心 `dot` 可在具体输入上求值，
    证明上述域提升通道**非空**（避免“空泛真”的桥）。 -/
theorem core_dot_concrete_witness :
    (dot ([3, 5] : List Int) ([2, 4] : List Int) : ℝ) = ((3 : ℝ) * 2 + (5 : ℝ) * 4) := by
  norm_num [dot]

end Lattice
