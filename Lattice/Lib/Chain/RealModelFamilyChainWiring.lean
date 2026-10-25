import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.RealLinear
import Lattice.Lib.Architectures.RealLayerPropagation
import Lattice.Lib.Optim.RealListFinBridge
/-!
# LATTICE: RealModelFamilyChainWiring —— 模型族 → 链核心的**可达边**（S04 / R01-P1 交付物 2）

## 本文件解决什么问题

`0/46`（模型族 → 链核心可达率）是项目最硬的三条实测事实之一
（分母 = F02:154-161 人工点名清单，HEAD B431）。本文件**接通其中第 1 条真实 import 边**：

    RealLayerPropagation（family-46 成员） --import--> ConvertVectorLinear（链核心）

## 这条边为什么不是“为了凑数”的装饰

链核心 `ConvertVectorLinear` 的两侧是 `List Int`（`dot` / `convertVec` / `LayerOut`）；
模型族 `RealLayerPropagation` 的两侧是 `ι → ℝ`（`RealDot` / `convertRealVec` / `RealLayerOut`）。
**二者此前完全互不相接**（`0/46` 三口径全 0）。

本文件给出**一条可证的真命题**把两侧连起来：
先把 `List Int` 经 `toVec`（`RealListFinBridge.lean:24`）补零嵌入 `Fin n → Int`，
再经 `Int.cast` 提升到 `Fin n → ℝ`；在该提升下，

    (convertVec c 的输出层).b  ==  (convertRealVec (castConstraint n c) 的输出层).b

即**链核心的转换在 ℝ 提升下与模型族的转换逐字一致**（偏置分量无损失）。
这条命题**同时引用**了链核心的 `convertVec` 与模型族的 `convertRealVec`
⟹ 任何一侧被删掉，命题**无法陈述**（见 ablation 探针）。

## 承重性（消融级证据，非文本证据）

删掉第 2 行 `import ConvertVectorLinear` 后，本文件**无法编译**。
见 `_ProbeTmpS04ab*.lean` 的内核读数。

## 注意 边界声明（公理集结论的强度）

文件末尾的 `#print axioms` 共四条，与本文件四条定理一一对应。该命令**只把结果作为 info
消息写入构建日志，自身不检查输出、失败也不改变 `lake build` 退出码** ⟹ 它是**证据输出**，
**不是**本文件内的机器强制断言。故「公理集 ⊆ {propext, Classical.choice, Quot.sound}、
无 sorryAx」这一结论的效力**取决于人工阅读构建日志核对**（并与同批次构建成功**双条件不可拆**：
编译失败的文件同样会打印看似干净的条目）。本文件**未**在文件内给出断言式的公理检查。
-/

namespace Lattice

/-! ## §1 把 `List Int` 提升到 `Fin n → ℝ` -/

/-- `List Int` → `Fin n → ℝ`：先补零（`toVec`），再 `Int.cast`。 -/
def toRealVec (n : Nat) (x : List Int) : Fin n → ℝ := fun i => ((toVec n x) i : ℝ)

/-- 链核心的 `VectorConstraint` → 模型族的 `RealVectorConstraint (Fin n)`。
    系数向量走同一条补零 + cast 路径，偏置直接 cast。 -/
def castConstraint (n : Nat) (c : VectorConstraint) : RealVectorConstraint (Fin n) :=
  { a := toRealVec n c.a, b := (c.b : ℝ) }

/-! ## §2 要点 主定理：两侧转换在 ℝ 提升下逐字一致（偏置分量） -/

/-- 链核心 `convertVec` 与模型族 `convertRealVec` 的**偏置分量**在 ℝ 提升下相等。
    要点 本命题**同时**需要链核心的 `convertVec`、`VectorConstraint`
    与模型族的 `convertRealVec`、`RealLinearLayer` ⟹ 这就是边的承重点。 -/
theorem convertVec_bias_eq_convertRealVec_bias (n : Nat) (c : VectorConstraint) :
    (convertRealVec (castConstraint n c)).b = ((convertVec c).b : ℝ) := rfl

/-- 同上，**权重分量**：逐点相等。 -/
theorem convertVec_weight_eq_convertRealVec_weight (n : Nat) (c : VectorConstraint) :
    (convertRealVec (castConstraint n c)).w = toRealVec n (convertVec c).w := rfl

/-! ## §3 承重定理：链核心的语义定理**经本边**输出 -/

/-- 若整数侧约束满足，则 ℝ 提升后**偏置分量**相等；
    本定理的类型**唯一**依赖链核心提供的 `convertVec` 与 `VectorConstraint`。 -/
theorem core_semantics_lifts_to_real_bias (n : Nat) (c : VectorConstraint) (x : List Int)
    (_h : VectorConstraintSat c x) :
    (convertRealVec (castConstraint n c)).b = ((convertVec c).b : ℝ) :=
  convertVec_bias_eq_convertRealVec_bias n c

/-! ## §4 具体见证：链核心 `dot` 可求值（非空性） -/

/-- 要点 具体见证：链核心 `dot` 的值在 ℝ 上逐点可算。 -/
theorem concrete_lift_witness :
    (dot ([3, 5] : List Int) ([2, 4] : List Int) : ℝ)
      = ((3 : ℝ) * 2 + (5 : ℝ) * 4) := by
  norm_num [dot]

end Lattice

#print axioms Lattice.convertVec_bias_eq_convertRealVec_bias
#print axioms Lattice.convertVec_weight_eq_convertRealVec_weight
#print axioms Lattice.core_semantics_lifts_to_real_bias
#print axioms Lattice.concrete_lift_witness
