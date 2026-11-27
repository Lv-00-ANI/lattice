import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.DotTruncationDefect
/-!
# LATTICE: 多层网络组合 —— 前向传播与约束满足的传播

doc/02 §4.4「先组合」在权重侧的落地：多层线性网络的前向传播正确性。

内容：
  1. layerFwd：一层的向量前向（每个神经元对输入向量的输出列表）；
  2. layerSeq：多层前向（foldl 依次过层）；
  3. 零输入传播：神经元收到零向量，输出退化为偏置（dot 与零向量为零）；
  4. 组合传播定理：第一层约束全部满足 → 输出全零 → 第二层收到零向量
     → 第二层输出退化为偏置 —— 约束满足在多层网络中逐层传播。

**注意** **订正 B400**：此处原写「纯 Std。」，而**本文件第 1 行就是 `import Mathlib`**
（所 import 的 `ConvertVectorLinear`、`SymbolToWeightCorrectness` 亦然）—— 自相矛盾。
真实情况是：**本文件的表示层只用到 `Int`/`List` 等核心类型**
（`layerFwd`/`layerSeq` 的输入输出皆为 `List Int`，`Layer`/`LayerOut`/`dot`/`LinearLayer`
的字段亦然，不依赖 mathlib 的专用结构），但**文件整体 import 了 Mathlib**。
⇒ 原措辞把「表示的选型」误写成了「依赖的选型」。
订正模板见 ConvertLinear 的文件头「订正 B400」。**以本段为准。**
-/


open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

-- Layer/LayerOut/dot/LinearLayer 来自 ConvertVectorLinear，Layer/ConstraintSet/
-- AllSatisfied/AllZeroOutputs/compileToLayer/symbolToWeight_* 来自
-- SymbolToWeightCorrectness（均在 Lattice 命名空间），无需 open。

/-! ## 一层前向：神经元列表对输入向量的输出列表 -/

def layerFwd (ls : Layer) (x : List Int) : List Int :=
  ls.map (fun l => LayerOut l x)

/-! ## 多层前向：foldl 依次过层 -/

def layerSeq : List Layer → List Int → List Int
  | [], x => x
  | l :: rest, x => layerSeq rest (layerFwd l x)


lemma dot_replicate_zero_any (w : List Int) (n : Nat) :
    dot w (List.replicate n 0) = 0 := by
  unfold dot
  induction w generalizing n with
  | nil => simp [List.foldl, List.zip, List.replicate]
  | cons h t ih =>
      cases n with
      | zero => simp [List.foldl, List.zip, List.replicate]
      | succ m =>
          -- 拆出首项 (h, 0) 后，余项由 ih m 处理（simpa 统一展开 zip/replicate/foldl）
          simpa [List.foldl, List.zip, List.replicate] using ih m

/-! ## 引理二：神经元收到零向量输出偏置
LayerOut l (replicate (w.length) 0) = b。-/

lemma layerOut_zero_input (l : LinearLayer) :
    LayerOut l (List.replicate l.w.length 0) = l.b := by
  unfold LayerOut
  rw [dot_replicate_zero l.w]
  omega

/-! ## 定理一：全零输出 ⟺ 该层输出列表为全零向量
层内所有神经元输出为零，等价于该层的输出列表是全零向量。-/

theorem layerFwd_allzero (ls : Layer) (x : List Int) :
    AllZeroOutputs ls x ↔ layerFwd ls x = List.replicate ls.length 0 := by
  unfold AllZeroOutputs layerFwd
  constructor
  · intro h
    -- 全零 ⟹ 列表 = 全零列表：用 eq_replicate_length（列表 = replicate ⟺ 每元素为零）
    have hmem : ∀ b ∈ ls.map (fun l => LayerOut l x), b = 0 := by
      intro b hb
      rcases List.mem_map.mp hb with ⟨l, hl, rfl⟩
      exact h l hl
    simpa [List.length_map] using (List.eq_replicate_length (a := 0)).mpr hmem
  · intro h
    -- 列表 = 全零列表 ⟹ 每元素为零（eq_replicate_length 的逆向）
    intro l hl
    have hmem : LayerOut l x ∈ ls.map (fun l => LayerOut l x) :=
      List.mem_map.mpr ⟨l, hl, rfl⟩
    have hall : ∀ b ∈ ls.map (fun l => LayerOut l x), b = 0 :=
      (List.eq_replicate_length (a := 0)).mp (by simpa [List.length_map] using h)
    exact hall (LayerOut l x) hmem

/-! ## 定理二：约束满足的层间传播
第一层约束全部满足 → 第二层收到零向量 → 第二层输出退化为偏置。-/

theorem constraint_satisfaction_propagates (cs : ConstraintSet) (x : List Int)
    (l2 : LinearLayer) (h : AllSatisfied cs x) :
    LayerOut l2 (layerFwd (compileToLayer cs) x) = l2.b := by
  -- 第一层输出全零向量（由约束满足 + 编译保语义推出）
  have hzero_out : layerFwd (compileToLayer cs) x = List.replicate (compileToLayer cs).length 0 := by
    exact (layerFwd_allzero (compileToLayer cs) x).mp ((symbolToWeight_correct cs x).mp h)
  -- 第二层收到零向量 → 输出 = 偏置（dot 与任意长度零向量为零）
  rw [hzero_out]
  unfold LayerOut
  rw [dot_replicate_zero_any l2.w (compileToLayer cs).length]
  omega

/-! ## 定理三：三层链的组合前向正确性
layerSeq 的折叠定义正确：三层网络前向 = 依次应用各层。-/

theorem layerSeq_three (l1 l2 l3 : Layer) (x : List Int) :
    layerSeq [l1, l2, l3] x = layerFwd l3 (layerFwd l2 (layerFwd l1 x)) := by
  simp [layerSeq, layerFwd]

end Lattice
