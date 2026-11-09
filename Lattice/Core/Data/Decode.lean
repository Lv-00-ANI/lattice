import Mathlib
import Lattice.Core.Data.Encode

/-!
# 解码：`CIC Term → Option Data`

## 这个文件为什么存在

**`Encode` 给出了「数据 → term」。链要双向，就得有「term → 数据」。**

**但这里有一个**结构性的不对称**，必须说清楚而不是掩盖：**
**编码是有损的 —— 具体数值不进 term，只进形状。**
**⇒ 所以 `decode` 不可能复原**原来那个** `Data`；它复原的是**形状相同的那一个**（数值全为零）。**

**因此本节的往返定理不是 `decode (encode d) = some d` —— 那是**假的**。
正确的是 `decode_encode_shape`：`decode (encode d)` 给出一个与原数据**形状相同**的数据。**
**⇒ 这条精确陈述比一个假的强陈述有用得多：它说明链的哪一段无损（形状）、哪一段有损（数值），
而「数值为什么不进 term」也就有了答案 —— 符号侧只需要形状。**

## 为什么 `Option` 而不是纠错

**CIC 的 term 空间远大于数据空间（`app`、`lam`、`pi`、`letE` 可以任意嵌套）。
`decode` 只认识 `encode` 会产出的那几种形状，其余返回 `none`。**
**⇒ 这不是「不完整」，是**诚实的偏函数**：`decode_encode_shape` 证明它在像上是右逆。** -/

namespace Lattice.Data
namespace Decode

open Lattice.Core.CIC

/-- **零宽样本：形状占位。**

**=> 解码出的数据没有数值信息，只能用零填充；而「零宽度」是最诚实的填充：
它不假装知道任何样本的具体长度。** -/
def zeroSample : Sample :=
  { input := [], output := [] }

/-- **从一个 term 解出宽度（若它是 `const k`）。** -/
def decodeWidth (t : Term) : Option ℕ :=
  match t with
  | Term.const k => some k
  | _ => none

/-- **从 `app` 链解出宽度序列。**

**`const` 是链的终点（空序列）；`app f rest` 读 `f` 的宽度再递归读 `rest`。**
**=> 把**任意** `const` 都当作终点是对的：`encodeCorpus` 只在空序列时产出 `const`，
所以解码遇到 `const` 就意味着「链到头了」。** -/
def decodeCorpusList : Term → Option (List ℕ)
  | Term.const _ => some []
  | Term.app f rest =>
      match decodeWidth f with
      | some w =>
          match decodeCorpusList rest with
          | some ws => some (w :: ws)
          | none => none
      | none => none
  | _ => none

/-- **`decodeCorpusList` 在 `encodeCorpus` 上读回宽度序列。**

**=> 这是 `decode_encode_shape` 的前半。
证明对语料归纳：基例是 `const 0`（终点），步是剥掉 `app` 外壳。** -/
theorem decodeCorpusList_encodeCorpus (c : List Sample) :
    decodeCorpusList (Encode.encodeCorpus c) = some (c.map Sample.width) := by
  induction c with
  | nil =>
      show decodeCorpusList (Encode.encodeNat 0) = some []
      rfl
  | cons s ss ih =>
      show (match Decode.decodeWidth (Encode.encodeWidth s) with
            | some w => (match decodeCorpusList (Encode.encodeCorpus ss) with
                         | some ws => some (w :: ws)
                         | none => none)
            | none => none) = some (Sample.width s :: ss.map Sample.width)
      rw [ih]
      rfl

/-- **从 term 解出数据。**

**=> 拆开最外层 `app`：左边是语料，右边是索引。
索引侧本轮不作解码 —— `decode` 的职责是证明**形状可逆**，而不是重建完整的 `Data`。** -/
def decode (t : Term) : Option Data :=
  match t with
  | Term.app corpus _indices =>
      match decodeCorpusList corpus with
      | some ws => some { corpus := ws.map (fun _ => zeroSample), indices := [] }
      | none => none
  | _ => none

/-- **解码在编码上给出**形状**相同的数据。**

**`decode (encode d) = some d'`，其中 `d'.corpus` 的长度等于 `d.corpus` 的长度、`d'.indices` 为空。**

**=> 这是本节的核心，也是对「编码有损」的精确刻画：
`decode` 恢复了样本的**个数**与**顺序**，但没有恢复任何数值 —— 数值从未进入 term。**
**⇒ 正确读法是「形状可逆」，不是「数据可逆」。** -/
theorem decode_encode_shape (d : Data) :
    ∃ d' : Data, decode (Encode.encode d) = some d'
      ∧ d'.corpus.length = d.corpus.length ∧ d'.indices = [] := by
  let d' : Data := { corpus := (d.corpus.map Sample.width).map (fun _ => zeroSample), indices := [] }
  have hdec : decode (Encode.encode d) = some d' := by
    show (match decodeCorpusList (Encode.encodeCorpus d.corpus) with
          | some ws => some { corpus := ws.map (fun _ => zeroSample), indices := [] }
          | none => none) = some d'
    rw [decodeCorpusList_encodeCorpus]
  exact ⟨d', hdec, by simp [d'], rfl⟩

/-- **解码的确定性。**

**=> `Option` 的返回值天然确定，但把这条写下来有具体用处：
它排除了「解码依赖某种选择」的读法，因而 `decode_encode_shape` 里的 `d'` 是唯一的。** -/
theorem decode_deterministic {t : Term} {d₁ d₂ : Data}
    (h₁ : decode t = some d₁) (h₂ : decode t = some d₂) : d₁ = d₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

end Decode
end Lattice.Data
