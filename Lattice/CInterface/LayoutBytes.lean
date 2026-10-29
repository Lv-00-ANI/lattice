import Mathlib
import Lattice.CInterface.Serialization
import Lattice.Lib.Quantization.RealFloatFormat

/-!
# 字节布局：从格式位宽推到缓冲大小（L0-3 的第一块）

## 这一块**不需要** `ℝ` 的字节表示

`CInterface/Serialization` 已经证明了**词级**的两件事：`k` 宽的层恰好 `k*k + k` 个词
（`layerWords_length`），且摊平**可逆**（`layerWords_injective`）。

**字节布局是这两条上的纯算术**：一个词占 `bytesPerWord` 字节，于是
**总字节数 = `(k*k + k) * bytesPerWord`**，第 `i*k+j` 个词的起始字节是 `(i*k+j) * bytesPerWord`。

**这部分完全可证，且与 `ℝ` 无关**——它只说「缓冲要多大、每个词从哪开始」。

## ⚠ 信任边界：`ℝ` 的**字节内容**没有形式化

实测（第 36 轮）：**Lean 里 `Float` 没有位级访问**——`Float.toBits` 不存在。
`ℝ` 更是抽象的。所以「一个词到底占哪 4 个字节、位模式是什么」**在树里没有、也不假装有**。

**做法**：把这件事**变成一个类型**——`WordEncoder` 是一个带**长度律**的结构。
下游要用字节就必须**传进来一个编码器**，而它的长度律是它自己的义务。**这样边界是显式的，不是散文。** -/

namespace Lattice.CInterface.LayoutBytes

open Lattice.Core
open Lattice.CInterface.Serialization

/-! ## 一、一个字占几个字节：从 `FloatFormat` 推出来 -/

/-- **一个词占的字节数**：符号位 1 + 指数位 + 尾数位，向上取整到字节。 -/
def bytesPerWord (F : FloatFormat) : ℕ := (F.expBits + F.mantBits + 1 + 7) / 8

/-- **fp16：2 字节**（1 + 5 + 10 = 16 位）。 -/
theorem bytesPerWord_fp16 : bytesPerWord fp16 = 2 := by decide

/-- **bf16：2 字节**（1 + 8 + 7 = 16 位）。 -/
theorem bytesPerWord_bf16 : bytesPerWord bf16 = 2 := by decide

/-- **fp32：4 字节**（1 + 8 + 23 = 32 位）。 -/
theorem bytesPerWord_fp32 : bytesPerWord fp32 = 4 := by decide

/-- **fp16 与 bf16 都是 2 字节，尽管它们的指数/尾数划分不同**——
字节宽度只由总位宽决定，这与 C 侧 `float16_t` 的 `sizeof` 一致。 -/
theorem bytesPerWord_16bit_agree : bytesPerWord fp16 = bytesPerWord bf16 := by
  rw [bytesPerWord_fp16, bytesPerWord_bf16]

/-! ## 二、布局：总字节数与每个词的偏移 -/

/-- **一层的字节数**。

`noncomputable`：`AffineLayer` 含 `Fin k → Fin k → ℝ` 这样的函数，没有可执行表示——
与 `layerWords` 相同的原因（`Lattice/CInterface/Serialization.lean` 里也是 `noncomputable`）。 -/
noncomputable def layerBytes (F : FloatFormat) {k : ℕ} (L : AffineLayer (Fin k)) : ℕ :=
  (layerWords L).length * bytesPerWord F

/-- ⭐ **总字节数 = 参数数 × 每词字节**，而参数数已由 `layerWords_length` 证死。 -/
theorem layerBytes_eq (F : FloatFormat) {k : ℕ} (L : AffineLayer (Fin k)) :
    layerBytes F L = (k * k + k) * bytesPerWord F := by
  unfold layerBytes
  rw [layerWords_length]

/-- **fp16 的一层是 `(k*k + k) * 2` 字节**。 -/
theorem layerBytes_fp16 {k : ℕ} (L : AffineLayer (Fin k)) :
    layerBytes fp16 L = (k * k + k) * 2 := by
  rw [layerBytes_eq, bytesPerWord_fp16]

/-- **fp32 的一层是 `(k*k + k) * 4` 字节**。 -/
theorem layerBytes_fp32 {k : ℕ} (L : AffineLayer (Fin k)) :
    layerBytes fp32 L = (k * k + k) * 4 := by
  rw [layerBytes_eq, bytesPerWord_fp32]

/-- **第 `i*k+j` 个词的起始字节偏移**（行主序）。 -/
def wordOffset (F : FloatFormat) {k : ℕ} (i j : Fin k) : ℕ :=
  (i.val * k + j.val) * bytesPerWord F

/-- **第 `j` 个偏置的起始字节偏移**（权重段之后）。 -/
def biasOffset (F : FloatFormat) {k : ℕ} (j : Fin k) : ℕ :=
  (k * k + j.val) * bytesPerWord F

/-- ⭐ **每个词都按字宽对齐**：偏移是 `bytesPerWord` 的倍数。 -/
theorem wordOffset_align (F : FloatFormat) {k : ℕ} (i j : Fin k) :
    bytesPerWord F ∣ wordOffset F i j :=
  ⟨i.val * k + j.val, by unfold wordOffset; ring⟩

/-- **偏置也按字宽对齐**。 -/
theorem biasOffset_align (F : FloatFormat) {k : ℕ} (j : Fin k) :
    bytesPerWord F ∣ biasOffset F j :=
  ⟨k * k + j.val, by unfold biasOffset; ring⟩

/-- ⭐ **权重段严格在偏置段之前**：行主序没有重叠。 -/
theorem wordOffset_lt_biasOffset (F : FloatFormat) (hF : 0 < bytesPerWord F)
    {k : ℕ} (i j : Fin k) :
    wordOffset F i j < biasOffset F j := by
  unfold wordOffset biasOffset
  apply Nat.mul_lt_mul_of_pos_right _ hF
  have := idxW_lt i j
  omega

/-- ⭐⭐ **最后一个词放得进缓冲**：`wordOffset + 字宽 ≤ layerBytes`。

**这就是「缓冲大小恰好」的机器形式**——不是「大概够」，而是每个词的末尾都在界内。 -/
theorem lastWord_fits (F : FloatFormat) (hF : 0 < bytesPerWord F) {k : ℕ}
    (L : AffineLayer (Fin k)) (i j : Fin k) :
    wordOffset F i j + bytesPerWord F ≤ layerBytes F L := by
  unfold wordOffset layerBytes
  rw [layerWords_length]
  have h1 : i.val * k + j.val + 1 ≤ k * k := by
    have := idxW_lt i j
    omega
  calc (i.val * k + j.val) * bytesPerWord F + bytesPerWord F
      = (i.val * k + j.val + 1) * bytesPerWord F := by ring
    _ ≤ (k * k) * bytesPerWord F := Nat.mul_le_mul_right _ h1
    _ ≤ (k * k + k) * bytesPerWord F := Nat.mul_le_mul_right _ (by omega)

/-- **偏置段的最后一个词也放得进缓冲**。 -/
theorem lastBias_fits (F : FloatFormat) (hF : 0 < bytesPerWord F) {k : ℕ}
    (L : AffineLayer (Fin k)) (j : Fin k) :
    biasOffset F j + bytesPerWord F ≤ layerBytes F L := by
  unfold biasOffset layerBytes
  rw [layerWords_length]
  have hj : j.val < k := j.isLt
  have h1 : k * k + j.val + 1 ≤ k * k + k := by omega
  calc (k * k + j.val) * bytesPerWord F + bytesPerWord F
      = (k * k + j.val + 1) * bytesPerWord F := by ring
    _ ≤ (k * k + k) * bytesPerWord F := Nat.mul_le_mul_right _ h1

/-! ## 三、信任边界：`ℝ` 的字节编码是一个**带长度律的结构** -/

/-- **词的字节编码器**：把 `ℝ` 编成恰好 `bytesPerWord F` 个字节。

**这是本文件唯一的「假设」**，而且它是**参数**，不是散在 prose 里的信任。
下游要写字节，就必须交出一个 `WordEncoder`；`size_eq` 是它自己的义务。

**为什么不能构造**：实测 `Float.toBits` 在 Lean 里不存在，`ℝ` 是抽象的。
真正的构造需要 `ℝ → Float` 的舍入模型 + 位模式分解，那是 L5-1（全 IEEE-754 细化）。 -/
structure WordEncoder (F : FloatFormat) where
  /-- 把一个词编成字节 -/
  encode : ℝ → ByteArray
  /-- **长度律**：恰好 `bytesPerWord F` 个字节 -/
  size_eq : ∀ x : ℝ, (encode x).size = bytesPerWord F

/-- **编码器给出的一层字节数**：`(k*k + k)` 个词各 `bytesPerWord F` 字节。

**这条定理说的是「编码器与布局一致」**——两个数字来自不同的地方
（`layerWords_length` 与 `WordEncoder.size_eq`），在这里相遇。 -/
theorem encoded_layer_size (F : FloatFormat) (enc : WordEncoder F) {k : ℕ}
    (L : AffineLayer (Fin k)) :
    (layerWords L).length * bytesPerWord F = layerBytes F L := by
  unfold layerBytes
  ring

end Lattice.CInterface.LayoutBytes
