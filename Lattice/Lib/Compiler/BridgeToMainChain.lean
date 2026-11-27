import Lattice.Lib.Compiler.AnalyticSelection
import Lattice.Runtime.ConvertVectorLinear

/-!
# **桥：新线的 `Segment` 与主链的标量 `LinearLayer` 在**整数标量片段**上一致**

## 本轮是**测量**，不是施工

**第 1080 轮的宏观盘点发现：新线（`Lib/Compiler/`，第 1043–1079 轮）在 `Lib/Compiler/` 之外**零引用**。
⇒ 故本轮先**测量**它与主链是否共享片段，再决定桥还是不桥。**

## 测量结果：**形状不同**，只有标量仿射处相交

| | 主链（`Runtime/ConvertVectorLinear.lean`） | 新线（`Lib/Compiler/`） |
|:--|:--|:--|
| 载体 | `LinearLayer = ⟨w : List ℤ, b : ℤ⟩`（`:138`） | `Segment = ⟨m : ℝ, c : ℝ⟩` |
| 求值 | `LayerOut l x = dot l.w x + l.b`（`:143`） | `Segment.eval s x = s.m * x + s.c` |
| 语义 | **精确**：约束满足 ⟺ 输出为零 | **逼近**：`|f − 插值| ≤ C/n²` |
| 输入 | `List ℤ` | `ℝ` |

**⇒ 故不能声称「两者是同一条链」：**
**⇒ `ℤ→ℝ` 的强制转换不是同构（`ℝ` 元素未必是整数），而「输出为零」与「误差有界」是**两种不同的判据**。**

**⇒ 唯一**真实**的交点是**标量仿射片段**：`List` 长度为 1 时，两者都是 `w·x + b` 形状。
⇒ 本文件只证明这个交点，并在末尾**明确记录**它不延伸到何处。**

## 这个桥说明了什么、不说明什么

**⇒ 说明：当新线的分段系数是**整数**时，它在**整数点**上求出的值等于主链那一层的输出（经 `ℤ→ℝ`）。**
**⇒ 不说明：两者在非整数系数、非标量、或「零 vs ε」语义上一致——那些**不在**本文件中，也不被声称。**
-/

namespace Lattice.Lib.Compiler.BridgeToMainChain

open Lattice.Lib.Compiler.WeightSequence

/-- **⭐⭐ 标量仿射片段：新线的 `Segment` 与主链的 `LinearLayer` 输出一致。**

**⇒ 前提是系数与输入都是**整数**（`w b x : ℤ`），故 `ℤ→ℝ` 的强制转换在两边取值相同。**
**⇒ 证明：两边都是 `w·x + b`，只是载体不同（`ℝ` vs `ℤ`）。** -/
theorem segment_eval_eq_scalar_layer_out (w b x : ℤ) :
    (⟨(w : ℝ), (b : ℝ)⟩ : Segment).eval (x : ℝ)
      = ((Lattice.LayerOut ⟨[w], b⟩ [x] : ℤ) : ℝ) := by
  -- **两边都是 `w·x + b`；`simp` 会把 `dot`、`LayerOut` 与 `Segment.eval` 都展开，
  -- 并用 `Int.cast_mul`/`cast_add` 把 `ℤ→ℝ` 推到最细粒度。**
  simp [Lattice.LayerOut, Lattice.dot, Segment.eval]

/-- **⭐ 反向读法：主链的标量层输出，就是新线那个分段在整数点的求值。**

**⇒ 与上一条是同一等式的对称陈述；单独命名是为了让「从主链看新线」也有一个可引用的方向。** -/
theorem scalar_layer_out_eq_segment_eval (w b x : ℤ) :
    ((Lattice.LayerOut ⟨[w], b⟩ [x] : ℤ) : ℝ)
      = (⟨(w : ℝ), (b : ℝ)⟩ : Segment).eval (x : ℝ) :=
  (segment_eval_eq_scalar_layer_out w b x).symm

/-! ## \u8fb9\u754c\uff1a\u672c\u6587\u4ef6**\u4e0d**\u58f0\u660e\u7684\u4e09\u4ef6\u4e8b -/

/-- **\u2b50\u2b50 \u8fb9\u754c\u58f0\u660e\uff08\u4e00\u6761\u5b9a\u7406\uff0c\u800c\u4e0d\u662f\u4e00\u53e5\u8bc4\u8bba\uff09\uff1a\u4e24\u4e2a\u7247\u6bb5\u5728**\u5341\u4e00\u4e2a\u5177\u4f53\u70b9**\u4e0a\u4e00\u81f4\u3002

**\u21d2 \u8fd9\u6761\u7684\u4f5c\u7528\u662f\u628a\u300c\u4ea4\u70b9\u786e\u5b9e\u5b58\u5728\u300d\u5199\u6210\u53ef\u5f15\u7528\u7684\u4e00\u4f8b**\uff08\u800c\u4e0d\u662f\u4e00\u4e2a\u8303\u56f4\uff09\uff0c
\u56e0\u4e3a\u4e0a\u4e00\u6761\u5df2\u7ecf\u662f**\u5bf9\u4efb\u610f `w b x`** \u7684\u4e00\u822c\u9648\u8ff0\u3002**
**\u21d2 \u6545\u672c\u6761\u53ea\u4f5c\u4e3a**\u4e0d\u53ef\u6dc7\u7684\u6837\u672c**\uff1a\u8bfb\u8005\u4e0d\u5fc5\u4fe1\u4efb\u4f55\u4e1c\u897f\u5c31\u53ef\u4ee5\u5bf9\u4e00\u4e2a\u5177\u4f53\u4f8b\u5b50\u6838\u5bf9\u3002** -/
theorem bridge_sample :
    ((Lattice.LayerOut ⟨[(3 : ℤ)], 5⟩ [(7 : ℤ)] : ℤ) : ℝ)
      = (⟨(3 : ℝ), (5 : ℝ)⟩ : Segment).eval (7 : ℝ) :=
  scalar_layer_out_eq_segment_eval 3 5 7

/-! ## 五、桥到此为止：**斜率非整数的分段不可能由任何 `LinearLayer` 表示** -/

/-- **⭐⭐ `1/2` 不是任何整数**。

**⇒ 这是下一条的**算术内核**：`Segment.m` 是 `ℝ`，`LinearLayer.w` 是 `List ℤ`。** -/
theorem half_is_not_an_integer_weight : ¬ ∃ z : ℤ, (z : ℝ) = 1 / 2 := by
  rintro ⟨z, hz⟩
  have h2 : ((2 * z : ℤ) : ℝ) = 1 := by
    push_cast
    rw [hz]
    norm_num
  have hz2 : 2 * z = 1 := by exact_mod_cast h2
  omega

/-- **⭐⭐⭐ 桥的**另一半**：只要斜率不是整数，就**不存在**一个 `LinearLayer` 能在整数输入上等于它。

**⇒ 理由是**一行**：`LayerOut l [x]` 的值是 `ℤ`，而它经 `ℤ→ℝ` 强转后必须等于 `m·x + c`。
⇒ 对 `x = 1`，那就要求 `m + c` 是一个整数；取 `c = 0` 就要求 `m` 是整数。**
**⇒ 故这不是「还没翻译」，而是**不可翻译**——且属于**数的域**而不是代码结构。** -/
theorem non_integer_slope_has_no_layer (m : ℝ) (hm : ∀ z : ℤ, (z : ℝ) ≠ m) :
    ¬ ∃ l : Lattice.LinearLayer, ∀ x : ℤ,
      (⟨m, 0⟩ : Segment).eval (x : ℝ) = ((Lattice.LayerOut l [x] : ℤ) : ℝ) := by
  rintro ⟨l, h⟩
  have h1 := h 1
  -- **注意 `↑1` 与 `1` 的区别：`h1` 的左边是 `eval ↑(1 : ℤ)`。**
  have hev : (⟨m, 0⟩ : Segment).eval ((1 : ℤ) : ℝ) = m := by
    simp [Segment.eval]
  rw [hev] at h1
  exact hm (Lattice.LayerOut l [1]) h1.symm

/-- **⭐⭐ 具体一例：斜率 `1/2` 的分段没有对应的层。** -/
theorem half_slope_has_no_layer :
    ¬ ∃ l : Lattice.LinearLayer, ∀ x : ℤ,
      (⟨(1 / 2 : ℝ), 0⟩ : Segment).eval (x : ℝ) = ((Lattice.LayerOut l [x] : ℤ) : ℝ) :=
  non_integer_slope_has_no_layer (1 / 2) (fun z hz => half_is_not_an_integer_weight ⟨z, hz⟩)

/-! ## 六、精确边界：**一个段有整数层**当且仅当**两个系数都是整数** -/

/-- **⭐⭐⭐ 完整刻画：一个分段能被某个 `LinearLayer` 在整数输入上表示 ↔ 它的斜率与截距**都是整数**。**

**⇒ 旧有的 `non_integer_slope_has_no_layer` 只说了**反面**（非整数斜率 ⇒ 不存在），而且只用 `x = 1` 看斜率。**
**⇒ 本条把两个方向都写完：**正面**（整数 ⇒ 构造出那个层，见参数化的 `⟨[mz], cz⟩`）与**
**反面（存在层 ⇒ `m` 由 `x=1`、`c` 由 `x=0` 各自得出是整数）。**
**⇒ 故「不可翻译」不是一句下断，而是一个**等价**：整数截面里那些点，正好是两个系数都是整数的段。 -/
theorem segment_has_layer_iff_integral (s : Segment) :
    (∃ l : Lattice.LinearLayer, ∀ x : ℤ,
        s.eval (x : ℝ) = ((Lattice.LayerOut l [x] : ℤ) : ℝ))
      ↔ (∃ z : ℤ, s.m = (z : ℝ)) ∧ (∃ z : ℤ, s.c = (z : ℝ)) := by
  constructor
  · rintro ⟨l, h⟩
    have h0 : s.c = ((Lattice.LayerOut l [0] : ℤ) : ℝ) := by
      have := h 0
      simpa [Segment.eval] using this
    have h1 : s.m + s.c = ((Lattice.LayerOut l [1] : ℤ) : ℝ) := by
      have := h 1
      simpa [Segment.eval] using this
    have hm : s.m = ((Lattice.LayerOut l [1] - Lattice.LayerOut l [0] : ℤ) : ℝ) := by
      have hsub : s.m = ((Lattice.LayerOut l [1] : ℤ) : ℝ) - ((Lattice.LayerOut l [0] : ℤ) : ℝ) := by
        linarith
      rw [hsub]
      push_cast
      ring
    exact ⟨⟨Lattice.LayerOut l [1] - Lattice.LayerOut l [0], hm⟩, ⟨Lattice.LayerOut l [0], h0⟩⟩
  · rintro ⟨⟨mz, hmz⟩, ⟨cz, hcz⟩⟩
    refine ⟨⟨[mz], cz⟩, fun x => ?_⟩
    have hval : ((Lattice.LayerOut ⟨[mz], cz⟩ [x] : ℤ) : ℝ) = (mz : ℝ) * (x : ℝ) + (cz : ℝ) := by
      simp [Lattice.LayerOut, Lattice.dot]
    calc s.eval ((x : ℤ) : ℝ) = s.m * (x : ℝ) + s.c := by simp [Segment.eval]
      _ = (mz : ℝ) * (x : ℝ) + (cz : ℝ) := by rw [hmz, hcz]
      _ = ((Lattice.LayerOut ⟨[mz], cz⟩ [x] : ℤ) : ℝ) := hval.symm

end Lattice.Lib.Compiler.BridgeToMainChain