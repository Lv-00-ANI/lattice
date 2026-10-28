import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealCanonicalForm
/-!
# LATTICE: `RealCanonicalCompileComm` 的**内核证据存档**（零锁可重跑、**零 olean 依赖**）

本文件是 `RealCanonicalCompileComm` 各项判定的**独立证据**：
**不引用该文件的任何定理**（⚠ 也**不 `import` 它** —— 见下），
只用既有模块的定义**从零重算**，使每条结论都可由**第二条独立路径**复核。

⚠⚠ **为什么不 `import RealCanonicalCompileComm`**：
该模块虽已登记 root，但**尚无 olean** ⟹ `import` 它会报
`unknown module prefix 'RealCanonicalCompileComm'`（STYLE 已登记的坑）。
⭐ **⇒ 本文件有意只依赖【已编译】的既有模块**，
故它**可在主模块构建前**独立验证（**这正是"内联探针法"的精神**）。
⇒ ⭐ **副产品**：本文件对主模块的每条关键判定给出**不共享代码路径**的复核。

⚠ **本文件的目的不是"再证一遍"，而是留下【可复算的反例】** ——
特别是**两条被本波次证伪的命题**（见 §二）。

**存档的判定**：
| § | 内容 | 内核结论 |
|:--|:--|:--|
| 一 | 权重侧往返是 `rfl`（零信息） | ✅ 定义恒等 |
| 二 | ⚠ **两条被证伪的命题** | ❌ **为假**（反例具体） |
| 三 | 交换律**真的**边界（`lam = ±1`） | ✅ 成立 |
| 四 | `b = 0` 分支的非平凡性（首元可为 0） | ✅ `content` 仍为 1 |

无 sorry / axiom / admit / native_decide。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、权重侧往返是 `rfl`（"经权重侧的交换律"空洞的**定义级**依据） -/

-- ⭐ `extractVec ∘ convertVec = id` **不是定理，是定义相等**
example (c : VectorConstraint) : extractVec (convertVec c) = c := rfl

-- ⭐ 反向也是定义相等（结构 eta）
example (l : LinearLayer) : convertVec (extractVec l) = l := by
  cases l with
  | mk w b => rfl

-- ⭐ 故 `canonicalize ∘ extract ∘ compile` 定义上就是 `canonicalize`
example : (fun c : VectorConstraint => canonicalize (extractVec (convertVec c)))
        = canonicalize := rfl

-- ⭐ 编译到列表级也是 `rfl`（`compileToLayer [c] = [convertVec c]`）
example (c : VectorConstraint) : compileToLayer [c] = [convertVec c] := rfl

/-! ## 二、⚠⚠ 两条**被证伪的命题**（本存档最重要的部分）

⚠ 两条都是**本波次 A8 初稿写的**，都在**内核**下被推翻。
⭐ 保留它们是为了**防止后来者重犯**（STYLE 的"登记假命题"纪律）。 -/

/-- ⭐ **假命题之一**：`Int.sign lam = lam ↔ lam = 1 ∨ lam = -1`（**无条件**）。

⚠ **`lam = 0` 是反例**：`Int.sign 0 = 0`（`Int.sign_zero`）**为真**，
而 `0 = 1 ∨ 0 = -1` **为假** ⟹ **`⟹` 方向失败**。
⭐ **⇒ 正确陈述必须带 `lam ≠ 0`**（`RealCanonicalCompileComm.int_sign_eq_self_iff`）。 -/
theorem sign_unconditional_version_is_false :
    ¬ (∀ lam : Int, Int.sign lam = lam ↔ lam = 1 ∨ lam = -1) := by
  intro h
  have h0 := (h 0).mp Int.sign_zero
  omega

/-- ⭐⭐ **假命题之二**：`canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam`（**`0 < lam`**）。

⚠ **`c = {a := [2], b := 2}`、`lam = 3` 是反例**：
- 左端 `canonicalize {a := [6], b := 6} = {a := [1], b := 1}`（内容 6 → 约掉）；
- 右端 `scaleVec {a := [1], b := 1} 3 = {a := [3], b := 3}`；
- ⭐ **`{[1],1} ≠ {[3],3}`**。

⭐ **根因（叙述性，非 tactic）**：该命题把**两条 RHS 形状不同的陈述**混为一谈 ——
`canonicalize_section_pos`（RHS **不含** `scaleVec`，**真**）
vs 真"交换律"（RHS **含** `scaleVec`，**假**）。
⇒ ⭐ **判据：RHS 是否含被交换的算子，决定该陈述是真"吸收"还是假"交换"**。 -/
theorem pos_commutation_version_is_false :
    ¬ (∀ (c : VectorConstraint) (lam : Int),
        constraintContent c ≠ 0 → 0 < lam →
        canonicalize (scaleVec c lam) = scaleVec (canonicalize c) lam) := by
  intro h
  have hc : constraintContent ({ a := [2], b := 2 } : VectorConstraint) ≠ 0 := by
    simp only [constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
    norm_num
  have h3 := h { a := [2], b := 2 } 3 hc (by norm_num)
  have h1 : canonicalize (scaleVec ({ a := [2], b := 2 } : VectorConstraint) 3)
          = ({ a := [1], b := 1 } : VectorConstraint) := by
    simp only [canonicalize, constraintContent, listGcdNat, scaleVec,
               List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
    norm_num
  have h2 : scaleVec (canonicalize ({ a := [2], b := 2 } : VectorConstraint)) 3
          = ({ a := [3], b := 3 } : VectorConstraint) := by
    simp only [canonicalize, constraintContent, listGcdNat, scaleVec,
               List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
    norm_num
  rw [h1, h2] at h3
  have hb : (1 : Int) = 3 := congrArg VectorConstraint.b h3
  omega

/-! ## 三、交换律的**真边界**：`lam = ±1`（具体反例 + 具体正例） -/

/-- ⭐ **`lam = -2` 是交换律的反例**（`RealCanonicalCompileComm` 的主反例，
此处**从零重算**，不引用该文件）。 -/
theorem comm_fails_at_neg_two :
    canonicalize (scaleVec ({ a := [2], b := 2 } : VectorConstraint) (-2))
      ≠ scaleVec (canonicalize ({ a := [2], b := 2 } : VectorConstraint)) (-2) := by
  intro h
  simp only [canonicalize, constraintContent, listGcdNat, scaleVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at h
  have hb : (-1 : Int) = -2 := congrArg VectorConstraint.b h
  omega

/-- ⭐ **`lam = 1` 时交换律【成立】**（充要条件的正面，`±1` 之一）。 -/
theorem comm_holds_at_one :
    canonicalize (scaleVec ({ a := [2], b := 2 } : VectorConstraint) 1)
      = scaleVec (canonicalize ({ a := [2], b := 2 } : VectorConstraint)) 1 := by
  rw [scaleVec_one, scaleVec_one]

/-- ⭐ **`lam = -1` 时交换律【成立】**（充要条件的正面，`±1` 之二）。

⚠ **注意 `-1` 也成立**，故"`lam < 0` 全假"是**错的** ——
交换律成立的**恰是 `±1`**（`RealCanonicalCompileComm.canonicalize_comm_scaleVec_iff`）。 -/
theorem comm_holds_at_neg_one :
    canonicalize (scaleVec ({ a := [2], b := 2 } : VectorConstraint) (-1))
      = scaleVec (canonicalize ({ a := [2], b := 2 } : VectorConstraint)) (-1) := by
  simp only [canonicalize, constraintContent, listGcdNat, scaleVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-- ⭐ **`canonicalize` 吞掉倍率**（`0 < lam` 时**为真**的那条陈述，具体见证 `lam = 3`）。

⭐ 与 `pos_commutation_version_is_false` 对照：**同一对 `c`/`lam`，
"吞掉"为真而"交换"为假** ⟹ 两者的差别**完全在 RHS 是否含 `scaleVec`**。 -/
theorem absorbs_scale_at_three :
    canonicalize (scaleVec ({ a := [2], b := 2 } : VectorConstraint) 3)
      = canonicalize ({ a := [2], b := 2 } : VectorConstraint) := by
  simp only [canonicalize, constraintContent, listGcdNat, scaleVec,
             List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil]
  norm_num

/-! ## 四、`b = 0` 分支的**非平凡性**：首元可以是 `0`

⚠ **这是 `RealCanonicalCompileComm` §三 `iff` 证明中 `b = 0` 分支的**必要性证据****：
`content = 1` **不保证**首元非零 ⟹ **不能用"首元"消去倍率**，必须用**非零分量的存在性**。 -/

/-- ⭐ **`a = [0, 1]`、`b = 0` 的内容为 `1`，而首元为 `0`**：

⭐ **它证明**："`content = 1` ⟹ 首元非零"是**假命题**
⟹ §三 的 `b = 0` 分支**必须**用 `exists_ne_zero_of_listGcdNat_ne_zero`（存在性），
**不能**用"取首元"。 -/
theorem content_one_does_not_force_head_nonzero :
    constraintContent ({ a := [0, 1], b := 0 } : VectorConstraint) = 1 ∧
    (0 : Int) = ({ a := [0, 1], b := 0 } : VectorConstraint).a.headD 1 := by
  refine ⟨?_, rfl⟩
  simp only [constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil]
  norm_num

end Lattice
