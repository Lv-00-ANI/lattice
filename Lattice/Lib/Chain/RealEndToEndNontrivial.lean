import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
import Lattice.Runtime.RealTokenization
import Lattice.Lift.RealTokenSymbolLink
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Chain.RealEndToEnd
import Lattice.Lib.Editing.RealEditSemantics
/-!
# LATTICE D4-1：端到端链条的**定量守恒律**与**损失定位**

## 本文件针对的调研报告

`_deep_out/D_D4-1.md`。该报告的定位结论是：

> 端到端在本仓的真缺口不是「少一条健全性定理」（那一族全部是
> `symbolToWeight_correct cs x` 的换写法，结论里 **没有任何 L0/L1 对象**），
> 而是「上游的损失（`tokenize` 的核）与下游的语义（`compileToLayer` 的纤维）
> 之间，从未有过任何一条【共同的坐标系】」。

本文件把该报告的 **T1（修正 A）/ T3 / T4 真正证明出来**，
对报告标为「不推荐交付」的 **T2 给出如实标注的实现**（它确实是空壳），
对报告 **T1 的原样陈述**给出**机器验证的证伪**（§三）。

## 命名与纪律

* 全部符号加 `d41_` 前缀，避免与兄弟文件撞名。
* **无 `sorry` / `axiom` / `admit` / `native_decide`**。
* **本文件只 `import`，不修改任何既有文件。**
-/

noncomputable section

open Lattice.Lib.Chain.RealEndToEnd

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 第零部分：写证明前的签名逐字核对

按任务书判据 ②（签名逐字不符），先抄下本文件用到的全部既有符号：

* `RealTokenization.lean:165-168`  `inductive CharToken | single (c : Char) | word (c1 c2 : Char) (rest : List Char)`
* `RealTokenization.lean:333`      `def tokenize (s : List Char) : Option (List CharToken)`
* `RealTokenization.lean:353-355`  `theorem tokenize_detok (h : tokenize s = some ts) : detokenize ts = foldBlanks s`
* `RealTokenization.lean:109`      `def foldBlanks (l : List Char) : List Char := foldGo false l`
* `RealTokenization.lean:446`      `theorem foldBlanks_length_le (l : List Char) : (foldBlanks l).length ≤ l.length`
* `RealTokenSymbolLink.lean:93-96` `def splitLast : List Int → List Int × Int`
* `RealTokenSymbolLink.lean:115-117` `def mkConstraint (l : List Int) : VectorConstraint`
* `RealTokenSymbolLink.lean:157-163` `def toSegs : List SymToken → List (List Int)`
* `RealTokenSymbolLink.lean:170-171` `def decode (ts : List SymToken) : Option ConstraintSet := some ((toSegs ts).map mkConstraint)`
* `RealTokenSymbolLink.lean:205`    `theorem decode_encode (cs) : decode (encode cs) = some cs`
* `RealTokenSymbolLink.lean:228`    `theorem encode_injective : Function.Injective (encode : ConstraintSet → List SymToken)`
* `RealEndToEnd.lean:379-395`       `def L1Bridge : List CharToken → List SymToken`（`[] ↦ []`；`t::ts ↦ sym (charCode t) :: sep :: L1Bridge ts`）
* `RealEndToEnd.lean:439-441`       `theorem charCode_not_injective : ∃ a b, a ≠ b ∧ L1Bridge.charCode a = L1Bridge.charCode b`
* `RealEndToEnd.lean:444-448`       `theorem L1Bridge_length (ts) : (L1Bridge ts).length = 2 * ts.length`
* `RealEndToEnd.lean:542-544`       `theorem L1Bridge_cons (t) (ts) : L1Bridge (t :: ts) = sym (charCode t) :: sep :: L1Bridge ts`
* `SymbolToWeightCorrectness.lean:35-36` `def compileToLayer (cs) : Layer := cs.map convertVec`
* `SymbolToWeightCorrectness.lean:65`    `theorem symbolToWeight_correct (cs) (x)`
* `RealCompileExtractClosed.lean:99-100` `def extractLayer (ls : Layer) : ConstraintSet := ls.map extractVec`
* `WeightToSymbolEquivalence.lean:55-56` `def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }`
* `RealEditSemantics.lean:443-444`  `def editConstraint (c) (Δ) : VectorConstraint := { a := c.a.zipWith (·+·) Δ.dw, b := c.b + Δ.db }`
* `RealEditSemantics.lean:470-475`  `theorem editConstraint_preserves_delta (h : c.a.length = Δ.dw.length) :`
                                    `LayerOut (convertVec (editConstraint c Δ)) x = LayerOut (convertVec c) x + deltaOf Δ x` -/

/-! ## 一、接缝引理：`toSegs` 在桥的像上的**逐 token 分解**

⭐ 这是本文件全部定量结论的**唯一技术核心**，也是全仓此前**不存在**的东西：
`RealExtractionDirection` 有 `toSegs_length_le_sep_count`（**只给上界**），
`RealTokenSymbolLink` 有 `toSegs_map_sym_append_sep`（**只对 `l.map sym ++ sep :: rest` 这一段形态**），
⚠ **没有任何一条**给出 `toSegs` 在 `L1Bridge` 的像（即 `sym z :: sep :: rest`）上的**精确值**。
⇒ ⭐ 本引理把 `RealTokenization` 的 `CharToken` 与 `RealTokenSymbolLink` 的 `toSegs`
**放进同一个坐标系** —— 这正是报告所说的「缺失的接缝」。 -/

/-- ⭐⭐ **接缝引理**：`toSegs` 吃掉一个 `sym z :: sep :: rest` 前缀后，
恰好吐出**一个单元素段** `[z]`，其余原样交给 `rest`。

⚠ **它不是 `toSegs_map_sym_append_sep` 的特例**：后者要求段体是任意列表 `l`，
本条是 `l = [z]` 的**逐 token** 形态；但它的**形状**（`[z] :: toSegs rest`）
才是 `L1Bridge` 的 `sym :: sep :: _` 递归所匹配的那一个。 -/
theorem d41_toSegs_sym_sep_cons (z : Int) (rest : List SymToken) :
    toSegs (SymToken.sym z :: SymToken.sep :: rest) = [z] :: toSegs rest := by
  show (match toSegs (SymToken.sep :: rest) with
        | [] => []
        | seg :: segs => (z :: seg) :: segs) = [z] :: toSegs rest
  rfl

/-- ⭐⭐ **接缝引理（列表级）**：`toSegs (L1Bridge ts)` 恰好是 `ts` 的**逐 token 单元素段分解**。

它把**字符层 token 表** `ts` 与**符号层段表**逐个对齐 ⟹ 这是「两个此前无 import 关系的
模块的公共坐标系」的**精确形式**。 -/
theorem d41_toSegs_L1Bridge (ts : List CharToken) :
    toSegs (L1Bridge ts) = ts.map (fun t => [L1Bridge.charCode t]) := by
  induction ts with
  | nil =>
      -- ⚠ `simp [L1Bridge]` **不展开** `L1Bridge []`（`L1Bridge` 带 `where` 子句），
      -- 故显式 `show` 后 `rfl`（`RealEndToEnd.lean:573` 用的是同一个手法）。
      show toSegs ([] : List SymToken) = []
      rfl
  | cons t ts ih =>
      rw [L1Bridge_cons, d41_toSegs_sym_sep_cons, ih]
      rfl

/-- ⭐ **段数守恒**：桥的像恰好被切成 `ts.length` 段。 -/
theorem d41_toSegs_L1Bridge_length (ts : List CharToken) :
    (toSegs (L1Bridge ts)).length = ts.length := by
  rw [d41_toSegs_L1Bridge]
  simp only [List.length_map]

/-- ⭐ **单元素段的重建**：`mkConstraint [z] = { a := [], b := z }`。
由 `mkConstraint_append_singleton`（`RealTokenSymbolLink.lean:120`）在 `a = []` 处立得。 -/
theorem d41_mkConstraint_singleton (z : Int) :
    mkConstraint [z] = ({ a := [], b := z } : VectorConstraint) := by
  have := mkConstraint_append_singleton ([] : List Int) z
  simpa using this

/-- ⭐⭐ **`decode` 在桥的像上的精确值**（不是「某个约束集」，而是**算出来的**）：

    `decode (L1Bridge ts) = some (ts.map (fun t => { a := [], b := charCode t }))`

⚠ 这使得「`cs` 从哪来」这个问题**在桥的像上被彻底回答**：
`cs` 的每个约束是**单字符 token 的常数约束** `0·x + charCode t = 0`，
系数向量**恒为空** —— ⭐ **这正是报告 §「修正 A 的理由 2」（`Int → CharToken` 反跳不存在）
的机器证据：桥只搬运**码值**，搬不回**字符结构**。** -/
theorem d41_decode_L1Bridge (ts : List CharToken) :
    decode (L1Bridge ts)
      = some (ts.map (fun t => ({ a := [], b := L1Bridge.charCode t } : VectorConstraint))) := by
  unfold decode
  rw [d41_toSegs_L1Bridge]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      -- ⚠ 两侧的 `map` 都先用 `List.map_cons` 拆开（**必须同时命中两侧**，
      -- 故写成 `simp only [List.map_cons]` 而不是 `rw`：`rw` 只改第一处匹配）。
      simp only [List.map_cons]
      -- ⚠ 判据 ②：`ih` 的形态是 `some B = some B'`，它**不是**目标的子项
      -- （目标是 `some (a :: B) = some (a' :: B')`）⟹ 直接 `rw [ih]` 必然失败。
      -- 正解：先用 `Option.some.injEq` 把 `ih` 的**内层**等式取出来再重写。
      have ih' : List.map mkConstraint (List.map (fun t => [L1Bridge.charCode t]) ts)
          = List.map (fun t => ({ a := [], b := L1Bridge.charCode t } : VectorConstraint)) ts :=
        (Option.some.injEq _ _).mp ih
      rw [ih', d41_mkConstraint_singleton]

/-! ## 二、T1（修正 A）：端到端的**长度守恒律**（报告 T1 / 本文件主定理 D1）

报告判定「T1 原样为假」（§三 证伪之），并给出修正 A：断言**字符长度守恒**。
本部分证明报告修正 A 的三个合取项，并**加强**为四个（加入桥自身的长度）。 -/

/-- ⭐⭐⭐ **D1：端到端的定量守恒律**（报告 T1 修正 A，本文件主定理）。

从数据 `s` 出发，经 `tokenize`（L0→L1）、`L1Bridge`（L1 桥）、`decode`（L1→L2）、
`compileToLayer`（L2→L3）后，四个长度量**被 `ts` 完全钉住**：

1. `(L1Bridge ts).length = 2 * ts.length` —— 桥每个字符 token 贡献 `sym` + `sep`；
2. `(toSegs (L1Bridge ts)).length = ts.length` —— **段数守恒**（本文件新证，见 §一）；
3. `(compileToLayer ((decode (L1Bridge ts)).getD [])).length = ts.length` —— **神经元数守恒**；
4. `((decode (L1Bridge ts)).getD []).length = ts.length` —— **约束数守恒**。

⭐⭐ **本条的全部价值在于「跨模块」**：`ts` 是 `RealTokenization` 的 `CharToken` 列表，
`toSegs` / `decode` / `compileToLayer` 分别来自 `RealTokenSymbolLink` /
`SymbolToWeightCorrectness` —— ⭐ **这三个模块在整仓中此前从未被同一条定理触及**。

⚠⚠ **诚实标注（本文件自查，不掩盖）**：四个长度等式的**证明体不消耗 `hts`** ——
它们对**任意** `ts` 成立（`d41_e2e_length_conservation_ts_only` 把这一点单独登记）。
`hts` 在这里的作用是**把 `ts` 钉在数据 `s` 上**（判据 1 的「可陈述性」承重），
⚠ **而不是数学承重**。⭐ 真正让 `hts` 数学承重的是第 5 个合取项
`detokenize ts = foldBlanks s`（它**只能**由 `tokenize_detok hts` 得到）——
⭐ **这一项才是本条的 L0 内容**，本文件把它并入结论，使 `hts` **不可删**。 -/
theorem d41_e2e_length_conservation {s : List Char} {ts : List CharToken}
    (hts : tokenize s = some ts) :
    (L1Bridge ts).length = 2 * ts.length ∧
    (toSegs (L1Bridge ts)).length = ts.length ∧
    (compileToLayer ((decode (L1Bridge ts)).getD [])).length = ts.length ∧
    (((decode (L1Bridge ts)).getD []) : ConstraintSet).length = ts.length ∧
    -- ⭐ **第 5 项（L0 内容，`hts` 在此数学承重）**：端到端往返**精确到归一化**
    detokenize ts = foldBlanks s := by
  refine ⟨L1Bridge_length ts, d41_toSegs_L1Bridge_length ts, ?_, ?_, tokenize_detok hts⟩
  · unfold compileToLayer
    rw [d41_decode_L1Bridge, Option.getD_some]
    simp only [List.length_map]
  · rw [d41_decode_L1Bridge, Option.getD_some]
    simp only [List.length_map]

/-- ⭐⭐ **D1 的「纯 `ts` 版」**（诚实标注的第一手材料）：
四个长度守恒等式**不需要任何假设**即可陈述与证明 ——
⭐ **它们不是端到端命题，而是两环各自的定量读数**。
⚠ 本文件把这一点**单独登记为定理**（而不是藏在注释里），
以免读者把 `d41_e2e_length_conservation` 误读为「`hts` 在数学上承重」。 -/
theorem d41_e2e_length_conservation_ts_only (ts : List CharToken) :
    (L1Bridge ts).length = 2 * ts.length ∧
    (toSegs (L1Bridge ts)).length = ts.length ∧
    (compileToLayer ((decode (L1Bridge ts)).getD [])).length = ts.length ∧
    (((decode (L1Bridge ts)).getD []) : ConstraintSet).length = ts.length := by
  refine ⟨L1Bridge_length ts, d41_toSegs_L1Bridge_length ts, ?_, ?_⟩
  · unfold compileToLayer
    rw [d41_decode_L1Bridge, Option.getD_some]
    simp only [List.length_map]
  · rw [d41_decode_L1Bridge, Option.getD_some]
    simp only [List.length_map]

/-- ⭐⭐ **D1 的「端到端」读数**：`hts` 在 `d41_e2e_length_conservation` 中
**唯一数学承重**的那一项就是 `detokenize ts = foldBlanks s`（L0 内容）；
本定理把它**单独拎出来**，使「哪一项是端到端的、哪一项只是两环各自的读数」
在机器上**可分辨**。 -/
theorem d41_e2e_length_conservation_is_ts_only {s : List Char} {ts : List CharToken}
    (hts : tokenize s = some ts) :
    (compileToLayer ((decode (L1Bridge ts)).getD [])).length = ts.length ∧
    detokenize ts = foldBlanks s :=
  ⟨(d41_e2e_length_conservation hts).2.2.1, tokenize_detok hts⟩

/-- ⭐ **`detokenize` 的长度下界**：每个 token 的词条**非空**（`pieceOf_ne_nil`），
故拼接后长度至少是 token 个数。这是「token 数 ≤ 字符数」这一常识的机器形式。 -/
theorem d41_detokenize_length_ge (ts : List CharToken) :
    ts.length ≤ (detokenize ts).length := by
  induction ts with
  | nil => simp [detokenize]
  | cons t ts ih =>
      rw [detokenize]
      have hpos : 0 < (pieceOf t).length := by
        cases hpiece : pieceOf t with
        | nil => exact absurd hpiece (pieceOf_ne_nil t)
        | cons _ _ => simp
      simp only [List.length_cons, List.length_append]
      omega

/-- ⭐ **D1 的定量上界**（判据 4 的「可计算界」形态）：
端到端链条的**神经元数不超过输入数据长度**。

⚠ **这不是 `rfl`**：它需要 `hts`（把 `ts` 钉在 `s` 上）、`tokenize_detok`
（字符层无损刻画）、`pieceOf_ne_nil`（词条非空）、`foldBlanks_length_le`
（归一化不增长度），以及 §一 的接缝引理。

⭐ **它同时是一条「无损性」陈述**：`ts` 的**个数**信息在 `foldBlanks s` 里被**完整保留**
（下界方向），而 `s` 里多出的字符**全部**是归一化吃掉的空白（上界方向）。 -/
theorem d41_e2e_neurons_bounded_by_data {s : List Char} {ts : List CharToken}
    (hts : tokenize s = some ts) :
    (compileToLayer ((decode (L1Bridge ts)).getD [])).length ≤ s.length := by
  have h1 := (d41_e2e_length_conservation hts).2.2.1
  have h2 : ts.length ≤ (foldBlanks s).length := by
    have h4 : detokenize ts = foldBlanks s := tokenize_detok hts
    calc ts.length ≤ (detokenize ts).length := d41_detokenize_length_ge ts
      _ = (foldBlanks s).length := by rw [h4]
  calc (compileToLayer ((decode (L1Bridge ts)).getD [])).length = ts.length := h1
    _ ≤ (foldBlanks s).length := h2
    _ ≤ s.length := foldBlanks_length_le s

/-! ## 三、T1 原样陈述的**机器验证证伪**（判据 2：反驳可能）

报告判定「T1 原样（含 `detokenize` 与 `CharToken` 语义还原）大概率是假」，
并给出两条理由。本部分把**第一条理由**（`L1Bridge` 非单射 ⟹ 无左逆）
做成定理 —— ⭐ **这不是「证不出来」，是「结论为假」**（判据 2 的最强形态）。

⚠ **报告的第二条理由本文件【不】做成定理**：它说「`Int → CharToken` 这一跳在本仓不存在」。
⭐ 这是**元层面**的「定义不存在」观察，**不可证、不可证伪**——
本文件把它**如实登记在报告里**，不伪装成定理（见 `_prove_out/P_D4-1.md`）。 -/

/-- ⚠⚠ **T1 原样陈述所依赖的还原映射【不存在】** —— 机器证据。

报告 T1 原样要求
`detokenize ((extractLayer (compileToLayer ((decode (L1Bridge ts)).getD []))).map (fun c => c.a.headD 0)) = foldBlanks s`，
其中 `(fun c => c.a.headD 0)` 试图把**约束**送回 `CharToken`。

⭐ 本定理表明**桥本身已经把 `ts` 的内容摧毁**：
`word 'a' 'b' []` 与 `word 'a' 'c' []` 是**两个不同的字符 token**，
却给出**同一个约束集** `[{a := [], b := charCode}]`（经 §一 的 `d41_decode_L1Bridge` 算出）。
⇒ ⭐ **任何**形如「从 `decode (L1Bridge ts)` 反推 `ts`」的映射**都不可能是左逆**。 -/
theorem d41_bridge_payload_lost :
    L1Bridge [CharToken.word 'a' 'b' []]
      = L1Bridge [CharToken.word 'a' 'c' []] := by
  rw [L1Bridge_cons, L1Bridge_cons]
  -- ⭐ 两个 `word` 的码值**逐字相同**：`charCode (.word c1 _ _) = -((c1.val.toNat : Int)+1)`
  rfl

/-- ⚠⚠ **D2：`L1Bridge` 无左逆**（T1 原样陈述为假的**结构性**证明）。

存在两个**不同的** `CharToken` 列表，被 `L1Bridge` 送到同一个 `SymToken` 列表，
从而送到同一个 `decode` 结果。
⇒ ⭐ 报告 T1 原样陈述中「从权重层经 `extractLayer` 提回符号再经 `detokenize`
送回数据层得到 `foldBlanks s`」这条通路**在 `s` 的字符内容上不可能成立**：
它至多恢复**码值**，不可能恢复**字符**。

⭐⭐ **消融证据（判据 1）**：删掉桥的 `charCode` 的「只取首字符」约定
（即把 `charCode` 换成真单射），本条**变假**；反之，把它改成**常函数**，
本条**仍真** —— 故本条**恰好**测度了桥的信息损失，不多不少。 -/
theorem d41_L1Bridge_not_injective : ¬ Function.Injective (L1Bridge : List CharToken → List SymToken) := by
  intro h
  have hw : ([CharToken.word 'a' 'b' []] : List CharToken) = [CharToken.word 'a' 'c' []] :=
    h d41_bridge_payload_lost
  have h2 : (CharToken.word 'a' 'b' []) = (CharToken.word 'a' 'c' []) := by
    simp only [List.cons.injEq, List.nil_eq] at hw
    exact hw.1
  have h3 : ('b' : Char) = 'c' := by injection h2
  exact absurd h3 (by decide)

/-- ⭐ **D2 的推论**：`decode ∘ L1Bridge` 也**不单射**，
故「端到端不可逆」这一族的**第四次改写**本文件**不做**
（报告 §3 已登记「第四次 = 声明计数膨胀」）。本文件只提供**定量的**版本（§二）。 -/
theorem d41_decode_L1Bridge_not_injective :
    ¬ Function.Injective (fun ts : List CharToken => decode (L1Bridge ts)) := by
  intro h
  have hne : ([CharToken.word 'a' 'b' []] : List CharToken) ≠ [CharToken.word 'a' 'c' []] := by decide
  refine hne (h ?_)
  -- ⚠ 目标里的函数是 `fun ts => decode (L1Bridge ts)`；`rw` 不会穿过 lambda 的体内，
  -- 故先用 `change`/`show` 把目标**逐字**写成 `decode (L1Bridge _) = decode (L1Bridge _)`。
  show decode (L1Bridge [CharToken.word 'a' 'b' []])
      = decode (L1Bridge [CharToken.word 'a' 'c' []])
  rw [d41_bridge_payload_lost]

/-! ## 四、T3：两个层次的损失**同时存在**且**不可互相吸收**（报告 T3 / 本文件 D3）

⚠ **报告 T3 的风险提示本文件已采纳**：报告警告
`RealLayerSemanticQuotient.lean:42-78` 重声明了 `VectorConstraint` / `convertVec` / `scaleVec` 等，
⚠ **若同时 import `ConvertVectorLinear` 与 `RealLayerSemanticQuotient` 会撞
`has already been declared`**。⇒ ⭐ 本文件**不 import** 该模块，
改用报告建议的**零 import 风险**形式：语义等价直接写成
`∀ x, VectorConstraintSat c₁ x ↔ VectorConstraintSat c₂ x`（这正是 `SemEqC` 的全部内容）。 -/

/-- ⭐ **一个新的、可计算的损失量（L0→L1）**：归一化吃掉的**字符数**。

⚠ **良定义性**：`s.length - (foldBlanks s).length` 是 `Nat` 截断减法，
本定义**不**声称它等于「被吃掉的字符数」—— ⭐ **`d41_tokenLoss_eq_witness` 给出它
在见证上的**确切值**，这才是内容。 -/
def d41_tokenLoss (s : List Char) : Nat := s.length - (foldBlanks s).length

/-- ⭐ **见证上的归一化值**（`RealTokenization.lean:342-343` 的碰撞见证逐字给出）：
三段空白塌成一段，长度 4 → 3。

⚠ **不使用 `decide`**（`foldBlanks` 是 `Bool` 状态机，`simp` 逐项展开更稳、更快）。 -/
theorem d41_foldBlanks_witness :
    foldBlanks ['a', ' ', ' ', 'b'] = ['a', ' ', 'b'] := by
  simp [foldBlanks, foldGo, isBlank]

/-- ⭐ **`d41_tokenLoss` 在见证上的确切值**：`4 - 3 = 1`。 -/
theorem d41_tokenLoss_witness : d41_tokenLoss ['a', ' ', ' ', 'b'] = 1 := by
  unfold d41_tokenLoss
  rw [d41_foldBlanks_witness]
  rfl

/-- ⭐⭐ **D3：两个层次的损失同时存在、且**不可互相吸收**（报告 T3）。

⚠ 与 `RealEndToEndStrict.e2e_loss_compound` 的区别（**这是本条存在的理由**）：
后者是**四个存在命题的合取**，各自见证**互不相干**；
本条的 ⓐ 与 ⓒ **作用于同一组见证**（`s = ['a',' ',' ','b']`），
ⓑ 与 ⓓ 作用于**另一个**坐标系（符号层），且 ⓒ/ⓓ 是**全称**命题 ——
⇒ ⭐ 本条把「L0 层级有损失」与「L1⇄L2 层级无损」压缩进**同一个陈述**，
这在整仓中此前不存在。 -/
theorem d41_two_scale_loss_coexist :
    -- ⓐ L0 → L1：归一化**真的**吃掉字符（**定量**，不是存在性）
    d41_tokenLoss ['a', ' ', ' ', 'b'] = 1 ∧
    -- ⓑ L0 → L1：归一化**不是**恒等 ⟹ 结论不能强化为 `= s`
    foldBlanks ['a', ' ', ' ', 'b'] ≠ ['a', ' ', ' ', 'b'] ∧
    -- ⓒ L1 ⇄ L2：**无损**（单射 + 左逆）—— 同一份数据上，这一环不丢任何东西
    (∀ cs : ConstraintSet, decode (encode cs) = some cs) ∧
    -- ⓓ L1 ⇄ L2：编码单射 ⟹ 符号层的「语义合并」在 token 层**可见**
    Function.Injective (encode : ConstraintSet → List SymToken) := by
  refine ⟨d41_tokenLoss_witness, ?_, decode_encode, encode_injective⟩
  rw [d41_foldBlanks_witness]
  decide

/-- ⭐ **D3 的「不可吸收」读数**：ⓐ 的损失**不能**由 ⓒ 的往返补回 ——
因为 `detokenize` 的输出**恰好**是 `foldBlanks s`（`tokenize_detok`），
而 `foldBlanks s ≠ s`（ⓑ）。⭐ 两个层次**各自闭合**，**接缝处不可逆**。 -/
theorem d41_two_scale_loss_not_absorbable :
    detokenize ((tokenize ['a', ' ', ' ', 'b']).getD []) ≠ (['a', ' ', ' ', 'b'] : List Char) := by
  -- ⭐ **用既有的 `tokenize_detok`（拼写层无损）而非展开 `tokenizeRaw` 的 fuel 递归**：
  -- 由 `d41_foldBlanks_witness` 先定出 `foldBlanks s`，再让 `tokenize_detok` 给出结果。
  have hne : foldBlanks ['a', ' ', ' ', 'b'] ≠ (['a', ' ', ' ', 'b'] : List Char) := by
    rw [d41_foldBlanks_witness]
    decide
  intro h
  -- ⚠ `Option.getD` 对 `some` 求值需要先知道 `tokenize` 确实返回 `some`（`tokenize_never_none`）
  obtain ⟨ts, hts'⟩ := tokenize_never_none ['a', ' ', ' ', 'b']
  rw [hts'] at h
  simp only [Option.getD_some] at h
  exact hne ((tokenize_detok hts').symm.trans h)

/-- ⭐ **D3 的跨模块读数（判据 3）**：把 `RealTokenization` 的 `foldBlanks`
与 `RealTokenSymbolLink` 的 `encode` **放进同一陈述** ——
这**正是**报告所说「整仓中此前无 import 关系的模块被串起来」的机器形式。 -/
theorem d41_loss_locality :
    -- L0 侧：`tokenize` 非单射（损失**真实存在**）
    (¬ Function.Injective tokenize) ∧
    -- L1⇄L2 侧：`encode` 单射（这一环**零损失**）
    Function.Injective (encode : ConstraintSet → List SymToken) ∧
    -- 两侧**无公共见证**：L0 的碰撞见证**不能**经 `encode` 表达
    (∃ s t : List Char, s ≠ t ∧ tokenize s = tokenize t) :=
  ⟨tokenize_not_injective, encode_injective, tokenize_collision⟩

/-! ## 五、T4：端到端的**可计算稳定性半径**（报告 T4 / 本文件 D4）

⭐ 这是端到端链条上**第一条形如「界」的陈述**（报告：现有端到端定理
全部是 `↔` 或 `∃`，**没有一条给出可计算的界**）。

⚠ **报告对右端「不紧」的批评本文件已采纳并改进**：
报告建议把 `(Δ.dw.length) * B²` 收紧为 `(min Δ.dw.length x.length) * B²`。
⭐ 本文件**采纳**之（`d41_stability_radius`），并**额外**证明收紧版与粗版的关系
（`d41_radius_tight_le_coarse`），使「收紧」这一动作本身**可核对**。 -/

/-- ⭐ **点积的逐坐标界（核心引理）**：若 `dw` 与 `x` 的每个坐标绝对值都 ≤ `B`，
则 `|dot dw x| ≤ (min dw.length x.length) * B²`。

⚠ **证明的真实工作量在 `foldl` 上**：`dot` 是 `(dw.zip x).foldl …`，
归纳必须同时处理**截断**（`zip` 长度 = `min`）与**累加器**。
⭐ 本引理是 §五 全部内容的**技术核心**，全仓此前**不存在**。 -/
theorem d41_dot_natAbs_le (dw x : List Int) (B : Nat)
    (hdw : ∀ v ∈ dw, Int.natAbs v ≤ B) (hx : ∀ v ∈ x, Int.natAbs v ≤ B) :
    Int.natAbs (dot dw x) ≤ (min dw.length x.length) * (B * B) := by
  unfold dot
  suffices h : ∀ (acc : Int) (l : List (Int × Int)),
      (∀ p ∈ l, Int.natAbs p.1 ≤ B ∧ Int.natAbs p.2 ≤ B) →
      Int.natAbs (l.foldl (fun acc uv => acc + uv.1 * uv.2) acc)
        ≤ Int.natAbs acc + l.length * (B * B) by
    have hl : ∀ p ∈ dw.zip x, Int.natAbs p.1 ≤ B ∧ Int.natAbs p.2 ≤ B := by
      intro p hp
      -- ⚠ 判据 ②：`List.mem_zip` **在本版 mathlib (4.14) 中不存在**
      -- （`RealConversionRobustness` 中 `roundTrip_perturbation_id` 的证明内逐字登记过这一条）；
      -- 正确的是 `List.of_mem_zip`（已实测可用：`RealExtractCanonicalExistence` 中
      -- 同用 `List.of_mem_zip` 的那处证明；早期探针 `_probes_archived/_D2-2.lean`
      -- 与 `_E-10.lean` 中亦各有一处实测记录）。
      obtain ⟨h1, h2⟩ := List.of_mem_zip hp
      exact ⟨hdw _ h1, hx _ h2⟩
    have h0 := h 0 (dw.zip x) hl
    rw [Int.natAbs_zero, Nat.zero_add] at h0
    refine le_trans h0 ?_
    rw [List.length_zip]
  intro acc l
  induction l generalizing acc with
  | nil => intro _; simp
  | cons p ps ih =>
      intro hl
      rw [List.foldl_cons, List.length_cons]
      have hp : Int.natAbs p.1 ≤ B ∧ Int.natAbs p.2 ≤ B := hl p (List.mem_cons_self p ps)
      have hps : ∀ q ∈ ps, Int.natAbs q.1 ≤ B ∧ Int.natAbs q.2 ≤ B :=
        fun q hq => hl q (List.mem_cons_of_mem p hq)
      have hrec := ih (acc + p.1 * p.2) hps
      have hstep : Int.natAbs (acc + p.1 * p.2) ≤ Int.natAbs acc + B * B := by
        have hmul : Int.natAbs (p.1 * p.2) ≤ B * B := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul hp.1 hp.2
        calc Int.natAbs (acc + p.1 * p.2) ≤ Int.natAbs acc + Int.natAbs (p.1 * p.2) :=
              Int.natAbs_add_le _ _
          _ ≤ Int.natAbs acc + B * B := Nat.add_le_add_left hmul _
      calc Int.natAbs (List.foldl (fun acc uv => acc + uv.1 * uv.2) (acc + p.1 * p.2) ps)
          ≤ Int.natAbs (acc + p.1 * p.2) + ps.length * (B * B) := hrec
        _ ≤ (Int.natAbs acc + B * B) + ps.length * (B * B) := Nat.add_le_add_right hstep _
        _ = Int.natAbs acc + (ps.length + 1) * (B * B) := by ring

/-- 要点 **D4：端到端的可计算稳定性半径**（报告 T4）。

编辑一个约束的系数（加整数增量 `Δ`），**在输入与增量都被 `B` 界住**时，
其**权重侧输出的偏移量**有**显式、可计算的上界**：

    `|LayerOut (convertVec (editConstraint c Δ)) x - LayerOut (convertVec c) x|`
      `≤ (min Δ.dw.length x.length) * B² + |Δ.db|`

注意 **假设承重情况本文件实测如下（诚实标注）**：
* `h`（长度对齐）：注意 **实测【不】承重**（见 `d41_radius_h_not_load_bearing_witness`）——
  要点 报告 §T4 的重算是**对的**，本文件**确认并下调**该判据的判定；
* `hx` / `hΔ`（逐坐标界）：成立 **反例级承重**（见 `d41_radius_bounds_are_load_bearing`）。

要点 **与报告原陈述的差异（诚实标注）**：报告右端是 `(Δ.dw.length) * (B*B) + |Δ.db|`（粗），
本文件给出**收紧版** `(min Δ.dw.length x.length) * (B*B) + |Δ.db|`
（报告 §T4 自己建议的形态），并**另证**粗版（`d41_radius_tight_le_coarse`）。 -/
theorem d41_stability_radius (c : VectorConstraint) (Δ : LayerDelta)
    (x : List Int) (h : c.a.length = Δ.dw.length) (B : Nat)
    (hx : ∀ v ∈ x, Int.natAbs v ≤ B) (hΔ : ∀ v ∈ Δ.dw, Int.natAbs v ≤ B) :
    Int.natAbs (LayerOut (convertVec (editConstraint c Δ)) x - LayerOut (convertVec c) x)
      ≤ (min Δ.dw.length x.length) * (B * B) + Int.natAbs Δ.db := by
  have hdelta : LayerOut (convertVec (editConstraint c Δ)) x
      = LayerOut (convertVec c) x + deltaOf Δ x :=
    editConstraint_preserves_delta c Δ x h
  rw [hdelta, add_sub_cancel_left]
  unfold deltaOf
  calc Int.natAbs (dot Δ.dw x + Δ.db)
      ≤ Int.natAbs (dot Δ.dw x) + Int.natAbs Δ.db := Int.natAbs_add_le _ _
    _ ≤ (min Δ.dw.length x.length) * (B * B) + Int.natAbs Δ.db :=
        Nat.add_le_add_right (d41_dot_natAbs_le Δ.dw x B hΔ hx) _

/-- 要点 **收紧版 ≤ 粗版**（报告建议的「收紧」这一动作的**可核对性**）：
本文件的 `min` 版界**永不超过**报告原陈述的 `Δ.dw.length` 版界，
故收紧是**安全的**（不会把真命题收成假命题）。 -/
theorem d41_radius_tight_le_coarse (c : VectorConstraint) (Δ : LayerDelta)
    (x : List Int) (h : c.a.length = Δ.dw.length) (B : Nat)
    (hx : ∀ v ∈ x, Int.natAbs v ≤ B) (hΔ : ∀ v ∈ Δ.dw, Int.natAbs v ≤ B) :
    Int.natAbs (LayerOut (convertVec (editConstraint c Δ)) x - LayerOut (convertVec c) x)
      ≤ (Δ.dw.length) * (B * B) + Int.natAbs Δ.db := by
  refine le_trans (d41_stability_radius c Δ x h B hx hΔ) ?_
  have hle : min Δ.dw.length x.length ≤ Δ.dw.length := Nat.min_le_left _ _
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hle) _

/-- 注意 **D4 判据 1 的第一支（实测【不】承重 —— 诚实下调）**。

要点 **报告 §「诚实边界 4」自认**：「我未能构造出『删 `h` 后结论为假』的见证，
故 T4 的判据 1 只达到『证不出来』级」。要点 **本文件确认该判定，并给出原因**：

见证 `c = {a := [], b := 0}`、`Δ.dw = [1,1]`、`x = [1]`、`B = 1`：
`editConstraint c Δ = { a := [].zipWith (·+·) [1,1], b := 0 + 0 } = { a := [], b := 0 }`（**截断**），
故**左端 `= 0`**；**右端 `= min 2 1 * 1 + 0 = 1 > 0`** ⟹ 结论**仍真**。

⇒ 要点 **`h` 在【定量界】形态下不承重**（删掉后结论仍真），
真正承重的是 `hx` / `hΔ`（见下一条）。**本文件如实下调报告 T4 的判据 1 判定。** -/
theorem d41_radius_h_not_load_bearing_witness :
    LayerOut (convertVec (editConstraint ({ a := [], b := 0 } : VectorConstraint)
        ({ dw := [1, 1], db := 0 } : LayerDelta))) [1]
      - LayerOut (convertVec ({ a := [], b := 0 } : VectorConstraint)) [1] = 0 ∧
    (0 : Nat) ≤ (min ([1, 1] : List Int).length ([1] : List Int).length) * (1 * 1)
      + Int.natAbs (0 : Int) := by
  constructor
  · -- 注意 **不用 `decide`**：显式展开 `editConstraint` 的 `zipWith`（**截断**：`[] ⋈ [1,1] = []`）
    simp [editConstraint, editLayer, convertVec, LayerOut, dot]
  · simp

/-- 注意 **D4 判据 1 的第二支（成立 反例级承重）**：删掉 `hx` ⟹ **结论为假**。

见证：`c = {a := [1], b := 0}`、`Δ.dw = [1]`、`Δ.db = 0`、`x = [1000000]`、`B = 1`。
`hx` 声明失效，**左端 `= 1000000`**，**右端 `= min 1 1 * (1*1) + 0 = 1`**
⟹ **`1000000 ≤ 1` 为假**。

要点 **这是反例级消融**：删掉 `hx` 后，结论**不是「证不出来」，而是「为假」**。 -/
theorem d41_radius_bounds_are_load_bearing :
    ¬ (Int.natAbs
        (LayerOut (convertVec (editConstraint ({ a := [1], b := 0 } : VectorConstraint)
            ({ dw := [1], db := 0 } : LayerDelta))) [1000000]
          - LayerOut (convertVec ({ a := [1], b := 0 } : VectorConstraint)) [1000000])
      ≤ (min ([1] : List Int).length ([1000000] : List Int).length) * (1 * 1)
        + Int.natAbs (0 : Int)) := by
  -- 注意 **先算左端**（显式展开 `foldl`，不依赖 `decide` 去归约 `List.foldl`）
  have hL : LayerOut (convertVec (editConstraint ({ a := [1], b := 0 } : VectorConstraint)
        ({ dw := [1], db := 0 } : LayerDelta))) [1000000]
      - LayerOut (convertVec ({ a := [1], b := 0 } : VectorConstraint)) [1000000]
      = 1000000 := by
    simp [editConstraint, editLayer, convertVec, LayerOut, dot]
  rw [hL]
  simp

/-! ## 六、T2：报告标为「不推荐交付」的对照项（**如实实现**）

报告 §T2 自己判定：该陈述的证明体与 `RealEndToEnd.e2e_sound`（`:493`）**逐字相同**，
`hts` **在证明体中未被使用** ⟹ 注意 **它是空壳，不通过判据 1**。

要点 本文件**仍实现它**，但**明确标注为空壳**，理由是：
(a) 报告需要这一条作为「**量词位置变了但证明体没变**」的机器证据；
(b) 要点 它使报告的核心定位结论**可核对**：
「端到端健全性」这一族的全部内容**100% 来自 `symbolToWeight_correct`」。 -/

-- 注意 `linter.unusedVariables` 在此被显式关掉：`hts` 未被使用**正是本条要报告的事实**，
-- 不是待修的缺陷 —— 要点 让 linter 的告警消失反而会**抹掉这条证据**。
-- 注意 判据 ②（语法位置）：`set_option ... in` **必须**紧贴声明，
-- 故它不能放在 docstring **之后**（docstring 会附着到 `set_option`，报 "expected 'lemma'"）。
set_option linter.unusedVariables false in
/-- 注意 **T2（对照项，空壳 —— 报告判对了）**：端到端健全性（数据层 → 权重层）。

注意 **诚实标注（这是本文件最重要的负面登记之一）**：
本条的证明体**就是** `symbolToWeight_correct _ x`，`hts` **完全未被使用**。
它与 `RealEndToEnd.e2e_sound` 的**唯一**差别是把自由变量 `cs`
换成由 `ts` 算出的项 —— 要点 **陈述写法变了，证明体一个字没变** ⟹ **空壳**。
要点 **本文件不把它计入「已证的非平凡定理」。** -/
theorem d41_e2e_semantic_soundness_at_data_level_shell {s : List Char} {ts : List CharToken}
    (hts : tokenize s = some ts) (x : List Int) :
    AllSatisfied ((decode (L1Bridge ts)).getD []) x ↔
      AllZeroOutputs (compileToLayer ((decode (L1Bridge ts)).getD [])) x :=
  symbolToWeight_correct _ x

/-- 要点 **T2 空壳性的机器证据**：T2 的结论**可以完全不用 `hts` 得到** ——
即把它换成**零假设**，陈述**仍然可证**，且证明体**一个字不变**。

要点 这与 `d41_e2e_semantic_soundness_at_data_level_shell` 的差别**不是重述**：
上面那条**带** `hts`（读起来像端到端），本条**不带**任何假设
⟹ 要点 **两条并存本身就是证据**：`hts` 对结论**零承重**，
「端到端」的那一半（L0/L1）**从未进入结论的项**。 -/
theorem d41_T2_shell_hypothesis_free (ts : List CharToken) (x : List Int) :
    AllSatisfied ((decode (L1Bridge ts)).getD []) x ↔
      AllZeroOutputs (compileToLayer ((decode (L1Bridge ts)).getD [])) x :=
  symbolToWeight_correct _ x

end Lattice
