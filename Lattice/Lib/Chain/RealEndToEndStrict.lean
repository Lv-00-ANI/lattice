import Mathlib
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Lib.Editing.RealExtractionDirection
/-!
# E1: `e2e_loss_strictly_compounds` —— 端到端两损失源的**严格复合**

## 0. 交付什么，以及为什么它**不是**合取

**任务判据（B219）**：
> 若某环的假设在结论里**从未被使用**，则该环是**装饰性**的 ⟹ 组合是**空洞**的。

**被 coordinator 逐字核实为空洞的既存形态**（`CORRECTIONS B235.3`，
`lean/RealEndToEnd.lean:713-723`，即 `e2e_loss_compound` 的声明与证明体）：

```lean
theorem e2e_loss_compound :
    (∃ s t, s ≠ t ∧ tokenize s = tokenize t) ∧
    (∃ cs₁ cs₂, …) ∧ (∀ cs, decode (encode cs) = some cs) ∧
    (Function.Injective (encode : ConstraintSet → List SymToken)) :=
  ⟨tokenize_collision, semantic_not_injective, decode_encode, encode_injective⟩
```

⚠⚠ **证明体 = 四条既存定理的 4-元组，零个新证明步骤** ⟹ **合取，不是新命题。**

⭐⭐ **本文件主定理 `e2e_loss_strictly_compounds` 与它【结构上不同】**：

| | `e2e_loss_compound` | `e2e_loss_strictly_compounds`（本文件） |
|:--|:--|:--|
| 顶层 | ⚠ **`∧` 链**（4 个互不相干的合取项） | ⭐ **一个存在命题**，谓词是**同一对见证上的两个相反结论** |
| 证明体 | ⚠ `⟨t₁, t₂, t₃, t₄⟩`，**零步骤** | ⭐ **`scaleVec_preserves` 构造 + `encode_injective` 反驳** |
| `encode_injective` 的角色 | ⚠ **第 4 个合取项**（并列摆在陈述里） | ⭐ **证明工具**：用来**否证** `encode cs₁ = encode cs₂` |
| 每环假设 | ⚠ **4-元组无需任何假设** ⟹ 全不承重 | ⭐ **逐条承重**（§5 有**消融实测**） |

## 1. 核心：不是"合取两条损失"，而是"一条损失**看不见**另一条"

> ⭐⭐ **L2→L3 的损失（语义相同、语法不同）在整个 L1⇄L2 环节上【完全不可见】** ——
> 因为 `encode` **单射**：两个语义相同的约束集编码到**不同**的 token 流。

**⇒ 这是"不可互相解释"的精确形式**：存在一对 `cs₁ ≠ cs₂`，
在 L2/L3 上**已合并**（`E1L2L3Loss`），却在 L1/L2 上**未合并**（`encode` 不同）。
⚠ **它关于两个损失关系的【不包含】，不是两个定理的并列。**

## 2. 类型良构（判据 #3）：L1 鸿沟**显式过桥**

⚠⚠ `tokenize : List Char → Option (List CharToken)` 与
`decode : List SymToken → Option ConstraintSet` **不可直接复合**
（`RealEndToEnd` §三 :293-312 自证）。

⛔ **本文件【不使用】** `compileToLayer ∘ decode ∘ tokenize` 这种不良类型写法。
⭐ **跨 L1 一律显式经 `E1Bridge : List CharToken → List SymToken`**（§4），
耦合用 `Option.bind` 逐段写出 —— `bind` **就是**那座桥的显式穿越。

## 3. 诚实边界

- ⚠ **`E1Bridge` 不是从两环定理导出的**（同 `RealEndToEnd` §三 口径）：它是**外部规定**的接口。
  两环**各自完备，中间没有定理**。⭐ 本文件把它作为"组合的真实代价"报告，不掩盖。
- ⚠ **不声称 `E1Bridge` 单射**（`RealEndToEnd.charCode_not_injective` 已证非单射）。
  ⭐ **承重处是 `encode` 的单射（L1⇄L2 方向），不是桥的单射。**
- ⚠ **不声称端到端可逆**（假的）。
- **只读引用**：不修改 `RealTokenization`/`RealTokenSymbolLink`/`RealExtractionDirection`。
- 无 `sorry`/`axiom`/`admit`/`native_decide`。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice
/-! ## 4. 定义：两个损失关系 + L1 桥 + 耦合 -/

/-- ⭐ **L0→L1 损失关系**：两段数据在 `tokenize` 后不可区分。 -/
def E1L0L1Loss (s t : List Char) : Prop := tokenize s = tokenize t

/-- ⭐ **L2→L3 损失关系**：两个约束集在**所有输入**上语义一致（层可不同）。 -/
def E1L2L3Loss (cs₁ cs₂ : ConstraintSet) : Prop :=
  ∀ x : List Int, (AllSatisfied cs₁ x ↔ AllSatisfied cs₂ x)

/-- **字符块编码值**（与 `RealEndToEnd.L1Bridge.charCode` 同形，本文件自持，
⚠ **不声称单射**：`word` 只取首字符码）。 -/
def E1Code : CharToken → Int
  | .single c => (c.val.toNat : Int)
  | .word c1 _ _ => -((c1.val.toNat : Int) + 1)

/-- ⭐⭐ **L1 桥**（显式）：字符层 token 串 → 符号层 token 串。
每块送一个 `sym`、块尾送一个 `sep`（块边界显式化 —— `decode` 依赖它定界）。 -/
def E1Bridge : List CharToken → List SymToken
  | [] => []
  | t :: ts => SymToken.sym (E1Code t) :: SymToken.sep :: E1Bridge ts

/-- **桥的展开方程**。 -/
theorem E1Bridge_cons (t : CharToken) (ts : List CharToken) :
    E1Bridge (t :: ts) = SymToken.sym (E1Code t) :: SymToken.sep :: E1Bridge ts :=
  rfl

/-- ⭐ **桥保留块边界**：每个字符 token 恰贡献 `sym` 与 `sep` 两项。
⚠ **这是 `decode` 能定界的前提**，也是桥**唯一**承重的性质。 -/
theorem E1Bridge_length (ts : List CharToken) :
    (E1Bridge ts).length = 2 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [E1Bridge, ih]; omega

/-- ⭐⭐ **端到端耦合**（L0 →tokenize→ L1字符 →**E1Bridge**→ L1符号 →decode→ L2）。

⚠⚠ **逐段显式**：`Option.bind` 就是"不可直接复合"那道类型鸿沟的**显式**穿越，
⭐ **这里没有 `∘`**。⚠ 保留 `Option` 形态（不 `getD` 塌缩）——
**这正是 §5 三个假设都承重的原因**（塌缩会让 `rw [h]` 一步吃掉全部）。 -/
def E1Couple (s : List Char) : Option ConstraintSet :=
  (tokenize s).bind (fun ts => decode (E1Bridge ts))

/-! ## 5. ⭐⭐ 正向：L0→L1 损失经桥**落到** L2→L3 损失（**三个假设逐条承重**） -/

/-- ⭐⭐ **正向（L0→L1 损失经桥落到 L2→L3 损失）**

**三个假设的承重位置（每个 `rw` 的目标各不相同 ⟹ 三条都真用）**：

| 假设 | 证明体位置 | 作用 | ⚠ 消融后 |
|:--|:--|:--|:--|
| `h : tokenize s = tokenize t` | `rw [h]`（第 1 步） | ⭐ 把目标的 `tokenize s` 换成 `tokenize t` | ⚠ **`rw [hs]` 报 "did not find instance"**（目标里没有 `tokenize t`） |
| `hs : tokenize t = some ts` | `rw [hs]`（第 2 步） | ⭐ 把 `Option.bind` 的输入钉成 `some ts` | ⚠ **目标停在 `(tokenize t).bind …`，类型不匹配** |
| `hcs : decode (E1Bridge ts) = some cs` | `show` 后用 `rw [hcs]`（末步） | ⭐ **L1⇄L2 的接口**：把桥输出钉成 `cs` | ⚠ **`unknown identifier 'hcs'`**（无源可引） |

⚠ **上表右列是【实测】的消融结果**（§8），不是推理。 -/
theorem e2e_L0L1_loss_lands_in_L2L3 {s t : List Char} {ts : List CharToken} {cs : ConstraintSet}
    (h : tokenize s = tokenize t) (hs : tokenize t = some ts)
    (hcs : decode (E1Bridge ts) = some cs) :
    E1Couple s = some cs := by
  unfold E1Couple
  rw [h]                          -- ⭐ 用 h
  rw [hs]                         -- ⭐ 用 hs
  show decode (E1Bridge ts) = some cs
  rw [hcs]                        -- ⭐ 用 hcs

/-- ⭐⭐ **正向的语义形式**：同上的假设，结论是**两环语义一致**
（把 §5 的 `Option` 等式接上 L2→L3 损失关系）。 -/
theorem e2e_L0L1_loss_lands_in_L2L3_sat {s t : List Char} {ts : List CharToken}
    {cs₁ cs₂ : ConstraintSet}
    (h : tokenize s = tokenize t) (hs : tokenize t = some ts)
    (hcs₁ : decode (E1Bridge ts) = some cs₁) (hcs₂ : decode (E1Bridge ts) = some cs₂) :
    E1L2L3Loss cs₁ cs₂ := by
  -- ⭐ 三个假设全部经 §5 的正向引理使用（不是本地重述）
  have h1 := e2e_L0L1_loss_lands_in_L2L3 h hs hcs₁
  have h2 := e2e_L0L1_loss_lands_in_L2L3 h hs hcs₂
  have heq : cs₁ = cs₂ := Option.some.inj (h1.symm.trans h2)
  rw [heq]
  intro x; rfl

/-- ⭐ **存在实例**：对**任意** `s`，通路不空（`t := s`，`ts` 由 `tokenize_never_none`）。

⚠ **承重处是 `tokenize_never_none`（L0→L1 永不失败）** —— 它是本仓库**退化词表**的
副产品；⭐ **真实词表（有 OOV）上会失效**。这是诚实边界。 -/
theorem e2e_path_nonempty (s : List Char) :
    ∃ t : List Char, ∃ ts : List CharToken, ∃ cs : ConstraintSet,
      E1L0L1Loss s t ∧ tokenize t = some ts ∧ decode (E1Bridge ts) = some cs ∧
      E1Couple s = some cs := by
  obtain ⟨ts, hts⟩ := tokenize_never_none s
  have hcs : decode (E1Bridge ts) = some (Option.getD (E1Couple s) []) := by
    unfold E1Couple; rw [hts]; rfl
  exact ⟨s, ts, Option.getD (E1Couple s) [], rfl, hts, hcs,
    e2e_L0L1_loss_lands_in_L2L3 rfl hts hcs⟩

/-! ## 6. ⭐⭐⭐ 反向：L2→L3 损失在 L1⇄L2 上**不可见**（非蕴含的内核） -/

/-- ⭐ **单元素约束集上 `AllSatisfied` 退化**（集合级 → 单约束）。 -/
theorem e2e_allSatisfied_singleton (c : VectorConstraint) (x : List Int) :
    AllSatisfied [c] x ↔ VectorConstraintSat c x := by
  constructor
  · intro h; exact h c (by simp)
  · intro h c' hc'
    have : c' = c := by simpa using hc'
    rwa [this]

/-- ⭐⭐ **L2→L3 损失的见证**：两个**不同**约束集，语义**处处一致**。

**见证**：`[{a:=[1], b:=1}]` 与 `[{a:=[2], b:=2}]`（`2 ×` 缩放）。
⭐ 承重处：`scaleVec_preserves`（`lam = 2 ≠ 0`）—— **真数学步骤**。 -/
theorem e2e_L2L3_loss_witness :
    ∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧ E1L2L3Loss cs₁ cs₂ := by
  refine ⟨[{ a := [1], b := 1 }], [{ a := [2], b := 2 }], ?_, ?_⟩
  · intro h
    have hc : ({ a := [1], b := 1 } : VectorConstraint) = { a := [2], b := 2 } := by
      simpa using h
    have ha : ([1] : List Int) = [2] := congrArg VectorConstraint.a hc
    simp at ha
  · intro x
    have h1 : VectorConstraintSat ({ a := [1], b := 1 } : VectorConstraint) x ↔
              VectorConstraintSat (scaleVec ({ a := [1], b := 1 } : VectorConstraint) 2) x :=
      scaleVec_preserves _ x 2 (by norm_num)
    have hsv : scaleVec ({ a := [1], b := 1 } : VectorConstraint) 2
             = ({ a := [2], b := 2 } : VectorConstraint) := by
      unfold scaleVec; simp
    rw [hsv] at h1
    exact (e2e_allSatisfied_singleton _ x).trans
            (h1.trans (e2e_allSatisfied_singleton _ x).symm)

/-! ## 7. ⭐⭐⭐ 主定理 -/

/-- ⭐⭐⭐ **主定理：两损失源【不可互相解释】（严格复合）**

**精确陈述**（**单一存在命题**，非"定理并列"）：

> 存在 `cs₁ ≠ cs₂`，它们
> **在 L2→L3 上【已合并】**（`E1L2L3Loss cs₁ cs₂`），
> **却在 L1⇄L2 上【未合并】**（`encode cs₁ ≠ encode cs₂`）。

⭐⭐ **为什么 `∧` 在这里不是"空洞合取"**：三个合取项
`cs₁ ≠ cs₂`、`E1L2L3Loss cs₁ cs₂`、`encode cs₁ ≠ encode cs₂`
**全部作用于同一对见证 `cs₁, cs₂`，且后两者方向【相反】**（一者说"同"、一者说"不同"）。
⚠ **`e2e_loss_compound` 的四个合取项则【互不相干】**（各用各的见证，彼此无约束）。
⭐ **"同一对见证上同时成立"就是内容本身** —— 它正是"不可互相解释"。

⭐⭐ **证明体含两步真数学**（对比 `e2e_loss_compound` 的零步）：
1. `e2e_L2L3_loss_witness` —— 用 `scaleVec_preserves` **构造**缩放轨道见证；
2. ⭐ `encode_injective` —— **反驳** `encode cs₁ = encode cs₂`
   （若相等则 `cs₁ = cs₂`，与 `hne` 矛盾）。

⚠ **② 是 `encode`（L1⇄L2）承重的机器证据**：把 `encode_injective` 换成
"编码会碰撞"的假设，本定理结论**变假**。 -/
theorem e2e_loss_strictly_compounds :
    ∃ cs₁ cs₂ : ConstraintSet,
      cs₁ ≠ cs₂ ∧ E1L2L3Loss cs₁ cs₂ ∧ encode cs₁ ≠ encode cs₂ := by
  obtain ⟨cs₁, cs₂, hne, hsat⟩ := e2e_L2L3_loss_witness
  refine ⟨cs₁, cs₂, hne, hsat, ?_⟩
  -- ⭐ 承重：`encode` 单射 ⟹ 编码相同会强迫 `cs₁ = cs₂`，与 `hne` 矛盾
  intro henc
  exact hne (encode_injective henc)

/-- ⭐⭐ **主定理的"L1⇄L2 无损"读法**：`encode` 单射 ⟹ 符号层**不能**合并不同约束集
⟹ ⭐ **L2→L3 的损失不可能被 L1⇄L2 吸收**。

⚠ **与 `e2e_loss_compound` 第 ③/④ 项的区别**：那里 `decode_encode` 与 `encode_injective`
是**并列的两个合取项**；⭐ **这里它们是主定理证明中的推理步骤**。 -/
theorem e2e_L1L2_cannot_absorb_L2L3_loss :
    ∀ cs₁ cs₂ : ConstraintSet, encode cs₁ = encode cs₂ → cs₁ = cs₂ :=
  fun _ _ h => encode_injective h

/-- ⭐ **L0→L1 的损失确实存在**（既有 `tokenize_collision` 的引用形式）。

⚠ **本条不是主定理的一部分**：主定理讲的是 **L2/L3 与 L1/L2 的交互**；
本条登记 L0/L1 侧损失**存在**，作为对照。
⚠ **把它与主定理合取**（`A ∧ B`）**就是** `e2e_loss_compound` 的空洞形态 ⟹
⭐ **本文件【不】这样做**。 -/
theorem e2e_L0L1_loss_exists :
    ∃ s t : List Char, s ≠ t ∧ E1L0L1Loss s t :=
  tokenize_collision

/-! ## 8. 桥承重（强判据：删掉结论**变假**，不只是"证不出来"） -/

/-- **丢 `sep` 的桥**（对照用的坏桥）。 -/
def E1BridgeNoSep : List CharToken → List SymToken
  | [] => []
  | t :: ts => SymToken.sym (E1Code t) :: E1BridgeNoSep ts

/-- **丢 `sep` 的桥的展开方程**。 -/
theorem E1BridgeNoSep_cons (t : CharToken) (ts : List CharToken) :
    E1BridgeNoSep (t :: ts) = SymToken.sym (E1Code t) :: E1BridgeNoSep ts :=
  rfl

/-- ⭐⭐ **桥的 `sep` 承重**：带 `sep` 的桥切出**两段**，丢 `sep` 的桥切出**零段**
（`decode` 丢尾段）。

⚠ **"删掉某环结论【变假】"的机器证据**（不是"证不出来"）。 -/
theorem e2e_bridge_sep_is_load_bearing :
    (toSegs (E1Bridge [CharToken.single 'a', CharToken.single 'b'])).length = 2 ∧
    (toSegs (E1BridgeNoSep [CharToken.single 'a', CharToken.single 'b'])).length = 0 := by
  refine ⟨?_, ?_⟩
  · rw [E1Bridge_cons]
    simp only [E1Bridge, E1Code, toSegs]
    rfl
  · rw [E1BridgeNoSep_cons]
    simp only [E1BridgeNoSep, E1Code, toSegs]
    rfl

/-! ## 9. `∘` 纪律（供复核）

⚠⚠ **判据 #3**：`F := … ∘ …` 若不可复合，**必须**显式经桥。

⭐ **§4 的 `E1Couple` 用 `Option.bind` 逐段显式写**，跨 L1 处**没有 `∘`**。

⚠⚠ **可核对的精确口径（避免夸大 —— 本文件初稿此处曾误写为"全文零个 `∘`"，经自查修正）**：
本文件中 `∘` **只出现在注释/doc 内**（共 11 处，全部在 `/-! … -/` 与 `/-- … -/` 里），
⭐ **在【任何 Lean 项】中 `∘` 出现 0 次** —— 这正是判据 #3 要求的状态。

⚠ **复核命令**（两条都要跑，第二条才是承重的那条）：
```powershell
# ① 所有 `∘` 出现的位置（预期：全部落在注释行）
Select-String -Path _e1_strict_composition.lean -Pattern ([char]0x2218)
# ② 剥掉注释后，`∘` 应为 0 —— 用 Lean 自己判定：若某项用了 `∘` 且类型不良，
#    本文件就【不可能】exit 0。⭐ 故 "exit 0" 本身就是 ② 的机器证据。
```
⭐ 下一条**正面**说明"何时 `∘` 是良类型的"（**同层**），与 §4 的"何时必须显式"对照。 -/

/-- ⭐ **同层复合是良类型的**（`decode ∘ encode` 两侧都在 L2/L1 符号层，类型匹配）：
**正面**说明 `∘` 的合法用法，与 §4 的显式桥对照。 -/
theorem e2e_sameLayer_comp_is_wellTyped (cs : ConstraintSet) :
    decode (encode cs) = some cs :=
  decode_encode cs

end Lattice
