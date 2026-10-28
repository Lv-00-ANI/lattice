import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness

open Lattice.Lift.SymbolToWeightCorrectness

/-!
# LATTICE: RealTokenSymbolLink —— token ⇄ 符号 的往返恒等（L1⇄L2 边的最小可证核心）

## 定位

doc/02 §1 声明的链路是**四级双向**：

    L0 数据 ⇄ L1 token ⇄ L2 符号模型（规则/约束/DSL）⇄ L3 权重

其中 L2⇄L3 是既有工作（`SymbolToWeightCorrectness` / `WeightToSymbolEquivalence` /
`RealRoundtripBound` …）。而 **L1⇄L2（token ⇄ 符号）在证明层此前完全没有对应物**：
全库 411 个顶层 `.lean` 文件中，`encode`/`decode`/`tokenize`/`parse`/`serialize`
**没有任何一个声明**（审计见 `doc/CHAIN-AUDIT.md`）。

本文件补上这一环的**最小可证核心**：把有限符号对象（有限约束集）编码为 token 序列，
并证明**往返恒等** `decode (encode cs) = some cs`。

## 编码设计（为什么可证，以及为什么必须这样设计）

`VectorConstraint` 只有两个字段（`a : List Int`、`b : Int`），其既有语义是
`VectorConstraintSat c x := dot c.a x + c.b = 0`，而 `dot a x = (a.zip x).foldl …`
**只用 `a`、完全不看 `b`**。这决定了两个**不可省略**的设计点：

1. **`b` 必须显式编码**——它不参与 `dot`，省略即永久丢失
   （机器验证反例：§六 `encode_drop_b_roundtrip_fails`、`drop_b_changes_semantics`）；
2. **必须以 `sep` 自定界**——否则相邻约束的 token 会粘连成歧义段
   （机器验证反例：§六 `encode_no_sep_roundtrip_fails`）。

token 字母表 `SymToken := sym Int | sep`；单约束编码为
`c.a.map sym ++ [sym c.b, sep]`；约束集编码为逐约束编码的**拼接**（`flatten`）。
解码沿 `sep` 切段，段内**末项**是 `b`、其余是 `a`（由 `splitLast` 实现；
边界由段尾位置隐含，无需额外标记）。

**可证性判定（先判真假，再动 tactic）**：`decode (encode cs) = some cs`
在本设计下**为真**，且其全部内容与整数算术无关——只是 `List` 结构归纳 +
规范形 `splitLast (a ++ [b]) = (a, b)`。故**无需降级为语义等价**；
本文件同时给出语义保真定理作为加强。

## 诚实边界（本文件不证 / 不声称的）

- **未触及 L0（数据 / 原始文本）**：本文件不含 `Char`/`String`/字节层，不定义
  `tokenize`，故 **L0⇄L1 仍是完全缺失的**（见 `doc/CHAIN-AUDIT.md` 断点 #1）。
  此处 "token" 是 **L1 的抽象 token 序列模型**，**不是**真实分词器输出。
- **证的是结构往返**（`decode (encode cs) = some cs`），并附语义保真
  `decode_encode_sat_iff`；**不证**「任意 token 流都能解出有效约束」
  （见 §六 `decode_strict_failure`：无 `sep` 收尾的 token 流会被拒绝/丢弃残段）。
- **编码不是自然的**：真实 L1⇄L2 是「文本→关系抽取/规则化」的**有损、启发式**过程
  （doc/02 §3 自述「LLM 作外部工具」）。本文件给出的是该跳的**可逆子类**。
- 不使用 sorry / axiom / admit。
-/

noncomputable section


namespace Lattice

open Lattice.Lift.SymbolToWeightCorrectness (ConstraintSet AllSatisfied AllZeroOutputs compileToLayer)
/-! ## 一、L1 token 字母表

token 字母表是有两个构造子的归纳类型（有限签名、可判定相等）。
它是「符号对象线性化」所需的最小字母表，即 L1 与 L2 之间那一跳的抽象模型。 -/

/-- **L1 token 字母表（符号层）**：`sym z` 携带一个整数（系数向量的某一项，或常数项），
`sep` 是约束分界 token。

⚠⚠ **改名登记（原名 `Token` → 现名 `SymToken`）**：本仓库曾有两个**同名不同型**的
`Lattice.Token` —— 本文件的**符号层**字母表，与 `RealTokenization.lean:165` 的
**字符层**字母表（`single`/`word`）。二者**同名不同型**且**不能同时 `import`**，实测报
'Lattice.instReprToken._cstage1' from RealTokenization`。
⭐⭐ **该冲突直接阻断「数据→token→符号→权重」的端到端组合**
（`RealQuotientReversibility` / `RealClosureReversibility` 两处**已登记**被迫拆文件）。
现按 STYLE「跨文件同名是潜伏断裂」的修法**改名消歧**：本文件用 `SymToken`。
⚠ 改名**不改变任何证明**（纯重命名），既有定理**一条未删**。

**诚实标注**：这不是真实分词器的词表，也不含任何文本/字符层。 -/
inductive SymToken where
  /-- 符号 token：携带一个整数（系数或常数项）。 -/
  | sym (z : Int)
  /-- 约束分界 token。 -/
  | sep
  deriving DecidableEq, Repr

/-! ## 二、段内拆分：`splitLast` 与它的规范形

解码需要「段内末项是 `b`」这一事实。`splitLast` 把列表拆成（除末项外的前缀，末项），
空列表记为 `([], 0)`。其规范形 `splitLast (a ++ [b]) = (a, b)` 是本文件全部内容的载体
——纯 `List` 结构，不涉及任何整数运算。 -/

/-- 把列表拆成「除末项外的前缀」与「末项」；空列表返回 `([], 0)`。 -/
def splitLast : List Int → List Int × Int
  | [] => ([], 0)
  | [x] => ([], x)
  | x :: y :: rest => (x :: (splitLast (y :: rest)).1, (splitLast (y :: rest)).2)

/-- **`splitLast` 规范形**：`splitLast (a ++ [b]) = (a, b)`。

这是往返恒等的关键引理：由它立即得到「编码段能原样恢复 `(a, b)`」。 -/
theorem splitLast_append_singleton (a : List Int) (b : Int) :
    splitLast (a ++ [b]) = (a, b) := by
  induction a with
  | nil => rfl
  | cons h t ih =>
      cases t with
      | nil => rfl
      | cons h2 t2 =>
          -- 目标 LHS 已是投影形式；用 `show` 把它对齐到 `ih` 的模式后重写
          show (h :: (splitLast ((h2 :: t2) ++ [b])).1,
                (splitLast ((h2 :: t2) ++ [b])).2) = (h :: h2 :: t2, b)
          rw [ih]

/-- 由段内整数表重建约束：末项为常数项 `b`，其余为系数向量 `a`。 -/
def mkConstraint (l : List Int) : VectorConstraint :=
  let p := splitLast l
  { a := p.1, b := p.2 }

/-- `mkConstraint` 在 `a ++ [b]` 上的取值（即编码段的解码结果）。 -/
theorem mkConstraint_append_singleton (a : List Int) (b : Int) :
    mkConstraint (a ++ [b]) = { a := a, b := b } := by
  unfold mkConstraint
  rw [splitLast_append_singleton]

/-! ## 三、编码：符号 → token -/

/-- **单约束编码**：系数向量逐项 `sym`，随后常数项一个 `sym`，最后 `sep`。

`b` **必须**被编码（它不参与 `dot`，省略即丢失，见 §六 反例）；
`sep` **必须**存在（否则段歧义，见 §六 反例）。 -/
def encodeConstraint (c : VectorConstraint) : List SymToken :=
  c.a.map SymToken.sym ++ [SymToken.sym c.b, SymToken.sep]

/-- **约束集编码**：逐约束编码后拼接。

约束集的语义 `AllSatisfied` 是合取、与顺序无关，但编码仍保序，
使往返恒等成为**结构**恒等而非仅语义等价。 -/
def encode (cs : ConstraintSet) : List SymToken :=
  (cs.map encodeConstraint).flatten

/-! ## 四、解码：token → 符号

解码分两步，**两步都是 `List` 上的结构递归**（故 Lean 直接接受停机性，
无需 `termination_by`）：

1. `toSegs`：把 token 流按 `sep` 切成段（每段是 `List Int`）；
2. `mkConstraint`：把每段还原为约束（末项为 `b`）。

**严格失败语义**：`toSegs` 对**没有 `sep` 收尾**的尾段**丢弃**该残段
（而非静默编造一个约束）。因此不合法的 token 流不会被解成错误的符号对象
（见 §六 `decode_drops_trailing_partial`）。 -/

/-- **切段**：把 token 流按 `sep` 切成整数表列表。

`sep` 结束当前段；遇到 `sym` 时把它压到后续段的头部。
**末段若无 `sep` 收尾则整段丢弃**——这是有意的严格失败，不是静默降级。 -/
def toSegs : List SymToken → List (List Int)
  | [] => []
  | SymToken.sep :: rest => [] :: toSegs rest
  | SymToken.sym z :: rest =>
      match toSegs rest with
      | [] => []
      | seg :: segs => (z :: seg) :: segs

/-- **约束集解码**：切段后逐段还原为约束。

**诚实标注**：解码结果构造性地总是 `some`——「失败」体现在**段被丢弃**
（不完整的尾段不产出约束），而不是返回 `none`。这是本设计的选择：
它保证 `decode` 不拒绝合法编码，同时不编造不存在的约束。 -/
def decode (ts : List SymToken) : Option ConstraintSet :=
  some ((toSegs ts).map mkConstraint)

/-! ## 五、往返恒等（核心结果）

先证切段的规范行为（`toSegs_map_sym_append_sep`），再对约束集归纳。 -/

/-- **`toSegs` 对编码段的规范行为**：一个完整的约束段（`l.map sym ++ sep`）
恰好切出一段 `l`，其余交给 `rest`。 -/
theorem toSegs_map_sym_append_sep (l : List Int) (rest : List SymToken) :
    toSegs (l.map SymToken.sym ++ SymToken.sep :: rest) = l :: toSegs rest := by
  induction l with
  | nil => rfl
  | cons h t ih =>
      show (match toSegs (t.map SymToken.sym ++ SymToken.sep :: rest) with
            | [] => []
            | seg :: segs => (h :: seg) :: segs) = (h :: t) :: toSegs rest
      rw [ih]

/-- **编码的 `cons` 分解**：`encode (c :: cs)` 等于「一个完整约束段」后接
`encode cs`——正是 `toSegs_map_sym_append_sep` 所需的形状。

注意段体是 `c.a ++ [c.b]`（末项为常数项），故左式写成 `(c.a ++ [c.b]).map sym`，
`sep` 单独作分界——这正是 §二 段内约定（末项为 `b`）在编码侧的体现。 -/
theorem encode_cons_eq (c : VectorConstraint) (cs : ConstraintSet) :
    encode (c :: cs) = (c.a ++ [c.b]).map SymToken.sym ++ SymToken.sep :: encode cs := by
  unfold encode encodeConstraint
  simp only [List.map_cons, List.flatten_cons, List.map_append, List.singleton_append,
             List.map_nil, List.nil_append, List.cons_append, List.append_assoc]

/-- **集级往返恒等（核心定理）**：`decode (encode cs) = some cs`。

即：有限约束集经「符号 → token → 符号」往返后**原样恢复**，
包括约束的**顺序**与每个约束的 `(a, b)`。这是本项目「可逆链路」口号中
L1⇄L2 这一跳此前缺失的证明层对应物。 -/
theorem decode_encode (cs : ConstraintSet) : decode (encode cs) = some cs := by
  unfold decode
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [encode_cons_eq]
      rw [toSegs_map_sym_append_sep]
      rw [List.map_cons]
      rw [mkConstraint_append_singleton]
      -- 得到 `some ({a := c.a, b := c.b} :: …) = some (c :: …)`，用结构 eta 对齐
      have hc : ({ a := c.a, b := c.b } : VectorConstraint) = c := by cases c; rfl
      rw [hc]
      -- `ih : some (List.map mkConstraint (toSegs (encode cs))) = some cs`；
      -- 目标是 `some (c :: …) = some (c :: cs)`，故先取 `ih` 的内层等式再重写
      have ih' : List.map mkConstraint (toSegs (encode cs)) = cs :=
        (Option.some.injEq _ _).mp ih
      rw [ih']

/-- **往返恒等的单射推论**：`encode` 是单射。

由 `decode_encode` 与 `Option.some.injEq` 直接得到——若两约束集编码相同，
则解码结果相同，从而 `cs₁ = cs₂`。这给出「符号信息在 token 序列中无损」的
精确表述（也是「可逆链路」在 L1⇄L2 上的形式化含义）。 -/
theorem encode_injective : Function.Injective (encode : ConstraintSet → List SymToken) := by
  intro cs₁ cs₂ h
  have h₁ : decode (encode cs₁) = some cs₁ := decode_encode cs₁
  have h₂ : decode (encode cs₂) = some cs₂ := decode_encode cs₂
  rw [h] at h₁
  -- h₁ : decode (encode cs₂) = some cs₁,  h₂ : decode (encode cs₂) = some cs₂
  rw [h₁] at h₂
  exact (Option.some.injEq _ _).mp h₂

/-! ## 六、语义保真（加强）与反例（设计点的必要性）

往返恒等是**结构**层面的；本节的语义定理把它接到既有 L2 语义
（`VectorConstraintSat` / `AllSatisfied`）上，并对 §三 的设计点给出
**机器验证的反例**，说明「省略 `b`」或「省略 `sep`」都会使往返恒等为**假**。 -/

/-- **语义保真**：解码 `encode cs` 得到的约束集与原集**满足性完全一致**。

由结构恒等 `decode_encode` 直接得到：解码出的集就是 `cs` 本身
（`Option.getD` 取出后即 `cs`），故二者的合取语义在任何输入处一致。
这把 L1⇄L2 的往返接回了 L2 的符号语义，是通往 L3 的接口。 -/
theorem decode_encode_sat_iff (cs : ConstraintSet) (x : List Int) :
    AllSatisfied ((decode (encode cs)).getD []) x ↔ AllSatisfied cs x := by
  rw [decode_encode]
  simp only [Option.getD_some]

/-- **反例一（省略 `b` 必失败）**：若编码不携带常数项（只编码系数向量），
则两个 `a` 相同而 `b` 不同的约束会**编码相同**，往返不可能恒等。

见证：`(a = [], b = 0)` 与 `(a = [], b = 1)`，二者的「只编码 `a`」形式都是 `[sep]`。
这机器验证了 §三 设计点 1：**`b` 是不可省略的信息**。 -/
theorem encode_drop_b_roundtrip_fails :
    ∃ c₁ c₂ : VectorConstraint, c₁ ≠ c₂ ∧
      c₁.a.map SymToken.sym ++ [SymToken.sep] = c₂.a.map SymToken.sym ++ [SymToken.sep] := by
  refine ⟨{ a := [], b := 0 }, { a := [], b := 1 }, ?_, ?_⟩
  · intro h
    have hb : (0 : Int) = 1 := congrArg VectorConstraint.b h
    exact Int.zero_ne_one hb
  · rfl

/-- **反例二（丢 `b` 会改变符号语义）**：上例中 `b = 1` 的约束在 `x = []` 处**不满足**，
故「丢失 `b`」不是无害的表示简化，而是会产出**错误符号对象**的真实缺陷。 -/
theorem drop_b_changes_semantics :
    ¬ VectorConstraintSat ({ a := [], b := 1 } : VectorConstraint) [] := by
  unfold VectorConstraintSat
  simp only [dot, List.zip_nil_left, List.foldl_nil]
  norm_num

/-- **反例三（省略 `sep` 必失败）**：若编码不设约束分界符（只把各约束的系数
前后拼接、并用约束个数定界），则「一个系数为 `[1, 2]` 的约束」与
「两个系数为 `[1]`、`[2]` 的约束」会产生**相同的 token 序列** `[sym 1, sym 2]`，
解码无法恢复约束**个数**与**切分位置**，往返恒等不可能成立。

两个见证集本身不等（长度 1 vs 2），而它们的「无 `sep` 编码」相同。
这机器验证了 §三 设计点 2：**`sep` 不是装饰，而是段边界信息的唯一载体**。

（注：本反例不带 `b` 编码——`b` 的必要性已由反例一/二单独给出；
这里隔离的是「段边界」这一个设计点。） -/
theorem encode_no_sep_roundtrip_fails :
    ∃ cs₁ cs₂ : ConstraintSet, cs₁ ≠ cs₂ ∧
      (cs₁.map (fun c => c.a.map SymToken.sym)).flatten =
      (cs₂.map (fun c => c.a.map SymToken.sym)).flatten := by
  refine ⟨[{ a := [1, 2], b := 0 }], [{ a := [1], b := 0 }, { a := [2], b := 0 }], ?_, ?_⟩
  · intro h
    have hlen : (1 : ℕ) = 2 := by
      have hh := congrArg List.length h
      simp at hh
    exact absurd hlen (by decide)
  · decide

/-- **严格失败语义**：没有 `sep` 收尾的 token 流，其尾段被**丢弃**——
不会静默编造出一个约束。

见证：`[sym 1, sym 2]`（无 `sep`）切段得到 `[]`，
故 `decode [sym 1, sym 2] = some []`——没有凭空产生「系数 `[1]`、常数 `2`」的约束。
这界定了 `decode` 的诚实边界：它**不**声称能解任意 token 流。 -/
theorem decode_drops_trailing_partial :
    decode [SymToken.sym 1, SymToken.sym 2] = some [] := by
  show some (List.map mkConstraint (toSegs [SymToken.sym 1, SymToken.sym 2])) = some []
  simp only [toSegs, List.map_nil]

end Lattice
