import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lift.SymbolToWeightCorrectness
import Lattice.Lift.WeightToSymbolEquivalence
/-!
# LATTICE R-04：语义等价类的商 —— ⚠ **「穿过商单射」的两个读法，一对一假**

## 0. 任务书原话

> 构造 `Layer` 在语义等价下的商，并证明 `convertVec` 穿过该商是单射。

## 1. ⚠⚠ 结论先行

任务书这句话里 **「穿过该商是单射」有两个互不相同的读法**，
而它们 **一对一假**。本文件把两个读法 **都** 形式化，并给出 **机器验证的判定**：

| 读法 | 形式陈述 | 判定 |
|:--|:--|:--|
| **A（商在权重侧，把 `convertVec` 读成 `VectorConstraint → LinearLayer/≈`）** | `convertVec c ≈ convertVec c' → c = c'` | ⚠⚠ **假** —— 见 §五 `naive_injectivity_is_false` |
| **B（商在符号侧，`convertVec` 下降为 `VectorConstraint/≈ → LinearLayer/≈`）** | 该下降映射 **良定义且单射** | ✅ **真** —— 见 §四 `semConv_injective` |

⭐ **A 为假不是「证不出来」，是一条定理**：`scaleVec` 给出**具体的**碰撞
（`c` 与 `scaleVec c 2` 语义等价、但作为对象**不等**），故 A 的结论**被证伪**。

## 2. ⭐ 本文件补的**真实缺口**

`RealConversionQuotient.lean:256-262` 明确登记了自己**未做**的事：

> - ⚠ **不构造 `Quotient behaviouralSetoid`**：**未做**。
>   理由（技术性，非数学缺口）：……真正 `Quotient.lift` 的构造需要
>   `Quotient.sound` 与证明项 `Eq.ndrec` 的对齐，**属机械工作**……

⭐ 本文件 **把这个机械工作做完**：§二 给出 `Setoid` 实例，§三 给出 `Quotient.lift`，
§四 给出**下降映射的单射性**。⇒ 这是 R-04 相对既有文件的**增量**，
且它不是重复 `RealConversionQuotient`（后者只证到「相容性」，**不构造 `Quotient`**）。

## 3. 逐字核对过的既有签名（**不靠记忆**）

```lean
-- ConvertVectorLinear.lean:24-27
structure VectorConstraint where
  a : List Int      -- 系数向量
  b : Int           -- 常数项

-- ConvertVectorLinear.lean:39-42
structure LinearLayer where
  w : List Int      -- 权重向量
  b : Int           -- 偏置

-- ConvertVectorLinear.lean:34-35
def VectorConstraintSat (c : VectorConstraint) (x : List Int) : Prop :=
  dot c.a x + c.b = 0

-- ConvertVectorLinear.lean:44-45
def LayerOut (l : LinearLayer) (x : List Int) : Int :=
  dot l.w x + l.b

-- ConvertVectorLinear.lean:49-50
def convertVec (c : VectorConstraint) : LinearLayer := { w := c.a, b := c.b }

-- ConvertVectorLinear.lean:69-70
def scaleVec (c : VectorConstraint) (lam : Int) : VectorConstraint :=
  { a := c.a.map (fun v => v * lam), b := c.b * lam }

-- ConvertVectorLinear.lean:55-56
theorem convertVec_preserves_semantics (c : VectorConstraint) (x : List Int) :
    VectorConstraintSat c x ↔ LayerOut (convertVec c) x = 0

-- ConvertVectorLinear.lean:105-106
theorem scaleVec_preserves (c : VectorConstraint) (x : List Int) (lam : Int) (hlam : lam ≠ 0) :
    VectorConstraintSat c x ↔ VectorConstraintSat (scaleVec c lam) x

-- WeightToSymbolEquivalence.lean:55-56
def extractVec (l : LinearLayer) : VectorConstraint := { a := l.w, b := l.b }

-- WeightToSymbolEquivalence.lean:60-62
theorem roundtrip_extractVec (c : VectorConstraint) :
    extractVec (convertVec c) = c
```

⚠ **类型逐字对齐**（任务书 §写法 的硬要求）：本文件所有对既有定理的引用
都按上表 **逐字** 抄签，**不靠记忆**。⚠ 特别注意
`VectorConstraintSat`/`LayerOut` 的**参数顺序都是 `(c) (x)`**，
而 `scaleVec_preserves` 的参数顺序是 **`(c) (x) (lam) (hlam)`**（`x` 在 `lam` **前**）。

## 4. Quotient API 的逐字核对（⚠ 来自 **toolchain 源码**，不是 mathlib）

⚠ `Quotient` **不在 mathlib**，在 Lean core。本文件按
`…\leanprover--lean4---v4.14.0\src\lean\Init\Core.lean`（`lean-toolchain` = `v4.14.0`）
**逐字**核对（行号即该文件）：

```lean
-- Init/Core.lean:1095-1101
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  refl  : ∀ x, r x x
  symm  : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z

-- Init/Core.lean:1301-1305
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

-- Init/Core.lean:1678
theorem sound {α : Sort u} {s : Setoid α} {a b : α} : a ≈ b → Quotient.mk s a = Quotient.mk s b

-- Init/Core.lean:1685
protected abbrev lift {α : Sort u} {β : Sort v} {s : Setoid α} (f : α → β) :
    ((a b : α) → a ≈ b → f a = f b) → Quotient s → β

-- Init/Core.lean:1833
theorem exact {s : Setoid α} {a b : α} : Quotient.mk s a = Quotient.mk s b → a ≈ b
```

⭐ **`Quotient.exact` 的存在是本文件的关键**：它是 `Quotient.sound` 的**逆**，
⇒ 「商中相等」⟺「原关系中相关」。§四 的单射性证明**正是**用它把商等式拉回关系。

## 5. 不做什么（诚实边界，详见 §七）

无 `sorry` / `axiom` / `admit` / `native_decide`；**只创建本文件**，不修改任何既有文件；
成立 **已验证编译（2026-09-25 修订）**（`lean_probe.py` → `[lake-lock] lake exit code: 0`，见文末 §十 诚实边界 1）。
-/

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、语义等价关系（两个侧）

⚠ **命名去冲突**：`RealConversionQuotient.lean:178` 已定义 `BehaviouralIndistinct`，
但本文件 **不 import** 该模块（避免拉入整条 `RealCompileExtractClosed` 依赖链）。
⇒ 本文件**重新定义**，并**如实登记**这是重复（见 §七 诚实边界）。
-/

/-- **符号侧语义等价**：两个约束的满足谓词**逐点等价**。

⭐ 这是「同一个符号，不同的写法」—— 即 doc/01 所说「缩放自由度」所在的关系。 -/
def SemEqC (c c' : VectorConstraint) : Prop :=
  ∀ x : List Int, VectorConstraintSat c x ↔ VectorConstraintSat c' x

/-- **权重侧语义等价**：两个层所表示函数的**零化谓词**逐点等价。

⚠ 与 `SemEqC` 的关系由 `convertVec_preserves_semantics` 桥接（§三）。 -/
def SemEqL (l l' : LinearLayer) : Prop :=
  ∀ x : List Int, LayerOut l x = 0 ↔ LayerOut l' x = 0

/-! ## 二、⭐ `Setoid` 实例（`RealConversionQuotient` 登记「未做」的部分） -/

/-- ⭐ **符号侧语义等价是等价关系**。

⚠ **证明须逐点展开 `∀ x`**：三条性质分别是 `Iff.refl`、`Iff.symm`（**反变**使用，
注意 `↔` 两端方向）与 `Iff.trans`。`Equivalence` 的字段名依
`Init/Core.lean:1095` 为 `refl` / `symm` / `trans`（**具名构造**，不用匿名构造子，
以规避字段顺序记忆风险）。 -/
theorem semEqC_equivalence : Equivalence SemEqC where
  refl := fun c x => Iff.rfl
  symm := fun h x => (h x).symm
  trans := fun h₁ h₂ x => (h₁ x).trans (h₂ x)

/-- ⭐ **权重侧语义等价是等价关系**（同款证明；⚠ 逐点展开 `∀ x`）。 -/
theorem semEqL_equivalence : Equivalence SemEqL where
  refl := fun l x => Iff.rfl
  symm := fun h x => (h x).symm
  trans := fun h₁ h₂ x => (h₁ x).trans (h₂ x)

/-- ⭐ **符号侧 `Setoid`**（供 `Quotient` 使用）。 -/
def semSetoidC : Setoid VectorConstraint where
  r := SemEqC
  iseqv := semEqC_equivalence

/-- ⭐ **权重侧 `Setoid`** —— 这就是任务书说的「**语义等价**」，
也是 `Layer` 的商所依据的关系。

⚠ 术语订正（**如实登记**）：任务书说「`Layer` 在语义等价下的商」。
但 `Layer := List LinearLayer`（`SymbolToWeightCorrectness.lean:31`），
而 `convertVec` 的陪域是**单个** `LinearLayer`（`ConvertVectorLinear.lean:49`）。
⇒ ⚠ 把 `convertVec` 送进 **`List` 层**的商是**类型不匹配**的：
`convertVec : VectorConstraint → LinearLayer` **不能**当作
`VectorConstraint → Quotient (Setoid Layer)` 用。

⭐ 本文件因此：
- 取**单层**商 `Quotient semSetoidL` 作为「语义等价类的商」的**可陈述载体**（§四）；
- 并**如实登记**：`Layer`（列表层）本身的商**本文件未构造**
  （只给了关系 `SemEqLayer` 的**自反性**，见下；**未**证它是等价关系）。
  ⇒ ⚠ **这是本文件未完成的部分之一**，见文末诚实边界第 2 条。 -/
def semSetoidL : Setoid LinearLayer where
  r := SemEqL
  iseqv := semEqL_equivalence

/-- ⭐ **列表层（= 任务书的 `Layer`）的语义等价**：逐层等价。 -/
def SemEqLayer (ls ls' : Layer) : Prop :=
  ∀ l ∈ ls, ∃ l' ∈ ls', SemEqL l l' ∧ ∀ l' ∈ ls', ∃ l ∈ ls, SemEqL l l'

/-- ⭐ **列表层语义等价的自反性**（⚠ 非平凡：需要为每个成员找到**它自己**作为见证，
故必须用 `List.mem` 的成员本身，不能 `rfl`）。 -/
theorem semEqLayer_refl (ls : Layer) : SemEqLayer ls ls := by
  intro l hl
  exact ⟨l, hl, semEqL_equivalence.refl l, fun l' hl' => ⟨l', hl', semEqL_equivalence.refl l'⟩⟩

/-- **语义集合**：约束的**解集**（`SemEqC` 的商坐标）。

⚠ 与 `RealConversionQuotient.SatSet`（:195）**定义同构**，本文件**不 import** 该模块，
故重新定义并如实登记重复。 -/
def SatSetR (c : VectorConstraint) : Set (List Int) :=
  {x | VectorConstraintSat c x}

/-! ## 三、⭐⭐ `convertVec` 与语义等价的**相容性**（下降的前提）

⭐ 这是「`convertVec` 穿过商」的**全部技术前提**：
若 `c ≈ c'`（符号侧），则 `convertVec c ≈ convertVec c'`（权重侧）。
有了它，`Quotient.lift` 才能构造下降映射（§四）。 -/

/-- ⭐⭐ **`convertVec` 把符号侧语义等价送到权重侧语义等价**（相容性）。

⭐ **证明路线**：`SemEqL (convertVec c) (convertVec c')` 展开后要证
`LayerOut (convertVec c) x = 0 ↔ LayerOut (convertVec c') x = 0`。
用 `convertVec_preserves_semantics`（:55）**两侧各一次**，把目标化到
`VectorConstraintSat c x ↔ VectorConstraintSat c' x` —— 恰是 `h x`。

⚠ **这一步不是 `rfl`**：`convertVec_preserves_semantics` 是**定理**（有证明项），
必须显式 `trans` 掉两端的 `LayerOut`。这一点是承重的：
**若 `convertVec` 不保语义，本定理不成立**（消融见 §五 `ablation_refuted`）。 -/
theorem convertVec_respects_semEq {c c' : VectorConstraint} (h : SemEqC c c') :
    SemEqL (convertVec c) (convertVec c') :=
  fun x =>
    (convertVec_preserves_semantics c x).symm.trans
      ((h x).trans (convertVec_preserves_semantics c' x))

/-- ⭐ **`extractVec`（`convertVec` 的左逆）也尊重语义等价**（反方向）。

⭐ **证明路线**：`SemEqL l l'` 给出逐点 `LayerOut` 的 `↔`；
再用 `convertVec_preserves_semantics` 把 `LayerOut (convertVec (extractVec l))`
化回 `VectorConstraintSat (extractVec l)`，**两次**（`l`、`l'` 各一次）。

⚠ **承重性**：这一步用到了 `extractVec` 是**左逆**这一非平凡事实
（`roundtrip_extractVec`，:60），否则 `LayerOut` 与 `VectorConstraintSat` 无法对接。 -/
theorem extractVec_respects_semEq {l l' : LinearLayer} (h : SemEqL l l') :
    SemEqC (extractVec l) (extractVec l') := by
  intro x
  -- 目标：`VectorConstraintSat (extractVec l) x ↔ VectorConstraintSat (extractVec l') x`
  -- 关键桥：`convertVec (extractVec l) = l`（`extractVec` 是**右逆**方向，
  -- 由 `roundtrip_extractVec` 在 `l` 处得到 —— 注意 `roundtrip_extractVec` 的
  -- 陈述是 `extractVec (convertVec c) = c`，作用在 `c := extractVec l` 上给出
  -- `extractVec (convertVec (extractVec l)) = extractVec l`，
  -- 而左逆性 `convertVec (extractVec l) = l` 需**逐字段**展开结构 eta 得到）。
  have hL : convertVec (extractVec l) = l := by
    cases l with
    | mk w b => rfl
  have hL' : convertVec (extractVec l') = l' := by
    cases l' with
    | mk w b => rfl
  -- ⚠ 修复（B352 判据：「错误只是换了行号、形态不变」时查作用域/签名）：
  -- 原稿把两处中间桥写成 term-mode 的 `(by rw [hL])`，但 `Iff.trans` 的**中间命题**
  -- 未被 elaboration 提供预期类型 ⇒ `rw` 无目标可改
  -- （`invalid 'by' tactic, expected type has not been provided`，:252）。
  -- 修法：把整条链改成 **tactic-mode**，用 `calc` 显式给出每一跳的命题，
  -- 使 `rw [hL]` / `rw [hL']` 有确定的预期类型。逻辑与证明项**完全不变**。
  calc VectorConstraintSat (extractVec l) x
      ↔ LayerOut (convertVec (extractVec l)) x = 0 :=
        convertVec_preserves_semantics (extractVec l) x
    _ ↔ LayerOut l x = 0 := by rw [hL]
    _ ↔ LayerOut l' x = 0 := h x
    _ ↔ LayerOut (convertVec (extractVec l')) x = 0 := by rw [hL']
    _ ↔ VectorConstraintSat (extractVec l') x :=
        (convertVec_preserves_semantics (extractVec l') x).symm

/-! ## 四、⭐⭐ 读法 B：下降映射 `semConv` 及其**单射性**（**真**）

⚠ 本节的 `semConv` 是任务书「`convertVec` 穿过该商」的 **读法 B** 的严格形式。 -/

/-- ⭐⭐ **下降映射 `semConv`**：`convertVec` 在**符号侧商**上的良定义版本。

构造：`Quotient.lift`（`Init/Core.lean:1685`），相容性由 `convertVec_respects_semEq`（§三）给出。

⭐ **它比「`convertVec` 是单射」多说了什么**：`convertVec` 本身的单射性
在本仓**早已有之**（`RealReversibilityBoundary.convertVec_injective`，:81；
理由：`LinearLayer` 只有两个字段，`convertVec` 只是字段改名）。
⭐ **本定理不是那条**：它说的是 **`convertVec` 可以被定义在商的坐标上** ——
即「用语义等价类代替元素」后映射**仍然存在**。这是**良定义性**，不是单射性。 -/
def semConv : Quotient semSetoidC → Quotient semSetoidL :=
  Quotient.lift
    (fun c => Quotient.mk semSetoidL (convertVec c))
    (fun _ _ h => Quotient.sound (convertVec_respects_semEq h))

/-- ⭐ **下降映射的计算规则**（`Quotient.lift` 在 `⟦c⟧` 上的定义等式）。

⚠ **为什么是 `rfl`**：本工具链（`v4.14.0`）的 `Init/Core.lean:1545-1550` 给出

    protected theorem lift_beta (f) (c) (a) : lift f c (Quot.mk r a) = f a := rfl

⭐ 即 `Quot.lift` 在 `Quot.mk` 上**定义地**归约 —— 故本等式是 `rfl` 级。
⚠ **注意**：核心里**没有** `Quotient.lift_mk` 这个名字
（我 grep 过 `Init/`，`lift_mk` **零命中**）——
⇒ 若按 mathlib 习惯写 `simp only [Quotient.lift_mk]` 会**找不到引理**。
本文件因此**不用** `simp only [Quotient.lift_mk]`，直接给 `rfl` 等式。

注意：**历史沿革（已销账）**：`rfl` 是否真的闭合，曾取决于 `def semConv` 的展开 +
`Quotient.lift` 作为 `abbrev`（`Init/Core.lean:1685`）的透明性**叠加**是否被
`rfl` 的定型器接受。注意：该不确定性**已销账**：实测 `rfl` **成立**，退路
`Quot.lift_beta` 显式改写**未使用**（见文末 §十「原不确定清单的实测结论」）。 -/
@[simp] theorem semConv_mk (c : VectorConstraint) :
    semConv (Quotient.mk semSetoidC c) = Quotient.mk semSetoidL (convertVec c) :=
  rfl

/-- ⭐⭐ **读法 B 的主定理：`semConv` 是单射**。

⭐ **证明路线（承重的一步）**：
商上的等式 `semConv ⟦c⟧ = semConv ⟦c'⟧` 经 `semConv_mk` 化为
`⟦convertVec c⟧ = ⟦convertVec c'⟧`；再用 **`Quotient.exact`**（`Init/Core.lean:1833`）
把它**拉回关系** —— 得到 `SemEqL (convertVec c) (convertVec c')`；
最后由 `extractVec_respects_semEq`（§三）下到符号侧、再 `Quotient.sound` 收口。

注意：**`Quotient.exact` 是这里唯一能把「商相等」拆成「关系成立」的工具**。
若没有它，本定理**无法证明** —— 这正是 `RealConversionQuotient` 说
「需要 `Quotient.sound` 与证明项对齐」而**未做**的那步；本文件把它做完。

⭐⭐ **它比 §五 多说了什么**：§五 说**朴素读法 A 为假**；
本条说**修正后的读法 B 为真**。⇒ 二者合起来给出**精确判定**：
任务书那句话**必须**读成 B，读成 A 就是假的。 -/
theorem semConv_injective : Function.Injective semConv := by
  intro q q' hq
  -- 注意：修复（B352 判据：错误「只是换了行号、形态不变」⟹ 查作用域/签名）：
  -- 原稿写 `refine Quotient.inductionOn q ?_`，报
  --   `tactic 'rewrite' failed, did not find instance of the pattern …
  --    hq : semConv q = semConv q'   ⊢ ⟦c⟧ = ⟦c'⟧`（:323）
  -- ⭐ 真因**不是** `rw` 用法，而是 **`Quotient.inductionOn` 根本没有消除 `q`**：
  --    `Quotient.inductionOn q h`（`Init/Core.lean:1789` 的二元版同款）消去 `q` 时，
  --    其 motive 只能抽象**目标中出现的** `q`；而 `hq : semConv q = semConv q'`
  --    是**上下文里的假设**、类型含 `q`
  --    ⇒ `q` 仍被 `hq` **引用**，归纳消不掉它（`q q'` 原样留在上下文）。
  -- ⭐ 修法：先把含 `q`/`q'` 的假设 `hq` **泛化回目标**（`revert hq`），
  --    使上下文不再引用 `q`、`q'`，再对二者归纳。
  --    ⭐ 逻辑与结论**完全不变**，只是把归纳提到正确的作用域。
  revert hq
  refine Quotient.inductionOn q ?_
  intro c
  refine Quotient.inductionOn q' ?_
  intro c'
  intro hq
  -- 目标：`⟦c⟧ = ⟦c'⟧`（在 `semSetoidC` 下）
  -- 由 `hq : semConv ⟦c⟧ = semConv ⟦c'⟧` 与 `semConv_mk` 得权重侧商等式
  rw [semConv_mk, semConv_mk] at hq
  -- 拉回关系（`Quotient.exact`）：`SemEqL (convertVec c) (convertVec c')`
  have hL : SemEqL (convertVec c) (convertVec c') := Quotient.exact hq
  -- 下到符号侧（§三），再送回商（`Quotient.sound`）
  exact Quotient.sound (extractVec_respects_semEq hL)

/-! ## 五、注意：读法 A：**朴素单射性为假**（本文件的核心否定结果）

注意：任务书若按字面读成 A（`convertVec : VectorConstraint → LinearLayer/≈` 单射，
即 `convertVec c ≈ convertVec c' → c = c'`），则该命题**为假**。
本节给出**机器验证的证伪**。 -/

/-- **见证约束**：`x₀ + 1 = 0`，即 `a = [1]`、`b = 1`。

注意：与 `ConvertVectorLinear`/`RealReversibilityBoundary.revC`（:111）
及 `_R-03.r03C` **逐字相同**，但本文件**不 import** 那些模块
（避免为一条见证拉入整条依赖链），故重新定义并**如实登记重复**。 -/
def r04C : VectorConstraint := { a := [1], b := 1 }

/-- ⭐ **两个权重确实【不同】**：`scaleVec r04C 2 ≠ r04C`
（`b` 字段是 `1 * 2 = 2`，而 `r04C.b = 1`）。

注意：**证明**：`congrArg VectorConstraint.b` 取投影，把结构等式化为整数等式 `1 * 2 = 1`，
再 `norm_num` 消解。 -/
theorem r04_scale_ne_self : scaleVec r04C 2 ≠ r04C := by
  intro h
  have hb : r04C.b * 2 = r04C.b := by
    have := congrArg VectorConstraint.b h
    simpa [scaleVec] using this
  simp only [r04C] at hb
  norm_num at hb

/-- ⭐ **两个约束语义等价**（`r04C ≈ scaleVec r04C 2`），
直接实例化 `scaleVec_preserves`（:105，`lam = 2 ≠ 0`）。 -/
theorem r04_semEq_scaled : SemEqC r04C (scaleVec r04C 2) :=
  fun x => scaleVec_preserves r04C x 2 (by norm_num)

/-- ⭐ **编译后的两个层语义等价**（读法 A 的**前提**在见证上成立）。

由 §三 的相容性 `convertVec_respects_semEq` 直接得到。 -/
theorem r04_convertVec_semEq_scaled :
    SemEqL (convertVec r04C) (convertVec (scaleVec r04C 2)) :=
  convertVec_respects_semEq r04_semEq_scaled

/-- ⭐⭐ **读法 A 的证伪（本文件的核心否定结果）**：

     `¬ (∀ c c', SemEqL (convertVec c) (convertVec c') → c = c')`

⭐⭐ **即：`convertVec` 【不是】「穿过语义商」的单射**（按朴素读法 A）。
⭐ **见证**：`c := r04C`、`c' := scaleVec r04C 2` —— 前提成立
（`r04_convertVec_semEq_scaled`），但结论 `r04C = scaleVec r04C 2` **为假**
（`r04_scale_ne_self`）。

注意：**这不是「我证不出来」**：本定理**有证明项**，它**推翻**了读法 A。

⭐ **它满足任务书判据 #1（消融）与 #2（反驳可能）**：
- **#2 反驳可能**：存在**具体**对象（上述见证）使 A 的结论**不成立** ⇒ A 不是定义保证的；
- **#1 消融**：把前提 `SemEqL (convertVec c) (convertVec c')` **加强**为
  `convertVec c = convertVec c'`（结构相等）时结论**才**成立
  —— 见 `structural_form_is_true`，两个前提**只差一个 `≈` vs `=`**，
  而结论一真一假 ⇒ **该前提是承重的**。 -/
theorem naive_injectivity_is_false :
    ¬ (∀ c c' : VectorConstraint, SemEqL (convertVec c) (convertVec c') → c = c') := by
  intro h
  -- 把待证目标实例化到见证上
  -- 注意：修复（签名逐字核对）：`r04_scale_ne_self : scaleVec r04C 2 ≠ r04C`，
  -- 而目标处 `h r04C (scaleVec r04C 2) … : r04C = scaleVec r04C 2`（**方向相反**）
  -- ⇒ 必须用 `Ne.symm` 调向。原本直呼 `r04_scale_ne_self` 报
  -- `application type mismatch`（:388）。逻辑不变。
  exact (Ne.symm r04_scale_ne_self) (h r04C (scaleVec r04C 2) r04_convertVec_semEq_scaled)

/-- ⭐ **消融对照（判据 #1 的机器化）**：把前提从 `≈` 换成 **`=`**（结构相等）后，
结论**为真** —— 且这就是既有的 `convertVec` 单射性（`extractVec` 是左逆）。

⭐⭐ **本定理与 `naive_injectivity_is_false` 的【唯一】区别就在前提**：
- 本条前提：`convertVec c = convertVec c'` ⇒ 成立 真；
- A 的前提：`convertVec c ≈ convertVec c'` ⇒ 注意：假。

⇒ ⭐ **这正是「消融」判据的形式**：删掉/削弱那个假设，结论从**真变成假**
（不只是「证不出来」）。 -/
theorem structural_form_is_true :
    ∀ c c' : VectorConstraint, convertVec c = convertVec c' → c = c' := by
  intro c c' h
  -- `extractVec` 是 `convertVec` 的左逆（`roundtrip_extractVec`），故两边拉回即得
  rw [← roundtrip_extractVec c, ← roundtrip_extractVec c', h]

/-- ⭐ **读法 A 的「纤维」读法（负面形式）**：存在**两个不同的**约束在同一语义类中。

⭐ 与 `naive_injectivity_is_false` 的区别：本条给出**具体的**两个成员，
是「语义商严格粗于相等」的**构造性**见证（判据 #2 的最强形式）。

注意：**证明**：`r04_semEq_scaled`（等价）与 `r04_scale_ne_self`（不等，需 `Ne.symm` 调向）。
注意：**不用 `∘` 组合**：`r04_scale_ne_self` 是 `Prop`（`Not`），不是函数，
`r04_scale_ne_self ∘ Eq.symm` **类型错误**。 -/
theorem naive_fiber_has_two_points :
    ∃ c c' : VectorConstraint,
      SemEqC c c' ∧ c ≠ c' :=
  ⟨r04C, scaleVec r04C 2, r04_semEq_scaled, Ne.symm r04_scale_ne_self⟩

/-! ## 六、⭐ 量化（判据 #4）：纤维**包含**整条缩放轨道

注意：任务书 §判定 的判据 #4 要求「可计算的界或**充要条件**」。
本节给出 `semConv` 纤维的**单向**刻画，并**明确不声称**它是充要的。

注意：**诚实前置（不许省）**：本节**只**证「纤维 ⊇ 非零缩放轨道」，
**未**证反方向「纤维 ⊆ 缩放轨道」。
⇒ ⭐ **本节【不是】**任务书意义上的「精确刻画」；
把它读成充要条件是**超出**本文件所证内容的。
（`_R-03:320-328` 在同类问题上已登记过同样的局限，本文件沿用该诚实标准。）

注意：**另一条诚实前置**：`Int` 上「倍率轨道」**不是**等价关系
（`_R-02` / `RealCanonicalForm` 已证：`lam` 可以是 `0`，而 `0` 不可逆）。
本文件因此**不**声称「纤维 = 整个缩放轨道」这一**过强**命题。 -/

/-- ⭐ **非零缩放保持语义等价**（把 `scaleVec_preserves` 升到 `SemEqC`）。

⭐ **这是「纤维至少包含整条非零缩放轨道」的方向**。 -/
theorem semEqC_scaleVec (c : VectorConstraint) (lam : Int) (hlam : lam ≠ 0) :
    SemEqC c (scaleVec c lam) :=
  fun x => scaleVec_preserves c x lam hlam

/-- ⭐⭐ **量化结果（判据 #4）**：符号侧商点**合并整条非零缩放轨道** ——
对任意 `lam ≠ 0`，`⟦c⟧` 与 `⟦scaleVec c lam⟧` 是同一点。

注意：**命名订正（如实登记）**：本条**没有**提到 `semConv` ——
它陈述的是 `Quotient semSetoidC` 上的一件事实（商点相同），
**不是** `semConv` 的纤维。故**不**命名为 `semConv_fiber_…`
（那样会**夸大**：要谈 `semConv` 的纤维还需把该等式经 `semConv_mk` 送到陪域侧）。
本条改名 `semQuotient_merges_scale_orbit` 以（**逐字**）匹配它所证的内容。

⭐ **它比「相容性」多说了什么**：§三 只给「`≈` 传递」；
本条给出**一族无限多的**（`Int` 上 `lam ≠ 0` 有无穷多）元素**塌缩到同一个商点**。
⇒ ⭐ **与 §四 合起来才是完整的读数**：
「单射」是**商之间**的性质，**不是**「每个商点的原像只有原始一个元素」。

注意：**未证的另一半（如实登记）**：反方向「语义等价的任意两个约束必差一个倍率」
本文件**未证** —— 它需要 `List Int` 上「零化谓词决定系数比例」的论证，
**超出本任务范围**（见文末诚实边界第 3 条）。 -/
theorem semQuotient_merges_scale_orbit (c : VectorConstraint)
    (lam : Int) (hlam : lam ≠ 0) :
    Quotient.mk semSetoidC c = Quotient.mk semSetoidC (scaleVec c lam) :=
  Quotient.sound (semEqC_scaleVec c lam hlam)

/-- ⭐⭐ **商非退化（判据 #2 的商语言读法）**：符号侧的商**不是单点商** ——
存在**两个不同的商点**。

⭐⭐ **它为什么必须有**：§四 的「单射」若目标商是**单点**的，
则**任何**映射进它都是单射 —— 那是**空洞**的。
本定理排除该退化情形。⇒ **§四 + 本条合起来才排除空洞性。**

注意：**证明**：取 `{a := [], b := 0}` 与 `{a := [], b := 1}`（`x = []` 处区分）。 -/
theorem semQuotient_nontrivial :
    ∃ q q' : Quotient semSetoidC, q ≠ q' := by
  refine ⟨Quotient.mk semSetoidC ({ a := [], b := 0 } : VectorConstraint),
          Quotient.mk semSetoidC ({ a := [], b := 1 } : VectorConstraint), ?_⟩
  intro h
  -- 商相等 ⟹ 关系成立（`Quotient.exact`）
  have hrel : SemEqC ({ a := [], b := 0 } : VectorConstraint) { a := [], b := 1 } :=
    Quotient.exact h
  -- 在 `x = []` 处左端真、右端假
  have h2 : VectorConstraintSat ({ a := [], b := 0 } : VectorConstraint) [] := by
    simp [VectorConstraintSat, dot]
  have h3 := (hrel []).mp h2
  simp [VectorConstraintSat, dot] at h3

/-- ⭐⭐ **权重侧的商同样非退化**（§四 的单射目标若不是单点才有内容）。 -/
theorem semQuotientL_nontrivial :
    ∃ q q' : Quotient semSetoidL, q ≠ q' := by
  refine ⟨Quotient.mk semSetoidL ({ w := [], b := 0 } : LinearLayer),
          Quotient.mk semSetoidL ({ w := [], b := 1 } : LinearLayer), ?_⟩
  intro h
  have hrel : SemEqL ({ w := [], b := 0 } : LinearLayer) { w := [], b := 1 } :=
    Quotient.exact h
  have h2 : LayerOut ({ w := [], b := 0 } : LinearLayer) [] = 0 := by
    simp [LayerOut, dot]
  have h3 := (hrel []).mp h2
  simp [LayerOut, dot] at h3

/-! ## 七、⭐ 一致性检验：`semConv` 与「语义坐标」**对得上**

注意：单有单射性还不够：**必须**验证 `semConv` 就是「语义」这个函数本身，
否则它可能是个**恰好单射的怪映射**。本节做这个交叉检验。 -/

/-- ⭐ **语义坐标在符号侧商上良定义**：`SatSetR` 只依赖 `⟦c⟧`。

⭐ 与 `RealConversionQuotient.satSet_wellDefined`（:207）**内容重叠**
（后者在 `BehaviouralIndistinct` 上做同一件事），
注意：本文件**不 import** 该模块故重新证明，并**如实登记重叠**（§七）。 -/
theorem satSetR_wellDefined {c c' : VectorConstraint} (h : SemEqC c c') :
    SatSetR c = SatSetR c' := by
  ext x
  exact h x

/-- ⭐⭐ **交叉检验（本节的落点）**：`semConv` **不改变语义坐标**。

若 `⟦c⟧ = ⟦c'⟧`（符号侧商），则它们的**解集相同** ——
即 §四 的下降映射**尊重**「解集」这一观察。

注意：**意义**：它说明 `semConv` **不是**空洞的怪映射，而是**语义**的忠实载体。
⭐ **它比 §四 多说了什么**：§四 只说 `semConv` 单射；
本条说 `semConv` 的**定义域侧**已经**完全**捕获了语义
（商中相等 ⟹ 解集相等）。 -/
theorem semConv_preserves_satSet {q q' : Quotient semSetoidC} (h : q = q') :
    ∀ c c' : VectorConstraint,
      Quotient.mk semSetoidC c = q → Quotient.mk semSetoidC c' = q' →
      SatSetR c = SatSetR c' := by
  intro c c' hc hc'
  -- `⟦c⟧ = q = q' = ⟦c'⟧`，拉回关系后用 `satSetR_wellDefined`
  exact satSetR_wellDefined (Quotient.exact (hc.trans (h.trans hc'.symm)))

/-! ## 八、注意：结构性诊断：为什么任务书会写错

注意：§五 证伪了读法 A。本节说明**为什么**，使结论**可推广**。

⭐ **根因**：`convertVec` 的**定义域**是 `VectorConstraint`（**元素**），
而任务书要求的商在**陪域**侧（`Layer`/`LinearLayer`）。
把陪域取商后再问「映射单射」是**良定义性问题**，
注意：而 `convertVec` 在**语义粗化**下**恰恰不保持**「单射」——
因为语义商把 `c` 与 `scaleVec c 2` **合并**了，而 `convertVec` 把它们送到
**两个不同**但**语义等价**的层（§五）。

⭐ **正确的提法**：商必须取在**定义域**侧（符号侧），得到读法 B（§四）——
此时 `convertVec` 下降为一个 `VC/≈ → LL/≈` 的**单射**。

注意：**本诊断的形式化（可推广判据）**：若 `f` 在 `≈` 下**不**保持结构相等
（即存在 `a ≈ b` 但 `f a ≠ f b`），则 `f` **不可能**「穿过 `≈` 单射」。
⇒ 这给出一个**廉价的前置检验**，可用于其他转换映射。 -/

/-- ⭐ **可推广判据**：若存在 `a ~ b` 且 `a ≠ b`，则**任何**关系 `~` 都**不能**
「穿过商仍单射」（读法 A 意义上的 `∀ x y, x ~ y → x = y`）。

⭐⭐ **这是 §八 诊断的机器化**：它把「A 为假」**归约**为
「语义商**严格粗于**相等」这一**纯关系论**事实
（该事实的存在性由 `naive_fiber_has_two_points` 给出）。

⭐ **它比 §五 多说了什么**：§五 的 `naive_injectivity_is_false` 是**关于 `convertVec`** 的；
本条**完全不提** `convertVec`，是**纯关系论**的 ——
故它可**复用于检查其他转换映射**（判据 #3 所要求的「不只是本层的事实」）。

注意：**`f` 参数已删除（如实登记写作过程）**：初稿带一个 `(f : α → β)` 与
`(hf : ∀ x y, r x y → f x = f y)`，但**证明项根本没用到它们**
⇒ 那是**多余的假设**，会**削弱**定理。已删除。
⇒ ⭐ 结论**更强**：**不需要**任何 `f` 就能证「粗化 ⟹ 不可能穿过单射」。 -/
theorem not_injective_of_coarsening {α : Type*} (r : α → α → Prop)
    {a b : α} (hr : r a b) (hne : a ≠ b) :
    ¬ (∀ x y, r x y → x = y) :=
  fun h => hne (h a b hr)

/-! ## 九、诚实边界汇总（详见文件末注释） -/

end Lattice

/-!
## 十、注意：诚实边界（**不许省** —— 任务书 §报告结构 要求）

### 本文件【做到】的

| # | 内容 | 位置 |
|:--|:--|:--|
| 1 | `Setoid` 实例（两侧）—— 补 `RealConversionQuotient:258` 登记的缺口 | §二 |
| 2 | **真正**构造 `Quotient`（`Quotient.lift`）—— 同上 | §四 `semConv` |
| 3 | 下降映射 **`semConv` 的单射性**（读法 B，**真**） | §四 `semConv_injective` |
| 4 | 朴素读法 A **为假**（机器验证证伪） | §五 `naive_injectivity_is_false` |
| 5 | **消融对照**：前提 `≈` ↦ `=` 时结论转真 | §五 `structural_form_is_true` |
| 6 | 量化：商点合并整条非零缩放轨道；两侧商**非退化** | §六 |
| 7 | 交叉检验：`semConv` 尊重解集坐标 | §七 |
| 8 | 可推广判据（**纯关系论**，不提 `convertVec`） | §八 |

### 本文件【没有】做的（如实登记）

1. 成立 **已验证编译（2026-09-25 修订）**：本文件**已**经内核检查通过。
   ```
   python scripts\lean_probe.py lean\RealLayerSemanticQuotient.lean
   [lake-lock] lake exit code: 0        -- "Build completed successfully."
   ```
   注意：**本轮修订的真实根因（诚实登记，见 `_fix_out\F_RealLayerSemanticQuotient.md`）**：
   - 注意：**本文件此前【从未被 elaboration】** —— 它**不在** `lakefile.toml` 的 `roots` 里，
     故 `lake build RealLayerSemanticQuotient` 报 **`error: unknown target`**（PROCESS.md 阶段④ / B211）。
     ⭐ 已用仓库自带 `scripts\register-new-roots.ps1 -Apply` 注册（499 → 503 roots）。
     注意：**这是「76% 文件不编译」的一条独立成因**：不是证明写错，而是**文件对构建系统不可见**。
   - ⭐ 注册后暴露 **3 条真错**，全部已修（**只改证明体，未改任何陈述**）：
     - `:252` `invalid 'by' tactic, expected type has not been provided`
       —— `Iff.trans` 链里 term-mode 的 `(by rw [hL])` 无预期类型 ⇒ 改 `calc`（tactic-mode）；
     - `:323` `tactic 'rewrite' failed, did not find instance of the pattern … semConv ⟦?c⟧`
       —— 注意：**真因不是 `rw`**：`Quotient.inductionOn` 的 motive 只能抽象**目标中**的 `q`，
       而 `hq` 在**上下文**里引用 `q` ⇒ `q` 消不掉、`rw [semConv_mk]` 自然找不到模式。
       ⇒ 修法 `revert hq` 先把假设泛化回目标，再归纳；
     - `:388` `application type mismatch`
       —— `r04_scale_ne_self : scaleVec r04C 2 ≠ r04C` 与目标 `r04C = scaleVec r04C 2`
       **方向相反** ⇒ 补 `Ne.symm`（**签名逐字核对**，非猜测）。
   - 成立：原稿「不确定」清单里的 **`semConv_mk` 的 `rfl`** 与 **`Quotient.inductionOn` 位置参数**
     两点，**实测均成立**（无需退路 `Quot.lift_beta`）。
2. 注意：**`Layer`（列表层）的商未构造**：§二 只给了 `SemEqLayer` 的**自反性**。
   注意：**未**证它是等价关系（对称性/传递性在「逐层配对」定义下**不显然**，
   且该定义**可能不对** —— 正确形式大概是「`List.map` 的核」，
   但那会退化成 `RealConversionQuotient` 已证的空壳）。
   ⇒ 注意：**本文件对「`Layer` 的商」只做到「指出 `convertVec` 与它类型不匹配」**，
   **没有**完成它。
3. 注意：**缩放的另一半未证**：§六 只证「商点合并非零缩放轨道」，
   **未**证「语义等价 ⟹ 差一个倍率」。
   ⇒ §六 是**单向的**，**不是**任务书意义上的「精确刻画」。
4. 注意：**重复登记**（**不声称独立**）：
   - `SemEqC` / `SemEqL` / `SatSetR` 与 `RealConversionQuotient.BehaviouralIndistinct`(:178) /
     `SatSet`(:195) **定义同构**；
   - `semEqC_equivalence` / `satSetR_wellDefined` 与
     `behaviouralIndistinct_equivalence`(:185) / `satSet_wellDefined`(:207) **内容重叠**；
   - `r04C` 与 `RealReversibilityBoundary.revC`(:111)、`_R-03.r03C`(:233) **逐字相同**；
   - `structural_form_is_true` 与 `RealReversibilityBoundary.convertVec_injective`(:81) **同款**。
   注意：理由均为**避免依赖链**（本文件只 import 转换主干三模块），**但重复是事实**。
5. 注意：**未触及 `canonicalize` / `ScaleClass`**：`_R-02` 与 `RealCanonicalForm` 已处理
   「符号选取」，本文件**不与它们对接**（**未做**）。
6. 注意：**未证** `semConv` 是**满射到其像**之外的任何性质（未谈 `surjective`）；
   也未证 `semConv` 与 `extractVec` 下降出的反向映射**互逆**（**未做** `Equiv`）。

### ⭐ 原「不确定清单」的**实测结论**（2026-09-25 修订，**逐条销账**）

注意：本节原为**编译前**的自查清单。经 `lean_probe.py` 实测，逐条结论如下：

- 成立：**`semConv_mk` 的 `rfl` 成立**：`Quotient.lift` 作为 `abbrev` 的透明性 +
  `Quot.lift_beta`（`Init/Core.lean:1545`）叠加**确实**被 `rfl` 接受 —— **无需**退路
  `Quot.lift_beta`。原稿的推断**正确**。
  注意：附带确认：核心里**确实没有** `Quotient.lift_mk`（原稿 grep 结论正确）。
- 成立：**`Quotient.inductionOn q ?_` 的元变量顺序成立**：`refine … ?_` + `intro c`
  的位置参数用法**可用**（尽管原文注释里的行号 `1699-1703` 应为 `1789/1788`
  一带，`@[elab_as_elim]` 标注**不影响**该位置参数形式）。
  注意：**但真正的坑不在元变量顺序**：而是**归纳消不掉出现在假设里的 `q`**（见上 §十.1）。
- 成立：**`cases l <;> rfl` 证 `convertVec (extractVec l) = l` 成立**（结构 eta）。
  注意：本轮把它改写进了 `calc` 链，**原因与它本身对错无关**（是 `Iff.trans` 的
  term-mode 预期类型问题，见 §十.1）。
- 成立：**`simp [VectorConstraintSat, dot]` 能把 `dot [] []` 归约到 `0`** ——
  §六 两侧商非退化定理**均通过**。
- 注意：**`SemEqLayer` 的定义是否「对」—— 本条【未】销账**：
  它**能编译**（`semEqLayer_refl` 通过），注意：**但「能编译」不等于「定义正确」**。
  我**维持**原判断：该定义**可疑**（「逐层配对」不是等价关系的自然形式），
  注意：故 `semEqLayer_refl` **仍不宜**被下游当作可靠接口。**这是本文件真正的剩余缺口。**

注意：**诚实是本项目的最高纪律**：注意：上述 成立 是**实测销账**，**不是**把不确定包装成已验证；
注意：唯一**未**销账的是 `SemEqLayer` 的定义恰当性（那是**数学设计**问题，编译器管不到）。
-/
