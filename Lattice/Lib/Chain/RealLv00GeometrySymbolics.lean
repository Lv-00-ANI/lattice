import Mathlib
import Lattice.Lib.Chain.RealLv00GeometryHilbert
/-! # RealLv00GeometrySymbolics

拆分自 `RealLv00Geometry.lean`（第 320–548 行，原「第二部分：符号数（GeometrySymbolicsTheory）」），2026-10-15。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00Geometry` 仍有效。

本模块重新声明了原文件的三项作用域设置（缺一不可）：
`noncomputable section`（原 :114）、`namespace Lattice.Lv00.Geometry`（原 :116）、
`open Real`（原 :118）。原文件**没有** `set_option`。
-/

noncomputable section

namespace Lattice.Lv00.Geometry

open Real

/-! ===========================================================================
## 第二部分：符号数（GeometrySymbolicsTheory）
===========================================================================

来源：`lvFormal/Theory/GeometrySymbolicsTheory.lean`（对应 C 文件
`core/src/layer3_geometry/symbolics/{rational,quadratic,algebraic,transcendental}.c`）。

**关键修复**：上游的四个数类型定义被未闭合的 `/-! ... -/` 注释块吞掉，
导致 `SymbolicCoord` 等引用悬空（也因此部分定理从未被 Lean 检查）。
本文件**重建**这四个类型为显式结构。
-/

/-- 有理数（GMP `mpq_t` 的抽象模型）：分子 / 分母 + 分母非零证据。
    **重建**（上游定义丢失）。 -/
structure RationalNumber where
  /-- 分子。 -/
  num : ℤ
  /-- 分母。 -/
  den : ℕ
  /-- 分母非零。 -/
  den_pos : 0 < den
  deriving DecidableEq

/-- 二次根式数 `a + b√n`（`ℚ(√n)` 基）。**重建**。 -/
structure QuadraticNumber where
  /-- 有理部分。 -/
  a : RationalNumber
  /-- 根号系数。 -/
  b : RationalNumber
  /-- 被开方数（无平方因子）。 -/
  n : ℕ
  deriving DecidableEq

/-- 代数数（极小多项式 + 隔离区间）。**重建**。 -/
structure AlgebraicNumber where
  /-- 极小多项式系数。 -/
  minimalPoly : List ℤ
  /-- 隔离区间下界。 -/
  lower : ℚ
  /-- 隔离区间上界。 -/
  upper : ℚ
  deriving DecidableEq

/-- 超越数（`π`、`e` 及其有理倍）。**重建**。 -/
structure TranscendentalNumber where
  /-- 符号名（如 `"pi"`、`"e"`）。 -/
  name : String
  /-- 有理系数。 -/
  coeff : ℚ
  deriving DecidableEq

/-- 符号数类型枚举。来源 `SymbolicType`。
    按包含性排序：`rational < quadratic < algebraic < transcendental`。 -/
inductive SymbolicType where
  | rational
  | quadratic
  | algebraic
  | transcendental
  deriving DecidableEq

/-- `SymbolicType` 的线性序（构造子声明顺序即包含性顺序）。
    注意 上游依赖 `deriving Ord` 并直接用 `≤`/`max`，此处**显式给出** `LinearOrder`
    以满足 `max` 与 `≤` 的类型类要求。

    用 `LinearOrder.lift'` 从 `ℕ` 拉回，单射性直接 `cases` 穷举 16 种组合。 -/
instance : LinearOrder SymbolicType :=
  LinearOrder.lift'
    (fun t => match t with
      | .rational => (0 : ℕ) | .quadratic => 1 | .algebraic => 2 | .transcendental => 3)
    (by
      intro a b h
      cases a <;> cases b <;> simp_all)

/-- 类型提升：取较大类型（来源 `SymbolicType.promote`）。 -/
def SymbolicType.promote (a b : SymbolicType) : SymbolicType := max a b

/-- **(A)** 提升结果 ≥ 左操作数。 -/
theorem promote_ge_left (a b : SymbolicType) : a ≤ SymbolicType.promote a b :=
  le_max_left a b

/-- **(A)** 提升结果 ≥ 右操作数。 -/
theorem promote_ge_right (a b : SymbolicType) : b ≤ SymbolicType.promote a b :=
  le_max_right a b

/-- **(A)** 提升满足结合律。 -/
theorem promote_assoc (a b c : SymbolicType) :
    SymbolicType.promote (SymbolicType.promote a b) c =
      SymbolicType.promote a (SymbolicType.promote b c) :=
  max_assoc a b c

/-- **(A)** 提升满足交换律。 -/
theorem promote_comm (a b : SymbolicType) :
    SymbolicType.promote a b = SymbolicType.promote b a :=
  max_comm a b

/-- 16 种类型组合的提升表（来源 `promotionTable`）。 -/
def promotionTable : List (SymbolicType × SymbolicType × SymbolicType) :=
  [(.rational, .rational, .rational),
   (.rational, .quadratic, .quadratic),
   (.rational, .algebraic, .algebraic),
   (.rational, .transcendental, .transcendental),
   (.quadratic, .rational, .quadratic),
   (.quadratic, .quadratic, .quadratic),
   (.quadratic, .algebraic, .algebraic),
   (.quadratic, .transcendental, .transcendental),
   (.algebraic, .rational, .algebraic),
   (.algebraic, .quadratic, .algebraic),
   (.algebraic, .algebraic, .algebraic),
   (.algebraic, .transcendental, .transcendental),
   (.transcendental, .rational, .transcendental),
   (.transcendental, .quadratic, .transcendental),
   (.transcendental, .algebraic, .transcendental),
   (.transcendental, .transcendental, .transcendental)]

/-- **(A)** 提升表对任意条目组合恰有一条记录（表是函数且完备）。
    对四个构造子两两穷尽即可（`cases` 展开 16 种组合，各自 `decide`）。 -/
theorem promotion_table_correct (t1 t2 : SymbolicType) :
    (promotionTable.filter (fun x => x.1 = t1 && x.2.1 = t2)).length = 1 := by
  cases t1 <;> cases t2 <;> decide

/-- 符号坐标联合体。来源 `SymbolicCoord`。 -/
inductive SymbolicCoord where
  | ofRational (r : RationalNumber)
  | ofQuadratic (q : QuadraticNumber)
  | ofAlgebraic (a : AlgebraicNumber)
  | ofTranscendental (t : TranscendentalNumber)

/-- 取符号坐标的类型。来源 `SymbolicCoord.typeOf`。 -/
def SymbolicCoord.typeOf : SymbolicCoord → SymbolicType
  | ofRational _ => .rational
  | ofQuadratic _ => .quadratic
  | ofAlgebraic _ => .algebraic
  | ofTranscendental _ => .transcendental

/-- 两个符号坐标的类型提升。来源 `SymbolicCoord.promoteType`。 -/
def SymbolicCoord.promoteType (a b : SymbolicCoord) : SymbolicType :=
  SymbolicType.promote a.typeOf b.typeOf

/-- **(A)** 类型提升对坐标是对称的（`promoteType` 展开为 `max` 后即交换律）。 -/
theorem promoteType_deterministic (a b : SymbolicCoord) :
    a.promoteType b = b.promoteType a := by
  unfold SymbolicCoord.promoteType SymbolicType.promote
  exact max_comm _ _

/-- 精确性标记。来源 `Exactness`。 -/
inductive Exactness where
  | exact
  | approx
  deriving DecidableEq

/- **降级 (C)**：上游 `rational_arithmetic_exact : True := by trivial` 与
   `algebraic_containment ... : True := by trivial` 是纯占位，丢弃。 -/

/-- 信任色（五级，用于电路断路器）。来源 `TrustColor`。 -/
inductive TrustColor where
  | green
  | blue
  | amber
  | yellow
  | red
  deriving DecidableEq

/-- `TrustColor` 的线性序（`green` 最好、`red` 最差；降级 = 序变大）。
    注意 上游依赖 `deriving Ord` 直接用 `≥`，此处**显式给出** `LinearOrder`。 -/
instance : LinearOrder TrustColor :=
  LinearOrder.lift' (fun c => match c with
    | .green => (0 : ℕ) | .blue => 1 | .amber => 2 | .yellow => 3 | .red => 4)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- 比特数上限阈值。来源 `BIT_CUTOFF_THRESHOLD`。 -/
def BIT_CUTOFF_THRESHOLD : Nat := 4096

/-- 整数的比特宽度（含符号位）。来源 `bitCount`。 -/
def bitCount (z : Int) : Nat :=
  if z = 0 then 0
  else if z > 0 then Nat.log2 (Int.toNat z) + 1
  else Nat.log2 (Int.toNat (-z)) + 1

/-- 有理数是否在电路规模限制内。来源 `RationalNumber.withinCircuitLimit`。 -/
def RationalNumber.withinCircuitLimit (r : RationalNumber) : Bool :=
  bitCount r.num ≤ BIT_CUTOFF_THRESHOLD && Nat.log2 r.den + 1 ≤ BIT_CUTOFF_THRESHOLD

/-- 代数数是否在电路规模限制内。来源 `AlgebraicNumber.withinCircuitLimit`。 -/
def AlgebraicNumber.withinCircuitLimit (a : AlgebraicNumber) : Bool :=
  a.minimalPoly.all (fun c => bitCount c ≤ BIT_CUTOFF_THRESHOLD)

/-- 电路断路器：超限则降级信任色。来源 `checkCircuitAndUpdateTrust`。 -/
def checkCircuitAndUpdateTrust (coord : TrustColor) (withinLimit : Bool) : TrustColor :=
  if withinLimit then coord
  else
    match coord with
    | .green => .amber
    | .blue => .amber
    | c => c

/-- 连续失败后永久降级。来源 `permanentDegrade`。 -/
def permanentDegrade (failCount : Nat) (current : TrustColor) : TrustColor :=
  if failCount ≥ 3 then
    match current with
    | .green => .yellow
    | .blue => .yellow
    | .amber => .yellow
    | c => c
  else current

/-- **(A)** 断路器只会降低或保持信任色（单调不升）。 -/
theorem circuit_breaker_monotone (old new : TrustColor)
    (h : new = checkCircuitAndUpdateTrust old false) : new ≥ old := by
  subst h
  cases old <;> decide

/-- **(A)** 永久降级只会降低或保持信任色。 -/
theorem permanent_degrade_monotone (c : TrustColor) (n : Nat) (h : n ≥ 3) :
    permanentDegrade n c ≥ c := by
  unfold permanentDegrade
  simp [h]
  cases c <;> decide

/-- 有理数序列化。来源 `RationalNumber.serialize`。 -/
def RationalNumber.serialize (r : RationalNumber) : String :=
  toString r.num ++ "/" ++ toString r.den

/-- 二次根式数序列化。来源 `QuadraticNumber.serialize`。 -/
def QuadraticNumber.serialize (q : QuadraticNumber) : String :=
  q.a.serialize ++ " + " ++ q.b.serialize ++ "*sqrt(" ++ toString q.n ++ ")"

/- **降级 (C)**：上游 `rational_serialize_deterministic (r) : True := by
   have _ := r.serialize; trivial` 是纯占位，丢弃。 -/


end Lattice.Lv00.Geometry
