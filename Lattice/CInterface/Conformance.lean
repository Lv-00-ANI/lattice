import Mathlib
import Lattice.CInterface.ABI

/-!
# `CInterface/Conformance` —— **可执行的对照向量**

## 这一层回答什么问题

`DIRECTORY-DESIGN.md` §8.1 要「Lean `#eval` 向量与 C 对照」。
本文件给 **11 个 primitive 各一条向量**：输入、期望输出，以及**期望输出是怎么算出来的**。

## ⚠ 为什么向量在 `Float` 上，而不在 `ℝ` 上

`ℝ` 在 Lean 里**不可计算**（`step`、`affineAct` 都是 `noncomputable`），所以 `#eval` 在 `ℝ` 上
**不可能**跑出向量。因此本文件用 **`Float` 作为 `ℝ` 的可执行模型**。

⚠⚠ **这制造了第二个权威**：`Domains/Geometry/ConstraintDescent.step` 在 `ℝ` 上，
本文件 `fStep` 在 `Float` 上，**同一公式两处实现**。这是**不可避免的**（不可计算 ⇔ 不可执行），
但必须写明：**两处必须手工保持同步**，而 `Float` 有舍入，所以 C 侧对照要按容差比较。

## 期望值不是我手敲的数字

每条向量的 `expected` 由 `fStep`/`fSgd`/… 这些 **`Float` 公式**算出——
**算术经过 Lean 的求值器，不经过我**。所以这条文件里没有一处「我认为 3 − 2 = 1」。

## 可证的是什么（这才是机器的部分）

**名字与 ABI 表一一对应**：`conformance_names_eq_abi`。

⚠ **它是一道真门禁**：`ABI.abiTable` 里加一条、删一条、改名，本文件**构建失败**。
所以「向量覆盖了所有 primitive」不是散文，是**类型检查**。

## 本文件**没有**证明什么

- **没有**证明 `Float` 公式与 `ℝ` 公式一致（那需要 `ℝ → Float` 的舍入模型，见 `Lib/Quantization/RealIEEE754`）；
- **没有**证明 C 实现与这些向量一致（那需要真的跑 C，即 §8.1 的 P6）；
- **没有**证明向量的**充分性**（11 条覆盖 11 个 primitive 的**一个**输入，不是全部输入）。 -/

namespace Lattice.CInterface.Conformance

open Lattice.CInterface.ABI

/-! ## 一、`Float` 侧的可执行公式

每一条都对应一个 `Primitive` 的语义，写在注释里。`Float` 是 `ℝ` 的可执行模型。 -/

/-- **`identity`**：`x ↦ x`。 -/
def fIdentity (x : Float) : Float := x

/-- **`compose`**：`g ∘ f`。 -/
def fCompose (f g : Float → Float) (x : Float) : Float := g (f x)

/-- **`descentStep`**：二次损失的精确梯度步 `β ↦ β − η·2·(β + c)`，
与 `Domains/Geometry/ConstraintDescent.step` 同式（那里在 `ℝ` 上）。 -/
def fStep (η c β : Float) : Float := β - η * (2 * (β + c))

/-- **`iterate`**：`f` 迭代 `n` 次。 -/
def fIterate (f : Float → Float) : Nat → Float → Float
  | 0, x => x
  | n + 1, x => fIterate f n (f x)

/-- **`applySgd`**：`β ↦ β − η·g`。 -/
def fSgd (η g β : Float) : Float := β - η * g

/-- **`applyMomentum`**：`β ↦ β − η·g + μ·v`。 -/
def fMomentum (η μ g v β : Float) : Float := β - η * g + μ * v

/-- **`applyAdam`**：`β ↦ β − η·m̂ / (√v̂ + ε)`。 -/
def fAdam (η mhat vhat eps β : Float) : Float := β - η * mhat / (Float.sqrt vhat + eps)

/-- **`choice`**：`b = 1` 取 `f`，否则取 `g`。 -/
def fChoice (b : Float) (f g : Float → Float) (x : Float) : Float :=
  if b == 1.0 then f x else g x

/-- **`optional`**：`n = 1` 表示 `some`，取 `f`；否则 `none`，返回 `0`。 -/
def fOptional (n : Float) (f : Float → Float) (x : Float) : Float :=
  if n == 1.0 then f x else 0.0

/-- **`parallel`**：`(f x, g x)` 的**和投影**（ABI 只回一个标量，故取和）。 -/
def fParallel (f g : Float → Float) (x : Float) : Float := f x + g x

/-- **`composeWith`**：带一致性桥的两段复合；本向量里桥取恒等，退化为 `g ∘ f`。 -/
def fComposeWith (f g : Float → Float) (x : Float) : Float := g (f x)

/-! ## 二、向量 -/

/-- **向量的种类**：内部点，还是**边界**。

L0-5 要「向量的充分性」。这里能证的那一半是**覆盖**：每个 primitive 至少有一条**边界**向量；
不能证的那一半写在文件末尾（`Float` 没有代数引理，边界**恒等式**本身在 `Float` 上不可证）。 -/
inductive VectorKind where
  /-- 内部点：一个普通输入。 -/
  | interior
  /-- 边界点：`η = 0`、在解处、分支的两端。**C 实现必须在这些点上与公式逐位一致。** -/
  | boundary
  deriving DecidableEq, Repr

/-- **一条对照向量**：名字（必须与 `ABI.abiTable` 一致）、输入词、期望输出。 -/
structure ConformanceVector where
  /-- 必须等于某个 `CFunction.name`，由 `conformance_names_eq_abi` 机器核对。 -/
  name : String
  /-- 输入词，按 ABI 的参数顺序。 -/
  inputs : List Float
  /-- 期望的输出词。**由上面的 `Float` 公式算出，不是手敲的。** -/
  expected : Float
  /-- 内部点还是边界点。 -/
  kind : VectorKind
  deriving Repr

/-- `f x = 2x`（各向量共用的小函数）。 -/
def _f2 : Float → Float := fun x => 2.0 * x

/-- `g x = x + 1`（各向量共用的小函数）。 -/
def _g1 : Float → Float := fun x => x + 1.0

/-- `f x = x`（边界向量的恒等）。 -/
def _fid : Float → Float := fun x => x

/-- **22 条向量**：11 个 primitive 各一条**内部点**、各一条**边界点**。

边界点选的正是「C 实现最容易写错、而定理最容易说清」的位置：
`η = 0`（不动）、在解处（`β + c = 0` 时损失为零）、`n = 0`（零步）、分支两端（`choice`/`optional`）。
**它们的 `expected` 同样由 `Float` 公式算出。** -/
def conformance : List ConformanceVector :=
  [ -- 内部点
    { name := "compose", inputs := [3.0], expected := fCompose _f2 _g1 3.0, kind := .interior }
  , { name := "composeWith", inputs := [3.0], expected := fComposeWith _f2 _g1 3.0, kind := .interior }
  , { name := "identity", inputs := [5.0], expected := fIdentity 5.0, kind := .interior }
  , { name := "descentStep", inputs := [0.5, -1.0, 3.0], expected := fStep 0.5 (-1.0) 3.0,
      kind := .interior }
  , { name := "iterate", inputs := [3.0, 0.0], expected := fIterate _g1 3 0.0, kind := .interior }
  , { name := "parallel", inputs := [3.0], expected := fParallel _f2 _g1 3.0, kind := .interior }
  , { name := "choice", inputs := [1.0, 3.0], expected := fChoice 1.0 _f2 _g1 3.0, kind := .interior }
  , { name := "optional", inputs := [1.0, 3.0], expected := fOptional 1.0 _f2 3.0, kind := .interior }
  , { name := "applySgd", inputs := [0.5, 4.0, 3.0], expected := fSgd 0.5 4.0 3.0, kind := .interior }
  , { name := "applyMomentum", inputs := [0.5, 0.9, 4.0, 1.0, 3.0],
      expected := fMomentum 0.5 0.9 4.0 1.0 3.0, kind := .interior }
  , { name := "applyAdam", inputs := [0.5, 0.0, 1.0, 0.125, 1.0],
      expected := fAdam 0.5 0.0 1.0 0.125 1.0, kind := .interior }
    -- 边界点
  , { name := "compose", inputs := [3.0], expected := fCompose _fid _g1 3.0, kind := .boundary }
  , { name := "composeWith", inputs := [3.0], expected := fComposeWith _fid _g1 3.0,
      kind := .boundary }
  , { name := "identity", inputs := [0.0], expected := fIdentity 0.0, kind := .boundary }
  , { name := "descentStep", inputs := [0.5, -3.0, 3.0], expected := fStep 0.5 (-3.0) 3.0,
      kind := .boundary }
  , { name := "iterate", inputs := [0.0, 7.0], expected := fIterate _g1 0 7.0, kind := .boundary }
  , { name := "parallel", inputs := [4.0], expected := fParallel _fid _fid 4.0, kind := .boundary }
  , { name := "choice", inputs := [0.0, 3.0], expected := fChoice 0.0 _f2 _g1 3.0, kind := .boundary }
  , { name := "optional", inputs := [0.0, 3.0], expected := fOptional 0.0 _f2 3.0, kind := .boundary }
  , { name := "applySgd", inputs := [0.0, 4.0, 3.0], expected := fSgd 0.0 4.0 3.0, kind := .boundary }
  , { name := "applyMomentum", inputs := [0.0, 0.0, 4.0, 1.0, 3.0],
      expected := fMomentum 0.0 0.0 4.0 1.0 3.0, kind := .boundary }
  , { name := "applyAdam", inputs := [0.5, 0.0, 1.0, 0.125, 1.0],
      expected := fAdam 0.5 0.0 1.0 0.125 1.0, kind := .boundary }
  ]

/-! ## 三、可证的：覆盖与命名 -/

/-- **向量有 22 条**：每个 primitive 一条内部点、一条边界点。 -/
theorem conformance_length : conformance.length = 22 := by decide

/-- **`dedup` 之后名字与 ABI 一一对应**（`decide` 已核对，见上一条）。

原始名字列表有重复——这是**设计**：每个 primitive 一条内部点、一条边界点。所以这里不再声称
原始列表 `Nodup`，而是声称**边界那一半**互不相同（每个 primitive 恰一条）。 -/
theorem conformance_names_dedup_length :
    (conformance.map ConformanceVector.name).dedup.length = 11 := by decide

/-- ⭐⭐ **向量覆盖的正是 ABI 表里的 11 个 primitive。**

**这是一道真门禁**：`ABI.abiTable` 增删或改名，本定理**构建失败**——
所以「每条 ABI 契约都有向量」不是声明，是类型检查。

⚠ **它只核对名字**，不核对期望值——期望值在 `Float` 上，与 `ℝ` 的一致性未证（见文件头）。 -/
theorem conformance_names_eq_abi :
    (conformance.map ConformanceVector.name).dedup = abiTable.map CFunction.name := by decide

/-- **同一条事实的排序无关形式**，便于门禁脚本使用。 -/
theorem conformance_iff_abi (s : String) :
    (s ∈ conformance.map ConformanceVector.name) ↔ (s ∈ abiTable.map CFunction.name) := by
  -- the raw name list has duplicates (one interior + one boundary per primitive), so go through `dedup`
  rw [← List.mem_dedup, conformance_names_eq_abi]

/-- **边界向量覆盖的 primitive 集合**。 -/
def boundaryPrimitives : List String :=
  (conformance.filter (fun v => v.kind == VectorKind.boundary)).map ConformanceVector.name

/-- ⭐⭐ **L0-5 的机器部分：每个 primitive 都有一条边界向量。**

**这是一道真门禁**：`ABI.abiTable` 加一条 primitive 而不加边界向量，本定理**构建失败**。
所以「边界覆盖」不是散文，是类型检查。

⚠ **它只核对「有边界向量」，不核对边界向量的值对不对**——后者需要 `Float` 上的恒等式，
而 `Float` 在 Lean 里没有代数引理（见文件末尾的实测记录）。 -/
theorem every_primitive_has_boundary (s : String) (hs : s ∈ abiTable.map CFunction.name) :
    s ∈ boundaryPrimitives := by
  have h22 : boundaryPrimitives.length = 11 := by decide
  have hall : ∀ t ∈ boundaryPrimitives, t ∈ abiTable.map CFunction.name := by decide
  -- both lists have the same 11 names; `decide` on the full statement is what closes it
  revert s
  decide

/-- **边界向量的名字互不相同**：每个 primitive 恰有一条边界向量。 -/
theorem boundaryPrimitives_nodup : boundaryPrimitives.Nodup := by decide

/-- **内部点与边界点各 11 条。** -/
theorem interior_length :
    (conformance.filter (fun v => v.kind == VectorKind.interior)).length = 11 := by decide

/-! ## 五、L0-5 做到了什么、没做到什么（第 32 轮，实测）

### 做到了：边界覆盖是**类型检查**的

`every_primitive_has_boundary`：`ABI.abiTable` 里任何一个名字，都在 `boundaryPrimitives` 里。
**加一条 primitive 而不加边界向量，本文件不编译。**

### 没做到：边界**恒等式**在 `Float` 上不可证

想证的东西本来很直白，例如「在解处一步不动」：

想证的是（这里**故意不写成声明形式**——`audit_aliases` 会把 docstring 里形如 `theorem …` 的行读成真声明，
第 32 轮实测踩到过一次）：

    fStep_at_solution : ∀ (η c β : Float), β + c = 0 → fStep η c β = β

**实测：证不出来。** 第 32 轮试了这一批，`simp` 在每一个上都报
**`simp made no progress`**：

    error: simp made no progress                  -- fStep, h : β + c = 0
    error: simp made no progress                  -- fSgd 0 g β
    error: simp made no progress                  -- fMomentum 0 0 g v β
    error: simp made no progress                  -- fAdam η 0 vhat eps β
    error: unsolved goals  ⊢ (0 == 1.0) = true → f x = g x

**原因**：`Float` 在 Lean 里是**不透明的 IEEE 类型**，没有 `ring`、没有 `add_zero` 这样的引理可推。
所以 `0 * g = 0`、`β - 0 = β` 这些在 `ℝ` 上一行 `ring` 的事，在 `Float` 上没有任何工具。

**这是 L0-6（`Float`/`ℝ` 一致性）之所以是独立一条的原因，不是疏忽**：要把这些恒等式变成定理，
需要一层 `ℝ → Float` 的舍入模型（`Lib/Quantization/RealIEEE754` 有），而那是另一条链。

### 因此本文件的边界向量靠什么

**靠同一个 `Float` 函数算出来**：`expected := fStep 0.5 (-3.0) 3.0`。C 侧要在这些点上与它逐位一致。
**「值算对了」不是定理，是同一次求值**——本文件不声称它是定理。

⚠ **一句话边界**：边界向量的**覆盖**是证过的；边界向量的**正确性**与 `Float` 的语义绑定，
而 `Float` 的语义没有在 Lean 里形式化。 -/

end Lattice.CInterface.Conformance
