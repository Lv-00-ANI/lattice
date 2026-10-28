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

/-- **一条对照向量**：名字（必须与 `ABI.abiTable` 一致）、输入词、期望输出。 -/
structure ConformanceVector where
  /-- 必须等于某个 `CFunction.name`，由 `conformance_names_eq_abi` 机器核对。 -/
  name : String
  /-- 输入词，按 ABI 的参数顺序。 -/
  inputs : List Float
  /-- 期望的输出词。**由上面的 `Float` 公式算出，不是手敲的。** -/
  expected : Float
  deriving Repr

/-- `f x = 2x`（各向量共用的小函数）。 -/
def _f2 : Float → Float := fun x => 2.0 * x

/-- `g x = x + 1`（各向量共用的小函数）。 -/
def _g1 : Float → Float := fun x => x + 1.0

/-- **11 条向量**，每条对应 `ABI.abiTable` 的一个名字。 -/
def conformance : List ConformanceVector :=
  [ { name := "compose", inputs := [3.0], expected := fCompose _f2 _g1 3.0 }
  , { name := "composeWith", inputs := [3.0], expected := fComposeWith _f2 _g1 3.0 }
  , { name := "identity", inputs := [5.0], expected := fIdentity 5.0 }
  , { name := "descentStep", inputs := [0.5, -1.0, 3.0], expected := fStep 0.5 (-1.0) 3.0 }
  , { name := "iterate", inputs := [3.0, 0.0], expected := fIterate _g1 3 0.0 }
  , { name := "parallel", inputs := [3.0], expected := fParallel _f2 _g1 3.0 }
  , { name := "choice", inputs := [1.0, 3.0], expected := fChoice 1.0 _f2 _g1 3.0 }
  , { name := "optional", inputs := [1.0, 3.0], expected := fOptional 1.0 _f2 3.0 }
  , { name := "applySgd", inputs := [0.5, 4.0, 3.0], expected := fSgd 0.5 4.0 3.0 }
  , { name := "applyMomentum", inputs := [0.5, 0.9, 4.0, 1.0, 3.0],
      expected := fMomentum 0.5 0.9 4.0 1.0 3.0 }
  , { name := "applyAdam", inputs := [0.5, 0.0, 1.0, 0.125, 1.0],
      expected := fAdam 0.5 0.0 1.0 0.125 1.0 }
  ]

/-! ## 三、可证的：覆盖与命名 -/

/-- **向量有 11 条**。 -/
theorem conformance_length : conformance.length = 11 := by decide

/-- **名字互不相同**。 -/
theorem conformance_names_nodup : (conformance.map ConformanceVector.name).Nodup := by decide

/-- ⭐⭐ **向量覆盖的正是 ABI 表里的 11 个 primitive。**

**这是一道真门禁**：`ABI.abiTable` 增删或改名，本定理**构建失败**——
所以「每条 ABI 契约都有向量」不是声明，是类型检查。

⚠ **它只核对名字**，不核对期望值——期望值在 `Float` 上，与 `ℝ` 的一致性未证（见文件头）。 -/
theorem conformance_names_eq_abi :
    conformance.map ConformanceVector.name = abiTable.map CFunction.name := by decide

/-- **同一条事实的排序无关形式**，便于门禁脚本使用。 -/
theorem conformance_iff_abi (s : String) :
    (s ∈ conformance.map ConformanceVector.name) ↔ (s ∈ abiTable.map CFunction.name) := by
  rw [conformance_names_eq_abi]

end Lattice.CInterface.Conformance
