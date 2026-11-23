import Lattice.Lib.Compiler.SymbolicEntry
import Lattice.Lib.Compiler.WriteBack

/-!
# **P1-a：一条显式证明配方——把「符号 → 产物 → 保证 → 提取 → 修复 → 写回 → 重验」串起来**

## 规划要求什么

规划 §5.2 要求**不追求自动证明搜索，先支持手工列出配方、机器检查每一步**：

1. 列出所需能力：源语义、精确/近似编译、行为提取、验证、修复；
2. 每个节点指定提供方与目标命题；
3. **每个接缝生成一个 Lean 义务**：类型匹配、前提可供给、语义域可承接、误差预算可合成；
4. 输出普通 Lean 定理。

**⇒ 本文件的每一个接缝都**引用既有定理**，没有新机制；新增的只有**接缝本身**。**

## 配方（节点与提供方）

| 节点 | 提供方 | 目标命题 |
|:--|:--|:--|
| 源语义 | `evalSym` | `evalSym x squareTerm = some (x · x)` |
| 编译 | `compileTarget` | `= some (.squareApprox)` |
| 构造 | `EvaluatedArtifact.ofSegments` + `Target.family` | 产物 |
| 求值 | `evalAt_ofSegments` | `evalAt x = some (gridEval …)` |
| 保证 | `irWeights_error_bound` | `\|x² − v\| ≤ (1/n)²/4` |
| **提取** | `decodedFamily_ofSegments` ← `gridLayout.retract` | **提取回的族**就是上面那个被证明有界的族** |
| 修复 | `slopeRepair` | 三条义务 |
| 写回 | `writeBack` | 重新编码进权重 |
| 重验 | `write_back_verifies_and_changes` | 判据成立 ∧ 可观察值改变 |

**⇒ 本文件新增的唯一接缝是**提取那一步**（`decodedFamily_ofSegments`）：
在此之前，`square_path_bound` 只说了「产物求值有界」，**没有说「提取回的东西就是那个有界的族」**。
而后者才是「提取 → 验证」在产物层真的接上的证据。**
-/

namespace Lattice.Lib.Compiler.Chain

open Lattice.Lib.Compiler.WeightSequence
open Lattice.Lib.Compiler.GridAlgebra
open Lattice.Lib.Compiler.PiecewiseWeights
open Lattice.Lib.Compiler.IRWeightsBridge
open Lattice.Lib.Compiler
open Lattice.Lib.Compiler.Samples
open Lattice.Lib.Compiler.SymbolicEntry
open Lattice.Lib.Compiler.WriteBack

/-- **⭐⭐ 接缝：由分段族构造的产物，其**提取回的载荷**就是该族本身。**

**⇒ 证明只用 `PartialSection.retract`（即 `decodeGrid_encodeGrid`）：
`decodedFamily = layout.extract weights = decode (encode g) = some g`。**

**⇒ 为什么这条是接缝而不是复述：它把「产物里有编码过的权重」与「提取能拿回原族」连接起来，
从而让**针对族的定理**（如 `irWeights_error_bound`）可以合法地用在**产物**上。** -/
theorem decodedFamily_ofSegments (g : ℕ → Segment) (dom : Lattice.Lib.Compiler.SemDomain)
    (r : Lattice.Lib.Compiler.CompileRecipe) :
    (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments g dom r).decodedFamily = some g := by
  show gridLayout.extract (gridLayout.compile g) = some g
  exact gridLayout.retract g

/-- **⭐⭐ A 段 + 提取接缝：`x²` 的完整近似链。**

**⇒ 四个合取项依次是：源语义、编译落点、产物整域界、**提取回的族就是被证明有界的那个族**。
最后一项使「提取 → 验证」不再依赖读者的记忆。** -/
theorem square_chain (r : Lattice.Lib.Compiler.CompileRecipe)
    (dom : Lattice.Lib.Compiler.SemDomain) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    evalSym x squareTerm = some (x * x)
      ∧ compileTarget r squareTerm = some (.squareApprox)
      ∧ (∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
              (Target.family r .squareApprox) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ (1 / (r.n : ℝ)) ^ 2 / 4)
      ∧ (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
            (Target.family r .squareApprox) dom r).decodedFamily
          = some (decodeGrid (piecewiseIRWeights r.n)) := by
  refine ⟨evalSym_squareTerm x, compileTarget_squareTerm r, ?_, ?_⟩
  · exact (square_path_bound r dom x hx).2
  · exact decodedFamily_ofSegments (decodeGrid (piecewiseIRWeights r.n)) dom r

/-- **⭐⭐ C 段：修复 → 写回 → 重验 ∧ 可观察变化。**

**⇒ 这是规划 §3.3 的四项要求在同一条陈述里的形式；逐项来源见 `WriteBack`：
改到的部分（`slopeFix_sat`）、保留的部分（`slopeFix_keeps_intercept`/`slopeFix_preserves_rest`）、
有限一步（`slopeMeasure` 的 `ℕ` 值）、无可观察变化则不算修复（`repair_changes_observable`）。** -/
theorem repair_chain (a b c : ℝ) (hba : b ≠ a)
    (dom : Lattice.Lib.Compiler.SemDomain) (r : Lattice.Lib.Compiler.CompileRecipe)
    (x : ℝ) (hx0 : x ≠ 0) (hidx : segmentIndex r.n x = 0) :
    slopeSat a (slopeFix a (constFamily b c))
      ∧ (writeBack (slopeFix a (constFamily b c)) dom r).evalAt x
          ≠ (writeBack (constFamily b c) dom r).evalAt x :=
  write_back_verifies_and_changes a b c hba dom r x hx0 hidx

/-- **⭐⭐⭐ P1-a：官方配方的单一陈述。**

**⇒ 它把两条分支并置（近似链与修复链），并使「这条链的每个接缝都是一个具名定理」这句话**可被检查**：
读完这条定理的合取项，再读 §配方 表格，逐项对应。**

**⇒ 为什么仍然值得有一条顶层定理：规划 §5.2 要求「输出普通 Lean 定理」，
而一条**可引用**的顶层陈述是把各段接起来的唯一方式——否则每个消费者都要自己重新拼一次，
拼法还可能不同。**

**⇒ 不承诺的东西：本定理**不**声称「修复后的产物仍满足 `x²` 的误差界」。
修复改变斜率，因此那条界**确实不再成立**；把两件事分开陈述，正是为了避免这种误读。** -/
theorem official_chain_recipe (a b c : ℝ) (hba : b ≠ a)
    (dom : Lattice.Lib.Compiler.SemDomain) (r : Lattice.Lib.Compiler.CompileRecipe)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hx0 : x ≠ 0) (hidx : segmentIndex r.n x = 0) :
    -- **A 段：符号 → 产物 → 整域保证 → 提取接缝**
    (evalSym x squareTerm = some (x * x)
      ∧ compileTarget r squareTerm = some (.squareApprox)
      ∧ (∃ v : ℝ,
          (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
              (Target.family r .squareApprox) dom r).evalAt x = some v
            ∧ |x ^ 2 - v| ≤ (1 / (r.n : ℝ)) ^ 2 / 4)
      ∧ (Lattice.Lib.Compiler.EvaluatedArtifact.ofSegments
            (Target.family r .squareApprox) dom r).decodedFamily
          = some (decodeGrid (piecewiseIRWeights r.n)))
      -- **C 段：修复 → 写回 → 重验 + 可观察变化**
      ∧ (slopeSat a (slopeFix a (constFamily b c))
          ∧ (writeBack (slopeFix a (constFamily b c)) dom r).evalAt x
              ≠ (writeBack (constFamily b c) dom r).evalAt x) :=
  ⟨square_chain r dom x hx, repair_chain a b c hba dom r x hx0 hidx⟩

end Lattice.Lib.Compiler.Chain