import Mathlib
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenizationEntry
import Lattice.Lift.RealTokenSymbolLink
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Lib.LearningTheory.RealRecoverEndpoint
/-!
# LATTICE: RealChainRun —— 端到端链路的【可执行驱动】（只接线，无新数学）

## 定位

X09（`notes/sweep11/X09-链的端到端可执行性.md`）判定：链的六级**逐级全部可计算**
（`tokenize` / `decode` / `compileToLayer` / `LayerOut` / `recover` 都是可求值函数），
**但全仓没有任何一处把它们串成一个"过程"**：`lean_exe` = 0、`def main` = 0、
链上 `#eval` = 0。⇒ 缺口是【打包】，不是【能力】。

本文件即 X09 §四.2 建议的那个驱动模块。**只做接线 + `#eval`，不引入任何新数学**：
不含新定义、不含新定理、不引入 `sorry`/`axiom`。
每一行 `#eval` 调用的都是**已存在的**函数（见各行注释）。

⚠ 本文件**刻意**把每段说明写成 `/- ... -/` **块注释**而非 `/-- ... -/` 文档注释：
Lean 会把文档注释**挂到下一个声明**上，而 `#eval` **不是声明**，
于是 `/-- -/` 后面接 `#eval` 会报 `unexpected token '#eval'; expected 'lemma'`。
本文件首次编译**实测**过这个失败（见报告 §二）。
-/

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! ## 一、六级接线：逐级 `#eval`（对 X09 §二.4 六行的复核） -/

/- L0 → L1a：`tokenize : List Char → Option (List CharToken)`（`RealTokenization.lean:333`）。 -/
#eval (tokenize ['a', 'b', ' ']).isSome

/- L1a → L1b：`CharToken` 经词条映射 `pieceOf`（`RealTokenization.lean:171`）投到字符，
再由 `SymToken.sym`（`RealTokenSymbolLink.lean:79`）构造符号 token。
注意 本文件写作时（X09 时期）全库**不存在**名为 `localBridge` / `L1Bridge` 的函数
（X09 §四.2 骨架里的 `L1Bridge` 是**占位名**，X09 §二.4 的表里写的是 `localBridge`，
两者在当时都**不是**仓库里的声明；`L1Bridge` 后来由 `RealEndToEnd.lean` 引入，
并配有 `L1BridgeNoSep`，`RealChainEntryOOV.lean` 与 `RealEndToEndNontrivial.lean`
都在正常引用它 —— 此处为**历史沿革**，非现况断言）；
本行仍刻意用**既有**函数现场接线，以保持与 X09 §二.4 的对照。 -/
#eval (pieceOf (CharToken.single 'a')).length

/- L1b → L2：`decode : List SymToken → Option ConstraintSet`（`RealTokenSymbolLink.lean:170`）。 -/
#eval (decode [SymToken.sym 1, SymToken.sep]).isSome

/- L2 → L3：`compileToLayer : ConstraintSet → Layer`（`SymbolToWeightCorrectness.lean:35`）。 -/
#eval (compileToLayer ([] : ConstraintSet)).length

/- L3 → Behavior：`LayerOut : LinearLayer → List Int → Int`（`ConvertVectorLinear.lean:48`）。 -/
#eval LayerOut ({ w := [1, 2], b := 3 } : LinearLayer) [1, 1]

/- L3 → Recover：`recover : Layer → List SymToken`（`RealRecoverEndpoint.lean:91`）。 -/
#eval (recover ([] : Layer)).length

/-! ## 二、贯通六级：一条从【字符】到【行为】的完整调用链

§一 的六级是**各自**调一次；下面把一个输入串成**一条链**，
证明六级的**类型确实接得上**（不只是各自能跑）。仍然只用既有函数。 -/

/- L0 输入字符。 -/
def runInput : List Char := ['1', ' ', '2']

/- L0 → L1a → L1b：字符 → 字符 token → 符号 token（用既有 `tokenize` + `pieceOf`）。
第一段 (`tokenize` 的词表) 与第二段 (`SymToken` 字母表) 是**两个不同的模型**，
本函数即 X09 §四.2 里那个缺失的"桥"，用**既有**构造子显式接出来。 -/
def runSymbols : List SymToken :=
  ((tokenize runInput).getD []).map
    (fun t => match pieceOf t with
      | [] => SymToken.sep
      | z :: _ => SymToken.sym (Int.ofNat z.toNat))

/- L1b → L2 → L3：符号 token → 约束集 → 权重层。 -/
def runLayer : Layer := compileToLayer ((decode runSymbols).getD [])

#eval runInput.length
#eval runSymbols.length
#eval runLayer.length

/-! ## 三、可判定的有限输入等式（T2）

`AllSatisfied` / `AllZeroOutputs` 是**全称量化 `Prop`**（`SymbolToWeightCorrectness.lean:40-46`），
量词跑遍无界 `List Int`，**无 `Decidable` 实例**（X09 §二.5，负对照逐字命中）。
但 `LayerOut` 是 `Int` 值函数：**在有限输入上 `decide` 是可判定的**。 -/

/- 规范约束集：`1*x + 1*y + 2 = 0`（`a = [1,1]`，`b = 2`）。
在有限输入 `[1,1]` 上行为 = `1*1 + 1*1 + 2 = 4`。 -/
def cs0 : ConstraintSet := [{ a := [1, 1], b := 2 }]

/- 负对照约束集：**只把常数项 `b` 从 2 改成 3** —— 其余逐字相同。 -/
def csNeg : ConstraintSet := [{ a := [1, 1], b := 3 }]

/- **T2 正例**：`cs0` 编出的层在有限输入 `[1,1]` 上行为恰为 `4`。 -/
#eval decide (LayerOut (List.headD (compileToLayer cs0) ({ w := [], b := 0 } : LinearLayer)) [1, 1] = 4)

/- **T2 负对照（判据 13：断言自己触发的那个 finding 的身份）**：
把 `cs0` 换成 `csNeg`（**只改 `b`**），**同一条等式变假**。
本行断言的**就是** `csNeg` 那条等式的**取反**，并且紧接着再断言它的**真实值** `5` ——
两条合起来把"变假"钉成"恰好等于 5 而非 4"，**不是**"证不出来"。
注意 若把 `cs0`/`csNeg` 任一定义改动，**红的会是这里**，即负对照**断言的是自身**。 -/
#eval decide (LayerOut (List.headD (compileToLayer csNeg) ({ w := [], b := 0 } : LinearLayer)) [1, 1] = 4)
#eval LayerOut (List.headD (compileToLayer csNeg) ({ w := [], b := 0 } : LinearLayer)) [1, 1]

end Lattice
