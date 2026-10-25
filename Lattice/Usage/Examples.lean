/-
# USAGE 的代码块：每一个都必须能编译

本文件是 `USAGE.md` 的**可执行部分**。`USAGE.md` 里写的每一段代码，
在这里都有一份对应实现。若本文件编译失败，说明使用说明是错的。

这比「写出看起来正确的示例」强：示例的错误会立刻被内核发现。
-/
import Lattice.Lift.SymbolToWeight
import Lattice.Lift.Extraction
import Lattice.Lift.EndToEnd
import Lattice.Lift.CompilerScheme
import Lattice.Core.Repair
import Lattice.Core.RepairConvergence
import Lattice.Lift.L1L2Roundtrip

namespace Lattice.Usage

/-! ## 一、最小 `Compiler`：把 `Bool` 编译成 `Nat` -/

/-- **一段可用的最小编译器。**

符号侧 `Bool`，权重侧 `Nat`；输入侧 `Unit`（没有输入）。
`sound` 是义务：`true` 编译成 `1`，而 `satW` 判定「值为 1」。 -/
def boolCompiler : Lattice.Lift.Compiler Bool Nat Unit Unit where
  encode := id
  compile := fun b => if b then 1 else 0
  satP := fun b _ => b = true
  satW := fun n _ => n = 1
  sound := by
    intro b _ hb
    simp [hb]

/-- 用它编译一个程序，并得到保语义的结论。 -/
example : boolCompiler.EntailsW (boolCompiler.compileProgram [true]) () :=
  boolCompiler.compileProgram_sound [true] () (by
    intro p hp
    simp at hp
    subst hp
    rfl)

/-! ## 二、最小 `Representation`：往返恒等 -/

/-- **一段可用的最小表示**：`compile` 与 `extract` 互逆。 -/
def boolRep : Lattice.Lift.Representation Bool Nat where
  inputP := Unit
  inputW := Unit
  encode := id
  decode := id
  compile := fun b => if b then 1 else 0
  extract := fun n => n = 1
  roundtrip := by
    intro b
    cases b <;> rfl

example (b : Bool) : boolRep.extract (boolRep.compile b) = b :=
  boolRep.extract_compile b

/-! ## 三、最小 `Ladder`：四跳串起来 -/

/-- **符号 → token** 的最小分词器：`Bool` 编成单元素列表，解码取首项。 -/
def boolTok : Lattice.Lift.Tokenizer Bool Bool where
  encode := fun b => [b]
  decode := fun ts => ts.head?
  roundtrip := fun _ => rfl

/-- **一段可用的最小 `Ladder`**：`Data = List Bool`，`Tok = Sym = W = Bool`。 -/
def boolLadder : Lattice.Lift.Ladder (List Bool) Bool Bool Bool where
  l0l1 := Lattice.Lift.identityTokenizer Bool
  l1l2 := boolTok
  l2l3 := id
  satSym := fun s => s = true
  satW := fun w => w = true
  l2l3_sound := by
    intro s hs
    simpa using hs

example (s : Bool) (h : boolLadder.satSym s) : boolLadder.satW (boolLadder.l2l3 s) :=
  boolLadder.ladder_forward s h

/-- 端到端的往返：数据编成 token 再解回自身。 -/
example (d : List Bool) : boolLadder.l0l1.decode (boolLadder.l0l1.encode d) = some d :=
  boolLadder.l0l1.decode_encode d

/-! ## 四、最小 `Repair`：一步到目标 -/

/-- **一段可用的最小修复算子**：`Sat` 是「等于 0」，一步减一。 -/
def natRepair : Lattice.Core.Repair ℕ where
  Sat := fun n => n = 0
  fix := fun n => n - 1
  μ := fun n => n
  absorbs := by
    intro n hn
    simp [hn]
  decreases := by
    intro n hn
    exact Nat.sub_one_lt (by omega)
  atomic := by
    intro n hn
    exact hn

/-- 收敛率：`μ x` 步之内满足。 -/
example (n : ℕ) : natRepair.Sat (natRepair.iterate (natRepair.μ n) n) :=
  Lattice.Core.RepairConvergence.converges_within natRepair n

/-! ## 五、把编译器提升为后端 -/

/-- **一个后端**：包住编译器与它的输入类型。 -/
def boolBackend : Lattice.Lift.CompilerScheme.Backend Bool Nat :=
  Lattice.Lift.CompilerScheme.realise boolCompiler

example (p : Bool) (x : Unit) (h : boolCompiler.satP p x) :
    boolCompiler.satW (boolCompiler.compile p) (boolCompiler.encode x) :=
  boolBackend.backend_sound p x h

/-! ## 六、L1 ⇄ L2 往返（链层已有的那一跳） -/

open Lattice.Lift.L1L2Roundtrip

example (n : ℕ) (c : Lattice.Core.LinearForm ℝ n) :
    Lattice.Lift.decodePayload n (Lattice.Lift.encodeForm c).payload = some c :=
  decodePayload_encodeForm n c

end Lattice.Usage
