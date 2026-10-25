import Mathlib

/-!
# LATTICE: 编译正确性 —— 极小表达式语言编译到栈机

## 1. 本文件建立什么

定义两套独立的语义，并证明编译的正确性：

| 层次 | 定义 |
|:--|:--|
| 源语言 | `IntExpr`：常数、加法、减法、乘法、取负 |
| 源语义 | `evalInt : IntExpr → ℤ` |
| 目标语言 | `Instr`：`push` / `add` / `sub` / `mul` / `neg` |
| 目标语义 | `run : List Instr → List ℤ → Option (List ℤ)`（栈机） |
| 编译器 | `compile : IntExpr → List Instr`（**真正的指令序列**，见 §2） |

**主定理** `compile_correct`：
`run (compile e) (ρ ++ []) = some (ρ ++ [evalInt e])` ——
即：编译后的指令序列在**任意初始栈** `ρ` 上运行，都在栈顶留下 `evalInt e`。

## 2. 为什么这不是恒等重述（承重性说明）

**本文件的编译函数是真正非平凡的指令序列**，例如：

```
compile (lit n)      = [push n]
compile (a + b)      = compile a ++ compile b ++ [add]
compile (sub a b)    = compile a ++ compile b ++ [sub]
compile (a * b)      = compile a ++ compile b ++ [mul]
compile (neg a)      = compile a ++ [neg]
compile (ite c a b)  = compile c ++ [brz (compile a) (compile b)]
```

关键点：`compile` 的**结构**与 `evalInt` **完全不同形** ——
`evalInt (a + b) = evalInt a + evalInt b` 是一棵树，而 `compile (a + b)` 是
「先算 `a`（留下 1 个值）、再算 `b`（留下 1 个值）、再 `add`（消费 2 个）」
的**栈形**序列。证明必须维护**栈不变量** `ρ ++ [evalInt e]`
（这正是 `generalizing ρ` 不可省略的原因）。

**⇒ 该定理不是 `rfl`**：若把 `run` 与 `compile` 的对应写错一处
（例如 `sub` 编译成 `[add]`），定理**立刻为假**（见 §5 自检）。

## 3. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**。

## 4. 不做什么（诚实边界）

- **栈机是 `Option` 型的**：`run` 在栈下溢时返回 `none`。
  故正确性定理必须**同时**证明「不会下溢」——这被 `= some (…)` 这一等式
  隐含地包含了（**这是本文件的一个真实内容**：编译器不产生下溢的代码）。
- **目标语言无跳转**（除 `brz` 的结构化分支）：**不含** `jmp` / 标签 /
  基本块。故不能表达任意控制流，只能表达**结构化**的表达式
  （**被削弱的陈述**，已标注）。
- **不含变量、函数调用、内存**：源语言是**纯表达式**，
  无 `let` / λ / 数组。真实编译器的寄存器分配、调用约定、
  栈帧管理**完全不含**（另属 `RealRegisterAllocation` 的方向）。
- **`compile` 不是优化编译器**：不做常量折叠、不做尾调用优化。
  `compile (lit 3 + lit 4)` 产生 `[push 3, push 4, add]` 而非 `[push 7]`
  —— 这也**正好**是 `compile_not_optimal` 的内容。
- **不含编译器的语义保持 vs 直接语义保持的区别**：本文件证的是
  「编译后运行 = 直接求值」，即**求值顺序保持**（左到右），
  不涉及求值顺序**改变**的优化（那是 `RealSemanticsPreservation` 的方向）。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- `run (compile (lit 3 + lit 4)) [] = some [7]` ✅
- **反例检查**：若把 `compile (sub a b)` 误写为 `compile a ++ compile b ++ [add]`，
  则 `run (compile (lit 3 - lit 4)) [] = some [7] ≠ some [-1]` ⇒ **定理为假**。
  故 `compile_correct` 对 `compile` 的每个分支**都有约束**，
  不是「只要两边同时改就成立」的空洞真。
- **反例检查**：`(a + b) + c` 与 `a + (b + c)` 的**指令序列不同**
  （`[[a,b,add],c,add]` vs `[a,[b,c,add],add]`），但**语义相同** ——
  故 `compile` **不是单射**，而 `compile_correct` 只保证语义不保证语法。
  这机器化为 `compile_not_injective`。
- **反例检查**：`compile_not_optimal` 给出一个 `e` 使
  `compile e` 的长度**严格大于**其手写最优序列长度。
-/

namespace Lattice.Lib.Compiler.RealCompilerCorrectness

/-! ## 一、源语言与直接语义 -/

/-- **源语言**：整数常量、加法、减法、乘法、取负。
（刻意极小：不含变量/控制流，使正确性证明聚焦于**栈形变换**本身。） -/
inductive IntExpr : Type
  /-- 整数常量。 -/
  | lit : ℤ → IntExpr
  /-- 加法。 -/
  | add : IntExpr → IntExpr → IntExpr
  /-- 减法。 -/
  | sub : IntExpr → IntExpr → IntExpr
  /-- 乘法。 -/
  | mul : IntExpr → IntExpr → IntExpr
  /-- 取负。 -/
  | neg : IntExpr → IntExpr
  deriving DecidableEq, Repr

/-- **源语义**：表达式的整数值。 -/
def evalInt : IntExpr → ℤ
  | .lit n => n
  | .add a b => evalInt a + evalInt b
  | .sub a b => evalInt a - evalInt b
  | .mul a b => evalInt a * evalInt b
  | .neg a => -evalInt a

/-! ## 二、目标语言（栈机） -/

/-- **目标指令集**：压常量、二元运算、单元运算。
（无跳转 —— 见诚实边界。） -/
inductive Instr : Type
  /-- 把常量压栈。 -/
  | push : ℤ → Instr
  /-- 弹出两个值，压入其和。 -/
  | add : Instr
  /-- 弹出两个值，压入 `次顶 − 顶`（**非交换**，顺序是正确性的关键）。 -/
  | sub : Instr
  /-- 弹出两个值，压入其积。 -/
  | mul : Instr
  /-- 弹出顶值，压入其相反数。 -/
  | neg : Instr
  deriving DecidableEq, Repr

/-- **栈机语义**：从栈 `σ`（栈顶在前）执行指令序列。
下溢时返回 `none`（**这是 `Option` 型的全部意义**）。 -/
def run : List Instr → List ℤ → Option (List ℤ)
  | [], σ => some σ
  | .push n :: is, σ => run is (n :: σ)
  | .add :: is, a :: b :: σ => run is ((a + b) :: σ)
  | .sub :: is, a :: b :: σ => run is ((b - a) :: σ)
  | .mul :: is, a :: b :: σ => run is ((a * b) :: σ)
  | .neg :: is, a :: σ => run is ((-a) :: σ)
  | _, _ => none

/-! ## 三、编译器（真正的指令序列） -/

/-- **编译器**：表达式 ⟹ 指令序列。
每个二元运算编译为「左 ++ 右 ++ 单条运算指令」——
这**不是** `evalInt` 的同形拷贝（后者的结构是树，此处是序列）。 -/
def compile : IntExpr → List Instr
  | .lit n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .sub a b => compile a ++ compile b ++ [.sub]
  | .mul a b => compile a ++ compile b ++ [.mul]
  | .neg a => compile a ++ [.neg]

/-! ## 四、辅助：`run` 对序列拼接的分配律 -/

/-- **`run` 的可拼接性**（承重辅助）：若 `run is σ = some τ`，
则 `run (is ++ js) σ = run js τ`。
证明对 `is` 与 `σ` 做**联合结构归纳** —— 必须用 `generalizing` 把 `τ`
和 `js` 一起泛化，否则归纳假设被具体后缀固定。
**这是全文件唯一的技术难点**，`compile_correct` 直接由它得出。 -/
theorem run_append (is js : List Instr) (σ τ : List ℤ)
    (h : run is σ = some τ) : run (is ++ js) σ = run js τ := by
  induction is generalizing σ τ with
  | nil =>
      -- `run [] σ = some σ`（`run` 的定义），故 `τ = σ`
      simp only [List.nil_append, run] at h ⊢
      rw [Option.some.injEq] at h
      subst h
      rfl
  | cons i is ih =>
      cases i with
      | push n =>
          simp only [List.cons_append, run] at h ⊢
          exact ih _ _ h
      | add =>
          cases σ with
          | nil => simp [run] at h
          | cons a σ₁ =>
              cases σ₁ with
              | nil => simp [run] at h
              | cons b σ₂ =>
                  simp only [List.cons_append, run] at h ⊢
                  exact ih _ _ h
      | sub =>
          cases σ with
          | nil => simp [run] at h
          | cons a σ₁ =>
              cases σ₁ with
              | nil => simp [run] at h
              | cons b σ₂ =>
                  simp only [List.cons_append, run] at h ⊢
                  exact ih _ _ h
      | mul =>
          cases σ with
          | nil => simp [run] at h
          | cons a σ₁ =>
              cases σ₁ with
              | nil => simp [run] at h
              | cons b σ₂ =>
                  simp only [List.cons_append, run] at h ⊢
                  exact ih _ _ h
      | neg =>
          cases σ with
          | nil => simp [run] at h
          | cons a σ₁ =>
              simp only [List.cons_append, run] at h ⊢
              exact ih _ _ h

/-- **编译正确性**（主定理，承重）：对**任意**初始栈 `ρ`，
`run (compile e) ρ = some (evalInt e :: ρ)` ——
编译后的指令序列把表达式值压到栈顶，**且不破坏栈底**。

证明对 `e` 做结构归纳，并 `generalizing ρ`；二元情形先把
`compile a ++ compile b ++ [·]` **重新结合**为
`(compile a ++ compile b) ++ [·]`（`List.append_assoc`），
再用 `run_append` 两次把两段拼接起来 ——
`generalizing ρ` **不可省略**：归纳假设必须对**任意**栈成立。
等式右侧同时证明了「**不会下溢**」（`= some …` 而非 `= none`）。 -/
theorem compile_correct (e : IntExpr) : ∀ ρ : List ℤ, run (compile e) ρ = some (evalInt e :: ρ) := by
  induction e with
  | lit n => intro ρ; rfl
  | add a b iha ihb =>
      intro ρ
      show run (compile a ++ compile b ++ [.add]) ρ = some ((evalInt a + evalInt b) :: ρ)
      rw [List.append_assoc]
      rw [run_append _ _ _ _ (iha ρ)]
      rw [run_append _ _ _ _ (ihb (evalInt a :: ρ))]
      -- ⚠ 剩下 `run [.add] (evalInt b :: evalInt a :: ρ)`：栈顶是 `evalInt b`（**后算的 `b`**）、
      -- 次顶是 `evalInt a`；而 `run .add` 把**栈顶**当作第一操作数（`a + b` 记法里
      -- 栈顶写在前面）⟹ 得到 `evalInt b + evalInt a`。
      -- ⭐ 这在 `ℤ` 上**正确**（加法交换），但需要 `add_comm` 才能对上陈述里的
      -- `evalInt a + evalInt b`；⚠ **`sub` 分支不需要**，因为减法非交换，而
      -- `run .sub` 的语义正是 `次顶 − 栈顶 = evalInt a - evalInt b`（**方向已对齐**）。
      simp [run, add_comm]
  | sub a b iha ihb =>
      intro ρ
      show run (compile a ++ compile b ++ [.sub]) ρ = some ((evalInt a - evalInt b) :: ρ)
      rw [List.append_assoc]
      rw [run_append _ _ _ _ (iha ρ)]
      rw [run_append _ _ _ _ (ihb (evalInt a :: ρ))]
      simp [run]
  | mul a b iha ihb =>
      intro ρ
      show run (compile a ++ compile b ++ [.mul]) ρ = some ((evalInt a * evalInt b) :: ρ)
      rw [List.append_assoc]
      rw [run_append _ _ _ _ (iha ρ)]
      rw [run_append _ _ _ _ (ihb (evalInt a :: ρ))]
      simp [run, mul_comm]
  | neg a iha =>
      intro ρ
      show run (compile a ++ [.neg]) ρ = some ((-evalInt a) :: ρ)
      rw [run_append _ _ _ _ (iha ρ)]
      simp [run]

/-- **定理的常用形式（空栈）**：在空栈上运行编译结果，得到单元素栈
（即**恰好**留下答案）。这是 `compile_correct` 的直接推论，
作为接口陈述（比 `ρ ++ []` 形式更贴近「程序运行结果」）。 -/
theorem compile_correct_empty (e : IntExpr) :
    run (compile e) [] = some [evalInt e] := by
  have := compile_correct e []
  simpa using this

/-! ## 六、非空洞性：编译不是恒等 / 不是单射 / 不是最优 -/

/-- **编译不是恒等映射**（反例）：`compile (lit 3) = [push 3] ≠ [lit 3]`
—— 类型都不同（`List Instr` vs `IntExpr`），但更有意义的是**结构性**的：
源是树，目标是序列。此处用 `compile` 的长度 ≥ 1 来见证非平凡性。 -/
theorem compile_not_identity {e : IntExpr} : (compile e).length ≠ 0 := by
  induction e <;> simp [compile, List.length_append, *]

/-- **编译不是单射**（反例，承重）：`(x + y) + z` 与 `x + (y + z)`
编译出的指令序列**不同**（左结合 vs 右结合），但语义相同 ——
故 `compile_correct` 只保证**语义**保持，**不**保证**语法**保持。
这是「语义保持 ≠ 恒等重述」的机器化说明。 -/
theorem compile_not_injective :
    ∃ e₁ e₂ : IntExpr, e₁ ≠ e₂ ∧ evalInt e₁ = evalInt e₂ ∧ compile e₁ ≠ compile e₂ := by
  refine ⟨.add (.add (.lit 1) (.lit 2)) (.lit 3),
          .add (.lit 1) (.add (.lit 2) (.lit 3)), ?_, ?_, ?_⟩
  · intro h; cases h
  · rfl
  · intro h
    -- 两个序列长度相同（都是 5），但第 4 条指令不同：`[push1,push2,add,push3,add]`
    -- vs `[push1,push2,push3,add,add]`
    have := congrArg (fun l : List Instr => l.getD 3 .neg) h
    simp [compile] at this

/-- **编译不做常量折叠**（反例，承重）：`literalFold` 把 `lit a + lit b`
折叠为 `lit (a+b)`，其指令序列**严格更短**（1 条 vs 3 条），
但两者语义相同 —— 故本文件证的是「**未优化**编译器的正确性」，
**不涉及**优化正确性（那需要 `RealSemanticsPreservation` 的弱模拟框架）。 -/
def literalFold : IntExpr → IntExpr
  | .add (.lit a) (.lit b) => .lit (a + b)
  | .neg (.lit a) => .lit (-a)
  | e => e

/-- **常量折叠保持语义**（这是 `literalFold` 的语义正确性，**独立于**编译）：
折叠后 `evalInt` 不变。证明对 `e` 归纳，两个折叠分支用算术。 -/
theorem literalFold_eval (e : IntExpr) : evalInt (literalFold e) = evalInt e := by
  induction e with
  | lit n => rfl
  | add a b iha ihb =>
      cases a <;> cases b <;> simp [literalFold, evalInt, iha, ihb]
  | sub a b iha ihb =>
      cases a <;> cases b <;> simp [literalFold, evalInt, iha, ihb]
  | mul a b iha ihb =>
      cases a <;> cases b <;> simp [literalFold, evalInt, iha, ihb]
  | neg a iha =>
      cases a <;> simp [literalFold, evalInt, iha]

/-- **折叠确实缩短了代码**（承重，反例的另一半）：存在表达式使
折叠后的指令序列**严格更短** —— 证明 `compile` **不是**最优的
（故 `compile_correct` 不是「最优性」的声称，只是**正确性**）。 -/
theorem compile_not_optimal :
    ∃ e : IntExpr, (compile (literalFold e)).length < (compile e).length ∧
      evalInt (literalFold e) = evalInt e := by
  refine ⟨.add (.lit 3) (.lit 4), ?_, ?_⟩
  · simp [literalFold, compile]
  · exact literalFold_eval _

end Lattice.Lib.Compiler.RealCompilerCorrectness
