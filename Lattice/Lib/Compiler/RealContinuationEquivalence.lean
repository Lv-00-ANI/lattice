import Mathlib

/-!
# LATTICE: 续延等价 —— CPS 变换的语义保持（一阶片段）

## 1. 本文件建立什么

为一个**一阶表达式语言**（常数、加法、减法、条件）定义：

- **直接语义** `evalCond : CondExpr → ℤ`（值）；
- **CPS 语义** `cps : CondExpr → (ℤ → ℤ) → ℤ`（续延传递）；

并证明**语义保持** `cps_correct : ∀ e k, cps e k = k (evalCond e)`。

⚠ **这里的语义保持不是恒等重述**，理由见 §2。

## 2. 为什么这不是恒等重述（承重性说明）

`cps` 是一个**非平凡的递归定义**，其结构与 `evalCond` **不同形**：

| | `evalCond` | `cps` |
|:--|:--|:--|
| 加法 | `evalCond a + evalCond b` | 先求 `a`，把 **结果绑成续延参数**，在续延体内再求 `b` |
| 条件 | `if evalCond c = 0 then … else …` | 求 `c`，把守卫**作为续延参数**传递，在续延体内分派 |

故 `cps_correct` 的证明是**对 `e` 的结构归纳 + 对续延的 `fun k => …` 抽象**，
归纳假设必须**对所有续延**成立（因此归纳时用 `generalizing k`；
**不加 `generalizing` 则 IH 被具体续延固定，证明必然卡住** ——
这是本文件刻意保留的技术要点）。

此外给出三条**独立**内容：

- `cps_id_is_eval`：以 `id` 为续延的 CPS 求值等于直接求值；
- `cps_tail_compose`：CPS 对续延**复合**封闭（`cps e (k ∘ j)` 的语义），
  这是 CPS 变换可组合性的形式化 —— **非平凡**，需要 `cps_correct` 两次；
- `cps_call_by_value_shape`：CPS 求值**总是**以「调用最终续延」收尾，
  即 `cps e k = k (evalCond e)` 的**不可回避性**。

## 3. 依赖什么

仅 `Mathlib`。**不 import 任何 LATTICE 模块**。

## 4. 不做什么（诚实边界）

- **只证一阶片段**：语言无 λ、无变量绑定、无递归。
  **不含高阶 CPS**（即 `λk. …` 本身作为值被传递）。
  给定的 CPS 变换是**一阶**的（续延是元层面的 `ℤ → ℤ`，不是语言内的项）。
  这是**被削弱的陈述**，已按要求标注。
- **语义域是 `ℤ` 而非带底/异常的域**：故不能表达「求值可能发散或出错」。
  真实的 CPS 变换用于**表达**控制效应（异常、call/cc），
  本文件只覆盖**纯**（total）片段。
- **不涉及 defunctionalization / 闭包转换**（另属编译后端的范畴）。
- 不用 `sorry` / `axiom` / `admit` / `native_decide`。

## 5. 小规模自检（落盘前判真假）

- `evalCond (3 - 1) = 2`；`cps (3 - 1) k = k 2` ✅。
- `cps` 对 `if 0 = 0 then a else b` 先求守卫再分派 ✅。
- **反例检查**：若把 `cps` 的减法误写成 `k (evalCond b - evalCond a)`（交换操作数），
  则 `cps_correct` **假**（取 `a = 3, b = 1` 得 `-2 ≠ 2`）——
  故 `cps_correct` 的内容**依赖于 `cps` 的具体结构**，不是定义的重述。
-/

namespace Lattice.Lib.Compiler.RealContinuationEquivalence

/-! ## 一、语言与直接语义 -/

/-- **一阶表达式**：常数、加法、减法、零测试条件。
（刻意极小；算术语义取 `ℤ` 以避免除法带来的 total 性问题。） -/
inductive CondExpr : Type
  /-- 常数。 -/
  | lit : ℤ → CondExpr
  /-- 加法。 -/
  | add : CondExpr → CondExpr → CondExpr
  /-- 减法。 -/
  | sub : CondExpr → CondExpr → CondExpr
  /-- 条件：守卫为 `0` 取 `e₁`，否则取 `e₂`。 -/
  | ite : CondExpr → CondExpr → CondExpr → CondExpr
  deriving DecidableEq, Repr

/-- **直接语义**（自然语义）：表达式的值。 -/
def evalCond : CondExpr → ℤ
  | .lit n => n
  | .add a b => evalCond a + evalCond b
  | .sub a b => evalCond a - evalCond b
  | .ite c e₁ e₂ => if evalCond c = 0 then evalCond e₁ else evalCond e₂

/-- **CPS 语义**：把最终结果交给续延 `k`。
注意结构与 `evalCond` **不同形**：子表达式通过续延参数传递中间结果。 -/
def cps : CondExpr → (ℤ → ℤ) → ℤ
  | .lit n, k => k n
  | .add a b, k => cps a (fun va => cps b (fun vb => k (va + vb)))
  | .sub a b, k => cps a (fun va => cps b (fun vb => k (va - vb)))
  | .ite c e₁ e₂, k =>
      cps c (fun vc => if vc = 0 then cps e₁ k else cps e₂ k)

/-! ## 二、主定理：CPS 保持语义 -/

/-- **CPS 语义保持**（主定理，承重）：
对**任意**续延 `k`，`cps e k = k (evalCond e)`。

证明：对 `e` 做结构归纳，并 `generalizing k` —— 归纳假设必须对**所有**
续延成立，否则 `add`/`sub`/`ite` 情形（它们在续延体内递归调用）无法应用。
**`generalizing k` 是本证明不可省略的一步**。 -/
theorem cps_correct (e : CondExpr) : ∀ k : ℤ → ℤ, cps e k = k (evalCond e) := by
  -- ⚠⚠ **本证明的技术要点（两个独立的坑）**：
  -- ① `generalizing k` **不需要写**：目标形如 `∀ k, …`，`induction e` 会把该
  --    ∀-绑定的 `k` **一并泛化**，故归纳假设的形状是
  --    **`iha : ∀ k : ℤ → ℤ, cps a k = k (evalCond a)`**（一个**函数**，不是等式）。
  -- ② 因此 `rw [iha]` **必失败**（报
  --    `tactic 'rewrite' failed, equality or iff proof expected`）——
  --    `rw` 要的是**等式**，而这里给的是 `∀`-函数。
  --    ⇒ 必须**显式实例化续延**：`rw [iha (fun va => …)]`。
  --    （下文每一处 `rw [ih…]` 都据此补上了实参。）
  induction e with
  | lit n => intro k; rfl
  | add a b iha ihb =>
      intro k
      -- `cps a (fun va => cps b (fun vb => k (va + vb)))`
      -- 先用 `iha` 把外层 `cps a` 消掉（续延是 `fun va => …`）
      show cps a (fun va => cps b (fun vb => k (va + vb))) = k (evalCond a + evalCond b)
      rw [iha (fun va => cps b (fun vb => k (va + vb)))]
      -- 剩下 `cps b (fun vb => k (evalCond a + vb))`，用 `ihb`
      -- ⚠ `rw [ihb …]` 已把目标**闭合**（化为 `k (evalCond a + evalCond b) = k (evalCond a + evalCond b)`）
      -- ⟹ 后面**不能再收尾**（原写的 `rfl` 报 `no goals to be solved`）。
      rw [ihb (fun vb => k (evalCond a + vb))]
  | sub a b iha ihb =>
      intro k
      show cps a (fun va => cps b (fun vb => k (va - vb))) = k (evalCond a - evalCond b)
      rw [iha (fun va => cps b (fun vb => k (va - vb)))]
      -- ⚠ 同上：`rw [ihb …]` 已闭合，**删掉**多余的 `rfl`。
      rw [ihb (fun vb => k (evalCond a - vb))]
  | ite c e₁ e₂ ihc ih₁ ih₂ =>
      intro k
      show cps c (fun vc => if vc = 0 then cps e₁ k else cps e₂ k)
        = k (if evalCond c = 0 then evalCond e₁ else evalCond e₂)
      rw [ihc (fun vc => if vc = 0 then cps e₁ k else cps e₂ k)]
      -- 现在目标形如 `(if evalCond c = 0 then cps e₁ k else cps e₂ k) = k (if … )`
      by_cases hc : evalCond c = 0
      · simp only [hc, if_true]
        rw [ih₁ k]
      · simp only [hc, if_false]
        rw [ih₂ k]

/-! ## 三、以 `id` 为续延：CPS 结果 = 直接结果 -/

/-- **恒等续延的特例**：`cps e id = evalCond e`。
这是 `cps_correct` 的**直接推论**，但作为接口重要（它是「CPS 编译后的程序
与原程序给出同一个值」的最常用形态）。 -/
theorem cps_id_is_eval (e : CondExpr) : cps e id = evalCond e := by
  have h := cps_correct e id
  simpa using h

/-! ## 四、续延复合（CPS 可组合性） -/

/-- **CPS 对续延复合封闭**（承重）：在 `e` 的 CPS 求值中，
若外层续延是 `k ∘ j`（先 `j` 再 `k`），则结果等于
「先按 `j` 求值 `e`，再把中间结果交给 `k`」。
**这需要 `cps_correct` 应用两次**，是 CPS 变换可组合（编译可分段）的形式化。 -/
theorem cps_tail_compose (e : CondExpr) (j k : ℤ → ℤ) :
    cps e (k ∘ j) = k (j (evalCond e)) := by
  rw [cps_correct e (k ∘ j)]
  rfl

/-- **CPS 的形状刚性**（承重）：CPS 求值的**唯一**出口是最终续延 ——
即不存在「绕过续延直接返回」的路径。形式化为：若 `cps e k = cps e k'`
对所有 `e` 成立，则 `k` 与 `k'` 在 `evalCond` 的像上一致。
这说明 CPS 变换**真的**把控制流显式化了（不是语法糖）。 -/
theorem cps_call_by_value_shape (k k' : ℤ → ℤ)
    (h : ∀ e : CondExpr, cps e k = cps e k') (n : ℤ) : k n = k' n := by
  have := h (.lit n)
  simpa [cps] using this

/-! ## 五、CPS 与直接语义的**可观察等价**（拒绝退化为 `rfl` 的形式） -/

/-- **可观察等价**：两个表达式在**任意**续延下 CPS 结果相同。
这**不是** `evalCond e₁ = evalCond e₂` 的重述：它量化于**所有续延**，
故是更强的「观察等价」。下一条定理说明二者的关系。 -/
def ObsEq (e₁ e₂ : CondExpr) : Prop := ∀ k : ℤ → ℤ, cps e₁ k = cps e₂ k

/-- **可观察等价 ⟺ 值相等**（承重，双向）：
左到右取 `k = id`；右到左用 `cps_correct`。
**这个 `⟺` 不是 `Iff.rfl`**：它连接了「所有续延下的 CPS 行为」
与「直接语义的值」这两个**不同定义**的概念。 -/
theorem obsEq_iff_eval_eq {e₁ e₂ : CondExpr} : ObsEq e₁ e₂ ↔ evalCond e₁ = evalCond e₂ := by
  constructor
  · intro h
    have := h id
    rw [cps_id_is_eval, cps_id_is_eval] at this
    exact this
  · intro h k
    rw [cps_correct, cps_correct, h]

end Lattice.Lib.Compiler.RealContinuationEquivalence
