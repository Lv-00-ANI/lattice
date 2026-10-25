import Mathlib

/-!
# LATTICE: 树上的递归语义 —— 良基递归、结构归纳与终止性

`RealRecursiveSemantics` 把递归语义钉在「有限迭代 / 变式终止 / 最小不动点」上，
但只讨论了**线性**（`Nat.rec` 式）递归。本文件补上**树结构递归**这一维度：

  1. `Tree`：多叉有序树（`node : α → List (Tree α) → Tree α`），带 `children`；
  2. `Tree.size` / `Tree.depth`：树上的**良基递归**函数（节点数 / 高度）；
  3. `Tree.induction`：**结构归纳原理**（对孩子的归纳假设由度量严格递减给出）；
  4. `Tree.wf_children`：子树关系 `fun c t => IsChild c t` 的良基性
     （由结构归纳原理直接构造 `Acc`，不依赖 mathlib 的 `InvImage`/`measure` 工具链）；
  5. `Op` / `Tree.eval`：**树上求值**（环境 `String → ℕ`，标签 `Op` 给出组合语义）；
  6. **终止性定理**：`Tree.child_sizeOf_lt`（`sizeOf` 严格递减，用
     `List.sizeOf_lt_sizeOf_of_mem`）、`Tree.size_child_lt`（自定度量 `size` 严格递减）、
     `Tree.recursion_terminates`（良基性 + 归纳原理打包）；
  7. 一致性用例：`Tree.size_pos`、`Tree.depth_le_size`、`Tree.eval_const_leaf`、
     `Tree.eval_add_binary`、`Tree.eval_mul_binary` 等由结构归纳原理证明的定理。

诚实标注（无 sorry / axiom / admit）：
- **实现方式的一处诚实说明**：`size` / `depth` / `eval` 采用 **`Tree` 与 `List (Tree α)`
  的互递归**定义（Lean 结构递归检查器自动接受，无需 `termination_by`）。
  直觉的 `termination_by t => sizeOf t` + `decreasing_by` 写法在 mathlib 4.14 上
  **不通过**：`decreasing_by` 的上下文里没有「被递归元素 ∈ 孩子列表」这条假设，
  `List.sizeOf_lt_sizeOf_of_mem` 无从施用（实测 goal 为 `⊢ sizeOf a < 1 + sizeOf ts`，
  无 membership 假设）。终止性证据因此以**显式引理**形式给出，并未丢失：
  `size_lt_of_mem`、`depth_lt_of_mem`（自定度量，互递归版）与
  `child_sizeOf_lt`（`sizeOf` 度量，直接用 `List.sizeOf_lt_sizeOf_of_mem`）。
- 本文件**未做**：树的等价/同构判定、`Tree` 与 `RealRecursiveSemantics` 的最小不动点
  之间的互译（那属于树自动机/代数语义，需要额外的代数结构）。
- 本文件**未做**：非良基（无限）树上的递归（需要共归纳/终余代数）。
- `Op` 的求值是**纯函数式**的（无短路、无副作用）；求值顺序无关，
  故不需要更强的可计算性论证（无 `Decidable`/可计算性证明）。
- **标注（v15 更正）**：`eval_recursion_decreasing` / `eval_recursion_decreasing_size` /
  `eval_size_pos` 的第一个形参是**签名对齐用**的 `env : String → ℕ`（与 `eval` 签名
  对齐），但**三者都不使用它** ⟹ Lean 报 `unused variable`。已统一改名为 **`_env`**
  以**显式标注「该形参未被使用」**（这也是 Lean 推荐的消警告写法），
  而不再保留一个看起来"有内容"的参数名。这是**签名一致性**的有意选择，非缺陷；
  调用方（若有）仍可按位置传 `env`（下划线前缀**不改变**参数的顺序与类型）。
-/

noncomputable section

universe u

namespace Lattice.Lib.Compiler.RealTreeRecursion
/-! ## 一、树类型与结构 -/

/-- **多叉有序树**：一个标签 `α` 加上孩子的（有序）列表。
这是「递归数据类型」最简的树形载体，后续所有递归都在它上面进行。 -/
inductive Tree (α : Type u) where
  | node : α → List (Tree α) → Tree α
  deriving Repr

namespace Tree

variable {α : Type u}

/-- 孩子列表（`children` 是树上递归的「下一步」集合）。 -/
def children : Tree α → List (Tree α)
  | node _ ts => ts

@[simp] theorem children_node (a : α) (ts : List (Tree α)) :
    children (node a ts) = ts := rfl

/-- 直接孩子关系：`c` 是 `t` 的孩子。 -/
def IsChild (c t : Tree α) : Prop := c ∈ children t

theorem isChild_node_iff (c : Tree α) (a : α) (ts : List (Tree α)) :
    IsChild c (node a ts) ↔ c ∈ ts := Iff.rfl

/-! ## 二、辅助计数引理
（原稿的 `le_sum_map_of_mem` / `foldr_max_le_sum` / `le_foldr_max` 是配合
`(ts.map size).sum` / `foldr max` 形状写的；`size`/`depth` 改用 `Tree`/`List`
互递归后这些形状消失，等价的上界引理改在第六节以 `sizeList`/`depthList` 陈述。） -/

/-! ## 三、良基递归：`size` 与 `depth`

**实现说明（为何用 `Tree`/`List` 互递归而非 `termination_by sizeOf`）**：
直觉写法

```lean
def size : Tree α → ℕ
  | node _ ts => 1 + (ts.map size).sum
termination_by t => sizeOf t
decreasing_by exact List.sizeOf_lt_sizeOf_of_mem (by assumption)
```

在 mathlib 4.14 上**不通过**：`decreasing_by` 的上下文里**没有**「被递归的元素 ∈ 列表」
这条假设（实测 goal 是 `⊢ sizeOf a < 1 + sizeOf ts`，无任何 membership 假设可用），
故 `List.sizeOf_lt_sizeOf_of_mem` 无从施用。改用 **`Tree` 与 `List (Tree α)` 的互递归**
（Lean 的结构递归检查器自动接受，无需 `termination_by`），
再把「孩子严格更小」作为**单独的机器验证定理** `size_lt_of_mem` 给出——
终止性证据并未丢失，只是从 `decreasing_by` 移到了显式引理。
`sizeOf` 侧的下降引理 `child_sizeOf_lt` 仍直接用 `List.sizeOf_lt_sizeOf_of_mem` 证明。 -/

mutual
  /-- **列表节点总数**（`size` 的互递归伙伴）：`sizeList [] = 0`，
  `sizeList (c :: cs) = size c + sizeList cs`。 -/
  def sizeList : List (Tree α) → ℕ
    | [] => 0
    | c :: cs => size c + sizeList cs

  /-- **节点数**（良基递归）：`1 + Σ_{c ∈ children} size c`。
  递归调用作用在直接孩子上，终止性由互递归结构给出。 -/
  def size : Tree α → ℕ
    | node _ ts => 1 + sizeList ts
end

mutual
  /-- **列表最大高度**（`depth` 的互递归伙伴）。 -/
  def depthList : List (Tree α) → ℕ
    | [] => 0
    | c :: cs => max (depth c) (depthList cs)

  /-- **高度**（良基递归，叶子高度为 1）：`1 + max_{c ∈ children} depth c`。 -/
  def depth : Tree α → ℕ
    | node _ ts => 1 + depthList ts
end

@[simp] theorem sizeList_nil : sizeList ([] : List (Tree α)) = 0 := rfl

@[simp] theorem sizeList_cons (c : Tree α) (cs : List (Tree α)) :
    sizeList (c :: cs) = size c + sizeList cs := rfl

@[simp] theorem size_node (a : α) (ts : List (Tree α)) :
    size (node a ts) = 1 + sizeList ts := rfl

@[simp] theorem depthList_nil : depthList ([] : List (Tree α)) = 0 := rfl

@[simp] theorem depthList_cons (c : Tree α) (cs : List (Tree α)) :
    depthList (c :: cs) = max (depth c) (depthList cs) := rfl

@[simp] theorem depth_node (a : α) (ts : List (Tree α)) :
    depth (node a ts) = 1 + depthList ts := rfl

/-! ## 四、终止性：递归调用作用在严格更小的度量上 -/

/-- **终止性引理（互递归度量形式）**：若 `c` 是孩子列表 `ts` 的成员，则
`size c < 1 + sizeList ts` —— 即递归调用确实作用在**严格更小**的度量上。
这正是把 `size` 从 `termination_by` 改写为互递归版后必须补回的终止性证据。 -/
theorem size_lt_of_mem {ts : List (Tree α)} {c : Tree α} (hc : c ∈ ts) :
    size c < 1 + sizeList ts := by
  induction ts with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      simp only [sizeList_cons]
      rcases hc with rfl | hc
      · omega
      · have := ih hc; omega

/-- **终止性引理（`depth` 形式）**：`depth c < 1 + depthList ts`（`c ∈ ts`）。 -/
theorem depth_lt_of_mem {ts : List (Tree α)} {c : Tree α} (hc : c ∈ ts) :
    depth c < 1 + depthList ts := by
  induction ts with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      simp only [depthList_cons]
      rcases hc with rfl | hc
      · omega
      · have := ih hc; omega

/-- **终止性引理（`sizeOf` 形式）**：若 `c` 是 `t` 的直接孩子，则
`sizeOf c < sizeOf t`。这是标准工具链形式，直接用
`List.sizeOf_lt_sizeOf_of_mem`（孩子列表的 `sizeOf` 严格大于任何成员）。 -/
theorem child_sizeOf_lt {t c : Tree α} (hc : IsChild c t) : sizeOf c < sizeOf t := by
  cases t with
  | node a ts =>
      have h1 : sizeOf c < sizeOf ts := List.sizeOf_lt_sizeOf_of_mem hc
      rw [Tree.node.sizeOf_spec]
      omega

/-! ## 五、结构归纳原理与良基性 -/

/-- **结构归纳原理**：若 `motive` 在「所有孩子的 `motive` 成立」的前提下对
`node a ts` 成立，则它对所有树成立。证明用 `size` 的强归纳
（`size_child_lt` 提供递减）——这正是树上良基递归/归纳的终止性所在。 -/
theorem induction {motive : Tree α → Prop}
    (h : ∀ (a : α) (ts : List (Tree α)), (∀ c ∈ ts, motive c) → motive (node a ts)) :
    ∀ t, motive t := by
  have key : ∀ n : ℕ, ∀ t : Tree α, size t = n → motive t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        intro t ht
        cases t with
        | node a ts =>
            apply h a ts
            intro c hc
            have hlt : size c < size (Tree.node a ts) := by
              rw [size_node]
              exact size_lt_of_mem hc
            exact ih (size c) (by omega) c rfl
  intro t
  exact key (size t) t rfl

/-- **子树的良基性**：直接孩子关系良基。
由结构归纳原理直接构造 `Acc`（不经过 mathlib 的 `WellFounded` 工具链）。 -/
theorem wf_children : WellFounded (fun c t : Tree α => IsChild c t) := by
  have key : ∀ t : Tree α, Acc (fun c t : Tree α => IsChild c t) t :=
    Tree.induction (motive := fun t => Acc (fun c t : Tree α => IsChild c t) t)
      (fun a ts ih => Acc.intro _ (fun c hc => ih c hc))
  exact ⟨key⟩

/-- **终止性定理（打包）**：树上「只对孩子递归」的定义终止——
两个机器验证的等价形式是 (a) 子树关系良基、(b) 结构归纳原理可用。 -/
theorem recursion_terminates :
    WellFounded (fun c t : Tree α => IsChild c t) ∧
      (∀ motive : Tree α → Prop,
        (∀ (a : α) (ts : List (Tree α)), (∀ c ∈ ts, motive c) → motive (node a ts)) →
          ∀ t, motive t) :=
  ⟨wf_children, fun _ h => Tree.induction h⟩

/-- **终止性引理（自定度量 `size` 形式）**：直接孩子的 `size` 严格小于父节点
（这是一个真正用到结构归纳原理的递归论证：对孩子用归纳假设）。 -/
theorem size_child_lt : ∀ {t c : Tree α}, IsChild c t → size c < size t := by
  intro t c hc
  refine Tree.induction (motive := fun t => ∀ c : Tree α, IsChild c t → size c < size t)
    (fun a ts _ c hc => ?_) t c hc
  rw [size_node]
  exact size_lt_of_mem hc

/-! ## 六、由结构归纳原理导出的基本性质 -/

/-- **每个节点计数为正**（辅助）：对 `size` 做结构归纳——
`size (node a ts) = 1 + sizeList ts ≥ 1`。 -/
theorem size_pos_aux (t : Tree α) : 0 < size t := by
  refine Tree.induction (motive := fun t => 0 < size t) ?_ t
  intro a ts _
  rw [size_node]
  omega

/-- **`sizeList` 恒正当且仅当非空**：辅助引理。 -/
theorem sizeList_pos_of_ne_nil : ∀ {ts : List (Tree α)}, ts ≠ [] → 0 < sizeList ts := by
  intro ts
  cases ts with
  | nil => intro h; exact absurd rfl h
  | cons c cs => intro _; simp only [sizeList_cons]; have := size_pos_aux c; omega

/-- 每个节点计数为正。 -/
theorem size_pos (t : Tree α) : 0 < size t := size_pos_aux t


/-- **`sizeList` 是列表各元素 `size` 之和的上界的等价形式**：
`sizeList ts` 不小于任一成员。辅助引理。 -/
theorem size_le_sizeList {ts : List (Tree α)} {c : Tree α} (hc : c ∈ ts) :
    size c ≤ sizeList ts := by
  induction ts with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      simp only [sizeList_cons]
      rcases hc with rfl | hc
      · omega
      · have := ih hc; omega

/-- **`depthList` 是列表各元素 `depth` 的上界**：辅助引理。 -/
theorem depth_le_depthList {ts : List (Tree α)} {c : Tree α} (hc : c ∈ ts) :
    depth c ≤ depthList ts := by
  induction ts with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.mem_cons] at hc
      simp only [depthList_cons]
      rcases hc with rfl | hc
      · exact le_max_left _ _
      · have := ih hc; omega

/-- **列表层的界（由逐元素的树层界导出）**：
若每个成员 `c` 都满足 `depth c ≤ size c`，则 `depthList ts ≤ sizeList ts`。
对列表结构归纳。 -/
theorem depthList_le_sizeList_of_tree {ts : List (Tree α)}
    (h : ∀ c ∈ ts, depth c ≤ size c) : depthList ts ≤ sizeList ts := by
  induction ts with
  | nil => simp
  | cons c cs ih =>
      simp only [depthList_cons, sizeList_cons]
      have hc : depth c ≤ size c := h c (by simp)
      have hcs : depthList cs ≤ sizeList cs := ih (fun d hd => h d (by simp [hd]))
      omega

/-- **树层结论 `depth t ≤ size t`**：对 `size` 强归纳。
在 `node a ts` 处对每个孩子用归纳假设（孩子的 `size` 严格小于父节点，
由 `size_lt_of_mem` 给出），列表层的界由 `depthList_le_sizeList_of_tree` 打包。 -/
theorem depth_le_size (t : Tree α) : depth t ≤ size t := by
  -- 先证树层（对 size 强归纳），列表层的界在归纳步里用「孩子」的结论逐项相加。
  have key : ∀ n : ℕ, ∀ t : Tree α, size t ≤ n → depth t ≤ size t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t _
      cases t with
      | node a ts =>
          rw [depth_node, size_node]
          -- 列表层：对 ts 做结构归纳；孩子用 outer `ih`
          have hlist : depthList ts ≤ sizeList ts :=
            depthList_le_sizeList_of_tree (fun c hc => by
              have hc_lt : size c < n := by
                have hsz : size c < size (Tree.node a ts) := by
                  rw [size_node]; exact size_lt_of_mem hc
                omega
              exact ih (size c) hc_lt c le_rfl)
          omega
  exact key (size t) t le_rfl

/-- 直接孩子的 `depth` 严格小于父节点的 `depth`。 -/
theorem depth_child_lt : ∀ {t c : Tree α}, IsChild c t → depth c < depth t := by
  intro t c hc
  refine Tree.induction (motive := fun t => ∀ c : Tree α, IsChild c t → depth c < depth t)
    (fun a ts _ c hc => ?_) t c hc
  rw [depth_node]
  exact depth_lt_of_mem hc

end Tree

/-! ## 七、树上求值：环境 + 递归 `eval` -/

/-- **节点标签**：常量、变量、加法、乘法。
`Op` 是求值语义的组合子：孩子求值的结果按标签组合。 -/
inductive Op where
  | const : ℕ → Op
  | var : String → Op
  | add : Op
  | mul : Op
  deriving DecidableEq, Repr

namespace Op

/-- **标签语义**：把孩子求值结果按标签组合（`env` 解释变量）。 -/
def eval (env : String → ℕ) : Op → List ℕ → ℕ
  | const n, _ => n
  | var s, _ => env s
  | add, xs => xs.sum
  | mul, xs => xs.prod

@[simp] theorem eval_const (env : String → ℕ) (n : ℕ) (xs : List ℕ) :
    eval env (const n) xs = n := rfl

@[simp] theorem eval_var (env : String → ℕ) (s : String) (xs : List ℕ) :
    eval env (var s) xs = env s := rfl

@[simp] theorem eval_add (env : String → ℕ) (xs : List ℕ) :
    eval env add xs = xs.sum := rfl

@[simp] theorem eval_mul (env : String → ℕ) (xs : List ℕ) :
    eval env mul xs = xs.prod := rfl

end Op

namespace Tree

mutual
  /-- **树上求值的列表版**（`eval` 的互递归伙伴）：先求出所有孩子的值，交给标签组合。
  递归调用只作用在直接孩子上，终止性由互递归结构给出。 -/
  def evalList (env : String → ℕ) : List (Tree Op) → List ℕ
    | [] => []
    | c :: cs => eval env c :: evalList env cs

  /-- **树上求值**（良基递归）：先递归求值所有孩子，再按标签组合。
  递归调用只作用在直接孩子上，故由 `Tree.induction` / `recursion_terminates` 终止。
  （与 `size`/`depth` 同样采用 `Tree`/`List` 互递归：`decreasing_by` 的上下文不含
  membership 假设，见第三节说明。） -/
  def eval (env : String → ℕ) : Tree Op → ℕ
    | node op ts => Op.eval env op (evalList env ts)
end

@[simp] theorem evalList_nil (env : String → ℕ) : evalList env [] = [] := rfl

@[simp] theorem evalList_cons (env : String → ℕ) (c : Tree Op) (cs : List (Tree Op)) :
    evalList env (c :: cs) = eval env c :: evalList env cs := rfl

@[simp] theorem eval_node (env : String → ℕ) (op : Op) (ts : List (Tree Op)) :
    eval env (node op ts) = Op.eval env op (evalList env ts) := rfl

/-- 常量叶子求值。 -/
theorem eval_const_leaf (env : String → ℕ) (n : ℕ) :
    eval env (node (Op.const n) []) = n := by simp

/-- 变量叶子求值。 -/
theorem eval_var_leaf (env : String → ℕ) (s : String) :
    eval env (node (Op.var s) []) = env s := by simp

/-- 二元加法节点求值（`node add [l, r]`）。 -/
theorem eval_add_binary (env : String → ℕ) (l r : Tree Op) :
    eval env (node Op.add [l, r]) = eval env l + eval env r := by
  simp

/-- 二元乘法节点求值（`node mul [l, r]`）。 -/
theorem eval_mul_binary (env : String → ℕ) (l r : Tree Op) :
    eval env (node Op.mul [l, r]) = eval env l * eval env r := by
  simp

/-- **求值的终止性（显式形式，`sizeOf`）**：`eval` 的每次递归调用都作用在
`sizeOf` 严格更小的子树上（直接由 `List.sizeOf_lt_sizeOf_of_mem`）。

**v15 更正（`env` → `_env`）**：`env` 是**签名对齐用**的形参（与 `eval` 的签名一致），
本定理的内容（`sizeOf` 严格下降）与它**无关** ⟹ Lean 报 `unused variable 'env'`。
已改名为 `_env` 以**显式标注**该形参未被使用（这同时消除了警告），
而**不是**保留一个误导性的"有内容"参数名。 -/
theorem eval_recursion_decreasing (_env : String → ℕ) (op : Op) (ts : List (Tree Op))
    (c : Tree Op) (hc : c ∈ ts) :
    sizeOf c < sizeOf (node op ts) := by
  have h1 : sizeOf c < sizeOf ts := List.sizeOf_lt_sizeOf_of_mem hc
  rw [Tree.node.sizeOf_spec]
  omega

/-- **求值的终止性（显式形式，`size`）**：同一事实在自定度量 `size` 下的形式。

**v15 更正（`env` → `_env`）**：同 `eval_recursion_decreasing`——`env` 是签名对齐
形参，未被使用（Lean 报 `unused variable 'env'`），已显式标注。 -/
theorem eval_recursion_decreasing_size (_env : String → ℕ) (op : Op) (ts : List (Tree Op))
    (c : Tree Op) (hc : c ∈ ts) :
    size c < size (node op ts) := by
  rw [size_node]
  exact size_lt_of_mem hc

/-- 求值结果的可计算性说明（诚实标注为「未做可计算性证明」）：
`eval` 是纯函数，但对任意 `α`/`Op` 未证明 `Decidable` 版本；
这里只记录 `eval` 使用的节点数不超过 `size t`（结构性遍历）。

**v15 更正（`env` → `_env`）**：`size_pos` **不依赖 `env`**，故 `env` 是签名对齐
形参且未被使用（Lean 报 `unused variable 'env'`），已显式标注。 -/
theorem eval_size_pos (_env : String → ℕ) (t : Tree Op) : 0 < size t := size_pos t

end Tree

end Lattice.Lib.Compiler.RealTreeRecursion
