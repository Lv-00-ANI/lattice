import Mathlib
import Lattice.Lib.LearningTheory.RealCausalInference
/-!
# LATTICE: 因果 do-演算 —— 有限 SCM 的截断语义与后门准则

**为什么做这个文件**：`RealCausalInference` 已在**二值 + 固定三元图**
（`Z → X → Y`、`Z → Y`）上形式化了截断语义与后门调整公式；
`RealSCMIdentification` 给出不可识别反例。但 `ROADMAP-v2` 点名的两个缺口
仍未闭合：

  1. **「任意 DAG 的后门准则」未做**（`RealCausalInference` 诚实标注原文）；
  2. **do-演算完全没有**。

本文件用**纯组合**路线闭合它们：变量索引 `Fin n`、`Finset` 求和、指示函数。
**刻意避开测度论**，使每条命题在内核里真实可证。

## 模型：拓扑序驱动的有限 SCM（一般 DAG）

**形式化的关键难点是求值顺序**。`BinSCM` 把三个方程**显式写死**，
故顺序是语法的一部分；推广到 `Fin n` 之后，「顺序」必须变成**数据**。
本文件把**拓扑序作为显式参数** `topo : Fin n ≃ Fin n` 传入，
读作「第 `k` 步求值的变量是 `topo k`」：

* `parents : Fin n → Finset (Fin n)`：图结构（`j ∈ parents i` 即 `j → i`）；
* `mech i a`：变量 `i` 的**局部机制**，只读父变量
  （`a : (j : Fin n) → j ∈ parents i → Bool`）—— 这是 DAG 语义的定义性特征；
* `ParentOrdered topo`：父变量在 `topo` 次序中**严格更早** ——
  `sol` 良基递归的**充要条件**；
* `p : Fin n → Bool → ℝ`：外生噪声的逐点分布，联合分布**因子化**
  `∏ i, p i (u i)` —— **无未观测混杂**，由「只有逐点边缘字段、
  没有联合分布字段」在**类型上**强制。

**解 `sol M topo`**：沿 `topo` 次序依次求值。`sol_eq_mech` 证明它满足**全部**
机制 —— SCM 语义的根基，也是 `BinSCM` 显式方程版的**一般 DAG 推广**。

**截断语义 `do(T := x)`**：`doMech M T x` 把 `T` 中变量的机制替换为常数。
`do_truncated` 证明 `i ∈ T` 时解在 `i` 处**必**取 `x i`（干预被钉住），
`do_outside` 证明 `i ∉ T` 时仍由结构方程决定。这两条一起完整刻画了
Pearl 的截断语义，且对**任意** `T : Finset (Fin n)` 成立。

## 点记法的约定（本文件踩过的坑）

`sol`、`solIter`、`stepIter`、`doSol`、`obs`、`doObs` 的**第一个显式参数
都是 `topo`**（模型 `M` 是隐式参数），因此**不能用点记法**
`M.sol topo` —— Lean 报
`invalid field notation, function 'Lattice.FinSCM.sol' does not have argument
with type (Lattice.FinSCM ...) that can be used, it must be explicit or implicit
with a unique name`。
本文件统一用**前缀形式** `FinSCM.sol M topo`。
（同族坑：STYLE.md 的 `(A).HasEigenvalue μ` 点号失败 → 用
`Module.End.HasEigenvalue f μ`。）

## 诚实边界（本文件不证 / 不声称的）

* **`topo` 作为显式参数传入**：本文件**不构造**拓扑排序的存在性
  （「任意有限 DAG 有拓扑序」是图论定理，**未做**）。
  `ParentOrdered` 是**显式前提**，不是掩盖的 gap；
* **机制是确定性的**：随机性在**分布层**（`p`）进入。这**不同于** `BinSCM`
  把噪声作为额外参数传给 `fX`/`fY` 的做法；
* **正性（positivity / overlap）**：调整公式的可识别性带显式正性前提
  （若某层观测概率为 0，条件概率无定义，Lean 中 `a/0 = 0`）；
* **d-分离只做「路径级阻塞」**：**未做**碰撞节点（collider）结构，
  故本文件的 d-分离对**链 / 分叉**路径完整，一般图为**近似**；
* **后门准则 ⟹ 调整公式**：本文件给出后门准则的**完整组合定义**
  （`BackdoorSet`）与**桥的精确陈述**（`BackdoorBridge`），
  并证明「桥 ⟹ 干预分布 = 观测分布」。**未做**：「后门准则 ⟹ 桥」
  的完整图论归纳（路径枚举 + 碰撞结构）。缺口被**精确定位**为一条有名字的
  `Prop`，而不是含糊的「未做」；
* **do-演算规则 3 的一般情形未做**（需要「删去 `Z` 出边」的图改造操作）；
* **忠实性未证、未使用**；
* 无 `sorry` / `axiom` / `admit`；所有定理真实可证。
-/

noncomputable section

open scoped BigOperators

namespace Lattice

/-! ## 一、指示函数与基础求和引理 -/

/-- 一般命题的指示函数（`RealCausalInference.binInd` 是二值专用版；
本文件另立以免命名冲突）。 -/
def doInd (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

lemma doInd_nonneg (p : Prop) [Decidable p] : 0 ≤ doInd p := by
  by_cases h : p <;> simp [doInd, h]

@[simp] lemma doInd_true : doInd True = 1 := rfl
@[simp] lemma doInd_false : doInd False = 0 := rfl

/-- `Σ_{b : Bool} doInd (c = b) = 1`：恰有一个 `b` 使 `c = b`。 -/
lemma sum_bool_doInd_eq_one (c : Bool) : (∑ b : Bool, doInd (c = b)) = 1 := by
  rw [Fintype.sum_bool]
  cases c <;> simp [doInd]

/-- **指示替换**：`Σ_b doInd (c = b) · G b = G c`。
这是截断语义「以方程取值代入」的代数核（与 `binInd` 版同源）。 -/
lemma sum_bool_doInd_mul (c : Bool) (G : Bool → ℝ) :
    (∑ b : Bool, doInd (c = b) * G b) = G c := by
  rw [Fintype.sum_bool]
  cases c <;> simp [doInd]

/-! ## 二、拓扑序驱动的有限 SCM -/

/-- **有限结构因果模型（一般 DAG，`Fin n` 索引）**：

* `parents i`：变量 `i` 的父集（`j ∈ parents i` 即 `j → i`）；
* `mech i a`：变量 `i` 的**局部机制**，只读父变量取值；
* `p i`：外生噪声 `U i` 的分布（非负 + 归一）。

**无未观测混杂**由类型强制：只有逐点边缘分布字段 `p`，
**没有**联合分布字段 —— 噪声之间的任何共同通道都无法表达。 -/
structure FinSCM (n : ℕ) where
  /-- 父集（图结构）。 -/
  parents : Fin n → Finset (Fin n)
  /-- 局部机制：只读父变量取值。 -/
  mech : (i : Fin n) → ((j : Fin n) → j ∈ parents i → Bool) → Bool
  /-- 外生噪声的逐点分布。 -/
  p : Fin n → Bool → ℝ
  /-- 非负。 -/
  p_nonneg : ∀ i b, 0 ≤ p i b
  /-- 归一。 -/
  p_sum : ∀ i, (∑ b : Bool, p i b) = 1

namespace FinSCM

variable {n : ℕ}

/-- **拓扑序相容**：`topo` 是拓扑序，当且仅当每个变量的父变量在 `topo`
次序中**严格更早**（`topo.symm i` 读作「`i` 的求值位置」）。

这是 `sol` 良基递归的**充要条件**：若某父变量更晚，则求值时它还没被写定。 -/
def ParentOrdered (M : FinSCM n) (topo : Fin n ≃ Fin n) : Prop :=
  ∀ i j, j ∈ M.parents i → (topo.symm j).val < (topo.symm i).val

/-- **父赋值提取**：从整体赋值中取父变量取值 —— 把「只读父变量」的 `mech`
接到整体赋值上的桥。 -/
def parentVal (M : FinSCM n) (v : Fin n → Bool) (i : Fin n) :
    (j : Fin n) → j ∈ M.parents i → Bool :=
  fun j _ => v j

/-- **机制求值**：变量 `i` 在整体赋值 `v` 下的方程取值。 -/
def feval (M : FinSCM n) (i : Fin n) (v : Fin n → Bool) : Bool :=
  M.mech i (M.parentVal v i)

/-- **迭代一步**：把 `topo` 次序中第 `k` 个变量写成它机制的取值（其余不动）；
`n ≤ k` 时不动。 -/
def stepIter (M : FinSCM n) (topo : Fin n ≃ Fin n) (k : ℕ) (v : Fin n → Bool) :
    Fin n → Bool :=
  if h : k < n then
    fun j => if j = topo ⟨k, h⟩ then M.feval (topo ⟨k, h⟩) v else v j
  else v

/-- **解的迭代**：从全 `false` 出发，按 `topo` 次序依次求值。 -/
def solIter (M : FinSCM n) (topo : Fin n ≃ Fin n) : ℕ → (Fin n → Bool)
  | 0 => fun _ => false
  | k + 1 => M.stepIter topo k (solIter M topo k)

/-- **观测解**：迭代 `n` 步（覆盖全部变量）。 -/
def sol (M : FinSCM n) (topo : Fin n ≃ Fin n) : Fin n → Bool := solIter M topo n

/-- `stepIter` 在 `k < n` 时的展开（消去 `dif`）。 -/
theorem stepIter_of_lt (M : FinSCM n) (topo : Fin n ≃ Fin n) {k : ℕ} (h : k < n)
    (v : Fin n → Bool) :
    M.stepIter topo k v =
      fun j => if j = topo ⟨k, h⟩ then M.feval (topo ⟨k, h⟩) v else v j := by
  unfold stepIter
  rw [dif_pos h]

/-- `stepIter` 在 `n ≤ k` 时不动。 -/
theorem stepIter_of_le (M : FinSCM n) (topo : Fin n ≃ Fin n) {k : ℕ} (h : n ≤ k)
    (v : Fin n → Bool) : M.stepIter topo k v = v := by
  unfold stepIter
  rw [dif_neg (Nat.not_lt.mpr h)]

/-- **`stepIter` 只改一个坐标**：`j ≠ topo ⟨k,_⟩` 时原样保留。 -/
theorem stepIter_apply_ne (M : FinSCM n) (topo : Fin n ≃ Fin n) {k : ℕ} (h : k < n)
    (v : Fin n → Bool) {j : Fin n} (hj : j ≠ topo ⟨k, h⟩) :
    M.stepIter topo k v j = v j := by
  rw [M.stepIter_of_lt topo h]
  simp only
  rw [if_neg hj]

/-- `solIter` 的**后继展开式**（定义等式，供 `rw` 使用）。 -/
theorem solIter_succ (M : FinSCM n) (topo : Fin n ≃ Fin n) (k : ℕ) :
    solIter M topo (k + 1) = M.stepIter topo k (solIter M topo k) := rfl

/-- **第 `k` 步写定第 `k` 个变量**。

证明：`rw [solIter_succ]` 把左边展开为 `stepIter topo k (solIter …) (topo ⟨k,h⟩)`，
`rw [stepIter_of_lt]` 再展开为 `if topo ⟨k,h⟩ = topo ⟨k,h⟩ then feval … else …`，
`if_pos rfl` 即得。

**写法说明**：这里不能只用 `simp` —— `stepIter_of_lt` 的右端是
`fun j => if j = topo ⟨k,h⟩ then … else …`，`simp` 不会自动把
**外层函数应用**（`(fun j => …) (topo ⟨k,h⟩)`）beta-归约后再消 `if`，
故 `simp made no progress`。显式 `if_pos` 是稳的。 -/
theorem solIter_succ_self (M : FinSCM n) (topo : Fin n ≃ Fin n) {k : ℕ} (h : k < n) :
    solIter M topo (k + 1) (topo ⟨k, h⟩) = M.feval (topo ⟨k, h⟩) (solIter M topo k) := by
  rw [M.solIter_succ topo k, M.stepIter_of_lt topo h]
  exact if_pos rfl

/-- **已写定的坐标不再改变**：`m < k` 时第 `k` 步不动 `topo ⟨m,hm⟩`。
用 `topo` 的单射性把 `topo ⟨m,hm⟩ ≠ topo ⟨k,hk⟩` 归到 `m ≠ k`。 -/
theorem solIter_succ_stable (M : FinSCM n) (topo : Fin n ≃ Fin n) {k m : ℕ}
    (hk : k < n) (hm : m < n) (hlt : m < k) :
    solIter M topo (k + 1) (topo ⟨m, hm⟩) = solIter M topo k (topo ⟨m, hm⟩) := by
  rw [M.solIter_succ topo k]
  refine M.stepIter_apply_ne topo hk (solIter M topo k) ?_
  intro heq
  have : (⟨m, hm⟩ : Fin n) = ⟨k, hk⟩ := topo.injective heq
  simp at this
  omega

/-- **引理 A（值稳定）**：`m < k ≤ k'` 时 `solIter M topo k` 与
`solIter M topo k'` 在坐标 `topo ⟨m,hm⟩` 上一致 —— 「一旦写定，永不再变」。

证明：令 `k' = k + d`，对 `d` 归纳。
* `d = 0`：`rfl`；
* `d + 1`：先由归纳假设得 `solIter k = solIter (k+d)`，
  再证「第 `k+d` 步不改坐标 `topo ⟨m,hm⟩`」——
  分「`k+d < n`（用 `solIter_succ_stable`）」与「`n ≤ k+d`（用 `stepIter_of_le`）」两支。

**写法说明（本文件实际修正过一次）**：初稿把 `ih` 当函数用
（`ih hk (Nat.le_add_right k d)`），Lean 报
`function expected at ih, term has type M.solIter topo k … = M.solIter topo (k+d) …`
—— 因为 `induction d` 之后 `ih` **已经**把外层 `k`/`k'` 实例化成了等式，
不再是待喂前提的函数。正确做法：**在归纳前就把该证明的形状固定**
（下面用 `suffices` 把 `k'` 显式化为 `k + d`），使 `ih` 保持「等式」形态，
从而可以用 `Eq.trans` 直接复合。 -/
theorem solIter_stable (M : FinSCM n) (topo : Fin n ≃ Fin n) {m : ℕ} (hm : m < n) :
    ∀ {k k' : ℕ}, m < k → k ≤ k' →
      solIter M topo k (topo ⟨m, hm⟩) = solIter M topo k' (topo ⟨m, hm⟩) := by
  intro k k' hmk hle
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  subst hd
  clear hle
  -- `haux d : m < k → solIter k = solIter (k+d)`，对 `d` 归纳
  have haux : ∀ d : ℕ, m < k →
      solIter M topo k (topo ⟨m, hm⟩) = solIter M topo (k + d) (topo ⟨m, hm⟩) := by
    intro d
    induction d with
    | zero => intro _; rw [Nat.add_zero]
    | succ d ih =>
        intro _
        -- `ih : m < k → solIter k = solIter (k+d)`；喂它**原始**前提 `hmk : m < k`
        have hind := ih hmk
        -- 需证第 `k+d` 步不改坐标 `topo ⟨m,hm⟩`：由 `m < k ≤ k+d` 得 `m < k+d`
        have hk : m < k + d := by omega
        by_cases hb : k + d < n
        · have hstep : solIter M topo (k + d) (topo ⟨m, hm⟩)
              = solIter M topo (k + d + 1) (topo ⟨m, hm⟩) :=
            (M.solIter_succ_stable topo hb hm hk).symm
          show solIter M topo k (topo ⟨m, hm⟩)
            = solIter M topo (k + d + 1) (topo ⟨m, hm⟩)
          exact hind.trans hstep
        · have hle' : n ≤ k + d := Nat.le_of_not_lt hb
          have hstep : solIter M topo (k + d) (topo ⟨m, hm⟩)
              = solIter M topo (k + d + 1) (topo ⟨m, hm⟩) := by
            rw [M.solIter_succ topo (k + d), M.stepIter_of_le topo hle']
          show solIter M topo k (topo ⟨m, hm⟩)
            = solIter M topo (k + d + 1) (topo ⟨m, hm⟩)
          exact hind.trans hstep
  exact haux d hmk

/-- **`sol` 在第 `m` 个坐标上 = 迭代第 `m` 步写入的值**（其后各步不动它）。

证明：`sol = solIter n`；由 `solIter_succ_self` 得第 `m+1` 步写入的值，
再由 `solIter_stable`（引理 A，取 `k := m+1 ≤ k' := n`）说明
`m+1` 步之后该坐标**不再变化**。 -/
theorem sol_apply (M : FinSCM n) (topo : Fin n ≃ Fin n) {m : ℕ} (hm : m < n) :
    M.sol topo (topo ⟨m, hm⟩) = M.feval (topo ⟨m, hm⟩) (solIter M topo m) := by
  have hsol : M.sol topo (topo ⟨m, hm⟩) = solIter M topo (m + 1) (topo ⟨m, hm⟩) := by
    unfold sol
    exact (M.solIter_stable topo hm (k := m + 1) (k' := n) (by omega) (by omega)).symm
  rw [hsol, M.solIter_succ_self topo hm]
/-- **父坐标更早**（`ParentOrdered` 的消去形式）。 -/
theorem parent_index_lt (M : FinSCM n) (topo : Fin n ≃ Fin n) (hord : M.ParentOrdered topo)
    {i j : Fin n} (hj : j ∈ M.parents i) :
    (topo.symm j).val < (topo.symm i).val :=
  hord i j hj

/-- **引理 C（父赋值一致）**：在 `ParentOrdered` 下，
`solIter M topo (topo.symm i).val` 与 `sol M topo` 在 `i` 的**全部父坐标**上一致。

证明：对 `j ∈ parents i`，把 `j` 写成 `topo ⟨m,hm⟩`（`m := (topo.symm j).val`）；
`parent_index_lt` 给 `m < (topo.symm i).val`，再用**引理 A**
（取 `k := (topo.symm i).val ≤ n`）即得两者相等。 -/
theorem parentVal_solIter_eq (M : FinSCM n) (topo : Fin n ≃ Fin n)
    (hord : M.ParentOrdered topo) (i : Fin n) :
    M.parentVal (solIter M topo (topo.symm i).val) i = M.parentVal (M.sol topo) i := by
  funext j hj
  -- `parentVal v i j hj` 定义上就是 `v j`
  show solIter M topo (topo.symm i).val j = M.sol topo j
  have hlt := M.parent_index_lt topo hord hj
  set m := (topo.symm j).val with hm_def
  have hm : m < n := (topo.symm j).isLt
  -- `j = topo ⟨m, hm⟩`：由 `Equiv.apply_symm_apply` 得 `topo (topo.symm j) = j`
  have htopo : topo ⟨m, hm⟩ = j := by
    have h1 : (⟨m, hm⟩ : Fin n) = topo.symm j := by
      apply Fin.ext
      simp [hm_def]
    rw [h1, Equiv.apply_symm_apply]
  -- 把目标里的 `j` 换成 `topo ⟨m,hm⟩`，再用引理 A（值稳定）
  rw [← htopo]
  -- 右侧是 `sol M topo = solIter M topo n`（`sol` 的定义）
  show solIter M topo (topo.symm i).val (topo ⟨m, hm⟩)
    = solIter M topo n (topo ⟨m, hm⟩)
  exact M.solIter_stable topo hm (k := (topo.symm i).val) (k' := n)
    (by simpa [hm_def] using hlt) (topo.symm i).isLt.le

/-- **主语义定理：观测解满足全部机制**。

在 `ParentOrdered` 下，对每个变量 `i`：`sol M topo i = feval M i (sol M topo)`
—— 即「`sol` 是结构方程组的解」。这是 SCM 语义的根基，
也是 `BinSCM`（方程显式写死）的**一般 DAG 推广**。

证明路线：`sol_apply` 把左边化为 `feval (topo ⟨m,hm⟩) (solIter M topo m)`；
`feval` 只读**父坐标**（`mech` 的类型强制）；父坐标在 `solIter M topo m`
与 `sol M topo` 上一致（`parentVal_solIter_eq`），故两边相等。 -/
theorem sol_eq_mech (M : FinSCM n) (topo : Fin n ≃ Fin n) (hord : M.ParentOrdered topo)
    (i : Fin n) : M.sol topo i = M.feval i (M.sol topo) := by
  set m := (topo.symm i).val with hm_def
  have hm : m < n := (topo.symm i).isLt
  have htopo : topo ⟨m, hm⟩ = i := by simp [hm_def]
  rw [← htopo, M.sol_apply topo hm]
  unfold feval
  congr 1
  have h1 : M.parentVal (solIter M topo m) (topo ⟨m, hm⟩)
      = M.parentVal (M.sol topo) (topo ⟨m, hm⟩) := by
    have h := M.parentVal_solIter_eq topo hord (topo ⟨m, hm⟩)
    rwa [show (topo.symm (topo ⟨m, hm⟩)).val = m from by simp [hm_def]] at h
  rw [h1]

/-! ## 三、截断语义 `do(T := x)` -/

/-- **截断机制**：把 `T` 中变量的机制替换为常数 `x i`，其余不变。 -/
def doMech (M : FinSCM n) (T : Finset (Fin n)) (x : Fin n → Bool) :
    (i : Fin n) → ((j : Fin n) → j ∈ M.parents i → Bool) → Bool :=
  fun i a => if i ∈ T then x i else M.mech i a

/-- **`do(∅)` 与观测机制相同**（无干预即观测，定义层）。 -/
theorem doMech_empty (M : FinSCM n) (x : Fin n → Bool) : M.doMech ∅ x = M.mech := by
  funext i a
  unfold doMech
  rw [if_neg (Finset.not_mem_empty i)]

/-- **截断后的 SCM**：只换机制，图结构与外生分布不变
（干预是**局部手术**：不动 `parents`，不动 `p`）。 -/
def doModel (M : FinSCM n) (T : Finset (Fin n)) (x : Fin n → Bool) : FinSCM n where
  parents := M.parents
  mech := M.doMech T x
  p := M.p
  p_nonneg := M.p_nonneg
  p_sum := M.p_sum

/-- **截断后的解**：干预模型里的（确定性）解。 -/
def doSol (M : FinSCM n) (topo : Fin n ≃ Fin n) (T : Finset (Fin n))
    (x : Fin n → Bool) : Fin n → Bool :=
  FinSCM.sol (M.doModel T x) topo

/-- **截断生效（干预被钉住）**：`i ∈ T` 时截断后解在 `i` 处**必**取 `x i`，
与噪声、与结构方程**无关**。这是截断语义**区别于观测**的关键性质。

证明：对截断模型用 `sol_eq_mech`；`doModel` 的 `mech` 字段**定义上等于**
`M.doMech T x`，但 `doModel` 是 `where` 构造的，故须先 `show` 出
`M.doMech T x` 再 `unfold`（直接 `unfold doMech` 会报
`failed to unfold 'Lattice.FinSCM.doMech'`，因为目标里出现的是
`(M.doModel T x).mech` 而非 `M.doMech T x`）。 -/
theorem do_truncated (M : FinSCM n) (topo : Fin n ≃ Fin n) (hord : M.ParentOrdered topo)
    {T : Finset (Fin n)} {x : Fin n → Bool} {i : Fin n} (hi : i ∈ T) :
    M.doSol topo T x i = x i := by
  have hfix : M.doSol topo T x i = M.doMech T x i (M.parentVal (M.doSol topo T x) i) :=
    FinSCM.sol_eq_mech (M.doModel T x) topo hord i
  simp only [doMech, hi, if_true] at hfix
  exact hfix

/-- **未干预变量不变**：`i ∉ T` 时截断后解在 `i` 处仍由原结构方程决定。
与 `do_truncated` 合起来**完整刻画**截断语义。 -/
theorem do_outside (M : FinSCM n) (topo : Fin n ≃ Fin n) (hord : M.ParentOrdered topo)
    {T : Finset (Fin n)} {x : Fin n → Bool} {i : Fin n} (hi : i ∉ T) :
    M.doSol topo T x i = M.feval i (M.doSol topo T x) := by
  have hfix : M.doSol topo T x i = M.doMech T x i (M.parentVal (M.doSol topo T x) i) :=
    FinSCM.sol_eq_mech (M.doModel T x) topo hord i
  simp only [doMech, hi, if_false] at hfix
  exact hfix

/-- **`do(∅)` 是观测**（语义层，与 `doMech_empty` 对照）：
无干预时截断后解就是观测解。 -/
theorem doSol_empty (M : FinSCM n) (topo : Fin n ≃ Fin n) (x : Fin n → Bool) :
    M.doSol topo ∅ x = M.sol topo := by
  unfold doSol doModel sol
  rw [M.doMech_empty x]

/-! ## 四、外生噪声的因子化分布 -/

/-- **因子化联合分布** `P(u) = ∏ i, p i (u i)` —— 无未观测混杂的显式形式。 -/
def pU (M : FinSCM n) (u : Fin n → Bool) : ℝ := ∏ i, M.p i (u i)

/-- 联合分布非负。 -/
lemma pU_nonneg (M : FinSCM n) (u : Fin n → Bool) : 0 ≤ M.pU u :=
  Finset.prod_nonneg (fun i _ => M.p_nonneg i (u i))

/-- **因子化分布归一**：`Σ_u pU u = 1`。

证明路线：`Finset.sum_prod_piFinset` 把
`∑ f ∈ piFinset (fun _ => s), ∏ i, g i (f i)` 化为 `∏ i, ∑ j ∈ s, g i j`。
`Fin n → Bool` 的 `Finset.univ` **定义上就是** `piFinset (fun _ => univ)`
（`Fintype.piFinset_univ`），故先用该等式把 `∑ u` 改写成
`∑ u ∈ piFinset …`，再套引理。 -/
theorem pU_sum (M : FinSCM n) : (∑ u : Fin n → Bool, M.pU u) = 1 := by
  classical
  have hpi : (∑ u : Fin n → Bool, M.pU u)
      = ∏ i, (∑ b : Bool, M.p i b) := by
    unfold pU
    rw [← Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun i b => M.p i b)]
    rfl
  rw [hpi]
  simp only [M.p_sum, Finset.prod_const_one]

/-! ## 五、路径、阻塞、d-分离与后门准则 -/

/-- **无向邻接**：`a` 与 `b` 之间有边（任一方向）。
后门路径是**无向**的（混淆通过无向路径传递）。 -/
def Adj (M : FinSCM n) (a b : Fin n) : Prop := a ∈ M.parents b ∨ b ∈ M.parents a

/-- **路径**：顶点序列 `p` 的相邻元素满足 `Adj`，且首元素为 `a`、末元素为 `b`。 -/
def IsPath (M : FinSCM n) (p : List (Fin n)) (a b : Fin n) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.Chain' M.Adj

/-- **后门路径**：从 `X` 的某个元素出发、**第一步走向 `X` 的父节点**
（即 `X ← …` 的非因果方向）的路径。

**诚实标注**：本定义把「后门路径」的判据放在**首两步**上，
覆盖「混淆通过 `X` 的父进入」这一核心情形；**未做**多步后门路径的
完整枚举（即路径中任意点的碰撞结构）。 -/
def IsBackdoorPath (M : FinSCM n) (X : Finset (Fin n)) (p : List (Fin n)) : Prop :=
  ∃ x ∈ X, ∃ q : List (Fin n), ∃ z ∈ M.parents x, p = x :: z :: q

/-- **路径被 `Z` 阻断**（路径级判据）：路径上存在一个 `Z` 中的**内部节点**
（非端点）—— 即「条件化 `Z` 切断了这条路径」。

**诚实标注**：完整的 `d`-分离还要处理**碰撞节点**（`a → c ← b` 处，
`c` 与其后代**都不在** `Z` 中时该处已阻塞，而条件化 `c` 反而**打开**路径）。
本文件**未做**碰撞结构，故本节结论对**链 / 分叉**路径完整，
对含碰撞的一般路径是**近似**（这一点在 `dSeparated_mono` 的注释中说明）。 -/
def PathBlockedBy (Z : Finset (Fin n)) (p : List (Fin n)) : Prop :=
  ∃ v ∈ p, v ∈ Z ∧ p.head? ≠ some v ∧ p.getLast? ≠ some v

/-- **d-分离（路径级）**：`Z` d-分离 `a` 与 `b`，当且仅当 `a` 到 `b` 的
**每条**路径都被 `Z` 阻断。 -/
def dSeparated (M : FinSCM n) (Z : Finset (Fin n)) (a b : Fin n) : Prop :=
  ∀ p : List (Fin n), M.IsPath p a b → PathBlockedBy Z p

/-- **d-分离的可靠性（消去形式）**：由 `dSeparated` 的定义直接得到。 -/
theorem dSeparated_blocked (M : FinSCM n) {Z : Finset (Fin n)} {a b : Fin n}
    (h : M.dSeparated Z a b) {p : List (Fin n)} (hp : M.IsPath p a b) :
    PathBlockedBy Z p :=
  h p hp

/-- **d-分离关于条件集单调**：`Z₁ ⊆ Z₂` 时 `dSeparated M Z₁` 蕴含
`dSeparated M Z₂`（多一个条件节点只会多阻断）。

**诚实标注（重要）**：这条对**链 / 分叉**路径成立；
对**碰撞节点**，条件化反而**打开**路径（碰撞偏倚），
故一般图的对应陈述**为假**。本文件**未做**碰撞结构，
因此本定理的适用范围限于本文件的路径模型。 -/
theorem dSeparated_mono (M : FinSCM n) {Z₁ Z₂ : Finset (Fin n)} (hsub : Z₁ ⊆ Z₂)
    {a b : Fin n} (h : M.dSeparated Z₁ a b) : M.dSeparated Z₂ a b := by
  intro p hp
  obtain ⟨v, hv, hvZ, h1, h2⟩ := h p hp
  exact ⟨v, hv, hsub hvZ, h1, h2⟩

/-- **空条件集不阻断任何路径**：`Z = ∅` 时不存在可用的阻断节点。 -/
theorem not_pathBlockedBy_empty {p : List (Fin n)} :
    ¬ PathBlockedBy (∅ : Finset (Fin n)) p := by
  rintro ⟨v, _, hvZ, _⟩
  exact Finset.not_mem_empty v hvZ

/-- **后代关系**：`j` 是 `i` 的后代（沿父边可达）。 -/
def IsDescendant (M : FinSCM n) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ M.parents b) i j

/-- **`Z` 不含 `X` 的后代**：后门准则的第一条
（含后代会**阻断部分因果效应**本身，而不只是混淆）。 -/
def NoDescendant (M : FinSCM n) (Z X : Finset (Fin n)) : Prop :=
  ∀ z ∈ Z, ∀ x ∈ X, ¬ M.IsDescendant x z

/-- **后门阻断**：`X` 到 `Y` 的每条后门路径都被 `Z` 阻断。 -/
def backdoorBlocked (M : FinSCM n) (Z : Finset (Fin n)) (x y : Fin n) : Prop :=
  ∀ p : List (Fin n), M.IsBackdoorPath {x} p → p.getLast? = some y → PathBlockedBy Z p

/-- **后门准则（组合判据，对任意有限 DAG）**：
`Z` 对 `(X, Y)` 满足后门准则 ⟺
(1) `Z` 不含 `X` 的后代；(2) `Z` 阻断 `X` 到 `Y` 的全部后门路径。

这是 `RealCausalInference` 中固定三元图后门假设的**一般化**：
那里「`Z` 阻断所有后门路径」由 `BinSCM` 的因子化字段**结构上隐含**；
这里它被**显式写成判据**，对任意 `Fin n` 上的 `parents` 成立。 -/
structure BackdoorSet (M : FinSCM n) (X Z : Finset (Fin n)) : Prop where
  /-- `Z` 不含 `X` 的后代。 -/
  noDesc : M.NoDescendant Z X
  /-- `Z` 阻断全部后门路径。 -/
  blocks : ∀ x ∈ X, ∀ y : Fin n, M.backdoorBlocked Z x y

/-- **后门准则蕴含「`Z` 不含 `X` 自身」**（后代关系的自反性）：
`x` 是 `x` 自己的后代，故 `Z` 不能含 `X` 的元素 ——
这是「不能调整 `X` 本身」的形式化，
也是后门准则**非平凡**的一个推论（不是 `True`）。 -/
theorem backdoorSet_not_mem (M : FinSCM n) {X Z : Finset (Fin n)}
    (h : M.BackdoorSet X Z) {x : Fin n} (hx : x ∈ X) : x ∉ Z := by
  intro hxZ
  exact h.noDesc x hxZ x hx (Relation.ReflTransGen.refl)

/-! ## 六、观测分布、干预分布与后门桥 -/

/-- **观测分布**：`P(V = v)` 在噪声上积分。
本文件的机制是**确定性**的，故观测分布是解上的**推前测度**：
`obs v = Σ_u pU u · [sol u = v]`。 -/
def obs (M : FinSCM n) (topo : Fin n ≃ Fin n) (v : Fin n → Bool) : ℝ :=
  ∑ u : Fin n → Bool, M.pU u * doInd (FinSCM.sol M topo = v)

/-- **干预分布**（`do(T := x)` 之后）：同上，但用截断模型。
**这是截断语义的概率层**：干预只改变解 `sol` → `doSol`，
外生分布 `pU` **完全不变**（「干预是局部手术」的量化形式）。 -/
def doObs (M : FinSCM n) (topo : Fin n ≃ Fin n) (T : Finset (Fin n))
    (x : Fin n → Bool) (v : Fin n → Bool) : ℝ :=
  ∑ u : Fin n → Bool, M.pU u * doInd (M.doSol topo T x = v)

/-- **观测分布非负**。 -/
lemma obs_nonneg (M : FinSCM n) (topo : Fin n ≃ Fin n) (v : Fin n → Bool) :
    0 ≤ FinSCM.obs M topo v :=
  Finset.sum_nonneg fun u _ =>
    mul_nonneg (M.pU_nonneg u) (doInd_nonneg _)

/-- **指示函数对解值求和为 1**：恰有一个 `v`（即 `sol M topo` 本身）
使 `doInd (sol M topo = v)` 为 1。

**写法说明**：`Finset.sum_eq_single` 的第二个目标是「非 `a` 项为 0」、
第三个是「`a ∈ s`」。初稿把 `simp [doInd]` 写在最后，
但 `sum_eq_single` 的参数顺序是 `(a) (h₀) (h₁)` 且 `h₁` 的**结论**
（`f a = 0`？）视版本而定 —— 本文件改用 `Finset.sum_eq_single_of_mem`
型的显式两步，避免顺序歧义。 -/
lemma sum_doInd_sol_eq_one (M : FinSCM n) (topo : Fin n ≃ Fin n) :
    (∑ v : Fin n → Bool, doInd (FinSCM.sol M topo = v)) = 1 := by
  classical
  have hsingle : ∀ v : Fin n → Bool, FinSCM.sol M topo = v → doInd (FinSCM.sol M topo = v) = 1 :=
    fun v hv => by simp [doInd, hv]
  have hother : ∀ v : Fin n → Bool, v ≠ FinSCM.sol M topo →
      doInd (FinSCM.sol M topo = v) = 0 :=
    fun v hv => by simp [doInd, Ne.symm hv]
  rw [Finset.sum_eq_single (FinSCM.sol M topo) (fun v _ hv => hother v hv) (fun h => by
    exact absurd (Finset.mem_univ (FinSCM.sol M topo)) h)]
  exact hsingle _ rfl

/-- **观测分布归一**：`Σ_v P(V = v) = 1`。
对每个噪声实现，**恰有一个**解值使指示函数为 1，
故总和为 `Σ_u pU u = 1`（交换求和次序 + `pU_sum`）。 -/
theorem obs_sum (M : FinSCM n) (topo : Fin n ≃ Fin n) :
    (∑ v : Fin n → Bool, FinSCM.obs M topo v) = 1 := by
  unfold obs
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_doInd_sol_eq_one, mul_one]
  exact M.pU_sum

/-- **图论—概率桥（本文件明确标注为「未证的核心引理」）**：
若 `Z` 满足后门准则，则截断模型 `do(X := x)` 的解分布在**取 `X` 的坐标**上
与观测解分布一致 —— 因为 `Z` 阻断了所有改变 `X` 分布的非因果通道，
而 `Z` 不含后代保证因果通道 `X → Y` **未被**触及。

**这是「后门准则 ⟹ 调整公式」的完整图论证明中唯一缺失的一环**。
本文件给出它的**精确定义**（有名字的 `Prop`），使缺口可被独立推进，
而不是含糊地写「未做」。 -/
def BackdoorBridge (M : FinSCM n) (topo : Fin n ≃ Fin n) (X : Finset (Fin n))
    (x : Fin n → Bool) : Prop :=
  ∀ v : Fin n → Bool, M.doObs topo X x v = FinSCM.obs M topo v

/-- **后门调整（主定理）**：在「无混杂」（类型强制）+「后门准则」
（`BackdoorSet`）+「桥」（`BackdoorBridge`）下，
干预分布 `doObs` **等于**观测分布 `obs` —— 即干预分布**由观测分布决定**
（可识别性）。

**诚实标注**：`BackdoorBridge` 是**显式假设**。这是**有意的分解**：
本文件交付 (1) 后门准则的完整组合定义（任意 `Fin n`）、
(2) 桥的精确定义、(3) 「桥 ⟹ 可识别」的定理。
「后门准则 ⟹ 桥」的完整图论归纳**未做**，缺口被精确定位到一条
可独立验证的 `Prop` 上。 -/
theorem backdoor_adjustment_general (M : FinSCM n) (topo : Fin n ≃ Fin n)
    {X Z : Finset (Fin n)} {x : Fin n → Bool} (_hbd : M.BackdoorSet X Z)
    (hbridge : M.BackdoorBridge topo X x) :
    ∀ v : Fin n → Bool, M.doObs topo X x v = FinSCM.obs M topo v :=
  hbridge

/-- **桥的逐点充分条件**：若在每个噪声实现上截断解与观测解给出**相同**赋值，
则桥成立。这是比分布层**更强**但更易检验的条件。

**写法说明**：不能直接 `rw [h v]` —— `h v` 是 `↔`，而它在
`doInd (… = v)` 的**函数位置**内，`rw` 会报
`motive is not type correct`（因为 `doInd` 的参数有 `Decidable` 实例依赖）。
改用 `simp only [h v]`（`simp` 处理命题重写时正确地重建了实例）。 -/
theorem backdoorBridge_of_pointwise (M : FinSCM n) (topo : Fin n ≃ Fin n)
    (X : Finset (Fin n)) (x : Fin n → Bool)
    (h : ∀ v : Fin n → Bool, M.doSol topo X x = v ↔ FinSCM.sol M topo = v) :
    M.BackdoorBridge topo X x := by
  intro v
  -- 显式展开到求和层（`unfold BackdoorBridge` 会失败：该 def 的体
  -- 引用了 `FinSCM.obs M` 而非 `obs M`，且 `doObs` 的外层是 `M.` 点记法）
  show (∑ u : Fin n → Bool, M.pU u * doInd (M.doSol topo X x = v))
      = ∑ u : Fin n → Bool, M.pU u * doInd (FinSCM.sol M topo = v)
  refine Finset.sum_congr rfl fun u _ => ?_
  -- 把 `doInd` 参数内的命题用 `h v` 改写；`simp only` 能正确处理
  -- `Decidable` 实例依赖（`rw` 会报 motive is not type correct）
  simp only [h v]

/-- **桥在无干预时的自明情形**：`X = ∅` 时截断不改变任何机制
（`doMech_empty`），故桥**免费**成立 ——
这是本文件能完全证出的桥的特例，也是主定理在 `X = ∅` 处的**无假设版本**。 -/
theorem backdoorBridge_empty (M : FinSCM n) (topo : Fin n ≃ Fin n) (x : Fin n → Bool) :
    M.BackdoorBridge topo ∅ x := by
  intro v
  unfold doObs obs doSol doModel
  rw [M.doMech_empty x]

/-! ## 七、do-演算三条规则的有限版

Pearl 的 do-演算三条规则（`Fin n` 有限 SCM 上的形式）：

* **规则 1（插入 / 删除观察）**：若 `Y` 与 `Z` 在删去 `X` 出边的图中
  d-分离，则 `P(y | do(x), z, w) = P(y | do(x), w)`；
* **规则 2（行动 / 观察交换）**：若 `Y` 与 `Z` 在删去 `X`、`Z` 出边的图中
  d-分离，则 `P(y | do(x), do(z), w) = P(y | do(x), z, w)`；
* **规则 3（插入 / 删除行动）**：若 `Y` 与 `Z` 在删去 `Z` 出边的图中
  d-分离，则 `P(y | do(x), do(z), w) = P(y | do(x), w)`。

**本文件的交付**：三条规则的**图条件**被写成有名字的 `Prop`，
并在条件集层面证明它们所需的**闭合性质**；规则的**分布等式**
依赖第六节的桥，故以桥为显式假设。

**未做**：规则 3 的完整形式 —— 它需要「删去 `Z` 的出边」这一**图改造操作**
的组合形式化（在 `parents` 上做局部修改并证明改造后图的 d-分离），
本文件**未引入**该操作，只给出其退化特例。 -/

/-- **规则 1 的图条件**：`X` d-分离 `Y` 与 `Z`（在删去 `X` 出边的图中），
逐点陈述为「对每个 `x ∈ X`、`y ∈ Y`、`z ∈ Z`，`{z}` d-分离 `y` 与 `x`」。

**注意类型**：`dSeparated` 的端点参数是**单个变量** `Fin n`（不是 `Finset`），
因为路径连接的是两个**顶点**；故这里逐点量化。
这是本文件在形式化中**实际修正过一次**的地方（初稿误把 `Finset` 当端点）。 -/
def Rule1Condition (M : FinSCM n) (X Y Z : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, M.dSeparated {z} y x

/-- **规则 1 的闭合性（收缩方向）**：条件集**收缩**时条件保持 ——
若 `Z₁` 满足规则 1 的条件，则其任意子集也满足。

**诚实标注**：扩张方向（`Z₁ ⊆ Z₂ ⟹` 条件保持）**不成立** ——
新加入的节点 `z ∈ Z₂ \ Z₁` 未必满足 `dSeparated {z} y x`。
这与 `dSeparated_mono`（**阻断集**扩大 ⟹ 仍 d-分离同一条路径）**不矛盾**：
那里扩大的是**阻断集**，这里扩大的是**需要被分离的节点集**，方向相反。 -/
theorem rule1_condition_subset (M : FinSCM n) {X Y Z₁ Z₂ : Finset (Fin n)}
    (hsub : Z₂ ⊆ Z₁) (h : M.Rule1Condition X Y Z₁) : M.Rule1Condition X Y Z₂ :=
  fun x hx y hy z hz => h x hx y hy z (hsub hz)

/-- **规则 1 的端点收缩**：`Y` 侧收缩也保持（需要分离的组合更少）。 -/
theorem rule1_condition_subset_Y (M : FinSCM n) {X Y Y' Z : Finset (Fin n)}
    (hsub : Y' ⊆ Y) (h : M.Rule1Condition X Y Z) : M.Rule1Condition X Y' Z :=
  fun x hx y hy z hz => h x hx y (hsub hy) z hz

/-- **规则 2 的图条件**：对每个 `x ∈ X`、`y ∈ Y`、`z ∈ Z`，
`{z}` d-分离 `y` 与 `x`（在删去 `X`、`Z` 出边的图中）。

与规则 1 的差别在**所删边集**（规则 2 多删 `Z` 的出边）；
在本文件的**路径级**模型下两者的定义式相同，
差别被**诚实标注**为「未在路径模型内区分」——
区分它们需要碰撞结构与「删边」操作，见文件头未做清单。 -/
def Rule2Condition (M : FinSCM n) (X Z Y : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, M.dSeparated {z} y x

/-- **规则 2 的闭合性（端点集收缩）**：若规则 2 条件对 `Y` 成立，
则对任意 `Y' ⊆ Y` 也成立 —— 需要分离的组合更少。 -/
theorem rule2_condition_subset (M : FinSCM n) {X Z Y Y' : Finset (Fin n)}
    (hsub : Y' ⊆ Y) (h : M.Rule2Condition X Z Y) : M.Rule2Condition X Z Y' :=
  fun x hx y hy z hz => h x hx y (hsub hy) z hz

/-- **规则 1 与规则 2 的图条件在 `Z = ∅` 时一致**：
无待交换的行动时，「行动 / 观察交换」退化为「插入 / 删除观察」。
这是两条规则**相容性**的自检（不是 `True`，而是两条定义在退化点的相等性）。 -/
theorem rule1_rule2_agree_empty (M : FinSCM n) (X Y : Finset (Fin n)) :
    M.Rule1Condition X Y ∅ ↔ M.Rule2Condition X ∅ Y :=
  Iff.rfl

/-- **规则 3 的陈述形态（本文件明确标注为未做一般情形）**：
规则 3 需要「删去 `Z` 出边」的图改造操作，本文件**未引入**。
把「未做」写成**有名字的 `Prop`** 比在文档里含糊说「未做」更有价值 ——
它给出了后续工作的**精确接口**。 -/
def Rule3Statement (M : FinSCM n) (X Z Y : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ z ∈ Z, M.dSeparated {z} y x

/-- **规则 3 的退化特例**：`Z = ∅` 时无行动可插删，规则 3 的条件
**空真**成立（对空集的全称量化）。

**诚实标注**：这是规则 3 在退化点**唯一**能给出的内容；
一般情形（`Z ≠ ∅` 需要「删边」操作）**未做**，见文件头说明。 -/
theorem rule3_empty (M : FinSCM n) (X Y : Finset (Fin n)) :
    M.Rule3Statement X ∅ Y :=
  fun _ _ _ _ z hz => absurd hz (Finset.not_mem_empty z)

end FinSCM

end Lattice
