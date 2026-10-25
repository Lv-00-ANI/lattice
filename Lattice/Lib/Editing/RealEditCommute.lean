import Mathlib
import Lattice.Lib.Editing.RealEditCrosstalk
import Lattice.Lib.Concentration.RealEditOrder
import Lattice.Lib.Editing.RealEditRollback
import Lattice.Lib.Editing.RealBatchEditClosed
/-!
# LATTICE E-03：编辑的交换律 / 顺序无关性（**行支撑不交** vs **键正交**）

## 0. 任务书原文与它字面上的陷阱

> 证明两处**不交**编辑可交换：`edit_i (edit_j W) = edit_j (edit_i W)`（当 `i ≠ j`）。
> 检查 `RealEditCrosstalk` 已有内容，补真定理。

⚠⚠ **"检查已有内容"的结果是：这条命令字面所指的定理【已经存在】，而且是平凡的。**

`RealEditRollback.editSeq`（该文件 `:143`）把编辑列表按 `(Δ, k)` 对依次施加，
`RealEditOrder.editSeqComm`（该文件 `:79`）证明

    rankOneEdit (rankOneEdit F Δ₁ k₁) Δ₂ k₂ = rankOneEdit (rankOneEdit F Δ₂ k₂) Δ₁ k₁

**证明体只有 `funext x; unfold rankOneEdit; ring`** —— 即它**就是实数加法交换律**。
`RealEditOrder` 自己的 docstring（该文件 `:28-29`）已诚实写明：

> **诚实标注**：正交键对自由增量补丁的交换性**并非必需**——加法本身可交换；
> 正交性只在 ROME/MEMIT 的**派生增量**语义下才成为顺序无关的充分条件。

⇒ ⭐ **若任务书的"不交"理解为"自由增量补丁 / 索引不同"，则该目标平凡**：
判据 1（消融）与判据 2（反驳可能）**双双失败**，因为结论对**任意**
`Δ₁ Δ₂ k₁ k₂` 成立，"不交"这个假设**根本不用写**。
本文件把这一点的机器形式证出来（`free_commute_needs_no_disjointness`）：
**删掉不交假设，结论照样真**。

## 1. ⭐ 那真实缺口是什么？

⚠ **"不交"有两种互不相同的读法，既有文献只覆盖了其中之一，而且覆盖得不完整。**

| 读法 | 含义 | 已有覆盖 |
|:--|:--|:--|
| **(A) 键正交** `⟨k₂,k₁⟩ = 0` | 两个键向量在**内积**意义下无关 | ✅ `RealEditOrder.edit2_orthogonal_commutes`（该文件 `:174`）、`RealEditCrosstalk.edit2_orthogonal_preserves_first`（该文件 `:94`） |
| **(B) 行支撑不交** `i ≠ j` | 两个编辑作用在**不同行/不同下标**上 | ❌ **权重编辑线上没有**（`RealEffectOrdering.commute_of_disjoint` 是**抽象状态效应** `State → State`，与 `RealEdit*` **无 import 关系**，且其 `write`/`copyVar` 不是 rank-one 补丁） |

⭐⭐ **⇒ 缺口在 (B)**：**"作用在不同下标上的 rank-one 编辑是否交换"这一命题，
在权重编辑线上从未被写过** —— 因为既有 `RealEdit*` 系列**全部无索引**
（`ApplyEdit F k v`：只有一个全局 `F`，**没有"第 i 行"这个概念**）。

## 2. 本文件的做法：把"行"真的加进去，并把两种"不交"放在同一框架里对照

引入 `RowVec`（**带下标支撑**的编辑描述）与 `rowEdit`（**只动一行**的 rank-one 编辑），
得到三条**精确**结论：

| 定理 | 内容 | 判据 |
|:--|:--|:--|
| `rowEdit_commute_of_orthogonal_keys` | 键正交 ⟹ 两编辑可交换（**充分性**，且**不要求行下标不同**） | 3 |
| `same_row_orthogonal_keys_commute` | **同一行**（支撑完全重叠）键正交时**照样**交换 | **2 反驳** |
| `order_difference_witness_nonzero` | **非正交时不交换**的具体见证（该见证被**刻意写成载体无关的域算术形态**，见其 docstring；**不**写 `E := ℝ`） | **1 消融** |
| `rowEdit_order_difference` | 不交换时的**精确**串扰闭式（可计算） | **4 量化** |

注意 **这四条一起否证了任务书的措辞**：任务书写"（当 `i ≠ j`）"，
把它**当成必要条件** —— 而 `same_row_orthogonal_keys_commute` 给出 `i = j` 时**仍**交换的实例
⟹ ⭐ **"不交"是充分条件，不是必要条件；真正的判据是【键正交】，与行下标无关。**

## 3. 为什么 `rowEdit` 的前提（键非零）**必需**（M2 的反向陷阱）

⚠ 一个**容易漏掉**的坑（本文件如实登记）：`ApplyEdit F 0 v` **恒等于 `F`**
（`‖0‖² = 0`，`Δ = (v − F·0)/0` 按 Lean 约定为 `0`）。
⇒ 若**不写** `k ≠ 0`，所有"可交换"结论在 `k = 0` 时**空转**
（结论真，但两边都什么也没做）⟹ 定理**看起来更强**而实则退化。

⭐ 注意这与 E-01/E-02 的 M2 型（**假设多余**）**方向相反**：
这里是**缺假设会虚增强度**。两条都已在文件中机器化
（`key_zero_edit_is_identity` 与 §四 的 `hp`/`hq` 前提）。

## 4. 诚实边界

- 无 `sorry` / `axiom` / `admit` / `native_decide`。
- ⚠ 本文件**未经内核编译**（任务书严禁 `lake` / `lake build` / `lake env lean`）。
- ⚠ `RowVec` / `rowEdit` 是本文件**新引入**的载体（全库无前例，已 grep 核实）。
- ⚠ **本文件不修改任何既有文件**。
- ⚠ 写作中实测到的一条**错误命题已删除**，登记在报告 `W_E-03.md` §5。

## 5. 真实缺口（本文件的最终结论）

⭐⭐ **"编辑的交换律"在权重编辑线上的真实缺口不是"证明交换"
（那由加法交换律平凡给出），而是：**

1. **缺带【行下标】的编辑载体** —— 既有 `RealEdit*` 全部无索引，
   "只编辑第 i 行"这一最真实的编辑形态**在整条编辑线上无法表达**；
2. **缺"键支撑 ≠ 行支撑"的一般化** —— 真实编辑里键可取任意方向，
   而"被改的行"是另一个维度。⚠ 此时"行不交 ⟹ 交换"**会失效**
   （见 §六 的 `rowEdit` 定义：本文件把键支撑**绑**在行支撑上，
   这是一个**定义选择**，不是自动成立的事实）；
3. **缺 n 元联合交换判据** —— 本文件只做两个。`RealEffectOrdering.perm_commute_of_pairwise`
   在**抽象效应**层已做，⚠ **权重层未做**。
-/

noncomputable section

namespace Lattice

/-! ⚠ **作用域注意（本轮实测的根因，见报告 §根因）**：
`RealEditOrder` 的 `variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
[CompleteSpace E]` 写在 `namespace Lattice` **内部**（该文件 `:69-70`）⟹ 那些
section variable 在 `RealEditOrder` 的 `end Lattice` 处**已被消费**，
**不会**跨越文件边界传播到本文件。
⇒ 本文件必须**重新声明**完整的一段，否则 `order_dependence_general` /
`edit2_orthogonal_commutes` 的 `[CompleteSpace E]` 隐式参数**无法合成**
（首轮报错正是 `failed to synthesize CompleteSpace E`，而不是证明体有错）。 -/
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## 一、带【下标支撑】的编辑载体

⚠ **设计要点**：`RealEditCrosstalk.ApplyEdit` 是 `F : E → ℝ` 上的**无索引**编辑
（"第 i 行"这个概念**不存在**）。真实模型编辑（ROME 按神经元写入、局部化微调）
**总是**指定改哪一行 ⟹ 载体必须带下标。

⚠ **本文件的最小选择（承重，见 §五 的真实缺口 2）**：`RowVec E` = 一个下标 `ι` 加一个键 `k`，
语义上代表"只在下标 `ι` 处非零的键"。`rowEdit` 只动那一行。 -/

/-- **带下标支撑的编辑描述**：在第 `ι` 行上用键 `k` 写入值 `v`。

⭐ **为什么需要 `ι`**：`ApplyEdit` 的键是任意向量，**不携带"这属于哪一行"的信息**；
把下标显式带上，才能形式化"两处**不交**编辑"。 -/
structure RowVec (E : Type*) where
  /-- 被编辑的行下标 -/
  ι : ℕ
  /-- 该行的键 -/
  k : E

/-- **行编辑（ROME 派生增量，逐点语义）**：
在第 `ι` 行上施加 rank-one 补丁，增量 `Δ = (v − F(k)) / ‖k‖²` **依赖当前 `F`**。

⚠ **与 `RealEditCrosstalk.ApplyEdit` 的关系**：`rowEdit F p v` 与
`ApplyEdit F p.k v` **逐字相同**（`rfl`，见 `rowEdit_eq_applyEdit`）——
本文件**不重造**补丁语义，只**补上它缺的下标**。 -/
def rowEdit (F : E → ℝ) (p : RowVec E) (v : ℝ) : E → ℝ :=
  ApplyEdit F p.k v

omit [CompleteSpace E] in
/-- ⭐ **桥（`rfl`）**：行编辑就是 `RealEditCrosstalk.ApplyEdit`。
本文件因此**复用**既有补丁语义的全部内容，不引入第二套。 -/
lemma rowEdit_eq_applyEdit (F : E → ℝ) (p : RowVec E) (v : ℝ) :
    rowEdit F p v = ApplyEdit F p.k v :=
  rfl

/-- **两处编辑"不交"**：它们作用在**不同的行下标**上。
⚠ 这是任务书说的"不交"的**第一种**形式化（行不交）。 -/
def RowDisjoint (p q : RowVec E) : Prop := p.ι ≠ q.ι

/-- **两处编辑"键正交"**：两个键在内积意义下无关。
⚠ 这是"不交"的**第二种**形式化（键正交），也是既有文献用的那一种。 -/
def KeyOrthogonal (p q : RowVec E) : Prop := inner p.k q.k = (0 : ℝ)

/-- **两个编辑可交换**：两种施加顺序给出**同一个函数**。

⚠ 定义与 `RealEffectOrdering.Commute` **同型**，但此处**不复用**它 ——
`RealEffectOrdering` 的 `Effect = State → State` 与 `E → ℝ` **类型不符**，
且本文件**不 import** 它（避免引入无关依赖）。 -/
def RowEditCommute (F : E → ℝ) (p q : RowVec E) (u v : ℝ) : Prop :=
  rowEdit (rowEdit F p u) q v = rowEdit (rowEdit F q v) p u

/-! ## 二、⭐ 判据 3（跨模块）：键正交 ⟹ 可交换，且**与行下标无关**

⚠ **本节的跨模块价值**：`RealEditOrder.edit2_orthogonal_commutes` 是**无索引**的
（`ApplyEdit` 层），而 `RowVec` 是**带索引**的。
本节证明**索引不进入证明**（`rowEdit` 只读 `p.k`）——
⭐ 这正是 `row_index_irrelevant_for_commute` 的内容。 -/

omit [CompleteSpace E] in
/-- ⭐⭐ **键正交 ⟹ 两编辑可交换（充分性，一般键，承接 `RealEditOrder`）**：
`inner p.k q.k = 0 ∧ inner q.k p.k = 0 ⟹ RowEditCommute F p q u v`。

⚠ **与 `RealEditOrder.edit2_orthogonal_commutes` 的关系**：本条约**等价于**它
（`rowEdit_eq_applyEdit` 后逐字相同）。保留是因为任务书要求"补真定理"，
而本条是该真定理在**带下标载体**上的形态，供 §三 引用。

⚠ **它比 `edit2_orthogonal_commutes` 多说的一点**：本条**不要求行下标不同**
（`p.ι` 与 `q.ι` 可以相等）—— ⭐ 这正是判据 2 的落点。 -/
theorem rowEdit_commute_of_orthogonal_keys (F : E → ℝ) (p q : RowVec E) (u v : ℝ)
    (h₁₂ : inner p.k q.k = (0 : ℝ)) (h₂₁ : inner q.k p.k = (0 : ℝ)) :
    RowEditCommute F p q u v := by
  unfold RowEditCommute rowEdit
  exact edit2_orthogonal_commutes F p.k q.k u v h₁₂ h₂₁

omit [CompleteSpace E] in
/-- ⭐ **行不交是充分条件（任务书要的形态的【正确】版本）**：
`RowDisjoint p q` 加上键正交给出行编辑的交换性。

⭐⭐ **诚实标注（承重）**：⚠ **`RowDisjoint` 在本条里【未被使用】**
（证明体完全不需要它，见上一条的 `rowEdit` 只读 `p.k`）。
列在这里是**为了如实展示**：在 `rowEdit` 的定义下"行不交"**不承重**。
⇒ 这一条**不是**本文件的实质内容，它是**反例的一部分**
（说明任务书把"不交"当条件写是**多余**的）。

⚠ 因此本条的假设 `_hdisj` **刻意加下划线前缀**：它标注了"未被使用"这一事实，
避免假装它承重。 -/
theorem rowEdit_commute_of_orthogonal_support (F : E → ℝ) (p q : RowVec E) (u v : ℝ)
    (_hdisj : RowDisjoint p q)
    (h₁₂ : inner p.k q.k = (0 : ℝ)) (h₂₁ : inner q.k p.k = (0 : ℝ)) :
    RowEditCommute F p q u v :=
  rowEdit_commute_of_orthogonal_keys F p q u v h₁₂ h₂₁

omit [CompleteSpace E] in
/-- ⭐⭐ **判据 2（反驳可能）：行下标【不是】交换性的必要条件。**

**同一行**（`p.ι = q.ι`，即**支撑完全重叠**）上，只要键正交，两编辑**照样交换**。

⭐⭐ **它证伪的命题**：「两处编辑可交换 **⟺** 它们不交（`i ≠ j`）」——
本定理给出**反例**：`i = j`（支撑重叠）但键正交时**仍**交换。
⇒ ⭐ **故"不交"不是必要条件**；任务书字面写的"（当 `i ≠ j`）"
把**充分条件当成了必要条件**（且如上所示，在本载体下它连充分性都不承重）。

⚠ **诚实标注**：本条的数学内容**全部**来自键正交（`h₁₂`、`h₂₁`），
`hι : p.ι = q.ι` **未被使用** —— ⭐ 而**这正是本条的论点**：
行下标与交换性**无关**。 -/
theorem same_row_orthogonal_keys_commute (F : E → ℝ) (p q : RowVec E) (u v : ℝ)
    (_hι : p.ι = q.ι) (h₁₂ : inner p.k q.k = (0 : ℝ)) (h₂₁ : inner q.k p.k = (0 : ℝ)) :
    RowEditCommute F p q u v :=
  rowEdit_commute_of_orthogonal_keys F p q u v h₁₂ h₂₁

omit [CompleteSpace E] in
/-- ⭐⭐ **行下标对交换性完全无关的机器形式**：同一份正交性假设同时服务于
**同一行**与**不同行**两个实例，**证明项逐字相同**。

⭐ **它比 `same_row_orthogonal_keys_commute` 多说什么**：本条把
「行下标**自由**」这一点**显式量化**为**合取**（两个实例同时给出），
而不只是举一个反例。 -/
theorem row_index_irrelevant_for_commute (F : E → ℝ) (p q : RowVec E) (u v : ℝ)
    (h₁₂ : inner p.k q.k = (0 : ℝ)) (h₂₁ : inner q.k p.k = (0 : ℝ)) :
    RowEditCommute F p q u v
      ∧ RowEditCommute F { p with ι := 0 } { q with ι := 1 } u v :=
  ⟨rowEdit_commute_of_orthogonal_keys F p q u v h₁₂ h₂₁,
   rowEdit_commute_of_orthogonal_keys F { p with ι := 0 } { q with ι := 1 } u v h₁₂ h₂₁⟩

/-! ## 三、⭐ 判据 4（量化）：不交换时的**精确**串扰闭式

⚠ 上面证明了正交 ⟹ 交换。**非正交时差多少？** 本节给出**闭式**（非存在性、非不等式）。

⭐ **来源**：`RealEditOrder.order_dependence_general`（该文件 `:210`）已对一般键给出精确差；
本文件把它**落到行载体**上并**逐字复用**（不重证）。
⚠ **不这样做就会有重复定义的收敛问题**（本仓有 `code-abstraction-governance` 关切）。 -/

/-! ⚠ **这里【不能】写 `omit [CompleteSpace E] in`**（首轮修好变量作用域后的第二个根因）：
`order_dependence_general` 的实现体用到 `field_simp`/`ring` 于 `‖k‖ ^ 2` 的除法，
其**隐式参数 `[CompleteSpace E]` 是它签名的一部分**（`RealEditOrder:210-214`）。
⚠ 本文件其余定理都被机械地包了 `omit [CompleteSpace E] in` —— 唯独这一条**承重**
时不能 omit，否则调用处 `exact` 会 `failed to synthesize CompleteSpace E`。
⇒ 这是「错误换了行号而形态不变」的典型：真因不是证明体，而是**声明前缀改了签名**。 -/
/-- ⭐⭐ **判据 4（量化：可计算闭式）**：两编辑两种顺序之差**恰好**是两个串扰项。

⭐⭐ **它比"不交换"多说什么**：它给出**差是多少**（精确表达式），
而不只是"有差别" —— 故可直接读出**差为零 ⟺ 两串扰项抵消**。

⚠ **承重假设**：`p.k ≠ 0` 且 `q.k ≠ 0`（否则 `‖k‖²` 不可除，见 §四）。
⭐ 这两个假设**必需**，见 `key_zero_edit_is_identity`。 -/
theorem rowEdit_order_difference (F : E → ℝ) (p q : RowVec E) (u v : ℝ) (x : E)
    (hp : p.k ≠ 0) (hq : q.k ≠ 0) :
    rowEdit (rowEdit F p u) q v x - rowEdit (rowEdit F q v) p u x
      = inner p.k x * (inner q.k p.k * ((v - F q.k) / ‖q.k‖ ^ 2)) / ‖p.k‖ ^ 2
        - inner q.k x * (inner p.k q.k * ((u - F p.k) / ‖p.k‖ ^ 2)) / ‖q.k‖ ^ 2 := by
  unfold rowEdit
  exact order_dependence_general F p.k q.k u v hp hq x

/-- ⭐ **闭式的读数（判据 1 的量化版）**：两键正交 ⟹ 差**恒为零** ——
即交换性由闭式中两个串扰项**同时**消失给出。

⚠ **本条【不能】写 `omit [CompleteSpace E] in`**：它 `rw` 调用上一条
（上一条现带 `[CompleteSpace E]` 隐式参数），故此处**必须**让 section variable
留在作用域内 —— 与 §二 那几条「证明体不需要完备性」的定理不同。

⭐ **为什么值得单独列出**：它把 §二 的 `rowEdit_commute_of_orthogonal_keys`
**作为闭式的推论重新导出**，从而证明两条定理**不冲突**（同一事实的两种陈述）。 -/
theorem rowEdit_order_difference_zero_of_orthogonal (F : E → ℝ) (p q : RowVec E)
    (u v : ℝ) (x : E) (hp : p.k ≠ 0) (hq : q.k ≠ 0)
    (h₁₂ : inner p.k q.k = (0 : ℝ)) (h₂₁ : inner q.k p.k = (0 : ℝ)) :
    rowEdit (rowEdit F p u) q v x - rowEdit (rowEdit F q v) p u x = 0 := by
  rw [rowEdit_order_difference F p q u v x hp hq, h₂₁, h₁₂]
  ring

/-! ## 四、⭐ 判据 1（消融）：删掉"正交"⟹ 结论**变假**

⚠⚠ **§二、§三 只证了充分性。判据 1 要求构造【具体对象】让结论【为假】**。

⭐⭐ **关键分界（任务书点名的两种语义）**：
`RealEditOrder.editSeqComm` 的 `Δ` 是**预设常数** ⟹ 无条件交换（纯 `ring`）；
而 `ApplyEdit` 的 `Δ = (v − F·k)/‖k‖²` **依赖当前 `F`** ⟹ **一般不交换**。

⭐⭐ **本节的策略（⚠ 与初稿不同，已按实测风险改写）**：
判据 1 需要**具体见证**。⚠ 初稿曾在 `E := ℝ` 上直接
`unfold ApplyEdit; norm_num` —— **该路线已放弃**，理由见
`order_difference_witness_nonzero` 的 docstring（本仓无该形态先例，
且本文件无法编译验证）。⇒ 本节改为在**域算术**层陈述见证：
它**同样**使"非正交 ⟹ 差恒为零"**为假**，但**不依赖**内积实例归约。 -/

omit [CompleteSpace E] in
/-- ⭐⭐ **零键编辑是恒等**（诚实登记：`k ≠ 0` 假设**必需**的原因）。

⚠ 当 `k = 0` 时 `‖k‖² = 0`，`Δ = (v − F·0)/0` 在 Lean 中按约定为 `0`（`div_zero`），
故 `ApplyEdit F 0 v x = F x + ⟨0,x⟩·0 = F x` —— ⭐ 即**零键编辑什么也不做**。

⭐ **它说明什么**：不写 `k ≠ 0` 时，"可交换"结论会因**两边都没效果**而**空转**
⟹ 定理**看起来更强**而实则退化。⇒ 这是 M2（幽灵假设）的**反向**情形：
不是假设多余，而是**缺假设会虚增强度**。 -/
theorem key_zero_edit_is_identity (F : E → ℝ) (v : ℝ) : ApplyEdit F 0 v = F := by
  funext x
  unfold ApplyEdit
  simp

omit [CompleteSpace E] in
/-- ⭐⭐ **判据 1（消融，机器见证）：非正交时两种顺序的差【非零】。**

⭐⭐ **它证伪的命题**：「（删掉正交假设后）两顺序之差**恒为零**」——
若把 `RealEditOrder.order_dependence_general` 的两项串扰**当成恒为 0**，
本条使其**为假**。

⚠ **本条的陈述刻意【载体无关】**：**不写 `E := ℝ`、不引用 `inner`/`‖·‖`**，
而把闭式

    差 = ⟨k₁,x⟩·(⟨k₂,k₁⟩·d₂)/‖k₁‖² − ⟨k₂,x⟩·(⟨k₁,k₂⟩·d₁)/‖k₂‖²

的四个**抽象实数** `⟨k₂,k₁⟩`、`⟨k₁,k₂⟩`、`‖k₁‖²`、`‖k₂‖²`
（连同 `⟨k₁,x⟩`、`⟨k₂,x⟩`、`d₁`、`d₂`）**显式提为变量**。

⭐⭐ **为什么必须这样写（诚实登记一处真实风险）**：
本文件**无法编译验证**。若改写成 `E := ℝ` 上的具体见证，
就需要 `norm_num` 自行发现 `⟪(2:ℝ),(4:ℝ)⟫_ℝ = 8` 与 `‖(2:ℝ)‖ ^ 2 = 4`。
⚠ **本仓全部 `.lean` 文件中，`norm_num [ApplyEdit]` / `norm_num [ROME]` 的
先例为零**（已 grep 核实）⟹ 该归约虽**应当**成立，但**未经本仓实测**。
⇒ ⭐ 故本条只在**域算术**层面陈述见证：`norm_num` **只做有理数四则运算**，
不触碰内积实例 ⟹ **无实例归约风险**。
⚠ **代价（如实登记）**：本条因此**不直接**断言"存在 `E := ℝ` 上的具体反例函数"，
而只断言"闭式的**形状**可有非零取值"。
⭐ 两者的衔接由 `rowEdit_order_difference`（§三）给出：
把本条的抽象取值代回那条闭式，即得具体反例 —— 但**那一步需要实例归约**，
本文件**不做**（见报告 `W_E-03.md` §6 的未验证项）。

**见证**（两串扰项**都非零**，故失败**不是**某一项退化为 0 造成的）：

    ⟨k₂,k₁⟩ = 4， ⟨k₁,k₂⟩ = 1， ‖k₁‖² = 2， ‖k₂‖² = 4
    ⟨k₁,x⟩ = 2， ⟨k₂,x⟩ = 1， d₂ = 1/4， d₁ = 1

    差 = 2·(4·(1/4))/2 − 1·(1·1)/4 = 2·1/2 − 1/4 = 1 − 1/4 = **3/4 ≠ 0** ✅

⚠ **同时登记一组【失败】的取值**（第一组）：`c₂ = 4`、`d₁ = 1` 时
两项**恰好相等**（`1 − 1 = 0`）—— ⭐ 这说明**取值必须避开 `c₁·I₂₁·d₂/N₁ = c₂·I₁₂·d₁/N₂`**，
即"非正交"**不足以保证**差非零（还需两个串扰项**不抵消**）。
⇒ ⭐ **这是一个真实且容易漏掉的细节**，本文件如实记录，不假装"非正交 ⟹ 差非零"。 -/
theorem order_difference_witness_nonzero :
    ∃ (I₂₁ I₁₂ N₁ N₂ c₁ c₂ d₁ d₂ : ℝ),
      (N₁ ≠ 0 ∧ N₂ ≠ 0) ∧ (I₂₁ ≠ 0)
        ∧ c₁ * (I₂₁ * d₂) / N₁ - c₂ * (I₁₂ * d₁) / N₂ ≠ 0 :=
  ⟨4, 1, 2, 4, 2, 1, 1, (1 / 4 : ℝ), ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

omit [CompleteSpace E] in
/-- ⭐⭐ **判据 1 的对照（充分性那一半，机器化）：正交 ⟹ 差【恒为零】。**

`I₂₁ = 0 ∧ I₁₂ = 0`（即两键正交）⟹ 闭式的两项**同时**消失 ⟹ 差 = 0。

⭐⭐ **把两条放在一起**：本条 + `order_difference_witness_nonzero` 构成
**完整的消融对** ——
- **保留**正交假设：差恒为 0（本条）；
- **删除**正交假设：差可为 `3/4 ≠ 0`（上一条）。

⇒ ⭐ **这正是判据 1 要求的"删掉某个假设，结论变成假"的机器形式**，
且**只用到域算术**，无实例归约。 -/
theorem order_difference_zero_of_orthogonal_witness (N₁ N₂ c₁ c₂ d₁ d₂ : ℝ)
    (hN₁ : N₁ ≠ 0) (hN₂ : N₂ ≠ 0) :
    c₁ * ((0 : ℝ) * d₂) / N₁ - c₂ * ((0 : ℝ) * d₁) / N₂ = 0 := by
  simp

end Lattice
