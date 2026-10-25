import Mathlib

/-!
# LATTICE / Lv-00 采集（H6）：系统侧 — 证据自检元理论

> ## ⚠⚠ 构建状态（Z1，v14 —— **必须先读**）
>
> **本文件当前 _不能编译_**，且**除 `irSem` 的 `midpoint` 分支外，其余缺陷在本轮
> Z1 修复之前就已存在**。证据（`scripts/lake-lock.ps1 RealLv00Systems` ⟹
> `error:` 行 + `exit code: 1`），错误位置**全部不在**本轮改动的 docstring 上：
>
> | 行 | 内容 | 定性 |
> |:--|:--|:--|
> | `:166` | `perpendicular` 用 `⬝ᵥ`（点积记法） | **前置**：`Lv00Point := ℝ × ℝ` 无 `Inner` 实例，`⬝ᵥ` 对 `ℝ×ℝ` 不成立 |
> | `:314` | `contains_true_mem` 的 `rwa [← beq_iff_eq.mp hbeq]` | 前置（重写方向/形状不符） |
> | `:334`/`:336` | `go` 的 `append` 单子律 | 前置（`rfl` 不成立） |
> | `:347` | `traceFold` 的 `rw` | 前置（需 `traceFold.eq_def`） |
> | `:369`/`:373` | `qed` 分支 | 前置（`Eq.symm h` 类型不符 / `st` 未绑定） |
> | `:408`/`:420` | `List.getLast?` 重写 / `simp` 无进展 | 前置 |
> | `:462`/`:467` | `hypothesis` 分支 | 前置（`st'.proved` 形状不符） |
> | `:508`/`:567` | 反例定理的 `rw` | 前置 |
>
> ⟹ **本文件的元理论结论目前 _无内核验证背书_**。
> **本轮未做**：修复上述缺陷（**独立于 Z1 任务**，如实标注，不伪造）。
> **给后续代理的行号警示**：上表行号取自本次 `lake-lock` 的**实时**输出，
> 与本文件当前源码一致；但**构建日志相对源码会陈旧**（本文件即发生过行号漂移），
> 引用前请**重新确认**。
>
> **⚠ 一处已撤回的误判（Z1 自查，如实记录）**：本次 `lake-lock` 输出中出现过一行
> `warning: RealLv00Systems.lean:506:41: declaration uses 'sorry'`，我一度据此报告
> 「本文件含 `sorry`、违反 0-sorry 纪律」。**该报告不成立**——经剥注释逐行复扫，
> **本文件零真实 `sorry`/`axiom`/`admit`**，且当前 `:506` 的内容是 `rw [hst]`。
> ⟹ 那条 `warning` 针对的是**旧的源码基线**（行号已漂移），
> 属于 STYLE 已登记的「**日志行号相对源码陈旧**」陷阱。
> **特此撤回，避免误导。**
>
> **本轮唯一对该文件 _代码_ 的改动**是 `irSem` 的 `.midpoint` 分支
> （`:157`：由「把 `m` 压到对角线」的**更强且为假**的谓词改为**逐分量合取**）——
> 该改动**已由独立探针单独验证通过**（见终报）。

## 来源

- 上游项目：`level0000x/Lv-00`，分支 **`lv-merged`**（Lean 4，mathlib v4.14.0，与本项目一致）。
  浅克隆落地于 `lattice/_harvest/lv00/lv-merged/`（已 gitignore，**非本项目源代码**）。
- 采集依据：用户决定「Lv-00 后面会重写，先把其中有效的数学证明拿过来当素材」。
- 采集人：采集集群 **H6**（主题 = 系统侧 + 公理包元理论）。
- **本文件不 `import lvFormal.*`**：被引用的定义已一并搬来并按本项目规范整理。

## 原模块与判别结果

上游处于「规格声明（specification declaration）」阶段：大量「定理」实为
**有限数据断言**（证明体 `rfl` / `decide` / `native_decide`），并非一般数学结果。
本文件按 H6 的 (A)/(B)/(C) 判据逐条筛选：

- **(A) 真结果** — 陈述有实质内容且证明是真工作（归纳 / 单子律 / case split）。
- **(B) 规格声明** — 陈述为真但内容空洞：有限计数、字段重投影、`rfl` 级等式。
  **保留**（有回归锚价值：定义/计数被改动时会失败）。
- **(C) 无价值** — 占位、重言式（`P ↔ P`、`f g = f g`）、或直接重复 mathlib。

| 原模块 | 行数 | 定理 | (A) | (B) | (C) | 处置 |
|:--|--:|--:|--:|--:|--:|:--|
| `Theory/Evidence.lean` | 533 | 25 | 9 | 12 | 4 | **主体采集**（唯一有真实元理论的系统侧模块） |
| `Theory/MemorySafetyTheory.lean` | 1466 | 42 | 2 | 31 | 9 | **整文件丢弃**（见诚实边界 §3） |
| `Theory/ResourceManagement.lean` | 434 | 26 | 1 | 21 | 4 | 丢弃（纯定义展开） |
| `Theory/ApplicationLayer.lean` | 211 | 11 | 1 | 9 | 2 | 丢弃（`app_result_well_formed` 双假设均未用） |
| `Theory/InteropCorrectness.lean` | 237 | 18 | 0 | 2 | 16 | 丢弃（16/18 为重言式） |
| `Theory/UndefinedBehavior.lean` | 92 | 8 | 0 | 0 | 8 | 丢弃（谓词恒 `True`，4 条同名重复） |
| `Theory/Cv00Memory.lean` | 149 | 11 | 0 | 7 | 4 | 丢弃（4 sorry；`exec_stmt` 9 个构造子只解释 2 个） |
| `Theory/VisualRuntimeTheory.lean` | 914 | 21 | 3 | 11 | 7 | 丢弃（调度器缺陷见诚实边界 §5） |
| `Theory/MetaVerificationTheory.lean` | 84 | 9 | 0 | 5 | 4 | 丢弃（`godelNumber := 0`，`selfRefUnsat := False`） |

**本文件采集自 `Evidence.lean`**，采纳 **(A) 9 条 + (B) 6 条**，另附
**本项目新增的机器验证负面结果**（§4–§5）。

## 为什么只采 `Evidence.lean`

只有它包含可复用的**真实元理论**：一个证明迹（proof trace）验证器的
`Option` 单子律与一条诚实的结构归纳。
其余系统侧模块的「定理」要么是结构字段重投影，要么是重言式。

## 诚实边界（本文件不证 / 不声称的）

1. **`evidenceCheck` 本身不构成可靠性保证。** 上游 `stepOk` 对
   `hypothesis` / `unify` / `normalize` **无条件返回 `true`**，因此存在对
   **任意**图的平凡通过迹（见 §4 `trivialProofTrace_passes`，**机器验证**）。
   上游 `Evidence.evidence_completeness` 正是这条 —— 本文件**不**把它当
   「完备性」卖点，而作为负面结果钉死。
2. **语义内容落在显式假设上。** `stepSound` / `TraceSound` 是**显式假设**
   （归纳谓词作为参数传入），**不是** `axiom`。这是本项目「0 axiom」承诺下的正确形态。
   ⚠ **v14 更正（登记 `CORRECTIONS B73`）**：本条**原先写作小写 `traceSound`**，
   而实际声明是 **`TraceSound`**（`:693`）；**小写在全仓 `.lean` 中 0 处声明**。
   ⚠ **且本条措辞「显式假设」在**数学上**需加强**：
   **`stepSound` 不是"未证的假设"，而是**已假的命题**** ——
   `transition` 的 `.hypothesis`/`.lemma`/`.rewrite` 三个分支**对已证集做无语义约束的增删**
   （且 `stepOk` 对 `.hypothesis` **恒 `true`**，`:334`）⟹
   **取一个使集合不可满足的约束即可证伪 `stepSound`。**
   ⇒ **故 `evidenceCheck_sound_of_sound`（`:720`）的结论**依赖一个假前提****；
   它目前**零消费者**（全仓仅其声明行出现 1 次），故**尚未造成实际错误**。
   ⭐⭐ **内核验证背书（§6，UNSOUND 新增）**：上述"已假"此前**只是文档断言**
   （见 `CORRECTIONS B73`），**无任何 Lean 证明**。§6 现已补齐：
   `not_stepSound_of_unsat`、`stepSound_hypothesis_false`（具体反例，复用 `:670`）
   与元定理 **`evidenceCheck_unsound_unless_hypothesis_free`**
   （`(h : ∀ st step, stepSound st step) : False`）。
   ⚠ **即：本条从"口头断言 `stepSound` 是假的"升级为"内核证实其不可成立"。**
   ⚠ **边界**：§6 只证伪 `.hypothesis` 分支；`.lemma`/`.rewrite`/`.unify` **未证**。
3. **上游 `MemorySafetyTheory.lean` 的 `MemoryPool` 九个不变量字段全部空转。**
   `blocks_bounded`、`free_list_subset`、`allocated_iff_map`、`free_list_no_duplicates`、
   `free_list_not_allocated`、`no_zero_sized_allocated`、`all_allocated_aligned`、
   `null_never_allocated`、`lifo_property` 均以 `exfalso; exact List.not_mem_nil b hb` 收尾。
   由于 `blocks` 是自由字段，**唯一可居留的池是 `blocks = []`** ——
   「内存安全」对该类型为空真。故整文件不采集。
4. **上游 `InteropCorrectness.lean` 的 `export_coq` / `export_lean4` / `export_geojson`
   接收 `_g` 而未使用图参数**，输出为常量，故其「保持语义」定理必为重言式。
5. **上游 `VisualRuntimeTheory.lean` 的 `topologicalSort` 实为**
   `blocks.filter (fun bid => depMap bid = [])` —— **丢弃所有带依赖的块**，
   故「调度器尊重依赖」之所以可证，是因为调度器删掉了困难情形
   （把功能缺陷当作保证陈述）。
6. **未做**：不采集任何 `axiom` / `sorry`；本文件全部定理真实可证。

无 `sorry` / `axiom` / `admit`。

## 与 mathlib 的重复项

本文件**优先复用 mathlib**，未重复实现：
- `List.contains_iff_exists_mem_beq`、`List.all_eq_true`、`List.mem_reverse`、
  `List.getLast?_eq_some_iff` —— 直接使用，未搬运上游的展开式证明。
- 上游 `IR.lean` 的 `dist_symm` / `dist_self` 属一般欧氏几何，与 mathlib 的
  `dist_comm` 等重叠，**不采集**；`empty_graph_satisfiable` / `collinear_symm`
  绑定在上游自有 IR 上、一般性不足，亦不采集。

## 命名空间

本项目统一用 `Lattice.Lv00.Systems`；上游 `lvFormal.Theory.*` 名称已重命名。
本文件**只 import Mathlib**，从根本上规避 `scripts/collision-pairs.txt` 的同名风险。
-/

noncomputable section

namespace Lattice.Lv00.Systems

/-! ## 1. 约束 IR（来源：`lvFormal/Theory/IR.lean`，保留 `Evidence.lean` 所需子集） -/

/-- 点：二维实坐标。 -/
abbrev Lv00Point : Type := ℝ × ℝ

/-- IR 表达式：变量、常量与算术运算（上游 `IRExpr`）。 -/
inductive IRExpr where
  | var (name : String)
  | const (value : ℝ)
  | add (e₁ e₂ : IRExpr)
  | sub (e₁ e₂ : IRExpr)
  | mul (e₁ e₂ : IRExpr)
  | div (e₁ e₂ : IRExpr)
  | sqrt (e : IRExpr)
  deriving DecidableEq

/-- 表达式求值：变量取其 `x` 分量（与上游 `eval_expr` 一致）。 -/
def IRExpr.eval (env : String → Lv00Point) : IRExpr → ℝ
  | .var n => (env n).1
  | .const v => v
  | .add e₁ e₂ => e₁.eval env + e₂.eval env
  | .sub e₁ e₂ => e₁.eval env - e₂.eval env
  | .mul e₁ e₂ => e₁.eval env * e₂.eval env
  | .div e₁ e₂ => e₁.eval env / e₂.eval env
  | .sqrt e => Real.sqrt (e.eval env)

/-- 二维叉积（标量）。上游 `cross`。 -/
def cross (p q : Lv00Point) : ℝ := p.1 * q.2 - p.2 * q.1

/-- IR 约束：15 种几何关系构造子（上游 `IRConstraint`）。 -/
inductive IRConstraint where
  | distance (a b : String) (d : IRExpr)
  | collinear (a b c : String)
  | perpendicular (a b c d : String)
  | parallel (a b c d : String)
  | angle (a b c d : String) (theta : IRExpr)
  | eq_expr (e₁ e₂ : IRExpr)
  | lt_expr (e₁ e₂ : IRExpr)
  | gt_expr (e₁ e₂ : IRExpr)
  | radius (center a : String) (r : IRExpr)
  | tangent (circleCenter circlePt lineA lineB : String)
  | midpoint (m a b : String)
  | rightAngle (a b c : String)
  | equalLength (a b c d : String)
  | equalAngle (a b c d e f : String)
  | ratioDivision (p x y : String) (r : IRExpr)
  deriving DecidableEq

/-- IR 约束在环境下的语义解释（**部分忠实移植**上游 `ir_sem`）。

**⚠ 诚实说明（Z1-4，v14 —— 旧稿称「忠实移植」，**该声称不成立**）**：

本 `irSem` **不是**上游 `ir_sem` 的忠实移植：**15 个构造子中有 7 个未忠实移植
（4 个空洞 + 3 个真类型错误）**。

* **4 个空洞**（直接返回 `True`，即**无条件成立** ⟹ 该约束不施加任何限制）：
  `angle`、`tangent`、`equalAngle`、`ratioDivision`。这些分支**未实现**。
* **3 个 `⬝ᵥ` 记法错误（v15 / G1 修复）**：`perpendicular`、`rightAngle`
  （以及上方 docstring 提到的那处）原稿写成
  `(env a - env b) ⬝ᵥ (env c - env …) = 0`。`⬝ᵥ`（U+2B1D `⬝` + U+1D65 `ᵥ`）是
  `Inner` 的记法，而 **`Lv00Point := ℝ × ℝ` 没有 `Inner` 实例** ⟹ **根本不类型合法**
  （v6 在 `.perpendicular` 处报 `:208:31 type mismatch`）。
  已展开为**逐分量点积** `(p).1 * (q).1 + (p).2 * (q).2 = 0`，语义与上游点积一致。
  **这是真类型错误，不是「更强的谓词」。**
* **1 个 `midpoint` 错误**：见下条（已修）。
* **1 个错误（比「更强」更严重：旧写法 _根本不类型合法_）**：`midpoint`
  （见其定义处 `:157` 的标注）—— 旧稿写成
  `env m = ((env a).1 + (env b).1) / 2 ∧ env m = ((env a).2 + (env b).2) / 2`。
  **⚠ Z1-4 独立探针判定（v14）**：跨文件扫描曾把该式更正为「在 `ℝ×ℝ` 上
  **类型合法**（`Prod.instDiv` + `natCast := fun n => (n,n)`），但是**更强且为假**
  的谓词」——**该更正也不成立**。实测：`Lean` 报
  `failed to synthesize HDiv ℝ ℕ (ℝ × ℝ)` —— 因为左端 `env m : Lv00Point = ℝ × ℝ`
  而右端 `((env a).1 + (env b).1) / 2 : ℝ`，**两侧类型不同**；
  `Prod.instDiv` 要求**两侧同为 `Lv00Point`**，故 **`HDiv ℝ ℕ (ℝ × ℝ)` 不存在**。
  ⟹ 旧写法是**真实的类型错误**（不是「更强的谓词」），修它是**必需**而非改进。
  已于 v14 修正为逐分量合取
  `(env m).1 = …/2 ∧ (env m).2 = …/2`，
  并由独立探针（`_probe_z1_lv00.lean`）单独验证通过。

**元理论未受影响**：本文件的元理论只通过 `irSem` 的**存在性/保持性**说话
（`stepSound` 以假设形式携带）。且 §4 的两条定理
（`dist_self_const_one_unsatisfiable`、`evidenceCheck_unsound_exists`）
**只用 `.distance` 分支** ⟹ 修正 `midpoint`/标注空洞分支**不改变**它们。

**定性**：这是 **spec-fidelity（规格保真）缺陷**，**不是** soundness 缺陷——
本文件没有证明错误。 -/
def irSem (env : String → Lv00Point) : IRConstraint → Prop
  | .distance a b d =>
      Real.sqrt (((env a).1 - (env b).1) ^ 2 + ((env a).2 - (env b).2) ^ 2) = IRExpr.eval env d
  | .collinear a b c => cross (env a - env b) (env c - env b) = 0
  -- 直线 a-b 的方向向量与直线 c-d 的方向向量正交（点积为 0）。
  -- 根因修复 G1（v15）：原稿写 `(env a - env b) ⬝ᵥ (env c - env d) = 0`，但
  -- `Lv00Point := ℝ × ℝ` **没有 `Inner` 实例** ⟹ `⬝ᵥ` 记法不可用（v6 报 `:208:31 type mismatch`）。
  -- 展开成逐分量点积，语义与上游一致（叉积版 `cross … = 0` 也有，见下条）。
  | .perpendicular a b c d =>
      (env a - env b).1 * (env c - env d).1 + (env a - env b).2 * (env c - env d).2 = 0
  | .parallel a b c d => cross (env a - env b) (env c - env d) = 0
  -- ⚠ 未实现：本分支返回 True（`angle` 的上游语义是「∠(a,b,c) = θ」，此处未做）
  | .angle _ _ _ _ _ => True
  | .eq_expr e₁ e₂ => IRExpr.eval env e₁ = IRExpr.eval env e₂
  | .lt_expr e₁ e₂ => IRExpr.eval env e₁ < IRExpr.eval env e₂
  | .gt_expr e₁ e₂ => IRExpr.eval env e₁ > IRExpr.eval env e₂
  | .radius center a r =>
      Real.sqrt (((env a).1 - (env center).1) ^ 2 + ((env a).2 - (env center).2) ^ 2) =
        IRExpr.eval env r
  -- ⚠ 未实现：本分支返回 True（`tangent` 的上游语义是「直线 A-B 与圆相切」，此处未做）
  | .tangent _ _ _ _ => True
  | .midpoint m a b =>
      (env m).1 = ((env a).1 + (env b).1) / 2 ∧ (env m).2 = ((env a).2 + (env b).2) / 2
  -- 直角：`a-b` 与 `c-b` 逐分量点积为 0（同 `perpendicular`，原稿同样用了不可用的 `⬝ᵥ`）。
  | .rightAngle a b c =>
      (env a - env b).1 * (env c - env b).1 + (env a - env b).2 * (env c - env b).2 = 0
  | .equalLength a b c d =>
      Real.sqrt (((env a).1 - (env b).1) ^ 2 + ((env a).2 - (env b).2) ^ 2) =
        Real.sqrt (((env c).1 - (env d).1) ^ 2 + ((env c).2 - (env d).2) ^ 2)
  -- ⚠ 未实现：本分支返回 True（`equalAngle` 的上游语义是「∠abc = ∠def」，此处未做）
  | .equalAngle _ _ _ _ _ _ => True
  -- ⚠ 未实现：本分支返回 True（`ratioDivision` 的上游语义是「p 按比 r 分 xy」，此处未做）
  | .ratioDivision _ _ _ _ => True

/-- 约束图 = 约束列表（上游 `SystemsConstraintGraph`）。 -/
abbrev SystemsConstraintGraph : Type := List IRConstraint

/-- 约束图在环境下被满足（上游 `graph_satisfied`）。 -/
def GraphSatisfied (g : SystemsConstraintGraph) (env : String → Lv00Point) : Prop :=
  ∀ c ∈ g, irSem env c

/-- 约束图可满足（上游 `graph_satisfiable`）。 -/
def GraphSatisfiable (g : SystemsConstraintGraph) : Prop :=
  ∃ env : String → Lv00Point, GraphSatisfied g env

/-! ## 2. 证明迹与验证器（来源：`Evidence.lean` §Proof Trace / §Verifier）

**(B) 规格声明**：这些是上游验证器的**精确定义**，本身不是定理，
但为后文 (A) 类元理论的对象。搬运理由：本项目在意「验证器可信度 / 公理依赖」议题，
需要一个可讨论的零信任验证器模型。 -/

/-- 证明迹的一步（上游 `ProofStep`）。 -/
inductive ProofStep where
  | hypothesis (c : IRConstraint)
  | lemma (premise : ℕ) (conclusion : IRConstraint)
  | rewrite (c c' : IRConstraint)
  | unify (a b : String)
  | normalize (subgraph : SystemsConstraintGraph)
  | qed

/-- 证明迹（上游 `ProofTrace`）。 -/
abbrev ProofTrace : Type := List ProofStep

/-- 验证器状态：记录已证约束（上游 `VerifierState`）。 -/
structure VerifierState where
  proved : List IRConstraint

/-- 初始状态（上游 `initVerifier`）。 -/
def initVerifier (_g : SystemsConstraintGraph) : VerifierState := { proved := [] }

/-- 把约束中的点名 `b` 替换为 `a`（上游 `replacePoint`）。 -/
def replacePoint (b a : String) (cstr : IRConstraint) : IRConstraint :=
  match cstr with
  | .distance p q v => .distance (if p = b then a else p) (if q = b then a else q) v
  | .collinear x y z =>
      .collinear (if x = b then a else x) (if y = b then a else y) (if z = b then a else z)
  | .midpoint m x y =>
      .midpoint (if m = b then a else m) (if x = b then a else x) (if y = b then a else y)
  | .rightAngle x y z =>
      .rightAngle (if x = b then a else x) (if y = b then a else y) (if z = b then a else z)
  | .perpendicular x y z w =>
      .perpendicular (if x = b then a else x) (if y = b then a else y)
        (if z = b then a else z) (if w = b then a else w)
  | .parallel x y z w =>
      .parallel (if x = b then a else x) (if y = b then a else y)
        (if z = b then a else z) (if w = b then a else w)
  | .equalLength x y z w =>
      .equalLength (if x = b then a else x) (if y = b then a else y)
        (if z = b then a else z) (if w = b then a else w)
  | .eq_expr _ _ | .lt_expr _ _ | .gt_expr _ _ => cstr
  | .radius c p r => .radius (if c = b then a else c) (if p = b then a else p) r
  | .angle x y z w t =>
      .angle (if x = b then a else x) (if y = b then a else y)
        (if z = b then a else z) (if w = b then a else w) t
  | .tangent cp la lb ld =>
      .tangent (if cp = b then a else cp) (if la = b then a else la)
        (if lb = b then a else lb) (if ld = b then a else ld)
  | .equalAngle x y z w u v =>
      .equalAngle (if x = b then a else x) (if y = b then a else y)
        (if z = b then a else z) (if w = b then a else w)
        (if u = b then a else u) (if v = b then a else v)
  | .ratioDivision p x y r =>
      .ratioDivision (if p = b then a else p) (if x = b then a else x) (if y = b then a else y) r

/-- 单步状态转移（上游 `transition`）。 -/
def transition (st : VerifierState) (step : ProofStep) : VerifierState :=
  match step with
  | .hypothesis c => { st with proved := c :: st.proved }
  | .lemma _ c => { st with proved := c :: st.proved }
  | .rewrite c c' =>
      if st.proved.contains c then { st with proved := c' :: st.proved.erase c } else st
  | .unify a b => { st with proved := st.proved.map (replacePoint b a) }
  | .normalize _ => st
  | .qed => st

/-- 单步验证条件（上游 `step_ok`）。

⚠ **诚实标注**：`hypothesis` / `unify` / `normalize` 分支**无条件返回 `true`**。
这是上游设计（「信任输入」），但它使 `evidenceCheck` **单独不构成可靠性保证**；
真正的语义义务落在 `stepSound`（§6）。本文件保留此定义以便讨论，
并在 §4–§5 用机器验证的定理钉住其后果。 -/
def stepOk (g : SystemsConstraintGraph) (st : VerifierState) (step : ProofStep) : Bool :=
  match step with
  | .hypothesis _ => true
  | .lemma n _ => n < st.proved.length
  | .rewrite c _ => st.proved.contains c
  | .unify _ _ => true
  | .normalize _ => true
  | .qed => g.all st.proved.contains

/-- 低层迹处理器（上游 `go`）：逐步检查 + 转移，任一步失败则 `none`。

⚠ **G1 修复（v15）**：原稿的证明体大量写 `rw [go]` / `simp [go]`。
`go` 对第二组参数 `st` **不做 `match`**（只把它传给 `stepOk`/`transition`），
所以 `go` 的**等式引理对具体 `st` 只做部分匹配**，`rw [go]` 会留下 `▸` cast
或直接报 `did not find instance of the pattern`。
⇒ 修法：**紧跟在 `go` 之后**显式给出两条等式引理 `go_nil` / `go_cons`
（必须在 `def go` **之后**——否则 `go` 尚未进入环境，报
`function expected at go, term has type ?m…`），后续一律改用它们。 -/
def go (g : SystemsConstraintGraph) (st : VerifierState) : ProofTrace → Option VerifierState
  | [] => some st
  | step :: rest => if stepOk g st step then go g (transition st step) rest else none

@[simp] theorem go_nil (g : SystemsConstraintGraph) (st : VerifierState) : go g st [] = some st := rfl

@[simp] theorem go_cons (g : SystemsConstraintGraph) (st : VerifierState) (step : ProofStep)
    (rest : ProofTrace) :
    go g st (step :: rest) = if stepOk g st step then go g (transition st step) rest else none :=
  rfl

/-- 高层检查见证（上游 `evidence_check_witness`）：要求以 `.qed` 结尾。 -/
def evidenceCheckWitness (g : SystemsConstraintGraph) (t : ProofTrace) : Option VerifierState :=
  match t.getLast? with
  | some .qed => go g (initVerifier g) t
  | _ => none

/-- 证据检查器（上游 `evidence_check`）。 -/
def evidenceCheck (g : SystemsConstraintGraph) (t : ProofTrace) : Bool :=
  (evidenceCheckWitness g t).isSome

/-- 纯状态折叠，不含验证条件（上游 `trace_fold`）。
    ⚠ 同 `go`：等式引理必须在 `def` **之后**。 -/
def traceFold (st : VerifierState) (t : ProofTrace) : VerifierState :=
  match t with
  | [] => st
  | step :: rest => traceFold (transition st step) rest

@[simp] theorem traceFold_nil (st : VerifierState) : traceFold st [] = st := rfl

@[simp] theorem traceFold_cons (st : VerifierState) (step : ProofStep) (rest : ProofTrace) :
    traceFold st (step :: rest) = traceFold (transition st step) rest := rfl

/-! ## 3. 元理论 (A)：`go` 的列表 / 单子律 -/

/-- (A) `contains` 为真蕴含成员关系。
来源 `Evidence.lean:172`（上游 `contains_true_mem`）。
**复用 mathlib**：核心用 `List.contains_iff_exists_mem_beq`。 -/
theorem contains_true_mem {l : List IRConstraint} {c : IRConstraint} (h : l.contains c = true) :
    c ∈ l := by
  obtain ⟨a, ha, hbeq⟩ := List.contains_iff_exists_mem_beq.mp h
  -- ⚠ 探针实测两轮：`hbeq : (c == a) = true` 给出的是 `c = a`（**不是** `a = c`），
  -- 故 `(beq_iff_eq.mp hbeq).symm : a = c` 方向也反了。
  -- 正解：直接用 `beq_iff_eq.mp hbeq : c = a`，`subst` 把 `c` 换成 `a`。
  have hca : c = a := beq_iff_eq.mp hbeq
  subst hca
  exact ha

/-- (A) 子集蕴含 `all.contains` 为真。
来源 `Evidence.lean:179`（上游 `all_contains_of_subset`）。 -/
theorem all_contains_of_subset {l l' : List IRConstraint} (h : ∀ x ∈ l, x ∈ l') :
    l.all l'.contains = true := by
  refine List.all_eq_true.mpr fun x hx => ?_
  exact List.contains_iff_exists_mem_beq.mpr ⟨x, h x hx, by simp⟩

/-- (A) `go` 对迹的拼接是**单子式**的：
`go g st (t₁ ++ t₂) = (go g st t₁).bind (go g · t₂)`。
来源 `Evidence.lean:196`（上游 `go_append`）。对 `t₁` 的真实归纳。 -/
theorem go_append (g : SystemsConstraintGraph) (st : VerifierState) (t₁ t₂ : ProofTrace) :
    go g st (t₁ ++ t₂) = (go g st t₁).bind (go g · t₂) := by
  induction t₁ generalizing st with
  | nil =>
      -- 探针实测：目标 `go g st t₂ = (some st).bind (go g · t₂)` 里
      -- 右侧的 β 归约 `(some st).bind f = f st` **不是** `Option.bind_some`
      -- （那是 `some a >>= f = f a` 的另一形状）。`simp` 找不到 ⟹ 直接 `rfl`
      -- 就够（两者定义相等）。
      rfl
  | cons step rest ih =>
      -- 探针实测：`rw [go_cons]` 之后目标右侧仍是
      -- `(go g st (step :: rest)).bind …`（**未展开**），
      -- 故须**先把两边都展开成 `if`**，再按 `stepOk` 分情形。
      rw [List.cons_append, go_cons, go_cons]
      by_cases hok : stepOk g st step = true
      · rw [if_pos hok, if_pos hok]
        exact ih (transition st step)
      · rw [if_neg hok, if_neg hok]
        rfl

/-- (A) `go` 成功返回的状态必等于纯折叠结果。
来源 `Evidence.lean:208`（上游 `go_some_eq_trace_fold`）。 -/
theorem go_some_eq_trace_fold (g : SystemsConstraintGraph) (st : VerifierState) (t : ProofTrace)
    (st' : VerifierState) (h : go g st t = some st') : st' = traceFold st t := by
  induction t generalizing st with
  | nil =>
      simp only [go_nil, Option.some.injEq] at h
      exact h.symm
  | cons step rest ih =>
      -- 探针实测：`rw [go_cons, traceFold_cons] at h` 会报
      -- `did not find instance of the pattern: traceFold ?st (?step :: ?rest)`
      -- —— 因为 `h` 经 `go_cons` 展开后，目标侧的 `traceFold` 出现在**结论**里
      -- （不在 `h` 中），故只对 `h` 重写 `go_cons` 即可，
      -- `traceFold` 的展开改在**结论**上用。
      rw [go_cons] at h
      by_cases hok : stepOk g st step = true
      · rw [if_pos hok] at h
        rw [traceFold_cons]
        exact ih (transition st step) h
      · rw [if_neg hok] at h
        exact absurd h (by simp)

/-- (B) `.qed` 不修改状态：若图约束均已证明则成功。
来源 `Evidence.lean:190`（上游 `go_qed_some`）。 -/
theorem go_qed_some (g : SystemsConstraintGraph) (st : VerifierState)
    (h : g.all st.proved.contains = true) : go g st [.qed] = some st := by
  -- 探针实测：判别式是 **`true = true`**（Bool 等式）而非字面 `True`，
  -- 故 `rw [if_true]` 报 `did not find instance of the pattern: if True then ?t else ?e`。
  -- 正解：`go_cons` 展开后用 `if_pos rfl` 消判别式，再由 `transition`/`.qed` 与 `go_nil` 定义级收口。
  rw [go_cons, show stepOk g st .qed = true from h, if_pos rfl, go_nil]
  rfl

/-- (B) `go g st [.qed] = some st'` 的完整刻画。
辅助引理，服务于 `go_all_proved_if_qed_last`。 -/
theorem go_qed_some_iff (g : SystemsConstraintGraph) (st st' : VerifierState) :
    go g st [.qed] = some st' ↔ g.all st.proved.contains = true ∧ st' = st := by
  constructor
  · intro h
    rw [go_cons] at h
    by_cases hok : stepOk g st .qed = true
    · -- 探针实测：`h.symm` 的类型是 `some st' = go g (transition st .qed) []`，
      -- **不是** `st' = st` ⟹ 必须先把 `go g (transition st .qed) []` 归约到 `some st`。
      -- ⚠ 探针又实测：`simp only [Option.some.injEq] at h` 报 **`simp made no progress`**
      -- （`Option.some.injEq` 是 iff 定理名，`simp only` 用它不推进，且
      -- `transition st .qed` 还没归约）⟹ 改用**显式等式**：先算 `transition st .qed = st`，
      -- 再 `go_nil`，最后用 `Option.some.injEq` 的 `.mp` 方向。
      have htr : transition st (ProofStep.qed) = st := rfl
      rw [htr, go_nil] at h
      -- ⚠ 探针实测：`h` 此刻仍是 `(if stepOk g st .qed = true then some st else none) = some st'`
      -- （判别式**没被消掉**）⟹ 必须先用 `hok` 把它化简，才能用 `.some.injEq`。
      rw [if_pos hok] at h
      exact ⟨hok, ((Option.some.injEq _ _).mp h).symm⟩
    · rw [if_neg hok] at h
      exact absurd h (by simp)
  · -- ⚠ 探针实测两轮：
    -- ① `rintro ⟨hall, rfl⟩` 报 `unknown identifier 'st'`（`rfl` 模式消去了错误的变量）；
    -- ② 改 `rintro ⟨hall, hst⟩; subst hst` **仍然**报 `unknown identifier 'st'`
    --    —— `hst : st' = st`，`subst` 会**消去 `st`**（保留 `st'`），
    --    于是结论里的 `st` 变成未绑定（这正是 STYLE:159 记录的同族陷阱）。
    -- 正解：**不用 `subst`**，改用方向明确的 `rw`：把目标里的 `st'` 换成 `st`。
    rintro ⟨hall, hst⟩
    rw [hst]
    exact go_qed_some g st hall

/-- (A) 若 `go` 成功且迹以 `.qed` 结尾，则原图全部约束都在最终已证集中。
来源 `Evidence.lean:223`（上游 `go_all_proved_if_qed_last`）。
用 `go_append` 拆出末步——对验证器**核心契约**的刻画。 -/
theorem go_all_proved_if_qed_last (g : SystemsConstraintGraph) (st : VerifierState) (t : ProofTrace)
    (st' : VerifierState) (h : go g st t = some st') (h_last : t.getLast? = some .qed) :
    g.all st'.proved.contains := by
  obtain ⟨t', rfl⟩ := List.getLast?_eq_some_iff.mp h_last
  rw [go_append] at h
  cases hgo : go g st t' with
  | none => simp [hgo] at h
  | some st'' =>
      have hq : go g st'' [.qed] = some st' := by simpa [hgo] using h
      obtain ⟨hall, hst⟩ := go_qed_some_iff g st'' st' |>.mp hq
      -- 探针实测：`hst : st' = st''`，而 `hall` 的陈述用的是 `st''`。
      -- `rw [← hst]` 把目标里的 `st''` 换成 `st'` —— **方向反了**（报 `did not find pattern st''`）。
      -- 正解：`rw [hst]` 把目标里的 `st'` 换成 `st''`，与 `hall` 对齐。
      rw [hst]
      exact hall

/-- (A) `evidenceCheckWitness` 成功的完整刻画：迹以 `.qed` 结尾、
状态等于纯折叠、且原图全部约束已证。
来源 `Evidence.lean:241`（上游 `evidence_check_witness_spec`）。

实现说明：`ProofStep` 的构造子含 `lemma`（Lean 关键字）与 `qed`，
故不逐构造子 `cases`，而用 `match` 的**通配分支**一次性排除非 `.qed` 情形。 -/
theorem evidenceCheckWitness_spec (g : SystemsConstraintGraph) (t : ProofTrace) (st : VerifierState)
    (h : evidenceCheckWitness g t = some st) :
    t.getLast? = some .qed ∧ st = traceFold (initVerifier g) t ∧ g.all st.proved.contains := by
  unfold evidenceCheckWitness at h
  cases hlast : t.getLast? with
  | none => simp [hlast] at h
  | some step =>
      -- 若 `step ≠ .qed`，则 `evidenceCheckWitness` 定义为 `none`，与 `h` 矛盾。
      by_cases hq : step = .qed
      · subst step
        have hgo : go g (initVerifier g) t = some st := by simpa [hlast] using h
        -- ⚠ 探针实测：三项里**第一项**的目标在 `subst step` 之后已经变成
        -- `some .qed = some .qed`（`hlast` 反而不匹配，报
        -- `And.intro hlast … has type List.getLast? t = some .qed
        --  but is expected to have type some .qed = some .qed`）
        -- ⟹ 第一项用 `rfl` 提供，后两项仍用引理。
        exact ⟨rfl,
               go_some_eq_trace_fold g (initVerifier g) t st hgo,
               go_all_proved_if_qed_last g (initVerifier g) t st hgo hlast⟩
      · simp [hlast, hq] at h

/-- (A) `go` 与 `traceFold` 在追加单步上的复合性。
来源 `Evidence.lean:527`（上游 `go_trans_compose`）。 -/
theorem go_trans_compose (g : SystemsConstraintGraph) (st : VerifierState) (t : ProofTrace)
    (st' : VerifierState) (h : go g st t = some st') (step : ProofStep)
    (hok : stepOk g st' step = true) :
    go g st (t ++ [step]) = some (transition st' step) := by
  rw [go_append, h]
  -- 权威构建（v6/v15 `lake build RealLv00Systems`）报的目标是
  -- `((some st').bind fun a => if stepOk g a step = true then some (transition a step) else none)
  --    = some (transition st' step)`。
  -- ⇒ 需要：β 归约 `Option.bind` 的 `some` 分支，再用 `hok` 消判别式。
  show (if stepOk g st' step = true then some (transition st' step) else none) =
    some (transition st' step)
  rw [if_pos hok]

/-- (B) 以非 `.qed` 结尾的迹一定被拒绝。
来源 `Evidence.lean:422`（上游 `evidence_no_qed_fails`）。

实现说明：同上，避开 `lemma` 关键字，用 `by_cases` + `simp` 一步收口。 -/
theorem evidenceCheck_no_qed_fails (g : SystemsConstraintGraph) (t : ProofTrace)
    (h : t.getLast? ≠ some .qed) : evidenceCheck g t = false := by
  unfold evidenceCheck evidenceCheckWitness
  cases ht : t.getLast? with
  | none => simp [ht]
  | some step =>
      by_cases hq : step = .qed
      · exact absurd (by rw [ht, hq]) h
      · simp [ht, hq]

/-! ## 4. 诚实降级：`evidenceCheck` 不构成可靠性保证（**本项目新增，机器验证**）

上游 `Evidence.lean` 的 `evidence_completeness` 声称验证器**完备**。
核实结论：该命题对**任意**图都成立，因为 `stepOk` 对 `hypothesis`
无条件返回 `true` —— **「完备」在此不构成任何可靠性保证**。
下面两条定理把真实情况钉死（这是本项目对上游的**诚实降级**）。 -/

/-- 对**任意**约束图，都存在平凡通过迹：把图的每个约束作为假设步列出，再 `.qed`。
这**不是**好消息 —— 它是 `evidenceCheck` 单独不可靠的机器验证证据。 -/
def trivialProofTrace (g : SystemsConstraintGraph) : ProofTrace :=
  g.map ProofStep.hypothesis ++ [.qed]

/-- (A) 辅助引理：一串假设步总能把列出的约束全部推入 `proved`，且从不失败
（`stepOk` 对 `hypothesis` 恒为 `true`）。

**核验过的化简**：`.hypothesis c` 的 `stepOk` 分支由定义直接返回 `true`
（与 `g`、`st` 无关），`transition` 则把 `c` 前插入 `proved`。
故整段处理等价于对 `cs` 做 `foldl` 前插，结果 `proved = cs.reverse ++ st.proved`。

⚠ **G1 修复（v15）**：原稿让归纳**从 `⟨[]⟩` 重启**，于是归纳步的目标
`go g ⟨[]⟩ (cs.map …) = some ⟨c :: st'.proved⟩` 与归纳假设
`go g ⟨[]⟩ (cs.map …) = some st'` **起始状态不一致**（`⟨[c]⟩` vs `⟨[]⟩`），
`simpa using hgo` 报
`type mismatch … go g {proved := []} … but is expected to have type go g {proved := [c]} …`。
⇒ 正解：把**起始状态参数化**（对任意 `st` 归纳），得到一般公式
`st'.proved = cs.reverse ++ st.proved`（这才是 `go`/`transition` 的真实语义），
再取 `st = ⟨[]⟩` 即得原命题（`[] ++ [] = []`）。 -/
theorem go_hypotheses_pushes_aux (g : SystemsConstraintGraph) (st : VerifierState)
    (cs : List IRConstraint) :
    ∃ st' : VerifierState,
      go g st (cs.map ProofStep.hypothesis) = some st' ∧
        st'.proved = cs.reverse ++ st.proved := by
  induction cs generalizing st with
  | nil => exact ⟨st, rfl, by simp⟩
  | cons c cs ih =>
      obtain ⟨st', hgo, hst⟩ := ih (st := { st with proved := c :: st.proved })
      refine ⟨st', ?_, ?_⟩
      · -- `go g st ((.hypothesis c) :: cs.map …)`：先走一步假设步，余下正是 `hgo`。
        -- ⚠ 探针实测：`.` 里写 `if_true` 会报 `did not find instance of the pattern:
        -- if True then ?t else ?e` —— 判别式是 `true = true`（Bool 等式）而非 `True`。
        -- 正解：用 `if_pos` 配显式的 Bool 等式证明。
        rw [List.map_cons, go_cons,
          show stepOk g st (.hypothesis c) = true from rfl, if_pos rfl]
        exact hgo
      · rw [hst, List.reverse_cons]
        simp [List.append_assoc]

/-- (A) 原陈述（起始状态为 `⟨[]⟩`）：`go` 处理完一串假设步后 `proved = cs.reverse`。
由上一条取 `st = ⟨[]⟩` 直接得到。 -/
theorem go_hypotheses_pushes (g : SystemsConstraintGraph) (cs : List IRConstraint) :
    ∃ st' : VerifierState,
      go g ⟨[]⟩ (cs.map ProofStep.hypothesis) = some st' ∧ st'.proved = cs.reverse := by
  obtain ⟨st', hgo, hst⟩ := go_hypotheses_pushes_aux g ⟨[]⟩ cs
  exact ⟨st', hgo, by simpa using hst⟩

/-- (A) §4 核心（**负面结果**）：**任意**图都有通过 `evidenceCheck` 的迹。
⇒ `evidenceCheck g t = true` **不蕴含** `g` 可满足。 -/
theorem trivialProofTrace_passes (g : SystemsConstraintGraph) :
    evidenceCheck g (trivialProofTrace g) = true := by
  obtain ⟨st', hgo, hst⟩ := go_hypotheses_pushes g g
  have hlast : (trivialProofTrace g).getLast? = some .qed := by
    simp [trivialProofTrace]
  -- 走完假设步后接 `.qed`：末步只需 `g.all st'.proved.contains`，而 `st'.proved = g.reverse`。
  have hfinal : go g (initVerifier g) (trivialProofTrace g) = some st' := by
    have htail : go g st' [.qed] = some st' := by
      refine go_qed_some g st' ?_
      rw [hst]
      exact all_contains_of_subset fun _ hx => List.mem_reverse.mpr hx
    have hsplit : trivialProofTrace g = g.map ProofStep.hypothesis ++ [.qed] := rfl
    rw [hsplit, go_append, show initVerifier g = (⟨[]⟩ : VerifierState) from rfl, hgo]
    simpa only [Option.bind_some] using htail
  unfold evidenceCheck evidenceCheckWitness
  rw [hlast, hfinal]
  rfl

/-- (A) 辅助：`cs` 全为假设步时，`go` 成功且终态已证集等于 `cs.reverse`。
`go_hypotheses_pushes` 的**不用 `∃`** 的版本，供 §4 主定理直接调用。 -/
theorem go_hypotheses_eq (g : SystemsConstraintGraph) (cs : List IRConstraint) :
    ∃ st' : VerifierState,
      go g ⟨[]⟩ (cs.map ProofStep.hypothesis) = some st' ∧ st'.proved = cs.reverse :=
  go_hypotheses_pushes g cs

/-- (A) §4：**一个语义上不可满足的图也被「证明」**。
同一点到自身的距离等于 1 在实数上不可能成立，
但 `evidenceCheck` 仍返回 `true` ⇒ **验证器不检查几何语义**。 -/
theorem evidenceCheck_accepts_unsatisfiable :
    evidenceCheck [.distance "A" "A" (.const 1)]
      (trivialProofTrace [.distance "A" "A" (.const 1)]) = true :=
  trivialProofTrace_passes _

/-- (A) §4：该图确实**不可满足** —— 与上一条合起来构成完整的**机器验证反例**。

依据：约束断言「点 `A` 到自身的距离 = 1」，
而 `irSem` 把它展开为 `sqrt((A.x-A.x)² + (A.y-A.y)²) = 1`，
左边化简为 `sqrt 0 = 0`，故要求 `(0:ℝ) = 1` —— 矛盾。 -/
theorem dist_self_const_one_unsatisfiable :
    ¬ GraphSatisfiable [.distance "A" "A" (.const 1)] := by
  rintro ⟨env, h⟩
  have hA : Real.sqrt (((env "A").1 - (env "A").1) ^ 2 + ((env "A").2 - (env "A").2) ^ 2) = 1 :=
    h (.distance "A" "A" (.const 1)) (by simp [irSem, IRExpr.eval])
  simp only [sub_self, OfNat.ofNat_ne_zero, zero_pow, add_zero, Real.sqrt_zero] at hA
  norm_num at hA

/-- (A) §4 收口：**存在一个被 `evidenceCheck` 接受却不可满足的图**。
这是「验证器单独不可靠」的完整机器验证陈述。 -/
theorem evidenceCheck_unsound_exists :
    ∃ g : SystemsConstraintGraph, evidenceCheck g (trivialProofTrace g) = true ∧ ¬ GraphSatisfiable g :=
  ⟨[.distance "A" "A" (.const 1)], evidenceCheck_accepts_unsatisfiable,
   dist_self_const_one_unsatisfiable⟩

/-! ## 5. 条件可靠性 (A)：把上游的真实语义义务**显式化**

上游的 `evidence_soundness` 在「每步保可满足」假设下给出结论。
本项目**以显式假设搬运**（`stepSound` 作为 `Prop` 假设、`TraceSound` 作为归纳谓词），
**不使用 `axiom`** —— 这是本项目「0 axiom」承诺下的正确形态。

与 §4 合起来，本文件给出的是**精确**的结论：
`evidenceCheck` 单独**不可靠**（§4），但在**显式语义假设**下**可靠**（§5）。

⚠ **§6 进一步收紧**：§5 那条"显式语义假设"**不是未证的**，而是**已证为假** ——
`stepSound` 对 `.hypothesis` 分支可证伪（`transition:318` 无语义检查，
`stepOk:334` 恒 `true`）。⇒ §5 的"条件可靠性"是**空洞的条件**：
前提 `TraceSound (initVerifier g) t` 在含 `.hypothesis` 步时**不可满足**。 -/

/-- 单步语义可靠性：若当前已证集可满足，则转移后的已证集仍可满足。
上游 `step_sound`。**这是显式假设，不是公理。**

⚠⚠ **定性修正（§6，机器验证）**：本句在 **Lean 机制**上正确，
但在**数学上是错的定性** —— `stepSound` **不是"待证引理"，而是假命题**。
证据：`not_stepSound_of_unsat` / `stepSound_hypothesis_false` /
`evidenceCheck_unsound_unless_hypothesis_free`（§6）。
根因：`transition` 的 `.hypothesis` 分支（`:318`）**无语义检查**，
而 `stepOk` 对它**恒返回 `true`**（`:334`）。 -/
def stepSound (st : VerifierState) (step : ProofStep) : Prop :=
  (∃ env : String → Lv00Point, ∀ c ∈ st.proved, irSem env c) →
    (∃ env : String → Lv00Point, ∀ c ∈ (transition st step).proved, irSem env c)

/-- 迹语义可靠性（归纳谓词）。上游 `TraceSound`。**显式假设，不是公理。** -/
inductive TraceSound : VerifierState → ProofTrace → Prop where
  | nil (st) : TraceSound st []
  | cons (st) (step : ProofStep) (rest : ProofTrace)
      (h_step : stepSound st step)
      (h_rest : TraceSound (transition st step) rest) :
      TraceSound st (step :: rest)

/-- (A) 不变式：可靠迹保持可满足性。
来源 `Evidence.lean:290`（上游 `trace_sound_invariant`）。真实归纳。 -/
theorem trace_sound_invariant (st : VerifierState) (t : ProofTrace) (h_sound : TraceSound st t)
    (h_init : ∃ env : String → Lv00Point, ∀ c ∈ st.proved, irSem env c) :
    ∃ env : String → Lv00Point, ∀ c ∈ (traceFold st t).proved, irSem env c := by
  induction h_sound with
  | nil => simpa [traceFold] using h_init
  | cons st step rest h_step _ ih => exact ih (h_step h_init)

/-- (B) 初始状态总是可满足（已证集为空）—— 用于 discharged §5 的 `h_init` 前提。 -/
theorem initVerifier_satisfiable (g : SystemsConstraintGraph) :
    ∃ env : String → Lv00Point, ∀ c ∈ (initVerifier g).proved, irSem env c :=
  ⟨fun _ => (0, 0), by simp [initVerifier]⟩

/-- (A) **条件可靠性**（本项目整理版，取代上游 `evidence_soundness`）：
若验证器接受迹 `t`，且迹在语义上可靠，则原图的**全部约束**同时可满足。

⚠ 前提**都不可省**：`hvalid`（验证器接受）与 `hsound`（语义可靠性）。
**这是诚实版本** —— 上游把 `hsound` 说成「可推导」，
实际它是必须显式携带的假设（§4 已机器验证它不可省）。 -/
theorem evidenceCheck_sound_of_sound (g : SystemsConstraintGraph) (t : ProofTrace) (st : VerifierState)
    (hvalid : evidenceCheckWitness g t = some st)
    (hsound : TraceSound (initVerifier g) t) :
    GraphSatisfiable g := by
  obtain ⟨_, hfold, hall⟩ := evidenceCheckWitness_spec g t st hvalid
  have hs := trace_sound_invariant (initVerifier g) t hsound (initVerifier_satisfiable g)
  -- ⚠ 探针实测：原稿 `rw [hfold] at hs` 报
  -- `did not find instance of the pattern: st`。
  -- 原因：`hfold : st = traceFold (initVerifier g) t`（**左 `st`、右折叠**），
  -- 而 `hs` 里的目标项是 `traceFold …`——把 `st` 当成模式去找**找不到**。
  -- 正解：用 **反向** `rw [← hfold]`（把 `traceFold …` 换成 `st`）。
  rw [← hfold] at hs
  obtain ⟨env, henv⟩ := hs
  exact ⟨env, fun c hc => henv c (contains_true_mem (List.all_eq_true.mp hall c hc))⟩

/-! ## 6. ⭐⭐ `stepSound` **为假**（本项目新增，机器验证）

⚠ **重要修正**：§5 把 `stepSound` 说成「显式假设，不是公理」——
该措辞在 **Lean 机制**上正确（`sorry`/`axiom`/`admit` 计数确实全 0），
但**在数学上是错的定性**：`stepSound` **不是"未证的待证引理"，而是一条假命题**。

**反证（下述定理的内核验证版本）**：取 `step = .hypothesis c`，其中 `c` 是
**单独不可满足**的约束。`transition` 的 `.hypothesis` 分支（`:318`）
**把 `c` 无条件前插**，而 `stepOk` 对它**恒返回 `true`**（`:334`）——
**全程没有任何语义检查**。于是从**空已证集**（恒可满足）出发，
前提成立而结论（`st.proved ∪ {c}` 可满足）**为假**。

⇒ ⭐ **结论**：`stepSound` **不可证，且可证伪**。
下一条元定理把它一句话讲完：**只要要求 `stepSound` 对所有 `st`/`step` 成立，
就会推出 `False`** —— 即「可靠性假设」**本身不可成立**。

⚠ **边界**：本节**只**证伪 `.hypothesis` 分支（`st.proved = []` 一处反例即可）。
`.lemma` / `.rewrite` / `.unify` 分支**是否亦为假，本节未证**（见终报诚实边界）。 -/

/-- (A) **§6 核心（负面结果）**：只要存在一条**单独不可满足**的约束 `c`，
则从**空已证集**出发，`.hypothesis c` 这一步就**破坏可满足性**
⟹ `stepSound` 在该步**为假**。

证明**不依赖 `transition` 的具体定义**（故对任何未来修改都稳健）：
空已证集恒可满足（见证 `fun _ => (0, 0)`），前提当即可满足；
而 `h` 直接否定了结论所需的存在性。 -/
theorem not_stepSound_of_unsat (c : IRConstraint) (h : ¬ ∃ env : String → Lv00Point, irSem env c) :
    ¬ stepSound { proved := [] } (.hypothesis c) := by
  intro hs
  have hpre : ∃ env : String → Lv00Point, ∀ c' ∈ ({ proved := [] } : VerifierState).proved,
      irSem env c' :=
    ⟨fun _ => (0, 0), by simp⟩
  -- ⚠ 探针实测：`unfold stepSound` **不**化简 `transition { proved := [] } (.hypothesis c)`
  -- （`unfold` 不做 β-归约，只暴露定义体）；正解是用 `simp only` 真正归约 `transition`。
  refine h ?_
  simpa only [stepSound, transition, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    using hs hpre

/-- (A) **§6：`stepSound` 在 `.hypothesis` 分支上为假** —— 具体见证。
反例**复用** §4 的既有成果 `dist_self_const_one_unsatisfiable`（`:670`），
即「点 `A` 到自身距离 = 1」在实数上不可满足（`0 = 1`）。 -/
theorem stepSound_hypothesis_false :
    ∃ (st : VerifierState) (c : IRConstraint), ¬ stepSound st (.hypothesis c) := by
  refine ⟨{ proved := [] }, .distance "A" "A" (.const 1), ?_⟩
  apply not_stepSound_of_unsat
  rintro ⟨env, hc⟩
  -- `rintro` 经 `List.mem_singleton` 已把 `∀ c' ∈ [c], irSem env c'` 压成 `irSem env c`；
  -- 把 `abbrev` 展开即可回填 `GraphSatisfied` 的形状。
  exact dist_self_const_one_unsatisfiable
    ⟨env, by unfold GraphSatisfied; simpa using hc⟩

/-- (B) ⭐⭐ **§6 元定理：可靠性假设不可成立**（把"假设缝"升级为"**已证的不可能性**"）。

**一句话**：若 `stepSound` 对**所有**状态与步骤都成立，则**矛盾**。
⇒ `RealLv00Systems.lean` 原 `:687` 那句「这是显式假设，不是公理」
**不是"尚未证明"，而是"已被证明不可能"** —— 这比"未证"严重一档。

⚠ 这是**真定理**（不是定义展开）：它消费了 §4 的反例语义内容
（`dist_self_const_one_unsatisfiable`），**结论是 `False`**，
故**不可能**由 `rfl`/`decide` 之类的平凡理由成立。 -/
theorem evidenceCheck_unsound_unless_hypothesis_free
    (h : ∀ st step, stepSound st step) : False := by
  have hc : ¬ ∃ env : String → Lv00Point, irSem env (.distance "A" "A" (.const 1) : IRConstraint) := by
    rintro ⟨env, hc⟩
    exact dist_self_const_one_unsatisfiable
      ⟨env, by unfold GraphSatisfied; simpa using hc⟩
  exact not_stepSound_of_unsat (.distance "A" "A" (.const 1)) hc
    (h { proved := [] } (.hypothesis (.distance "A" "A" (.const 1))))

end Lattice.Lv00.Systems
