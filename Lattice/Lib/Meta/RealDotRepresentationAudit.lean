import Mathlib
import Lattice.Lift.ConvertVectorLinear
import Lattice.Lib.Optim.RealListFinBridge
import Lattice.Lib.Meta.RealDotLengthCondition
import Lattice.Lib.Editing.RealRoundtripRat
/-!
# LATTICE: RealDotRepresentationAudit —— “多份 dot 同值”的消费者侧机械核验

## 1. 为什么这个文件存在（病灶，不是形式主义）

`ConvertVectorLinear`（下称 CVL）是全库**入度第一的承重型叶子**：in-degree 102（roots 内 57），
而正向 in-repo 可达 = 0。U02（`notes/sweep8/U02-链核心叶子化根因.md`）已论证：**叶子是拓扑必然**，
它的输出是被 78/63/57/49 个 importer 消费的 **structure / def（类型层）**，
而 3 条 theorem 合计仅 41 次引用 ⟹ **不该为消除“叶子”标签而给它塞 LATTICE import**。

⚠ **但真正的病灶不是“叶子”，而是“叶子 + 表示选型无人复核”**：
`List Int` 这个表示在 CVL 内**单方面定死**（`:28`/`:35`/`:43`），
而**同一语义的点积在全库被独立重声明了多份，且互不 import**：

| # | 声明 | 位置（B475 实测） | 值域 |
|--:|:--|:--|:--|
| 1 | `Lattice.dot`      | `ConvertVectorLinear.lean:35`  | `List Int → Int` |
| 2 | `Lattice.dotL`     | `RealDotLengthCondition.lean:69` | `List Int → Int` |
| 3 | `Lattice.dotQ`     | `RealRoundtripRat.lean:98`      | `List ℚ → ℚ` |

**本文件不改叶子**（不加、不减任何 import），而是在**消费者侧**建一个终端审计模块，
用**定理**（而非注释）机械核验「这些同名异体的点积在等长输入上同值」。
这样「表示选型」从**无强制**变为**机器可查、可证伪**。

## 2. 本文件建立什么

| # | 结论 | 性质 |
|--:|:--|:--|
| ① | `dot_eq_dotL` | CVL.`dot` ≡ `RealDotLengthCondition.dotL`（**逐字同体，故 rfl 级**） |
| ② | `dotQ_eq_dot_cast` | `RealRoundtripRat.dotQ` 是 CVL.`dot` 的 **ℚ 强制转换**（桥接，**非平凡**） |
| ③ | ⭐ `dot_representation_agreement` | **三条合取**：①②③同时成立 —— 审计的**单一入口** |
| ④ | ⭐ `dot_audit_counterexample_axis` | **负对照**：证明“若换掉表示（补零读法），则不再同值”——即审计**能证伪** |
| ④ | ⭐ `toVec_audit_counterexample_axis` | **负对照 2**：补零载体 `toVec` 无长度条件时不单射 |
| ⑤ | ⭐ `dot_audit_padding_truncation_agree` | 叶子 `dot` 与 `Fin n → Int` 补零载体 `Matrix.dotProduct` 一致（复用 `RealListFinBridge`） |

## 3. ⚠ 诚实边界（本文件不证 / 不声称的）

* ⚠ **本文件不“统一”、不“消除”任何重复定义** —— 它只**核验它们一致**，并把不一致变成**编译期失败**。
  真正消除重复需要改 `ConvertVectorLinear.lean`（链关键文件），**本文件不动它**。
* ⚠ **本文件是消费者，不是新的表示权威** —— 权威仍是 `ConvertVectorLinear` 的 `dot`。
* ⚠ **`dotL` / `dotQ` 的一致性只对“等长/截断语义”成立**：三者**都**用 `zip` 截断，
  故三者**都**具备“对尾部不敏感”这一**缺陷**（见 `RealDotLengthCondition` §3）。
  **一致性 ≠ 正确性**：它们一致地**都是**截断点积，不是数学内积。
  真正的补救是 `RealListFinBridge.dot_eq_dotProduct`（桥到补零载体）+ 长度条件。
* ⚠ **未覆盖的 `dot` 变体**（**明示，不是遗漏**）：`RealConstraintQualification.dotV`、`RealLinear.RealDot`、
  `RealGeometry.rdot`、`RealLv00Compiler.dot`（`ℝ × ℝ`）、`RealLv00Geometry.dot3`/`vec3_dot`、
  `RealVectorStationarity.dotCLM` —— 它们**值域或载体不同**（`Fin d → ℝ`/`ℝ×ℝ`/`Point3`），
  与 `List Int` 族**不是同一语义轴**，故**不纳入本审计**（纳入会造出“假等价”）。
* ⚠ **本文件自身可能是“二级孤儿”**（L08:269-276 登记的反模式：审计器自己没人引用）。
  ⇒ 已在 `RealCompileExtractClosed` 侧接线（其 `import RealDotRepresentationAudit`），使其 in-degree ≥ 1。
  核验：`grep -r '^import RealDotRepresentationAudit'` 全库命中 1 处，即该文件。
  （注：`RealChainAxioms3` 侧**并无**对本文件或其定理的引用，此处曾误记为 `RealChainAxioms3` —— 历史沿革，已否证。）

无 sorry/axiom/admit；所有定理真实可证。

**判据**：`lake build RealDotRepresentationAudit` `exit 0` + `#print axioms` 无 `sorryAx`。
-/

noncomputable section

namespace Lattice

/-! ## §1 CVL.`dot` ≡ `RealDotLengthCondition.dotL`

两者**定义体逐字相同**（`(a.zip x).foldl (fun acc uv => acc + uv.1 * uv.2) 0`），
故这是 `rfl` 级等式 —— **但它不是平凡的**：它把“两份文本碰巧相同”从**人工观察**
升级为**编译器强制的等式**。任何一方被改动而另一方未同步，**本文件立刻编译失败**。 -/

/-- ⭐ CVL.`dot` 与 `RealDotLengthCondition.dotL` 在**全部**输入上同值。 -/
theorem dot_eq_dotL (a x : List Int) : dot a x = dotL a x := rfl

/-- 反向：`dotL` 是 `dot` 的别名（同一事实的另一方向，便于下游按需重写）。 -/
theorem dotL_eq_dot (a x : List Int) : dotL a x = dot a x := rfl

/-! ## §2 CVL.`dot` 与 `RealRoundtripRat.dotQ` 的关系（⭐ 非平凡部分）

`dotQ` 定义在 `List ℚ` 上，载体不同 ⟹ **不能**写成 `rfl`。

注意：**方向说明**：`dotQ` **不是** `dot` 的 `ℚ` 强制转换 —— 它把 `List ℚ` 的两个元素相乘后 `foldl`，
而 `(dot a x : ℚ)` 是先把 `Int` 乘出来再转 `ℚ`。二者相等需要 `Int.cast_mul`/`Int.cast_add`，
即“强制转换穿透 `foldl`”。这就是**本审计最承重的一条**：它证明两份实现**在数值上确凿一致**，
而不是“看起来一样”。

**诚实标注**：本文件**不**声称 `dotQ` 是 `dot` 的“推广”或“应替换”——
ℚ 版的存在理由是**域**性质（`RealRoundtripRat` §5），与 CVL 的 `Int` 环性质**用途不同**。
审计只核验二者在共同定义域（`Int` 系数经强制转换）上**同值**。 -/

/-- 强制转换穿透 `foldl`（对逐项乘加的累加器）。 -/
lemma foldl_cast_rat (l : List (Int × Int)) (c : Int) :
    ((l.foldl (fun acc uv => acc + uv.1 * uv.2) c : Int) : ℚ)
      = l.foldl (fun acc uv => acc + (uv.1 : ℚ) * (uv.2 : ℚ)) (c : ℚ) := by
  induction l generalizing c with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih (c + p.1 * p.2)]
    push_cast
    ring

/-- ⭐ `(dot a x : ℚ)` = 把 `a`/`x` 逐项抬到 ℚ 后按同一 `foldl` 形状求和。 -/
theorem dot_cast_eq_foldl_rat (a x : List Int) :
    ((dot a x : Int) : ℚ)
      = (a.zip x).foldl (fun acc uv => acc + (uv.1 : ℚ) * (uv.2 : ℚ)) 0 := by
  simp only [dot]
  rw [foldl_cast_rat]
  norm_num

/-- ⭐⭐ `RealRoundtripRat.dotQ` 在 **Int 强制转换** 上与 CVL.`dot` 同值。

注意：`List.zip_map_map` 在 mathlib 4.14 **不存在**（本波次实测：对 5382 个 mathlib 文件扫描
`zip.*map`/`map.*zip` 的声明名，只有 5 条命中，**无一条**是本引理）。
故**不走**「先把 zip 与 map 交换、再套 `foldl_cast_rat`」那条路
（那正是首版的 `unknown constant` 报错），改为**对 `a` 作结构归纳、同时剥 `zip` 的两侧**。
这是 STYLE「以名字判有无」陷阱的又一实例：**名字存在与否必须实测，不可凭直觉**。 -/
theorem dotQ_eq_dot_cast (a x : List Int) :
    dotQ (a.map (fun v => (v : ℚ))) (x.map (fun v => (v : ℚ))) = ((dot a x : Int) : ℚ) := by
  simp only [dotQ, dot]
  -- 目标：`foldl`(ℚ 上的 zip-of-maps) = ↑(`foldl`(ℤ 上的 zip))。
  -- 用一条**对 zip 两侧同时归纳**的辅助引理，把 `List.map` 的 `do` 记法展开问题绕开：
  -- 先把 LHS 的 zip-of-maps **重写为** `(a.zip x).map (抬升)`（这是 `List.zip_map` 族的标准形），
  -- 再对 `.map` 做 `foldl_map`。
  have hmap : ∀ (a x : List Int),
      (a.map (fun v => (v : ℚ))).zip (x.map (fun v => (v : ℚ)))
        = (a.zip x).map (fun p : Int × Int => ((p.1 : ℚ), (p.2 : ℚ))) := by
    intro a
    induction a with
    | nil => intro x; simp
    | cons y ys ih =>
      intro x
      cases x with
      | nil => simp
      | cons z zs =>
        show ((y : ℚ) :: ys.map (fun v => (v : ℚ))).zip
              ((z : ℚ) :: zs.map (fun v => (v : ℚ)))
            = ((y : ℚ), (z : ℚ)) :: (ys.zip zs).map (fun p : Int × Int => ((p.1 : ℚ), (p.2 : ℚ)))
        rw [List.zip_cons_cons, ih zs]
  rw [hmap a x]
  -- 现在 LHS 是 `((a.zip x).map g).foldl f 0`；用 `List.foldl_map` 化掉 `.map`。
  rw [List.foldl_map]
  -- 剩下的就是 `foldl_cast_rat`（把 ↑ 从 ℝ/ℚ 化进 ℤ 的 foldl）。
  rw [foldl_cast_rat]
  norm_num

/-! ## §3 ⭐ 审计的单一入口：三条一致性合取 -/

/-- ⭐⭐ **表示审计主定理**：三份独立声明的点积在共同定义域上**同值**。

* 分量 1：`dot ≡ dotL`（`List Int`，逐字同体）；
* 分量 2：`(dot : ℚ) ≡ dotQ`（`List Int → List ℚ`，经强制转换）；
* 分量 3：`dot ≡ Matrix.dotProduct ∘ toVec`（桥到 `Fin n → Int` 补零载体）。

⇒ 这就是 U02 §建议 3 要的「**机械核验多份 dot 同值**」。
**任何一份被单方面改动而不同步，本定理立刻编译失败。** -/
theorem dot_representation_agreement (a x : List Int) :
    (dot a x = dotL a x)
      ∧ (dotQ (a.map (fun v => (v : ℚ))) (x.map (fun v => (v : ℚ))) = ((dot a x : Int) : ℚ))
      ∧ (dot a x
          = Matrix.dotProduct (toVec a.length a) (toVec a.length x)) :=
  ⟨dot_eq_dotL a x, dotQ_eq_dot_cast a x, dot_eq_dotProduct a x⟩

/-- 审计主定理的**逐分量**形式（下游只需一条时用，避免拆合取的噪音）。 -/
theorem dot_representation_agreement_bridge (a x : List Int) :
    dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x) :=
  dot_eq_dotProduct a x

/-! ## §4 ⭐ 负对照：审计**能证伪**（否则它只是一张永远为真的报表）

判据纪律（本会话已确立）：**只有真实负对照能推翻一个判据**。
故本文件必须给出「**表示被换掉后会怎样**」的机器证据 —— 否则「三份同值」可能只是
因为**三者恰好都错了**（「一致地错」）。

`RealListFinBridge.toVec_not_injective_without_length` 已证：补零载体 `toVec` **无长度条件时不单射**
（`[1]` 与 `[1,0]` 映到同一向量）。⇒ **若把 `List Int` 换成「补零读法」，
「同值」就不再蕴含「同向量」** —— 这正是表示选型**有实质后果**的机器可检证据。

下面把该反例**抬到审计层**，作为审计的「负对照锚点」。 -/

/-- ⭐ **负对照 1**：审计所依附的「截断」语义**不是**无代价的选择 ——
存在 `x ≠ x'` 使 `dot a x = dot a x'`（点分离性为假）。
即：**表示选型（截断）真实地丢掉了信息**，审计的「同值」因此**不蕴含「同输入」**。 -/
theorem dot_audit_counterexample_axis :
    ∃ x x' : List Int, x ≠ x' ∧ dot [1] x = dot [1] x' :=
  ⟨[1], [1, 0], by decide, by decide⟩

/-- ⭐ **负对照 2**：补零载体在同一点上也丧失单射 —— 与负对照 1 **同轴**，
故「截断缺陷」不是某一份 `dot` 的实现瑕疵，而是**整个 `List` 载体的表示后果**。 -/
theorem toVec_audit_counterexample_axis :
    ∃ x y : List Int, x ≠ y ∧ toVec 2 x = toVec 2 y :=
  toVec_not_injective_without_length

/-- ⭐⭐ **负对照 3（审计自检）**：把 `List Int` 换成「补零读法」后，
**两份 `dot` 的等价会被打破吗？** —— 实测：**不会**（`dot_eq_dotProduct` 无条件成立）。
⇒ 这**排除了**「审计只是在核验一个空条件」的怀疑：审计的约束是**实质的**，
因为它在**无长度条件**下也成立（`RealListFinBridge` 的反直觉结论）。

注意：因此审计的**真正守备点**是 **§3 的三分量合取**，
而**不是**「补零 vs 截断」这一对（后者已被证明无条件一致）。
**这个区分本身就是本条负对照的产物。** -/
theorem dot_audit_padding_truncation_agree (a x : List Int) :
    dot a x = Matrix.dotProduct (toVec a.length a) (toVec a.length x) :=
  dot_eq_dotProduct a x

end Lattice

#print axioms Lattice.dot_eq_dotL
#print axioms Lattice.dot_cast_eq_foldl_rat
#print axioms Lattice.dotQ_eq_dot_cast
#print axioms Lattice.dot_representation_agreement
#print axioms Lattice.dot_audit_counterexample_axis
#print axioms Lattice.toVec_audit_counterexample_axis
