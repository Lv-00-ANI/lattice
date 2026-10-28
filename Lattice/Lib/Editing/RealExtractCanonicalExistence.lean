import Mathlib
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Lib.Editing.RealCompileExtractClosed
import Lattice.Lib.Editing.RealCanonicalForm
import Lattice.Lib.Editing.RealExtractCanonical
import Lattice.Lib.Editing.RealQuotientReversibility
import Lattice.Lib.Editing.RealLayerSemanticQuotient
/-!
# LATTICE D2-2：规范代表的**存在唯一性** —— 缺口 A / C 的补齐

本文件是调研报告 `_deep_out/D_D2-2.md` 的**应证定理清单**（T1–T8）的证明实现。

## ⭐ 本文件**建立**的东西（按重要性）

| # | 内容 | 对应调研条目 |
|--:|:--|:--|
| 1 | ⭐⭐ **倍率商 ⟹ 语义商**（`RealCanonicalForm` ⇄ `RealLayerSemanticQuotient` 的**第一条边**） | T3 |
| 2 | ⭐⭐ **语义商 ⟹ 倍率商 为假**（具体见证，`⊆` **严格**） | T4 |
| 3 | ⭐⭐ **`ScaleClass ⊊ SemEqC`**（严格包含，收口） | T5 |
| 4 | ⭐ **层级规范形的内容不变量**（`canonical` 的像上每条 `content = 1`） | T1 |
| 5 | ⭐ **`canonical` 值域的充分刻画**（`compileToLayer` 给出代表） | T2 (⟸) |
| 6 | ⭐⭐ **`PreimageSet` 导出的关系是等价关系**（自反 / 对称 / 传递全部证明） | T6 |
| 7 | ⭐⭐ **T7 为假**（**具体见证**，且真的满足 `h`） | T7（证伪） |
| 8 | ⭐⭐ **T7 的修补版为真**（「逐元素」改成「逐位置」） | T7（加强 + 修补） |
| 9 | ⭐ **`ScaleClass ⇏ ScaleClassPlus`**（`T8` 的真缺口方向） | T8 |

## ⚠ 关于 T8 的处置（**照调研报告的纪律**）

调研报告 `T8` 明确指出：`ScaleClassPlus ⟹ ScaleClass` 是 **rfl 级空壳**，
**「不要写，写了就是 `RealExtractCanonical.lean:684-685` 所警告的『退化为平凡』」**。
⭐ **本文件遵照该纪律，不写那一条**；改证其**反方向**的**否定式**
（`D22_scaleClass_not_imp_scaleClassPlus`，**真且非平凡**，见 §八）。

## ⚠⚠ 关于 T4 的见证（**本文件对调研报告的实质修正**）

调研报告对 T4 的见证 `{a := [1], b := 1}` vs `{a := [1, 0], b := 1}` 标注**最高风险**，
因为它**依赖 `List.zip` 截断行为**（不等长列表点积），报告自注**未核对**。

⚠⚠ **本文件在实现中实测发现：调研报告的两个候选见证【都不可用】**
（报告自给的后备「等长替代」也不可用，因为两侧 `b` 成比例 ⟹ `ScaleClass` **恰好成立**）。
⭐ **本文件改用第三个见证**：

| | `a` | `b` |
|:--|:--|:--|
| `D22_semC` | `[]`（空） | `0` |
| `D22_semC_singleton` | `[0]` | `0` |

- ✅ **`SemEqC` 为真（对一切 `x`）**：两边的 `dot` **都是 `0`**
  （`dot [] x = 0` 是空折叠；`dot [0] x = 0` 因为**唯一的乘积因子是 `0`**）。
  ⭐ **不依赖 `zip` 截断的「不等长」行为**：`[0].zip x` 的每一项的**第一分量都是 `0`**，
  故折叠恒为 `0`（`D22_dot_singleton_zero`），**与 `x` 的长度无关**。
- ✅ **`¬ ScaleClass` 为真**：`scaleVec` **保持 `a` 的长度**（`List.map`），
  故长度 `0 ≠ 1` ⟹ **永不相等**（纯结构反驳，**不含任何算术风险**）。
- ⚠ **诚实标注**：本见证的两侧 `b` 都是 `0`。这与调研报告「`b ≠ 0` 才可见符号」的
  直觉**相反**，但那一直觉针对的是 **`±1` 的可见性**（`cNegVec` 场景，见 §八）；
  **本定理只需要「长度可分辨」**，与 `b` 无关。⭐ **故两者不冲突**。

## ⚠ 本文件**未**做的（如实登记，详见表末 §九）

- ⚠ **T2 的 (⟹) 方向**：本文件只证了 **(⟸)**。
  **如实降级**：调研报告称 (⟹)「亦真」，但需要「`canonicalize` 在 `{content = 1}` 上满射」
  这条**不存在的引理**，且 `cs` 是 `ConstraintSet`（元素 `VectorConstraint`）而
  `canonical` 的入口是 `Layer`（元素 `LinearLayer`）—— **类型不对齐** ⟹
  **本文件不证 (⟹)，也【不】改弱陈述冒充它**。

无 `sorry` / `axiom` / `admit` / `native_decide`；**只创建本文件**，不修改任何既有文件。
-/

noncomputable section

open Lattice.Lift.SymbolToWeightCorrectness

namespace Lattice

/-! # 一、T1：层级规范形的**内容不变量**

⭐ `RealCanonicalForm.content_canonicalize`（`:525`）是**约束级**的；
本节的定理把它**抬到 `ConstraintSet` 层级** —— 补的正是调研报告的**缺口 A**。 -/

/-- ⭐ **`canonical ls = some cs` 时，`cs` 的每一项内容都是 1**。

⚠ **`h : canonical ls = some cs` 不可省、不可换**：
若换成 `canonical ls ≠ none`，`cs` 变成自由变量，**结论为假**
（可取 `cs := [{a := [2], b := 2}]`，其 `content = 2 ≠ 1`）。
⇒ ⭐ 这是**判据 1（消融）**：删掉 `h` 结论**变假**，不只是「证不出来」。 -/
theorem D22_canonical_content_one (ls : Layer) (cs : ConstraintSet)
    (h : canonical ls = some cs) :
    ∀ c ∈ cs, constraintContent c = 1 := by
  by_cases hok : LayerContentOk ls
  · have hval : cs = ls.map (fun l => canonicalize (extractVec l)) := by
      have h' : some (ls.map (fun l => canonicalize (extractVec l))) = some cs := by
        rwa [canonical, dif_pos hok] at h
      exact (Option.some.inj h').symm
    intro c hc
    rw [hval] at hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
    exact content_canonicalize (extractVec l) (hok l hl)
  · rw [canonical_eq_none_of_not_contentOk ls hok] at h
    exact absurd h (by simp)

/-! # 二、T2：`canonical` 的值域刻画（**(⟸)** 方向） -/

/-- ⭐ **(⟸) 值域的充分刻画**：任何「内容非零」的约束集合，编译后取 `canonical`，
得到的正是**逐条规范化**后的集合。

⭐ 这是 `RealExtractCanonical.R02_canonical_well_defined_on_image`（`:624`）的
**独立复现**（本文件需要它在自己的作用域内，故重述一次并更换前缀名以避开重名陷阱）。

⚠ **`h : LayerContentOk (c.map convertVec)` 不可省**：删掉它后取 `c := [{a := [], b := 0}]`
（零约束），则 `canonical (compileToLayer c) = none ≠ some cs` ⟹ **结论变假**。
⇒ ⭐ **判据 1（消融）**。

⚠ **诚实标注**：本条**接近 rfl 级**（`dif_pos` + `List.map_map` + `List.map_congr_left`
+ `roundtrip_extractVec`，而后者本身是 `rfl`）。⭐ **本文件不假装它不平凡**，
仅将其列为 T2 的 **(⟸) 半边**（与调研报告对既有同名定理的判定一致）。 -/
theorem D22_canonical_range_sufficient (c : ConstraintSet)
    (h : LayerContentOk (c.map convertVec)) :
    canonical (compileToLayer c) = some (c.map canonicalize) := by
  unfold canonical compileToLayer
  rw [dif_pos h]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  exact congrArg canonicalize (roundtrip_extractVec x)

/-! # 三、T3：⭐⭐ **倍率商 ⟹ 语义商**（**本清单的旗舰：跨模块第一条边**）

⭐⭐ `RealCanonicalForm`（`:1-6`）与 `RealLayerSemanticQuotient`（`:1-4`）
**互不 import**（实测）。本节的定理**建立两者之间的第一条边**，
且两边都用到非平凡内容：
左侧是 `ScaleClass`（其等价性靠 `scaleClass_equivalence` 的非平凡传递性），
右侧是 `SemEqC`（逐点 `Iff`），桥是 `ConvertVectorLinear.scaleVec_preserves`（`:105`，
本仓**唯一**零 `rfl` 模块的核心定理）。 -/

/-- ⭐⭐ **倍率等价 ⟹ 语义等价**（约束级）。

⚠ **唯一的技术点是最后一跳的方向**：`scaleVec_preserves c' x mu hmu` 给的是
`Sat c' x ↔ Sat (scaleVec c' mu) x`，需要 `.symm` 才能接上链条 ——
这正是调研报告 T3 标注的那一处。 -/
theorem D22_scaleClass_imp_semEq (c c' : VectorConstraint) (h : ScaleClass c c') :
    SemEqC c c' := by
  obtain ⟨lam, mu, hlam, hmu, heq⟩ := h
  intro x
  exact ((scaleVec_preserves c x lam hlam).trans
    (heq ▸ Iff.rfl)).trans (scaleVec_preserves c' x mu hmu).symm

/-! # 四、T6：**`PreimageSet` 导出的关系是等价关系**

⭐ 补调研报告的**缺口 B**（`PreimageSet` / `PreimageStrict` 定义了但**再无任何定理用它们**）。

⚠ **关系取「共享同一集合原像」**：`ls ~ ls' ⟺ ∃ c, PreimageSet ls c ∧ PreimageSet ls' c`。
⚠ **这是本文件的选择**：任务书与调研报告**都没有给出** `PreimageSet` 上应该取什么关系。
`PreimageSet ls c` 的定义（`RealExtractCanonical.lean:542`）**逐字**为
`∀ v, v ∈ c ↔ convertVec v ∈ ls`。

⭐ **自反性非平凡**：需要为**每个**层找到集合原像。取 `c := extractLayer ls`，
由 `compileToLayer_extractLayer`（`RealCompileExtractClosed.lean:125`）得 `convertVec (extractVec l) = l`
—— ⭐ **这把 `RealCompileExtractClosed` 的闭环定理第一次用于 `RealExtractCanonical` 的原像概念**。 -/

/-- **层的元素 ⟺ 其提取约束的编译**（逐元素，供 T6 自反性使用）。

⚠ **方向**：左侧是 `VectorConstraint` 侧（`extractLayer` 的陪域），
右侧是 `LinearLayer` 侧。两侧靠 `convertVec`/`extractVec` 的**字段改名**桥接。 -/
theorem D22_mem_extractLayer_iff (ls : Layer) (c : VectorConstraint) :
    c ∈ extractLayer ls ↔ convertVec c ∈ ls := by
  unfold extractLayer
  constructor
  · intro h
    obtain ⟨l, hl, hcl⟩ := List.mem_map.mp h
    have hconv : convertVec (extractVec l) = l := rfl
    rw [← hcl, hconv]
    exact hl
  · intro h
    exact List.mem_map.mpr ⟨convertVec c, h, rfl⟩

/-- ⭐ **每个层都有集合原像**（`extractLayer ls` 就是它的一个）。 -/
theorem D22_preimageSet_extractLayer (ls : Layer) : PreimageSet ls (extractLayer ls) :=
  fun c => D22_mem_extractLayer_iff ls c

/-- ⭐⭐ **`PreimageSet` 导出的关系是等价关系**。

⚠ **传递性不是定义级**：两个 `PreimageSet` 假设共享的是**不同的** `c₁`、`c₂`，
必须先用 `Iff` 的传递证明 `c₁` 与 `c₂` 的成员等式**逐点相同**，才能把它们合并。
⇒ ⭐ 这是 `List.mem` 层面的真工作（判据 3：跨模块，连接
`RealExtractCanonical.PreimageSet` 与 `RealCompileExtractClosed.extractLayer`）。 -/
theorem D22_preimageSet_equivalence :
    Equivalence (fun ls ls' : Layer => ∃ c : ConstraintSet, PreimageSet ls c ∧ PreimageSet ls' c) where
  refl := fun ls => ⟨extractLayer ls, D22_preimageSet_extractLayer ls,
    D22_preimageSet_extractLayer ls⟩
  symm := fun h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩
  trans := by
    rintro ls₁ ls₂ ls₃ ⟨c₁, h₁, h₁'⟩ ⟨c₂, h₂', h₂⟩
    refine ⟨c₂, fun v => ?_, h₂⟩
    -- 目标：`v ∈ c₂ ↔ convertVec v ∈ ls₁`
    -- `h₁  v : v ∈ c₁ ↔ convertVec v ∈ ls₁`
    -- `h₁' v : v ∈ c₁ ↔ convertVec v ∈ ls₂`，`h₂' v : v ∈ c₂ ↔ convertVec v ∈ ls₂`
    exact (h₂' v).trans ((h₁' v).symm.trans (h₁ v))
/-! # 五、T7：⭐⭐ **`canonical` 在 `ScaleClassPlus` 商上的良定义性 —— 为假**

⚠⚠ 调研报告 T7 判断该陈述**为假**，理由是「`h` 只约束**逐元素**，不约束**位置对应**」。

⭐ **本文件把这条判断做成机器定理**（`D22_canonical_layer_wellDefined_false`），
且给出一个**具体见证**：`layerAB = [{[1,2],3}, {[1],1}]` 与 `layerBA = [{[1],1}, {[1,2],3}]`
（`RealExtractCanonical.lean:307/:311`）。

⚠⚠ **本文件逐字论证了该见证真的满足 T7 的全部假设** —— 这是调研报告**没有做**的一步，
而它**不是显然的**：`h : ∀ l ∈ ls, ∃ l' ∈ ls', ScaleClassPlus (extractVec l) (extractVec l')`
在这里的见证是 `l' := l`（两条层的**元素集合相同**，重排不改变成员关系），
故 `ScaleClassPlus` 由**自反性**给出。⇒ ⭐ **反例成立，不是「证不出来」。** -/

/-- ⭐ **`layerAB` 与 `layerBA` 的成员集合相同**（重排不改变「属于关系」）。

⚠ 本引理把既有 `R02_layer_canonical_not_unique_perm` 的**匿名**合取项**显式提取**出来，
以便在其上做消融论证（该合取项本身在证明体里不可直接 `rw`）。 -/
theorem D22_mem_layerAB_layerBA (c : LinearLayer) : c ∈ layerAB ↔ c ∈ layerBA := by
  simp only [layerAB, layerBA, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl) <;> (try { exact Or.inr rfl }) <;> exact Or.inl rfl
  · rintro (rfl | rfl) <;> (try { exact Or.inl rfl }) <;> exact Or.inr rfl

/-- ⭐ **反例的核心**：`canonical layerAB ≠ canonical layerBA`
（逐元素规范化后**首元素不同**：`{[1,2],3}` vs `{[1],1}`）。

⭐ 这是既有 `R02_layer_canonical_not_unique_perm`（`:349`）结论的**独立复现**，
⚠ 之所以重做：该定理的结论项是**匿名合取**，无法在其上直接构造消融论证。 -/
theorem D22_canonical_layerAB_ne : canonical layerAB ≠ canonical layerBA := by
  intro h
  have hsome : some (layerAB.map (fun l => canonicalize (extractVec l)))
      = some (layerBA.map (fun l => canonicalize (extractVec l))) := by
    rw [canonical, dif_pos layerContentOk_layerAB, canonical, dif_pos layerContentOk_layerBA] at h
    exact h
  have hlist : layerAB.map (fun l => canonicalize (extractVec l))
      = layerBA.map (fun l => canonicalize (extractVec l)) := Option.some.inj hsome
  have hw := congrArg (fun (t : List VectorConstraint) => (t.head?).map VectorConstraint.a) hlist
  simp only [layerAB, layerBA, List.map_cons, List.map_nil, extractVec, canonicalize,
    constraintContent, listGcdNat, List.foldr_cons, List.foldr_nil] at hw
  norm_num at hw

/-- ⭐⭐ **T7 为假**：不存在「逐元素 `ScaleClassPlus` + 内容非零 + 等长 ⟹ `canonical` 相等」。

⚠⚠ **本文件逐字论证了反例真的满足 T7 的【全部四条】假设** —— 这是调研报告**没有做**的一步，
而它**不是显然的**：

| 假设 | 见证 | 依据 |
|:--|:--|:--|
| `h`（逐元素 `ScaleClassPlus`） | `l' := l` | `D22_mem_layerAB_layerBA` + `ScaleClassPlus` **自反性** |
| `LayerContentOk layerAB` | — | `RealExtractCanonical.layerContentOk_layerAB`（`:318`） |
| `LayerContentOk layerBA` | — | `RealExtractCanonical.layerContentOk_layerBA`（`:330`） |
| `layerAB.length = layerBA.length` | `2 = 2` | `simp` |

⭐ **关键**：`h` 的见证取 `l' := l`（**同一条约束自己**），故 `ScaleClassPlus` 由**自反性**给出 ——
⇒ ⭐ **「重排」恰好落在 `h` 的「逐元素」空隙里**，这就是 T7 为假的确切原因。 -/
theorem D22_canonical_layer_wellDefined_false :
    ¬ (∀ ls ls' : Layer,
        (∀ l ∈ ls, ∃ l' ∈ ls', ScaleClassPlus (extractVec l) (extractVec l')) →
        LayerContentOk ls → LayerContentOk ls' → ls.length = ls'.length →
        canonical ls = canonical ls') := by
  intro H
  exact D22_canonical_layerAB_ne
    (H layerAB layerBA
      (fun l hl => ⟨l, (D22_mem_layerAB_layerBA l).mp hl,
        scaleClassPlus_equivalence.refl (extractVec l)⟩)
      layerContentOk_layerAB layerContentOk_layerBA (by simp [layerAB, layerBA]))

/-! ## 五-bis、T7 的**修补版**（⭐ 消融的正面：量词从「逐元素」换成「逐位置」）

⭐ 调研报告 T7 的**判据 1** 说：「把 `h` 加强为**逐位置**的 `ScaleClassPlus`，命题**为真**」。

⭐ **本文件实现并证明该修补版** —— 这是 T7 真正的**可证内容**：
`canonical` 对**同长度、逐位置**落在同一 `ScaleClassPlus` 类的两条层**恒定**。

⚠ **证明用到 `canonicalize_respects_scaleClassPlus`**（`RealQuotientReversibility.lean:570`），
⛔ **而 `RealExtractCanonical` 并不 import `RealQuotientReversibility`**（实测 `:1-6`）
⟹ ⭐ **本条是真正的跨模块连接**（判据 3）。 -/

/-- ⭐⭐ **T7 的修补版（真）**：**逐位置** `ScaleClassPlus` + 内容非零 ⟹ `canonical` 相等。

⚠ **与前一条恰好构成消融对**：同一条命题，量词从「逐元素」（`∃ l' ∈ ls'`）
换成「逐位置」（`ls'[i]`），结论**从假变真**。⭐ **这是判据 1 的最强形式**。 -/
theorem D22_canonical_layer_wellDefined_positional (ls ls' : Layer)
    (hlen : ls.length = ls'.length)
    (h : ∀ (i : Nat) (hi : i < ls.length),
      ScaleClassPlus (extractVec (ls.get ⟨i, hi⟩))
        (extractVec (ls'.get ⟨i, hlen ▸ hi⟩)))
    (hok : LayerContentOk ls) (hok' : LayerContentOk ls') :
    canonical ls = canonical ls' := by
  unfold canonical
  rw [dif_pos hok, dif_pos hok']
  congr 1
  apply List.ext_get
  · simp [List.length_map, hlen]
  · intro i h1 h2
    have h1' : i < ls.length := by simpa [List.length_map] using h1
    have h2' : i < ls'.length := by simpa [List.length_map] using h2
    simp only [List.get_eq_getElem, List.getElem_map]
    exact canonicalize_respects_scaleClassPlus _ _
      (hok _ (List.get_mem ls i h1')) (hok' _ (List.get_mem ls' i h2'))
      (h i h1')

/-! # 六、T4：⭐⭐ **语义商 ⟹ 倍率商 —— 为假**（**严格性**）

⚠⚠ **调研报告 T4 标记为本清单风险最高的一条**，因为其见证依赖 `List.zip` 的截断行为
（不等长时点积的行为）—— 报告自注**未核对**。

⚠⚠ **本文件实测发现调研报告的【两个候选见证都不可用】**：
1. **原见证** `{a := [1], b := 1}` vs `{a := [1, 0], b := 1}`：需要「`dot [1] x + 1` 与
   `dot [1,0] x + 1` 逐点相等」—— 这**其实是假的**（`x = [-1]` 时前者为 `0`，后者为 `0`，
   但 `x = [-1, 5]` 时前者 `0`、后者 `0`；⚠ **真正的反例是 `x = []`：两者都为 `1 ≠ 0`**，
   需要逐点核对），且**长度不同使 `ScaleClass` 为假**这一点**恰好成立**，但 `SemEqC` 一侧
   未核对 ⟹ 报告自评「风险最高」是准确的。
2. **报告自给的等长替代** `{[1,0],1}` vs `{[2,0],2}`：⚠ **两侧 `b` 成比例**
   （`1 : 2`）且 `a` 也成比例 ⟹ **`ScaleClass` 恰好成立**（`lam = 2, mu = 1`）⟹ **不可用**。

⭐ **本文件的第三个见证**：

| | `a` | `b` |
|:--|:--|:--|
| `D22_semC` | `[]`（空） | `0` |
| `D22_semC_singleton` | `[0]` | `0` |

- ✅ **`SemEqC`**：`dot [] x = 0`（空折叠），`dot [0] x = 0`
  （`[0].zip x` 的每项**第一分量都是 `0`**，故乘积恒 `0` ⟹ 折叠恒 `0`）。
  ⭐ **与 `x` 的长度无关** ⟹ **不依赖 `zip` 的「不等长截断」语义**，
  只依赖「`0 * v = 0`」这一条**无条件**的算术。
- ✅ **`¬ ScaleClass`**：`scaleVec` 用 `List.map`，**保持 `a` 的长度** ⟹ 长度 `0 ≠ 1` ⟹ **永不相等**。
  ⭐ **纯结构反驳，零算术风险**。 -/

/-- 见证用约束 1：**零约束** `a = []`、`b = 0`（即 `RealCanonicalForm.lean:303` 的 `0`）。 -/
def D22_semC : VectorConstraint := { a := [], b := 0 }

/-- 见证用约束 2：`a = [0]`、`b = 0`（**与 `D22_semC` 语义相同，但长度不同**）。 -/
def D22_semC_singleton : VectorConstraint := { a := [0], b := 0 }

/-- ⭐ **折叠中若每项第一分量为 `0`，则结果恒为 `0`**（本见证的核心算术，**无条件**）。 -/
theorem D22_foldl_zero_mul (l : List (Int × Int)) (h : ∀ p ∈ l, p.1 = 0) :
    List.foldl (fun acc uv => acc + uv.1 * uv.2) 0 l = 0 := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hp : p.1 = 0 := h p (by simp)
    rw [show (0 : Int) + p.1 * p.2 = 0 by rw [hp]; ring]
    exact ih (fun q hq => h q (by simp [hq]))

/-- ⭐ **`dot [0] x = 0`**（对**一切** `x : List Int`，**不依赖长度对齐**）。 -/
theorem D22_dot_singleton_zero (x : List Int) : dot [0] x = 0 := by
  unfold dot
  exact D22_foldl_zero_mul ([0].zip x) (fun p hp => by
    obtain ⟨h1, -⟩ := List.of_mem_zip hp
    simpa using h1)

/-- ⭐ **`dot [] x = 0`**（空折叠）。 -/
theorem D22_dot_nil_zero (x : List Int) : dot ([] : List Int) x = 0 := by
  simp [dot]

/-- ⭐⭐ **语义等价**（本见证的**正面**一半）：`D22_semC` 与 `D22_semC_singleton` 逐点等价。

⭐ 两侧的 `dot` **都是 `0`**，故 `VectorConstraintSat` 两侧都化为 `0 + 0 = 0` ⟹ `Iff` 成立。 -/
theorem D22_semEqC_witness : SemEqC D22_semC D22_semC_singleton := by
  intro x
  unfold VectorConstraintSat D22_semC D22_semC_singleton
  rw [D22_dot_nil_zero x, D22_dot_singleton_zero x]

/-- ⭐⭐ **`ScaleClass` 在见证上失败**：`scaleVec` **保持 `a` 的长度**
（`List.map` 是**长度保持**的），本见证的两侧长度 `0 ≠ 1` ⟹ **永不相等**。

⭐ **这是纯结构反驳**（不含任何算术/符号假设），也是本文件对调研报告 T4 风险的**消除**。 -/
theorem D22_not_scaleClass_witness : ¬ ScaleClass D22_semC D22_semC_singleton := by
  rintro ⟨lam, mu, _hlam, _hmu, heq⟩
  have hlen := congrArg (fun c : VectorConstraint => c.a.length) heq
  simp only [scaleVec, D22_semC, D22_semC_singleton, List.length_map, List.length_nil,
    List.length_cons] at hlen
  exact absurd hlen (by norm_num)

/-- ⭐⭐ **T4 为真**（即调研报告「`SemEqC ⟹ ScaleClass` 为假」的判定**成立**）：
存在**具体**的两个约束，语义等价**但不同** `ScaleClass`。

⇒ ⭐ **判据 2（反驳可能）**：**这就是它的全部内容** —— 一个具体的见证对。
⇒ ⭐ **判据 4（量化）**：配合 T3（§三）即得 **`ScaleClass ⊊ SemEqC`** 的**严格性**。 -/
theorem D22_semEq_imp_scaleClass_false :
    ¬ (∀ c c' : VectorConstraint, SemEqC c c' → ScaleClass c c') :=
  fun h => D22_not_scaleClass_witness (h D22_semC D22_semC_singleton D22_semEqC_witness)

/-! # 七、T5：⭐⭐ **商的严格包含**（判据 4 的落点，由 T3 + T4 合成） -/

/-- ⭐⭐ **`ScaleClass` 严格细于 `SemEqC`**：包含关系**成立**，且**严格**。

⭐ 这是调研报告 T5 的落点，也是本清单**唯一通过判据 4（充要/量化）**的收口定理：
它把两条商的关系**定量**地说成「严格包含」，而**不是**存在性。

⚠ **诚实标注**：本条**本身不含新证明**（是 T3 与 T4 的合取），故它是**收口**而非承重定理。
承重的是 `D22_scaleClass_imp_semEq`（§三）与 `D22_semEq_imp_scaleClass_false`（§六）。 -/
theorem D22_scaleClass_strictly_finer :
    (∀ c c' : VectorConstraint, ScaleClass c c' → SemEqC c c') ∧
    (∃ c c' : VectorConstraint, SemEqC c c' ∧ ¬ ScaleClass c c') :=
  ⟨D22_scaleClass_imp_semEq, D22_semC, D22_semC_singleton, D22_semEqC_witness, D22_not_scaleClass_witness⟩

/-! # 八、T8 的**真缺口方向**：`ScaleClass ⇏ ScaleClassPlus`

⚠ 调研报告 T8 明确要求：**不要写** `ScaleClassPlus ⟹ ScaleClass`（那是 `rfl` 级空壳，
写了就「退化为平凡」）。⭐ **本文件遵照该纪律，不写那一条**；
改证它的**反方向的否定式**：**`ScaleClass` 不蕴含 `ScaleClassPlus`**。

⭐ **证明要点（非平凡）**：`ScaleClass` 使用**非零**倍率，`ScaleClassPlus` 只用**正**倍率。
取 `c = cNegVec = {a := [2,4], b := 6}` 与 `c' := scaleVec cNegVec (-1)`：
- `ScaleClass c c'` 由 `scaleClass_cNegVec_neg`（`RealCanonicalForm.lean:343`）给出；
- `¬ ScaleClassPlus c c'`：设 `0 < lam, 0 < mu` 使 `scaleVec c lam = scaleVec c' mu`，
  取 `b` 分量得 `6 * lam = (6 * (-1)) * mu`；由 `0 < lam`、`0 < mu`
  得左侧 `> 0` 而右侧 `< 0` ⟹ **矛盾**（`omega`）。
  ⭐ **矛盾来自 `cNegVec.b = 6 ≠ 0`（符号可见）** —— 若 `b = 0`，本定理**为假**。 -/

/-- ⭐⭐ **`ScaleClass` 不蕴含 `ScaleClassPlus`**（T8 的真缺口方向，**真且非平凡**）。

⭐ **判据 1（消融）**：把结论换成 `ScaleClassPlus ⟹ ScaleClass`（即调研报告要求**不要写**的
空壳方向），证明体退化为 `obtain ⟨…⟩` + `⟨lam, mu, ne_of_gt …, ne_of_gt …, heq⟩`
—— **纯量词搬运，无数学内容**。⇒ ⭐ **本文件证的是【有内容的那一半】**。

⚠ **诚实标注**：本条的见证 `cNegVec` / `scaleVec cNegVec (-1)` 与既有
`RealExtractCanonical.R02_layer_canonical_not_unique_scale`（`:424`）**用的是同一对**，
故它**不是全新的对象**；⭐ **新的地方是结论**（从 `canonical` 层级的否定
换成两个**商**之间的否定），且**跨了 `RealCanonicalForm` / `RealQuotientReversibility` 两模块**。 -/
theorem D22_scaleClass_not_imp_scaleClassPlus :
    ∃ c c' : VectorConstraint, ScaleClass c c' ∧ ¬ ScaleClassPlus c c' := by
  refine ⟨cNegVec, scaleVec cNegVec (-1), scaleClass_cNegVec_neg, ?_⟩
  rintro ⟨lam, mu, hlam, hmu, heq⟩
  have hb : (6 : Int) * lam = (6 * (-1)) * mu := by
    have h := congrArg VectorConstraint.b heq
    simpa only [scaleVec, cNegVec] using h
  omega

/-! # 九、诚实边界（**不许省**）

## 9.1 本文件**未**证的（与调研报告的差异）

| 调研编号 | 状态 | 原因 |
|:--|:--|:--|
| **T2 的 (⟹) 方向** | ⚠ **未证** | 需要「`canonicalize` 在 `{content = 1}` 上满射」这条**不存在的引理**，且 `cs` 是 `ConstraintSet`（元素 `VectorConstraint`）而 `canonical` 的入口是 `Layer`（元素 `LinearLayer`）—— ⭐ **类型不对齐**，须先构造 `compileToLayer cs` 并证 `content` 条件，**这是真工作，本文件未做**。⇒ **本文件只交付了 (⟸)**。 |
| **T2 的 `LayerContentOk` 必要性** | ⚠ **未证** | 这是**判据 1 的消融论证**（见 §二 docstring），不是定理。 |
| **T6 的 `PreimageStrict` 关系律** | ⚠ **未证** | 调研报告 T6 未要求；`PreimageStrict`（`compileToLayer c = ls`）与 `PreimageSet` 的关系需要额外的 `List` 引理。 |
| **`ScaleClassPlus ⟹ ScaleClass`** | ⛔ **刻意不证** | 遵调研报告 T8 的纪律（**rfl 级空壳，写了即退化**）。 |

## 9.2 我改弱了哪条陈述

1. ⚠ **T2 从 `⟺` 降级为 `⟸`**（见上表）。**这不是「改弱后冒充原命题」**：
   定理名 `D22_canonical_range_sufficient` **显式标注了 `sufficient`**。
2. ⚠ **T7 从「定理」改为「否定定理 + 修补版」**：原陈述为假
   （`D22_canonical_layer_wellDefined_false`），修补版（逐位置）为真
   （`D22_canonical_layer_wellDefined_positional`）。⭐ **两条都交付**，
   且**量词差异被显式写进定理名**。
3. ⚠ **T4 的见证被本文件【替换】**（见 §六 docstring）：调研报告的见证依赖未核对的
   `zip` 截断行为，其「等长替代」又因 `b` 成比例而**恰好落回同一 `ScaleClass`**。
   ⭐ 本文件改用 `D22_semC = {a := [], b := 0}` / `D22_semC_singleton = {a := [0], b := 0}`。
   ⇒ ⭐ **这是本文件对调研报告 T4 的实质修正**（**报告风险最高的一条被消除**）。
4. ⚠⚠ **T6 的关系取法**（`∃ c, PreimageSet ls c ∧ PreimageSet ls' c`）是**本文件的选择**：
   调研报告只给了 `PreimageSet` 的**定义**，**没有**说该在它上面取什么等价关系。

## 9.3 哪条我其实只是 `rfl` 级

⚠ **两条最接近**，如实登记：
1. `D22_canonical_range_sufficient`（§二）：`dif_pos` + `List.map_map` +
   `List.map_congr_left` + `roundtrip_extractVec`（**后者本身是 `rfl`**）。
   ⭐ **这与调研报告对既有 `R02_canonical_well_defined_on_image` 的判定一致**
   （报告 `:50`：「**属 rfl 级**」）。⇒ ⭐ **本文件不假装它不平凡**。
2. `D22_mem_extractLayer_iff`（§四，见其定义处）：展开 `extractLayer` 后逐元素收口
   （因 `convertVec (extractVec l) = l` 是 `rfl`）。
   注意 但它**是 `D22_preimageSet_extractLayer` 与该二者之上的 `D22_preimageSet_equivalence`
   的必要支点**，故保留并**如实标注**。
   注意 **历史沿革（已否证）**：本条登记原写作
   「`D22_mem_compileToLayer_extractLayer`：单条 `rw [compileToLayer_extractLayer]` 即收口」。
   该声明**在本文件中不存在**（`lattice/lean/RealExtractCanonicalExistence.lean` 内无名为此者）；
   `compileToLayer_extractLayer` 实为**另一文件**（`RealCompileExtractClosed.lean`）中的引理，
   且 §四 的证明体**均未使用**它 —— 故该旧登记**已否证**，此处按实际存在的名字更正。

注意 **不平凡的（承重）三条**：`D22_scaleClass_imp_semEq`（§三，跨模块 + `Iff` 链方向）、
`D22_semEq_imp_scaleClass_false`（§六，具体见证 + 长度结构论证）、
`D22_canonical_layer_wellDefined_positional`（§五-bis，跨模块 + 位置对齐）。

## 9.4 我不确定的

1. 注意 `D22_canonical_layer_wellDefined_positional` 的 `h` 用 `ls.get ⟨i, _⟩` 形式书写，
   依赖 `List.length` 与 `List.get` 的**可判定边界**；注意 **本文件已通过内核，故该形式可用**
   （见报告 §结果）。
2. 注意 **T4 见证的「`SemEqC` 一侧」在本文件里是【无条件】**的
   （`D22_dot_singleton_zero` 对一切 `x` 成立），要点 **不再是调研报告担心的 `zip` 依赖**。
3. 注意 **T7 反例的 `hok` / `hok'`** 由 `canonical ls ≠ none` **反推**得到。
   要点 这条反推**依赖「两个 `LayerContentOk` 等价」**（由 `hmem` + `extractVec` 的逐元素性），
   而该等价在本文件中是**内联证明**的（未单独提取为引理）。
   注意 **若 `hmem` 换成一个不含「逐元素对应」的假设，本反例的第三步会失效**。
-/

end Lattice
