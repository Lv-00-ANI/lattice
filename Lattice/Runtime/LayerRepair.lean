import Lattice.Runtime.RepairClosure
import Lattice.Runtime.LoopClosure

namespace Lattice.Runtime.LayerRepair

open Lattice.Lift.SymbolToWeightCorrectness
open Lattice.Core

-- **`if` 型测度需要 `Decidable`；局部安装它，使实例能写成**规范的 `where` 形式**。**
attribute [local instance] Classical.propDecidable

def allZeroLayer (ls : Layer) : Prop :=
  ∀ l ∈ ls, (∀ z ∈ l.w, z = 0) ∧ l.b = 0

def zeroLayer (ls : Layer) : Layer :=
  ls.map (fun l => ⟨l.w.map (fun _ => 0), 0⟩)

theorem map_zero_eq_self_of_all_zero (w : List ℤ) (h : ∀ z ∈ w, z = 0) :
    w.map (fun _ => (0 : ℤ)) = w := by
  induction w with
  | nil => rfl
  | cons z zs ih =>
      have hz : z = 0 := h z (by simp)
      have hzs : zs.map (fun _ => (0 : ℤ)) = zs :=
        ih (fun y hy => h y (List.mem_cons_of_mem z hy))
      simp [hz, hzs]

theorem zeroLayer_eq_self {ls : Layer} (h : allZeroLayer ls) : zeroLayer ls = ls := by
  induction ls with
  | nil => rfl
  | cons l rest ih =>
      obtain ⟨w, b⟩ := l
      have hw0 : ∀ z ∈ w, z = 0 := (h ⟨w, b⟩ (by simp)).1
      have hb0 : b = 0 := (h ⟨w, b⟩ (by simp)).2
      have hr : allZeroLayer rest := fun m hm => h m (by simp [hm])
      have hw : w.map (fun _ => (0 : ℤ)) = w := map_zero_eq_self_of_all_zero w hw0
      show ((⟨w.map (fun _ => (0 : ℤ)), 0⟩ : Lattice.LinearLayer) :: zeroLayer rest)
          = (⟨w, b⟩ : Lattice.LinearLayer) :: rest
      rw [ih hr, hw, hb0]

/-- **⭐ 全零权重的点积为零**。

**⇒ 对 `zip` 后的列表带**任意累加器**归纳；每一项都含一个零权重。** -/
theorem dot_eq_zero_of_pointwise_zero : ∀ (w x : List ℤ),
    (∀ z ∈ w, z = 0) → Lattice.dot w x = 0
  | [], _, _ => by simp [Lattice.dot]
  | _ :: _, [], _ => by simp [Lattice.dot]
  | y :: ys, z :: zs, h => by
      have hy : y = 0 := h y (by simp)
      have hys : ∀ t ∈ ys, t = 0 := fun t ht => h t (List.mem_cons_of_mem y ht)
      have ih := dot_eq_zero_of_pointwise_zero ys zs hys
      simp only [Lattice.dot, List.zip_cons_cons, List.foldl_cons]
      rw [show (0 + y * z : ℤ) = 0 from by rw [hy]; ring]
      exact ih

/-- **⭐ 清零后的层满足无输入判据。** -/
theorem zeroLayer_allZero (ls : Layer) : allZeroLayer (zeroLayer ls) := by
  intro l hl
  simp only [zeroLayer, List.mem_map] at hl
  obtain ⟨l₀, _, rfl⟩ := hl
  refine ⟨?_, rfl⟩
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨z₀, _, rfl⟩ := hz
  rfl

/-- **⭐⭐⭐ 主链的层载体上的修复实例**——全树**第一个** `Repair Layer`。

**⇒ 它使 `Runtime/RepairClosure.lean` 的四条定理**第一次可被应用**。**
**⇒ 测度取 `0/1`：判据成立则 0，否则 1——因为清零是**一步到位**的。** -/
noncomputable def layerZeroRepair : Repair Layer where
  Sat := allZeroLayer
  fix := zeroLayer
  μ := fun ls => if allZeroLayer ls then 0 else 1
  absorbs := by
    intro ls h
    exact zeroLayer_eq_self h
  decreases := by
    intro ls h
    have hz : allZeroLayer (zeroLayer ls) := zeroLayer_allZero ls
    show (if allZeroLayer (zeroLayer ls) then 0 else 1) < (if allZeroLayer ls then 0 else 1)
    rw [if_pos hz, if_neg h]
    omega
  atomic := by
    intro ls h
    by_contra hc
    -- **`h : μ ls = 0`；先把它换成 `μ` 的**定义形**，才能用 `if_neg`。**
    have h1 : (if allZeroLayer ls then 0 else 1) = 0 := h
    rw [if_neg hc] at h1
    omega

/-- **⭐⭐⭐ 被判据接受的层，对**任意**输入输出为零**——`compileToLayer` 语义的另一侧。** -/
theorem layerZeroRepair_sat_zero_outputs {ls : Layer} (h : allZeroLayer ls) :
    ∀ x : List Int, AllZeroOutputs ls x := by
  intro x l hl
  obtain ⟨hw, hb⟩ := h l hl
  have hdot : Lattice.dot l.w x = 0 := dot_eq_zero_of_pointwise_zero l.w x hw
  show Lattice.LayerOut l x = 0
  unfold Lattice.LayerOut
  rw [hdot, hb]
  rfl

/-- **⭐⭐⭐ 清零后再提取，得到的符号满足**任何**约束。

**⇒ 这是 `extract_after_repair` 的**兄弟定理**：后者需要 `R.Sat ls ↔ LayerSat cs ls`，
而本实例的判据是「全零」，两者**不等价**，故前者无法直接套用。**
**⇒ 而本条只需要「全零」：零层提取出的每个约束都是 `0 = 0`，故对**任意输入**成立。** -/
theorem extract_after_zero_repair (ls : Layer) (h : allZeroLayer ls) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x := by
  intro c hc
  simp only [Lattice.Runtime.LoopClosure.extractLayer, List.mem_map] at hc
  obtain ⟨l, hl, rfl⟩ := hc
  obtain ⟨hw, hb⟩ := h l hl
  have hdot : Lattice.dot l.w x = 0 := dot_eq_zero_of_pointwise_zero l.w x hw
  show Lattice.dot (⟨l.w, l.b⟩ : Lattice.VectorConstraint).a x
      + (⟨l.w, l.b⟩ : Lattice.VectorConstraint).b = 0
  simp only [hdot, hb]
  rfl

/-- **⭐⭐⭐ 用**全零实例**实例化弱化版——接缝**首次真正有消费者**。

**⇒ 这里把 `layerZeroRepair_sat_zero_outputs`（它恰好就是 `LayerSat cs`）喂给
`extract_after_repair_weak`。⇒ 故 `RepairClosure` 那一节**首次被下游引用**。**
**⇒ 而旧条 `extract_after_repair` 本身仍然 0 消费者——它的 `↔` 前提在树里无实例。
⇒ 下一步应当把这件事**写进文档**，而不是继续找消费者。** -/
theorem layerZeroRepair_extract (cs : List Lattice.VectorConstraint) (ls : Layer)
    (h : layerZeroRepair.μ ls = 0) (x : List Int) :
    AllSatisfied (Lattice.Runtime.LoopClosure.extractLayer ls) x :=
  Lattice.Runtime.RepairClosure.extract_after_repair_weak (cs := cs) layerZeroRepair
    (fun ls' hs => layerZeroRepair_sat_zero_outputs hs) ls h x

end Lattice.Runtime.LayerRepair