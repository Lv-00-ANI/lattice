import Mathlib
import Lattice.Lib.Architectures.RealMoELoadBalance
import Lattice.Lib.Attention.RealDynamicRoute
/-!
# LATTICE: MoE 路由容量桥 —— 选择集计数负载接上容量丢弃理论

本文件是 `RealMoELoadBalance` 的**语义下游消费者**（W11/W24 收尾：消灭孤岛，判据 11）。
X10（sweep11）建了 `RealMoELoadBalance` 的离散计数内核（负载/容量/丢弃），
但该模块的 **in-degree = 0**——被构建根「注册」却无任何语义消费者
（X10 报告 §三-发现 4 已诚实登记，并**拒绝**用装饰性 import 刷绿）。

本文件给出**真实的**入边：把 `RealDynamicRoute` 的**路由选择集**语义
（每 token 一个 top-k 集 `R t : Finset iota`）与 `RealMoELoadBalance` 的
**负载/容量/丢弃**语义接起来——

  1. `routeLoad R e`：专家 e 在整批 token 上的**扇入**（= 被容量约束的那个量）；
  2. `capacityRespecting R capacity`：每个专家扇入 ≤ 容量（= 可路由而不丢弃）；
  3. `routeLoad_drop_eq_zero_iff`：**扇入超容 <-> 丢弃 > 0**（转调 `droppedCount_eq_zero_iff`）；
  4. `route_over_capacity_drops` *：**某专家扇入超容 => 该批必丢弃**（消费 `imbalance_forces_drop`）；
  5. `balanced_route_no_drop`：全部不超容 => 零丢弃；
  6. `topk_route_capacity_exceeded` *：**top-k 路由的扇入必然 = k * |token|**，
     故**当 k * |token| > Sum capacity 时，任何 top-k 路由都必然丢弃**。

## 强制负对照（判据 13：断言自己触发的那个 finding 的身份）

  · `nc_witness_over_capacity_drops`：容量 0 时选满 2 专家 => **丢弃 > 0**；
  · `nc_witness_fits_no_drop`：**同一路由 R**、容量放宽到各 1 => **丢弃 = 0**；
  · `nc_route_flip`：**同一路由**下结论翻转（>0 vs =0）——身份断言；
  · `nc_k_exceeds_capacity_witness`：k=2、|T|=2、容量各 1 => `4 > 2` 成立 => 丢弃 > 0；
  · `nc_k_fits_no_drop`：同一实例、容量各 2 => `4 > 4` 假 => 丢弃 = 0（假设可失败）。

  **区分力**（防「不能区分」）：若 `droppedCount` 写成**恒 0**，则
  `nc_witness_over_capacity_drops` 不可证；若 `droppedCount` **忽略 capacity**，
  则 `nc_witness_fits_no_drop` 不可证。两条 NC 锁死**两个不同**的失效方向。

真实性声明：本文件**不**声称形式化了 token 级最优分配，也**不**声称形式化了
辅助损失动力学（与 `RealMoELoadBalance` 文件头一致）。

## ⚠ 未接线（not wired）声明 —— 末环孤岛，显式登记

本文件是这条消费链的**末环**：`RealMoE`（保序）→ `RealMoELoadBalance`（计数内核）
→ `RealMoERouteCapacity`（路由桥）。它**自身 in-degree = 0**（无下游模块 import 它）。
这是**有意为之**，不是遗漏：

  · 按 W05 实测教训「防孤岛会把孤岛**逐层下推**」——每补一条入边，新节点就成为新的末环；
    链条必然在某一环终止，**末环 in-degree = 0 是结构必然，不是缺陷**；
  · 本文件**拒绝**制造装饰性 import 来把这个读数刷绿（判据 8「无法被行使的修复不是修复」）；
  · 真正的下游消费者（把容量丢弃接进训练动力学 / 端到端 loss）**尚未存在**，
    而这需要形式化辅助损失，超出本轮离散计数模型的范围。

⟹ 依据 `scripts/check-new-roots-indegree.py` 的约定，此处**显式**声明：本模块 **not wired**
（未接线 / zero in-degree），**不**属于「静默孤岛」。

全部证明无 sorry / axiom / admit。
-/

noncomputable section

namespace Lattice

variable {iota tau : Type*} [Fintype iota] [DecidableEq iota]
  [Fintype tau] [DecidableEq tau]

/-! ## 路由扇入（把选择集语义接上负载语义） -/

/-- 批 `T` 上、路由 `R` 下，专家 `e` 的**扇入**：批内选中 `e` 的 token 数。
这正是 `RealMoELoadBalance.expertLoad` 的**具体来源**。 -/
def routeLoad (T : Finset tau) (R : tau -> Finset iota) (e : iota) : Nat :=
  (T.filter (fun t => e ∈ R t)).card

/-- 路由 `R` 在批 `T`、容量 `capacity` 下**不超容**。 -/
def capacityRespecting (T : Finset tau) (R : tau -> Finset iota) (capacity : iota -> Nat) :
    Prop :=
  Balanced (routeLoad T R) capacity

/-- 该批在路由 `R`、容量 `capacity` 下的**丢弃数**。 -/
def routeDropped (T : Finset tau) (R : tau -> Finset iota) (capacity : iota -> Nat) : Nat :=
  droppedCount (routeLoad T R) capacity

/-! ## 定理 1：路由层刻画（转调 -- 这是真实的消费边） -/

/-- * **路由层无丢弃 <-> 每专家扇入不超容**。 -/
theorem routeLoad_drop_eq_zero_iff (T : Finset tau) (R : tau -> Finset iota)
    (capacity : iota -> Nat) :
    routeDropped T R capacity = 0 <-> capacityRespecting T R capacity :=
  droppedCount_eq_zero_iff (routeLoad T R) capacity

/-- * **某专家扇入超容 => 该批必丢弃**（消费 `imbalance_forces_drop`）。 -/
theorem route_over_capacity_drops (T : Finset tau) (R : tau -> Finset iota)
    (capacity : iota -> Nat) (h : ∃ e, capacity e < routeLoad T R e) :
    0 < routeDropped T R capacity :=
  imbalance_forces_drop (routeLoad T R) capacity h

/-- **全部不超容 => 零丢弃**（消费 `balanced_no_drop`）。 -/
theorem balanced_route_no_drop (T : Finset tau) (R : tau -> Finset iota)
    (capacity : iota -> Nat) (h : capacityRespecting T R capacity) :
    routeDropped T R capacity = 0 :=
  balanced_no_drop (routeLoad T R) capacity h

/-! ## 定理 2（核心）：top-k 路由的扇入计数与容量冲突 -/

/-- 每个 token 恰好选 `k` 个专家时，**总扇入 = k * |T|**：双重计数恒等式。 -/
theorem routeLoad_sum_eq_card_mul (T : Finset tau) (R : tau -> Finset iota) (k : Nat)
    (hcard : ∀ t ∈ T, (R t).card = k) :
    (∑ e, routeLoad T R e) = k * T.card := by
  classical
  have hswap : (∑ e, routeLoad T R e) = ∑ t in T, (R t).card := by
    conv_lhs => arg 2; intro e; rw [routeLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [show (∑ e : iota, ∑ a ∈ T, (if e ∈ R a then 1 else 0))
          = ∑ e ∈ (Finset.univ : Finset iota), ∑ a ∈ T, (if e ∈ R a then 1 else 0) by simp]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_boole (fun e => e ∈ R t) Finset.univ]
    simp
  rw [hswap, Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- * **top-k 路由 + 容量不足 => 必丢弃**。 -/
theorem topk_route_capacity_exceeded (T : Finset tau) (R : tau -> Finset iota)
    (capacity : iota -> Nat) (k : Nat) [Nonempty iota]
    (hcard : ∀ t ∈ T, (R t).card = k)
    (hover : (∑ e, capacity e) < k * T.card) :
    0 < routeDropped T R capacity := by
  apply drop_of_total_exceeds_capacity
  rw [routeLoad_sum_eq_card_mul T R k hcard]
  exact hover

/-! ## 强制负对照 -/

/-- 具体路由：2 专家、1 个 token、选满两个专家。 -/
private def ncRoute : Fin 1 -> Finset (Fin 2) := fun _ => Finset.univ

/-- NC-1：**同一路由**、容量各 0 => **丢弃 > 0**。 -/
theorem nc_witness_over_capacity_drops :
    0 < routeDropped (Finset.univ : Finset (Fin 1)) ncRoute (fun _ : Fin 2 => 0) := by
  apply route_over_capacity_drops
  exact ⟨0, by decide⟩

/-- NC-2：**同一路由**、容量各 1 => **丢弃 = 0**。 -/
theorem nc_witness_fits_no_drop :
    routeDropped (Finset.univ : Finset (Fin 1)) ncRoute (fun _ : Fin 2 => 1) = 0 := by
  apply balanced_route_no_drop
  intro e
  fin_cases e <;> decide

/-- * **身份断言**：**同一路由** `ncRoute` 下结论翻转。 -/
theorem nc_route_flip :
    ∃ capacity capacity2 : Fin 2 -> Nat,
      routeDropped (Finset.univ : Finset (Fin 1)) ncRoute capacity ≠ 0 ∧
      routeDropped (Finset.univ : Finset (Fin 1)) ncRoute capacity2 = 0 := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, nc_witness_fits_no_drop⟩
  intro h
  have hpos := nc_witness_over_capacity_drops
  omega

/-- * **k 侧触发**：k=2、2 token、容量各 1 => `4 > 2` 成立 => 丢弃 > 0。 -/
theorem nc_k_exceeds_capacity_witness :
    0 < routeDropped (Finset.univ : Finset (Fin 2))
      (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) (fun _ : Fin 2 => 1) := by
  apply topk_route_capacity_exceeded (k := 2) <;> decide

/-- **k 侧不触发**：同一实例、容量各 2 => `4 > 4` 假 => 丢弃 = 0。 -/
theorem nc_k_fits_no_drop :
    routeDropped (Finset.univ : Finset (Fin 2))
      (fun _ : Fin 2 => (Finset.univ : Finset (Fin 2))) (fun _ : Fin 2 => 2) = 0 := by
  apply balanced_route_no_drop
  intro e
  fin_cases e <;> decide

end Lattice
