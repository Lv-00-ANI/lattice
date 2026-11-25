import Lattice.Core.IR.Semantics

/-!
# **零数据合成：条款 2.2 的前提是**内部可满足**的**

## 这一条回答的是路线 B 的问题

**第 1090–1092 轮把条款 2.2 记为「接口性条款」：它的判据是关于**调用者提供的数据函数**的
（「若 `f` 在所有未命名位置取零，则……」），故其消费者按定位在框架外。**

**⇒ `NEXT-STAGE.md` 的路线 B 问：这个前提能否**由内部产生**？**
**⇒ 若能，则 2.2 可以内部消费；若不能，就结案为接口性条款。**

## 答案：**能，而且是平凡的**

**⇒ 取 `f := fun _ _ => 0`。⇒ 它**在每一点**都取零，故**当然**在所有未命名位置取零。**
**⇒ 于是 `models_of_covered_data` 对**任意**骨架都可应用，得到 `ModelsIRSWith (compileSkel k) k 0`。**

**⇒ 故 2.2 的缺口**不在前提**——前提内部可满足；**缺口在下游**：
⇒ 没有任何步骤**读取**「零数据是骨架的模型」这个结论（因为读它的那一步是训练，而本项目的定位不实现训练框架）。**

**⇒ 这一条因此同时做两件事：**
1. 给 `models_of_covered_data` 一个**真实的内部应用**（本文件在 `Runtime/`，故是**链内**消费者）；
2. 把结论**从「前提不可达」修正为「下游不存在」**——两者不同，而后者才是定位决定的。
-/

namespace Lattice.Runtime.ZeroDataSynthesis

open Lattice.Core.IR

/-- **⭐⭐ 零数据函数是**任意**骨架的模型。**

**⇒ 前提（「在未命名位置取零」）由 `f = 0` 平凡满足，故 `models_of_covered_data` 对每个骨架都给出结论。**
**⇒ 这条的存在本身就是一个事实：条款 2.2 的判据**不**依赖调用者的数据设计。** -/
theorem zero_data_models (k : IRSkeleton) (hnd : (k.tensors.map (fun t => t.id)).Nodup) :
    ModelsIRSWith (compileSkel k) k (fun _ _ => 0) :=
  models_of_covered_data k hnd (fun _ _ => 0) (fun _ _ _ _ _ => rfl)

/-- **⭐ 推论：零数据也**覆盖**其张量形状。**

**⇒ 与上一条同一前提，取 `covered_of_vanishing`。** -/
theorem zero_data_covered (k : IRSkeleton) (hnd : (k.tensors.map (fun t => t.id)).Nodup) :
    covered (materializeWith k (fun _ _ => 0)).tensors
      (shapesOf (materializeWith k (fun _ _ => 0))) :=
  covered_of_vanishing k (fun _ _ => 0) hnd (fun _ _ _ _ _ => rfl)

end Lattice.Runtime.ZeroDataSynthesis