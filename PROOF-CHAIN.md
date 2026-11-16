# 证明链索引（**由 `gov/gen_proof_chain.py` 生成，勿手改**）

> **本表把项目目标的六个子句逐句对应到具名定理。**
> **每一行都由**测量**得来：定理是否仍定义在所指文件里、被引用多少次。**
> **重新生成：`python gov/gen_proof_chain.py`；核验：`python gov/gen_proof_chain.py --check`。**

## 目标原句

> **正向把符号知识编译成权重（约束损失、数据合成、结构化初始化），
> 逆向把权重行为提取回符号，用于验证、修正、再注入；闭环就是验证回路。**

## 逐句落点

| 子句 | 定理 | 位置 | 内容 | 引用 |
|:--|:--|:--|:--|--:|
| 正向：符号知识 → 权重 | `symbolToWeight_correct` | `Lattice/Runtime/SymbolToWeightCorrectness.lean` | 符号约束全部成立 ⟺ 编译出的权重层输出全为零 | 119 |
| 逆向：权重 → 符号 | `extract_compile_constraints` | `Lattice/Runtime/LoopClosure.lean` | 先编译再提取，回到原约束集 | 9 |
| 闭环：回路是双射 | `compile_extract_bijective` | `Lattice/Runtime/LoopClosure.lean` | `extractLayer` 与 `compileToLayer` 互为左右逆 | 4 |
| 验证：语法判据 | `faithful_iff_extract_eq` | `Lattice/Runtime/Faithfulness.lean` | 层忠于数据 ⟺ 提取结果等于数据的约束集 | 10 |
| 验证：语义判据 | `satisfies_extractLayer_iff_self` | `Lattice/Runtime/SemanticFaithfulness.lean` | 提取出的符号成立 ⟺ 该层输出为零 | 4 |
| 修正：吸收性 | `repair_preserves_verdict` | `Lattice/Runtime/RepairClosure.lean` | 判据为真 ⟹ 修复不动它 | 4 |
| 修正：严格进展 | `repair_makes_progress` | `Lattice/Runtime/RepairClosure.lean` | 判据为假 ⟹ 测度严格下降 | 2 |
| 修正：终止即满足 | `repair_terminates_at_sat` | `Lattice/Runtime/RepairClosure.lean` | 测度为零 ⟹ 判据为真 | 6 |
| 再注入 | `extract_after_repair` | `Lattice/Runtime/RepairClosure.lean` | 修复到测度为零后，提取出的符号满足原约束 | 2 |
| 端到端：数据 → 权重 | `data_to_weight_iff` | `Lattice/Runtime/EndToEndComposite.lean` | 数据的约束全部成立 ⟺ 权重层输出全为零 | 9 |
| 回路闭合（既有） | `verification_loop_closes_holds` | `Lattice/Runtime/VerificationLoop.lean` | 修复回路闭合 | 3 |
| 表达力：线性严格弱于非线性 | `linear_strictly_weaker_than_relu` | `Lattice/Lib/Compiler/Expressiveness.lean` | 线性载体覆盖等式子类；relu 侧的非等式解确实存在 | 1 |
| 抽象：载体无关的判据 | `criterion` | `Lattice/Lib/Compiler/CarrierClosure.lean` | 任何载体上：约束成立 ⟺ 编译输出为零（两条义务的合取） | 100 |
| 抽象：三个独立载体共享闭环 | `three_carriers_share_loop` | `Lattice/Lib/Compiler/CarrierCoverage.lean` | 线性（列表+层）、relu（实数）、sign（实数）三个独立载体共用同一判据 | 1 |
| 抽象覆盖全链 | `carrier_covers_whole_chain` | `Lattice/Lib/Compiler/CarrierReproduction.lean` | 编译、验证、修正三段都是 Carrier 的形状或其特化 | 1 |

## 状态

**全部 15 条定理就位，且都被引用至少一次。**

## 链的**形状**

**上表十五条不是十五个相干事实，而是同一个形状的实例。那个形状是 `Carrier`：**

```lean
structure Carrier where
  Symbol   : Type
  Weight   : Type
  Sat      : Symbol → Prop
  out      : Weight → Prop
  compile  : Symbol → Weight
  sound    : ∀ s, Sat s → out (compile s)
  complete : ∀ s, out (compile s) → Sat s
```

**两条义务（可靠性 + 完备性），闭环随之而来：`Carrier.criterion : Sat s ↔ out (compile s)`。**
**于是上表里的每一条，要么是该形状的实例，要么是它在某个载体上的特化。**
**新增一个载体的代价是**履行两条义务**，其余部分免费。**

## 诚实边界

**这些定理合起来说明「表示链与验证回路在**这条线性/约束表示**上是闭合的」，**不**说明「任意权重都能被还原成有意义的符号」。**
**后者的困难见 `PIPELINE-COVERAGE.md` 与第 895 轮的否证；本表不声称它。**
