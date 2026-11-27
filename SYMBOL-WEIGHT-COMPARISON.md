# 两套「符号 ⇄ 权重」实现的对照

**本文由第 1087 轮撰写。每个数字都来自 `gov/` 的工具输出（`gen_objective_map.py`、`chain_connectors.py`、
`git grep`），不是来自对文件的印象。⇒ 若日后数字变化，**本文的结论会随之失去依据**，
故底部给出重新测量的命令。**

---

## 一、为什么需要这份对照

**目标条款 1.3（符号 → 权重）与 1.4（权重 → 符号）各有**两套**实现，且它们**互不引用**。
⇒ 这本身不是错误——规划允许按能力族声明——但**同一条款下两个互不引用的实现**必须被**登记**，
否则「实现了」这句话就有两个不同的意思。**

---

## 二、两套实现的形状

| | 主链（`Runtime/`） | 新线（`Lib/Compiler/`） |
|:--|:--|:--|
| 正向入口 | `compileToLayer : ConstraintSet → Layer`（`Runtime/SymbolToWeightCorrectness.lean:35`） | `compileTarget : ExprExt → Option Target`（`Lib/Compiler/SymbolicEntry.lean`） |
| 载体 | `ConstraintSet = List VectorConstraint`；`Layer = List LinearLayer` | `ExprExt`；`Target`；`Segment = ⟨m, c⟩ : ℝ × ℝ` |
| 数的域 | **`ℤ`**（`LinearLayer = ⟨w : List ℤ, b : ℤ⟩`） | **`ℝ`** |
| 语义 | **精确**：`AllSatisfied cs x ↔ AllZeroOutputs (compileToLayer cs) x` | **逼近**：`\|f x − gridEval g n x\| ≤ C/n²` |
| 逆向 | `extract : …`（`Core/IR/Extract.lean`）、`extract_compile` | `decodedFamily : Option (ℕ → Segment)`、`decodedFamily_ofSegments` |
| 判据 | 提取后的符号**满足原约束** | 载荷**满足斜率判据** + 整域精度 |

---

## 三、条款引用（横向引用数，来自 `OBJECTIVE-MAP.md`）

| 载体 | 所属条款 | 定义于 | 跨文件 | 同文件 |
|:--|:--|:--|--:|--:|
| `compileToLayer` | 1.3 | `Runtime/SymbolToWeightCorrectness.lean` | **52** | 6 |
| `compileToLayerN` | 1.3 | `Runtime/WeightLadderN.lean` | 2 | 1 |
| `compileTarget` | 1.3 | `Lib/Compiler/SymbolicEntry.lean` | **2** | 20 |
| `EvaluatedArtifact` | 1.3 | `Lib/Compiler/Layout.lean` | **7** | 7 |
| `extract` | 1.4 | `Core/IR/Extract.lean` | **51** | 9 |
| `extract_compile` | 1.4 | `Core/IR/Extract.lean` | 5 | 3 |
| `decodedFamily` | 1.4 | `Lib/Compiler/Layout.lean` | **2** | 7 |

**⇒ 读法：主链的载体被 50 余处引用；新线的载体只有 2–7 处，**且全部落在 `Lib/Compiler/` 内部**
（第 1080 轮的全库测量：`compileTarget`/`EvaluatedArtifact`/`decodedFamily` 在 `Lib/Compiler/` 之外**零引用**）。
⇒ 故**新线是**被登记但不被依赖**的一侧。这是当前事实，不是评价。**

---

## 四、唯一的**真实**交点：标量仿射片段

**两套实现在**唯一的**片段上可证一致：长度为 1 的整数标量仿射情形。**

```lean
theorem segment_eval_eq_scalar_layer_out (w b x : ℤ) :
    (⟨(w : ℝ), (b : ℝ)⟩ : Segment).eval (x : ℝ)
      = ((Lattice.LayerOut ⟨[w], b⟩ [x] : ℤ) : ℝ)
```
（`Lib/Compiler/BridgeToMainChain.lean`，第 1081 轮；`bridge_sample` 给出 `(3, 5)` 在 `x = 7` 的可手算实例。）

**⇒ 这条说明：当新线的分段系数是**整数**时，它在**整数点**上求出的值等于主链那一层的输出。
⇒ 它**不**说明非整数系数、非标量宽度、或「零 vs ε」语义上的一致——那三者**不在**桥里，也不被声称。**
---

## 五、各自覆盖什么、不覆盖什么

| 能力 | 主链 | 新线 |
|:--|:--|:--|
| 多约束（每个约束一个神经元） | ✅ | ❌（新线按**段**组织，不按约束） |
| 整数精确满足（输出恰为零） | ✅ | ❌（新线是 ε-逼近） |
| **任意精度**逼近（`ε` 可小到 `1/(4n²)` 量级） | ❌ | ✅ |
| **任意幂次**（`x^d` 对任意 `d`） | ❌ | ✅（`powAnalyticRow`，常数 `d(d−1)/8`） |
| 符号**表面语法**（`ExprExt` 项） | ❌（输入是约束表） | ✅（`compileTarget`） |
| 布局/载荷/配方的产物契约 | ❌ | ✅（`EvaluatedArtifact`） |
| 名称/版本/迁移的插件治理 | ✅（`Plugins/`） | ❌ |

**⇒ 两者不是「一个更弱、一个更强」，而是**覆盖不同的能力**。**
**⇒ 这正是规划 §1.6 允许「按能力族声明」的含义：能力清单可以有重叠的条款，但每一行要写清它覆盖什么。**

---

## 六、为什么**没有**合并（测量出的理由，不是判断）

1. **数的域不同**：`ℤ` vs `ℝ`。**⇒ 第 1125 轮把这一条从「判断」升为「定理」**：`non_integer_slope_has_no_layer`（`Lib/Compiler/BridgeToMainChain.lean`）说——只要斜率 `m` **不是整数**，就**不存在**一个 `LinearLayer` 能在整数输入上等于该分段（`half_slope_has_no_layer` 是 `m = 1/2` 的实例）。**⇒ 故这不是「还没翻译」，而是**在「保持 `LinearLayer` 值域 `ℤ` + 输入 `[x]` + 逐点精确相等」这一种表示下不可嵌入**。
**⇒ （第 1184 轮校正）旧文写「再强的结构改造也不会改变它」，而 `Lib/Compiler/RealLayer.lean` **已给出共同推广**：
`realLayer_single_eq_segment`（:120）与 `two_sections_of_one_generalisation`（:130）说明 `LinearLayer` 与 `Segment` 是**同一推广的两个截面**。
**⇒ 故正确的说法是：在**整数精确截面**不可嵌入；而**实数截面**（`RealLayer`）已经存在。**
2. **判据不同**：`AllZeroOutputs`（恰为零）与 `|f − interp| ≤ C/n²`（有界）是**两种**谓词。
   把后者写成前者会得到假定理；把前者写成后者会丢掉精确性。
3. **组织的轴不同**：主链按**约束**（每约束一神经元），新线按**段**（每段一条线性函数）。
   两者需要的索引（约束下标 vs 段号）不可互换。

**⇒ 故「合成一条链」在**当前载体**上不可证。把这一点写下来，比写一条看起来像桥的弱定理更有用。**
**⇒ 若要做真正的统一，需要先**选定一个共同载体**（例如把 `LinearLayer` 推广到实数系数、并按段组织），
那是一次**架构级改动**——按本项目的纪律，应在分支上尝试、验证后 `--no-ff` 合并，且需先证明旧结果在新载体上仍成立。**

---

## 七、如何重新测量本文的数字

```powershell
cd gov
python gen_objective_map.py            # 第 3 节的跨/同文件引用数
python chain_connectors.py --provenance # 八阶段接缝的年龄
cd ..
git grep -l "compileTarget" -- 'Lattice/**/*.lean'      # 第 3 节末尾的「零外部引用」判断
```

**⇒ 若某天新线的跨文件引用不再全在 `Lib/Compiler/` 内，本文的第四节之后应随之更新。**
**⇒ 本文**不**声称两套实现中哪一套「更正确」：它们在不同的判据下都是正确的，而判据不同正是它们需要并存的原因。**