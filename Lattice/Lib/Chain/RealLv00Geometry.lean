/-
# LATTICE: Lv-00 采集 —— 几何 / 微分几何 / CSG / 经典公理几何

## 来源

- 采集源：`level0000x/Lv-00`，浅克隆于 `lattice/_harvest/lv00/`（已 gitignore）
- 主采集分支：`lv-merged/`（Lean 4 / `lean4:v4.14.0`，与本项目 toolchain 一致）
- 对照分支：`formal/`（同为 v4.14）；`lv-formal/` 为 v4.33，**未采集**
- 上游依赖：仅 `Mathlib`（本项目 `lakefile.toml` 锁定 `mathlib4 @ 4bbdccd9`）；
  上列采集分支/对照分支均如此。本文件 import 亦仅 `Mathlib`（见文末 `import Mathlib`），
  但同采集包的其它文件（如 `RealLV.lean`）另 import 了 `RealLinear`/`RealNonlinear`/
  `RealTotalLoss` 等项目内部模块，故上栏系「上游依赖」而非「采集包整体依赖」
- 上游模块：
  - `lvFormal/Theory/DifferentialGeometry.lean`（485 行）
  - `lvFormal/Theory/GeometryInfrastructure.lean`（350 行）
  - `lvFormal/Theory/GeometrySymbolicsTheory.lean`（225 行）
  - `lvFormal/Theory/CSGGeometryTheory.lean`（412 行）
  - `lvFormal/Theory/PresetGeometryDefs.lean`（193 行）
  - `lvFormal/Theory/GeometryPresetDefs.lean`（159 行）
  - `lvFormal/Classical/Hilbert/{Basic,Incidence,Betweenness,Congruence,Order,Parallel,Continuity,HilbertAxioms,EuclideanPlane}.lean`
  - `lv/`（与 `Classical/Hilbert` 逐字节重复的 10 个模块）

## 采集理由

Lv-00 已决定重写，但其**规格层与抽象层定义**（曲面/CSG/公理几何的类型骨架）是可复用的
素材：它们把 C 侧实现（`geometry_csg.c`、`symbolic_coord_ops.c`、`layer3_geometry/*`）
的对象模型固化成了 Lean 类型。本文件把其中**经得起检查**的部分搬入本项目，
统一到命名空间 `Lattice.Lv00.Geometry`，并**逐条诚实标注**原本的证明强度。

## 判别口径（A / B / C）

- **(A) 真结果**：证明体有实质推理（`ring` / `linarith` / `omega` / 结构化 `calc` /
  `decide` 于有内容的目标），且命题本身非平凡。
- **(B) 规格声明**：命题平凡或不含命题（纯定义、纯数据），但**定义本身有价值**，
  且**命题为真**（可能是 `rfl` 级的真）。
- **(C) 无价值**：占位（`True := by trivial`）、重言（`X = X`）、
  **证明体 `trivial` 而命题为假**、或跨文件重复。

### 本文件计数

| 类别 | 条目数 | 去向 |
|---|---|---|
| (A) 真结果 | 21 | 全部保留，重写为可检查形式 |
| (B) 规格声明 | 34 | 保留定义/真命题；**丢弃**其中的伪命题 |
| (C) 无价值 | 27 | 丢弃（含 8 条被证伪的"定理"） |

## 与 mathlib 的重复项（不搬运，直接用 mathlib）

| Lv-00 符号 | mathlib 现成设施 | 处置 |
|---|---|---|
| `lv.Basic.MetricSpace`（自造距离公理类） | `MetricSpace`（`PseudoMetricSpace`/`Dist`） | 丢弃，直接复用 |
| `lv.EuclideanPlane.triangle_inequality` | `dist_triangle` | 丢弃 |
| `lv.EuclideanPlane.dist_zero_iff_eq` | `eq_of_dist_eq_zero` / `dist_eq_zero` | 丢弃 |
| `lv.EuclideanPlane.dist_comm` | `dist_comm` | 丢弃 |
| `DifferentialGeometry.dot3` / `cross3` | `EuclideanSpace ℝ (Fin 3)` + `inner` / `cross` | 未替换（保持上游公式形状），仅**记录**重复 |
| `DifferentialGeometry.plane` / `sphere` / `cylinder` | `EuclideanGeometry.Sphere`、`InnerProductGeometry` | 未替换（此处只需具体坐标公式），仅**记录**重复 |
| `CSGGeometryTheory.vec3_*` | `EuclideanSpace` 向量运算 | 仅记录重复 |
| `GeometryPresetDefs.dist` | `dist` / `Real.sqrt` 组合 | 仅记录重复 |
| `SolverInfrastructure.gcd_lcm_identity` | `Nat.gcd_mul_lcm` | 保留（薄包装，本项目其它模块在用同一形状） |

> 说明：`DifferentialGeometry` 与 `CSGGeometryTheory` 里的三维向量代数（`dot3`/`cross3`/
> `vec3_*`）在 mathlib 中确有对应（`EuclideanSpace ℝ (Fin 3)` 的 `inner`、`cross`），
> **本文件未做替换**，理由有二：(1) 上游是**有限差分数值**定义（`h = 1e-6` 定步长），
> 不是抽象黎曼几何，替换会改变命题语义；(2) 替换后本文件将无法作为"Lv-00 原式"的
> 忠实存档，而存档正是本次采集的目的。此项**列为重复但暂不合并**。

## 诚实降级清单（逐条）

1. **`gaussian_curvature` 的 `second_fundamental` 恒为 `(0,0,0)`**（上游自己承认）：
   因此 `theorema_egregium`、`curvature_invariant_under_isometry`、
   `cylinder_gaussian_curvature_zero` 都是**同义反复**（两边都展开为 `0`），
   不构成对真正 Theorema Egregium 的证明。→ **降级为 (B)**，本文件保留为
   "平坦/退化情形的定义性事实"，并**显式改名**为 `..._degenerate` 以杜绝误读。
2. **`hyperbolic_paraboloid_analytic_curvature_at_origin`**（上游 `sorry`，结论 `K = -4`）：
   在原点 `(u,v) = (0,0)` 处 `first_fundamental` 给出 `(E,F,G) = (1,0,1)`，
   故 `K = (2·(-2) - 0)/(1·1 - 0) = -4`。**命题为真**，本文件**补证**并**不再保留 sorry**。
3. **`sphere_analytic_curvature`**（上游 `sorry`，结论 `K = 1/R²`）：
   `EG - F² = R⁴ sin²u`，需 `R ≠ 0 ∧ sin u ≠ 0`，上游只给了 `R > 0` 与自由变量 `u`，
   **命题在 `u = 0` 处为假**（分母为 0，函数走 `else` 分支返回 `0 ≠ 1/R²`）。
   → **判定：上游命题为假**；本文件将其**改为带显式假设 `hsin : sin u ≠ 0` 的正确版本**，
   并用 `hsin` 排除奇点。见 `sphere_analytic_curvature`。
4. **`gauss_equation`**（上游 `sorry`）：比较"法向二次型"与"Christoffel 曲率"两个
   **数值**公式，二者取整误差与差分公式都不同，**一般不为真**。→ **(C) 丢弃**，
   以平面情形的精确事实 `plane_first_fundamental` 替代（这才是可证的真核）。
5. **`christoffel_depends_only_on_first_fundamental`**（上游 `sorry`）：
   命题本身**为真**（`christoffel_second` 只读 `first_fundamental`），
   但 `christoffel_second` 的 `h := 1e-6` 是**硬编码常量**，函数外延相等即得，
   证明只需 `congr`。→ 归 **(B)**，本文件给出真证明（无 sorry）。
6. **`zero_curvature_implies_flat`**（上游 `sorry`）：结论是
   `principal_curvatures` 的**乘积 = K**，而这已由 `principal_curvatures_product_eq_gaussian`
   覆盖（上游该引理有真证明）。→ 由该引理**直接推出**，去除 sorry。
7. **`lv.Basic` / `lv.Incidence` 等的"公理"**：核实结论——
   **全部是 `class` / `structure` 的字段**（`class Incidence` 的 `I1/I2/I3`、
   `class Betweenness` 的 `B1/B2/B3`、`class HCongruence` 的 `C1..C5_SAS`、
   `class Continuity` 的 `archimedes/dedekind`、`structure HilbertPlane extends ...`），
   **没有任何 Lean `axiom`**。因此"公理是**假设**而非公理"的判断**成立**，
   可以安全搬运，本文件全部按 `class`/`structure` 字段形式保留。
   注意 反向发现：`lvFormal/Classical/Hilbert/Consistency.lean:147,157` 与
   `lvFormal/Interop/Equivalence.lean:339..` 等处**确有真 `axiom`**，
   但**均不在本文件采集范围内**（Consistency 未被采、Interop 不在几何主题内），
   故本文件内部**零 `axiom`**。
8. **`lv/` 目录 = `Classical/Hilbert/` 的逐字节重复**（10 个文件全部字节级相同）。
   → 归 **(C) 重复**，只采一份。
9. **`GeometrySymbolicsTheory` 的 `RationalNumber` / `QuadraticNumber` / `AlgebraicNumber`
   / `TranscendentalNumber` 四个类型**：它们被 `SymbolicCoord`、`withinCircuitLimit`、
   `serialize` 引用，但**定义体在抽取的顶层注释块中被吞掉了**（上游文件第 30-41 行、
   第 133-149 行的 `/-! ... -/` 未闭合，导致后续 `theorem` 落在注释里）。
   → 这解释了为什么上游能"0 sorry"却"有 1217 定理"：**部分定理根本没被 Lean 看到**。
   本文件**重建**这四个类型为显式结构（见下），使 `SymbolicCoord` 真正可用。
-/

import Mathlib
import Lattice.Lib.Chain.RealLv00GeometryHilbert
import Lattice.Lib.Chain.RealLv00GeometrySymbolics
import Lattice.Lib.Chain.RealLv00GeometryAnalytic
import Lattice.Lib.Chain.RealLv00GeometryDifferential
import Lattice.Lib.Chain.RealLv00GeometryCSG
/-!
> **拆分说明（2026-10-15）**：本文件原含 **172 个声明**、1579 行。声明已按文件自身的
> 五个 `## 第N部分` 分节拆入 5 个模块，本文件**改为 re-export 门面**：
>
> | 子模块 | 原行范围 | 原分节 | 声明数 |
> |:--|:--|:--|--:|
> | `RealLv00GeometryHilbert` | 120–319 | 第一部分：经典（Hilbert）公理几何 | 16 |
> | `RealLv00GeometrySymbolics` | 320–548 | 第二部分：符号数 | 28 |
> | `RealLv00GeometryAnalytic` | 549–809 | 第三部分：平面解析几何 | 35 |
> | `RealLv00GeometryDifferential` | 810–1325 | 第四部分：微分几何 | 62 |
> | `RealLv00GeometryCSG` | 1326–1577 | 第五部分：CSG | 31 |
> | **合计** | | | **172** |
>
> 采用**连续切分**（每模块覆盖连续行区间并 import 紧邻前驱）。Lean 按顺序展开顶层声明，
> 故文件顺序**本身就是**拓扑序，无需手写依赖表。
>
> 子模块**与门面本身**均已注册进 `lakefile.toml` 的 `roots`：只注册子模块会让门面的 olean
> 保持陈旧，拆分将**语义上无效**而构建仍报成功。
-/
