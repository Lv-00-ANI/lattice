# `Zero/Geo/` 证明链地图

> 由 `gov/proof_chain_geo.py` 生成。

本层是重建的符号侧：把几何约束变成可以喂给权重层的平方损失。

## 一、拓扑分层

依赖严格向下，无环。自底向上读：

## 二、四条靶定理在几何层中的落点

### T1 编译保语义

| 文件 | 声明 |
|:--|:--|
| `Lattice/LvFormal/Theory/CompilerCorrectness.lean` | `compile_preserves_satisfiability` **（缺失）** |

### T2 约束嵌入可靠

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Exact.lean` | `geo_penalty_exact` **（缺失）** |
| `Lattice/Geo/Nondegenerate.lean` | `perpResid_bump` **（缺失）** |
| `Lattice/Geo/Differentiable.lean` | `hasFDerivAt_coord` **（缺失）** |
| `Lattice/Lib/Penalty/PolyExact.lean` | `sq_eq_zero_of_localMin` |

### T3 提取等价

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Extract.lean` | `configOf` **（缺失）** |
| `Lattice/Geo/Extract.lean` | `perp_neg_iff` **（缺失）** |
| `Lattice/Geo/Flatten.lean` | `flattenEquiv` **（缺失）** |

### T4 回路收敛

| 文件 | 声明 |
|:--|:--|
| `Lattice/Geo/Repair.lean` | `no_identity_repair` **（缺失）** |
| `Lattice/Core/Repair.lean` | `progress` |

## 三、一条贯穿的读法

1. **`Expr.lean`** 定义 `GeoExpr n`：以点的坐标为原子的多项式表达式。
2. **`Dist.lean`** 把距离的平方 `sqDist` 定义为多项式，并证明 `dist = d ⟹ sqDist = d²`（`Real.sqrt_inj`），从而消去平方根。
3. **`Constraint.lean`** 把几何约束按多项式层 / 平方层分开；超越层（角度）被**排除在类型之外**，而不是假装可代数化。
4. **`Loss.lean`** 把等式约束变成平方损失 `f²`；`EqConstraint` 的类型只含可损失化的层。
5. **`Flatten.lean`** 把配置压成有限向量，并证明**对象层双射**。
6. **`Differentiable.lean`** 证明坐标为投影，从而残差可微。
7. **`Perturb.lean` + `Nondegenerate.lean`** 用坐标扰动证明残差沿方向的线性响应，这是梯度非零的基础。
8. **`Exact.lean`** 接上 `Zero/Lib/Penalty/PolyExact`：非退化局部极小 ⟹ 约束成立。
9. **`Extract.lean`** 是反方向：从权重向量读回配置与它所满足的约束；`perp_neg_iff` 是**语义层不可逆**的一个具体实例。

## 四、刻意不做的事

| 未做 | 理由 |
|:--|:--|
| 超越层（`angle` / `equalAngle`） | 含 `Real.cos`，不可能是多项式；排除在 `GeoConstraint` 之外 |
| `eqZero`（`leZero` / `ltZero`）的损失 | 不等式不是任何东西的零点集，强行写成 `g²` 是掺假 |
| `collinear` 的损失 | 陈述含存在量词，未消元前无法构造损失 |
| 一般 `GeoExpr` 的可微性 | 需要按表达式结构归纳；两个承载几何内容的约束不需要它 |
