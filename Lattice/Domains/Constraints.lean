import Lattice.Domains.Constraints.ComputableExpr
import Lattice.Domains.Constraints.Constraint
import Lattice.Domains.Constraints.ConstraintSet
import Lattice.Domains.Constraints.ConstraintTokenizer
import Lattice.Domains.Constraints.Differentiable
import Lattice.Domains.Constraints.Dist
import Lattice.Domains.Constraints.DistContinuous
import Lattice.Domains.Constraints.DistLipschitz
import Lattice.Domains.Constraints.EqConstraintListTokens
import Lattice.Domains.Constraints.EqConstraintToken
import Lattice.Domains.Constraints.EqConstraintTokenizer
import Lattice.Domains.Constraints.EqConstraintTokens
import Lattice.Domains.Constraints.Eval
import Lattice.Domains.Constraints.Expr
import Lattice.Domains.Constraints.ExprDeriv
import Lattice.Domains.Constraints.Flatten
import Lattice.Domains.Constraints.FlattenAgreement
import Lattice.Domains.Constraints.Lipschitz
import Lattice.Domains.Constraints.Loss
import Lattice.Domains.Constraints.NetLoss
import Lattice.Domains.Constraints.PenaltyLoss
import Lattice.Domains.Constraints.Perturb
import Lattice.Domains.Constraints.Pipeline
import Lattice.Domains.Constraints.RealToken
import Lattice.Domains.Constraints.RealTokenRoundtrip
import Lattice.Domains.Constraints.SeqRepresentation
import Lattice.Primitives.TokenizeStrategy
import Lattice.Primitives.TokenizerPattern

/-!
# `Lattice.Domains.Constraints`

## 这一半是什么

约束语义、损失、距离、表达式与分词：`Domains` 的**下层**（28 个模块）。**它不 import `Geometry` 的任何模块**——这是划分的依据，不是命名。

## 边界（第 246 轮的子划分）

实测：本半对另一侧的边数为 **0**；另一侧对本半为 71 条。（第一版按入度切分留下 5 条反向边，**被否决**。）
-/