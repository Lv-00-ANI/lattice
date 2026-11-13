import Lattice.Reference.Geometry.Constraints.ComputableExpr
import Lattice.Reference.Geometry.Constraints.Constraint
import Lattice.Reference.Geometry.Constraints.ConstraintSet
import Lattice.Reference.Geometry.Constraints.ConstraintTokenizer
import Lattice.Reference.Geometry.Constraints.Differentiable
import Lattice.Reference.Geometry.Constraints.Dist
import Lattice.Reference.Geometry.Constraints.DistContinuous
import Lattice.Reference.Geometry.Constraints.DistLipschitz
import Lattice.Reference.Geometry.Constraints.EqConstraintListTokens
import Lattice.Reference.Geometry.Constraints.EqConstraintToken
import Lattice.Reference.Geometry.Constraints.EqConstraintTokenizer
import Lattice.Reference.Geometry.Constraints.EqConstraintTokens
import Lattice.Reference.Geometry.Constraints.Eval
import Lattice.Reference.Geometry.Constraints.Expr
import Lattice.Reference.Geometry.Constraints.ExprDeriv
import Lattice.Plugins.Domains.Constraints.Tokens.Flatten
import Lattice.Reference.Geometry.Constraints.FlattenAgreement
import Lattice.Reference.Geometry.Constraints.Lipschitz
import Lattice.Reference.Geometry.Constraints.Loss
import Lattice.Reference.Geometry.Constraints.NetLoss
import Lattice.Plugins.Domains.Constraints.Penalty.PenaltyLoss
import Lattice.Reference.Geometry.Constraints.Perturb
import Lattice.Reference.Geometry.Constraints.Pipeline
import Lattice.Reference.Geometry.Constraints.RealToken
import Lattice.Reference.Geometry.Constraints.RealTokenRoundtrip
import Lattice.Plugins.Domains.Constraints.Tokens.SeqRepresentation
import Lattice.Primitives.TokenizeStrategy
import Lattice.Primitives.TokenizerPattern
import Lattice.Reference.Geometry.Constraints.DistDerivative
import Lattice.Reference.Geometry.Constraints.ExprDerivative
import Lattice.Reference.Geometry.Constraints.PenaltyLossDerivative
import Lattice.Plugins.Domains.Constraints.Penalty.NetLossDerivative
import Lattice.Reference.Geometry.Constraints.FlatLoss
import Lattice.Plugins.Domains.Constraints.Tokens.LossExtraction
/-!
# `Lattice.Domains.Constraints`

## 这一半是什么

约束语义、损失、距离、表达式与分词：`Domains` 的**下层**（28 个模块）。**它不 import `Geometry` 的任何模块**——这是划分的依据，不是命名。

## 边界（第 246 轮的子划分）

实测：本半对另一侧的边数为 **0**；另一侧对本半为 71 条。（第一版按入度切分留下 5 条反向边，**被否决**。）
-/