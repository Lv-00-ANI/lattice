import Lattice.Runtime.VecCarrierCensus
import Lattice.Runtime.DotTruncationDefect
import Lattice.Runtime.ActivationLadder
import Lattice.Runtime.ApproxExact
import Lattice.Runtime.ApproxExtraction
import Lattice.Runtime.ApproxLadder
import Lattice.Runtime.ApproximationBridge
import Lattice.Runtime.ChainComposition
import Lattice.Runtime.ComboN
import Lattice.Runtime.CompilerScheme
import Lattice.Runtime.ConstraintEmbeddingSoundness
import Lattice.Runtime.ConstraintRepresentation
import Lattice.Runtime.ConstraintToLoss
import Lattice.Runtime.ConvertLinear
import Lattice.Runtime.ConvertVectorLinear
import Lattice.Runtime.EncodingAbstraction
import Lattice.Runtime.EndToEnd
import Lattice.Runtime.EndToEndApproximation
import Lattice.Runtime.ErrorCalculus
import Lattice.Runtime.Extraction
import Lattice.Runtime.ExtractionStrength
import Lattice.Runtime.GeoSampledBound
import Lattice.Runtime.GridDensity
import Lattice.Runtime.IntRoundtrip
import Lattice.Runtime.L1L2
import Lattice.Runtime.L1L2Roundtrip
import Lattice.Runtime.LayerComposition
import Lattice.Runtime.LayerQuantization
import Lattice.Runtime.LayerQuantizationBits
import Lattice.Runtime.LayerNormSemantics
import Lattice.Runtime.LossyRepresentation
import Lattice.Runtime.MultiLayerLadder
import Lattice.Runtime.NonIdenticalEncoding
import Lattice.Runtime.NondegenerateInstance
import Lattice.Runtime.PenaltyAnalysis
import Lattice.Runtime.PenaltyEmbedding
import Lattice.Runtime.PartialRepresentation
import Lattice.Runtime.ProgramAST
import Lattice.Runtime.ProgramLipschitz
import Lattice.Runtime.ProgramRepresentation
import Lattice.Runtime.QuantErrorPropagation
import Lattice.Runtime.RatRepresentation
import Lattice.Runtime.RealLV
import Lattice.Runtime.RealLinear
import Lattice.Runtime.RealModLoss
import Lattice.Runtime.RealNonlinear
import Lattice.Runtime.RealRandomVerify
import Lattice.Runtime.RealTokenSymbolLink
import Lattice.Runtime.RealTokenization
import Lattice.Runtime.RealTokenizationEntry
import Lattice.Runtime.RealTotalLoss
import Lattice.Runtime.RealVerifierReliable
import Lattice.Runtime.RectangularRepresentation
import Lattice.Runtime.RectangularWeightEncoding
import Lattice.Runtime.RepresentationFamilies
import Lattice.Runtime.RoundingBackend
import Lattice.Runtime.SaturationQuantization
import Lattice.Runtime.StackCodegen
import Lattice.Runtime.StackError
import Lattice.Runtime.SemanticRepresentation
import Lattice.Runtime.SymbolToWeight
import Lattice.Runtime.SymbolToWeightCorrectness
import Lattice.Runtime.TokenAlphabet
import Lattice.Runtime.TotalLoss
import Lattice.Runtime.VerificationSoundness
import Lattice.Runtime.VerifierRate
import Lattice.Runtime.VerifyLoopProgress
import Lattice.Runtime.WeightLadder
import Lattice.Runtime.WeightLadderFullWidth
import Lattice.Runtime.WeightLadderFullWidthInstance
import Lattice.Runtime.WeightLadderInverse
import Lattice.Runtime.WeightLadderN
import Lattice.Runtime.WeightSymbolRepresentation
import Lattice.Runtime.WeightToSymbolEquivalence
import Lattice.Runtime.LadderClosure
import Lattice.Runtime.VerificationLoop
import Lattice.Runtime.CICToConstraint
import Lattice.Runtime.CICToConstraintSet
import Lattice.Runtime.DataToConstraint
import Lattice.Runtime.AcceptanceLayer
import Lattice.Runtime.EndToEndComposite
import Lattice.Runtime.ExtractionClosure
import Lattice.Runtime.LoopClosure
import Lattice.Runtime.Faithfulness
import Lattice.Runtime.SemanticFaithfulness
import Lattice.Runtime.RepairClosure
import Lattice.Runtime.TypedNumericAlignment
import Lattice.Runtime.EngineFirst
import Lattice.Runtime.EngineSemantics
import Lattice.Runtime.EngineReduces
import Lattice.Runtime.ScopeBoundary
import Lattice.Runtime.StructuredInit
import Lattice.Runtime.HopExpressiveness

/-!
# `Lattice.Runtime` —— 运行语义层（P2 目标层的聚合器）

按 `DIRECTORY-DESIGN.md` §3，`Runtime/` 放操作语义；它由 `Lift/` 的搬迁填充。
**第 242 轮搬迁完成**：`Lift/` 的 66 个模块全部在此，`Lattice/Lift/` 已清空，
`Lattice/Lift.lean` 一并删除（没有第二条聚合路径，见 §2.8 的「零轮」定义）。

## 为什么这个文件是必要的，而不只是整齐

`lakefile.toml` 只声明了 `roots = ["Lattice"]`，所以 `lake build Lattice` **只构建从根可达的闭包**。
第 239 轮实测到后果：`Lattice/Runtime/ConstraintToLoss.lean` 无人 import，
它的 olean 是历史遗留；批量搬迁删掉那个 olean 之后，**没有任何构建会把它重建**，
而 I7（每个源模块必须有 olean）就在这时报了红。

**这暴露的是一个盲点**：一个孤岛模块只要有**遗留 olean**，I7 就通过，
而它**从未被重新编译**——所以如果它坏了，没有任何东西会发现。
全库范围这个盲点只落在 `Reference/`（冻结区，按设计不编译）；
**但在新层里不应存在**，因为新层是活代码。

**所以本文件 import `Runtime/` 下的每一个模块**：新层从此没有孤岛，
每个模块都在 `lake build Lattice` 的闭包里。

⚠ **这是一条纪律，不是一次性修补**：以后往 `Runtime/` 加模块，
必须同时加进这里，否则它不在构建闭包内。
-/
