"""The `PATH_MAP`: old module path -> new module path, for PROOF-DEBT's key join.

## Why this is its own module

Round 234 first put `PATH_MAP` inside `gen_proof_debt.py` and had `check_proof_debt_orphans.py` do
`from gen_proof_debt import PATH_MAP`. **That made the checker regenerate `PROOF-DEBT.md` as a side
effect**, because `gen_proof_debt.py` writes the file at module scope. A checker must not write the
artifact it is checking.

This is the same lesson as `_debt_coverage.py` in round 226: **anything a checker imports must be safe to
import.** One module, one job.

## What it is for

`DIRECTORY-DESIGN.md` §2.8 says "`PROOF-DEBT` is regenerated with a `PATH_MAP`". **That mechanism did not
exist** until round 234. Without it, a `git mv` silently orphans every verdict for the moved file: the
inventory join misses, `in_degree` falls back to 0, and the ledger reports a reviewed file as unreviewed
**while the coverage table still claims 100% of the load-bearing set**.

Paths are relative to `Lattice/`, matching the `file` field in `verdicts_*.jsonl`.
"""

#: (old path relative to Lattice/) : (new path relative to Lattice/)
PATH_MAP = {
    # round 234, P2 pilot: the first module moved out of `Lift/`
    "Lift/ProgramAST.lean": "Runtime/ProgramAST.lean",
    # round 237, batch A1: the five `Lift/` modules that import NO other Lattice module at all
    "Lift/ComboN.lean": "Runtime/ComboN.lean",
    "Lift/RealLinear.lean": "Runtime/RealLinear.lean",
    "Lift/StackCodegen.lean": "Runtime/StackCodegen.lean",
    "Lift/ErrorCalculus.lean": "Runtime/ErrorCalculus.lean",
    "Lift/PenaltyAnalysis.lean": "Runtime/PenaltyAnalysis.lean",
    # round 238, batch A2: the remaining batch-A modules, plus the ProgramAST alias removed
    "Lift/ConvertVectorLinear.lean": "Runtime/ConvertVectorLinear.lean",
    "Lift/RealModLoss.lean": "Runtime/RealModLoss.lean",
    "Lift/RealNonlinear.lean": "Runtime/RealNonlinear.lean",
    "Lift/RealRandomVerify.lean": "Runtime/RealRandomVerify.lean",
    "Lift/RealTokenization.lean": "Runtime/RealTokenization.lean",
    "Lift/RealVerifierReliable.lean": "Runtime/RealVerifierReliable.lean",
    "Lift/Extraction.lean": "Runtime/Extraction.lean",
    "Lift/L1L2.lean": "Runtime/L1L2.lean",
    "Lift/PenaltyEmbedding.lean": "Runtime/PenaltyEmbedding.lean",
    "Lift/RepresentationFamilies.lean": "Runtime/RepresentationFamilies.lean",
    "Lift/SymbolToWeight.lean": "Runtime/SymbolToWeight.lean",
    # round 239, batch A3 = prefix 1 of the Lift graph (14 modules, zero internal deps)
    "Lift/CompilerScheme.lean": "Runtime/CompilerScheme.lean",
    "Lift/ConstraintToLoss.lean": "Runtime/ConstraintToLoss.lean",
    "Lift/ConvertLinear.lean": "Runtime/ConvertLinear.lean",
    "Lift/EndToEnd.lean": "Runtime/EndToEnd.lean",
    "Lift/GridDensity.lean": "Runtime/GridDensity.lean",
    "Lift/L1L2Roundtrip.lean": "Runtime/L1L2Roundtrip.lean",
    "Lift/LossyRepresentation.lean": "Runtime/LossyRepresentation.lean",
    "Lift/NonIdenticalEncoding.lean": "Runtime/NonIdenticalEncoding.lean",
    "Lift/RatRepresentation.lean": "Runtime/RatRepresentation.lean",
    "Lift/RealTokenizationEntry.lean": "Runtime/RealTokenizationEntry.lean",
    "Lift/RealTotalLoss.lean": "Runtime/RealTotalLoss.lean",
    "Lift/SymbolToWeightCorrectness.lean": "Runtime/SymbolToWeightCorrectness.lean",
    "Lift/VerificationSoundness.lean": "Runtime/VerificationSoundness.lean",
    "Lift/VerifierRate.lean": "Runtime/VerifierRate.lean",
    # round 241, batch A4 = the next closed prefix of the Lift graph
    "Lift/ActivationLadder.lean": "Runtime/ActivationLadder.lean",
    "Lift/ApproxExact.lean": "Runtime/ApproxExact.lean",
    "Lift/ChainComposition.lean": "Runtime/ChainComposition.lean",
    "Lift/ConstraintEmbeddingSoundness.lean": "Runtime/ConstraintEmbeddingSoundness.lean",
    "Lift/EncodingAbstraction.lean": "Runtime/EncodingAbstraction.lean",
    "Lift/GeoSampledBound.lean": "Runtime/GeoSampledBound.lean",
    "Lift/LayerComposition.lean": "Runtime/LayerComposition.lean",
    "Lift/RealLV.lean": "Runtime/RealLV.lean",
    "Lift/RealTokenSymbolLink.lean": "Runtime/RealTokenSymbolLink.lean",
    "Lift/RoundingBackend.lean": "Runtime/RoundingBackend.lean",
    "Lift/VerifyLoopProgress.lean": "Runtime/VerifyLoopProgress.lean",
    "Lift/WeightLadder.lean": "Runtime/WeightLadder.lean",
    "Lift/WeightLadderN.lean": "Runtime/WeightLadderN.lean",
    "Lift/WeightToSymbolEquivalence.lean": "Runtime/WeightToSymbolEquivalence.lean",
    # round 242, batch A5 = prefix 2 of the recomputed Lift graph (15 modules, closed under deps)
    "Lift/ApproxExtraction.lean": "Runtime/ApproxExtraction.lean",
    "Lift/ApproxLadder.lean": "Runtime/ApproxLadder.lean",
    "Lift/ApproximationBridge.lean": "Runtime/ApproximationBridge.lean",
    "Lift/EndToEndApproximation.lean": "Runtime/EndToEndApproximation.lean",
    "Lift/ExtractionStrength.lean": "Runtime/ExtractionStrength.lean",
    "Lift/IntRoundtrip.lean": "Runtime/IntRoundtrip.lean",
    "Lift/LayerQuantization.lean": "Runtime/LayerQuantization.lean",
    "Lift/LayerQuantizationBits.lean": "Runtime/LayerQuantizationBits.lean",
    "Lift/MultiLayerLadder.lean": "Runtime/MultiLayerLadder.lean",
    "Lift/NondegenerateInstance.lean": "Runtime/NondegenerateInstance.lean",
    "Lift/RectangularWeightEncoding.lean": "Runtime/RectangularWeightEncoding.lean",
    "Lift/TokenAlphabet.lean": "Runtime/TokenAlphabet.lean",
    "Lift/TotalLoss.lean": "Runtime/TotalLoss.lean",
    "Lift/WeightLadderFullWidth.lean": "Runtime/WeightLadderFullWidth.lean",
    "Lift/WeightLadderInverse.lean": "Runtime/WeightLadderInverse.lean",
}
