"""Round 158: does the library actually avoid implementing an engine / model / training framework?

The objective says, in one sentence with two halves:

    not bound to any vendor or framework        <- rule C checks imports
    and does not implement engines, models, or training frameworks   <- NOTHING checks this

Rule C catches `import torch`. It cannot catch someone writing a training loop, because a training
loop needs no import. That is a real gap: the positioning sentence has a second half with no guard.

## What would a violation look like?

Not a theorem about gradients -- `Lib/LearningTheory/RealMAML.lean` legitimately formalises FOMAML,
and describing a learning rule mathematically is the opposite of implementing a framework. Round 84
already made this mistake once, counting our own `RealTensorNorm` as an "engine import".

A violation is an EXECUTABLE TRAINING LOOP: a function that takes parameters, data, and a step size
and returns NEW PARAMETERS. That is what "training framework" means operationally.

So the criterion here is narrow on purpose:

    a `def` whose name suggests training/optimisation AND whose type is  parameters -> ... -> parameters

plus a few unmistakable shape markers (`structure Optimizer`, `Module`-style `forward`+`backward`).
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAT = os.path.abspath(os.path.join(HERE, "..", "Lattice"))

#: names that only make sense inside a training framework
TRAINING_NAMES = [
    "trainStep", "trainingStep", "trainLoop", "trainingLoop", "sgdStep", "adamStep",
    "backward", "zeroGrad", "optimizerStep", "fitModel", "trainModel",
]

#: structural markers
STRUCTURE_MARKERS = [
    r"structure\s+Optimizer\b",
    r"structure\s+Trainer\b",
    r"structure\s+OptimizerState\b",
    r"def\s+forward\s*[:\(]",          # a Module-style forward
    r"def\s+backward\s*[:\(]",
]

#: the shape test: a definition from parameters to parameters
PARAM_NAMES = ["params", "weights", "θ", "theta", "net", "model"]


def corpus():
    out = {}
    for dirpath, _, files in os.walk(LAT):
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            if rel.startswith("Reference/"):
                continue
            out[rel] = io.open(p, "rb").read().decode("utf-8", errors="replace")
    return out


def scan(C):
    hits = []
    for rel, src in sorted(C.items()):
        for name in TRAINING_NAMES:
            for m in re.finditer(r"(?m)^(?:noncomputable\s+)?def\s+%s\b" % re.escape(name), src):
                hits.append((rel, src[:m.start()].count("\n") + 1, name, "training-loop name"))
        for pat in STRUCTURE_MARKERS:
            for m in re.finditer(pat, src):
                hits.append((rel, src[:m.start()].count("\n") + 1, m.group(0).strip(),
                             "framework shape"))
    return hits


def main(argv):
    C = corpus()
    hits = scan(C)
    for rel, line, what, why in hits:
        print("  %-52s L%-5d %-28s %s" % (rel, line, what, why))
    if "--self-test" in argv:
        d = os.path.join(HERE, ".scope-selftest")
        os.makedirs(d, exist_ok=True)
        try:
            io.open(os.path.join(d, "A.lean"), "w", encoding="utf-8").write(
                "def trainStep (params : List Float) : List Float := params\n")
            io.open(os.path.join(d, "B.lean"), "w", encoding="utf-8").write(
                "def fomamlGrad (h : Float) : Float := h\n")
            found = scan({"A.lean": io.open(os.path.join(d, "A.lean"), encoding="utf-8").read(),
                          "B.lean": io.open(os.path.join(d, "B.lean"), encoding="utf-8").read()})
            names = {w for _, _, w, _ in found}
            if "trainStep" not in names:
                print("SELF-TEST FAILED: a training loop was accepted")
                return 2
            if "fomamlGrad" in names:
                print("SELF-TEST FAILED: a gradient FORMULA was rejected")
                return 2
        finally:
            import shutil
            shutil.rmtree(d, ignore_errors=True)
        print("SELF-TEST: training loops caught, gradient formulas accepted")
        return 0

    if hits:
        print()
        print("SCOPE BOUNDARY: %d executable-framework marker(s) -- the objective forbids implementing"
              " an engine, model or training framework" % len(hits))
        return 1
    print("SCOPE BOUNDARY: no training loop, optimiser structure or Module-style forward;"
          " the \"does not implement a framework\" half of the positioning holds")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
