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

#: The shape test: what a training step looks like operationally -- parameters in, parameters out.
#:
#: Round 170. `PARAM_NAMES` here used to be `["params", "weights", "θ", "theta", "net", "model"]`:
#: VARIABLE names, and it was defined and never used, so the docstring's promise of a "shape test" was
#: not kept. Variable names are the wrong axis anyway -- the checker reads signatures, where the
#: variable name is nearly always `x`, `p` or `q`.
#:
#: So the shape test works on TYPE names. A training step carries the same parameter-carrying type on
#: the argument side and the return side: `def update (p : Params) : Params`. Legitimate conversions in
#: this tree carry DIFFERENT types across that arrow (`def ofParams (q : LayerParams n n) :
#: AffineLayer n`), which is what keeps the test from firing on them.
PARAM_TYPES = ["Params", "Weights", "Tensor", "Tensors", "Optimizer", "Grads"]

#: `def <name>` -- the signature is taken as the text from here to the first `:=` (or `where`).
#:
#: The first attempt used one regex that required a NEWLINE inside the signature, so every single-line
#: `def update (p : Params) : Params := p` was skipped and the shape test silently tested nothing. The
#: self-test caught it: "a parameters-in/parameters-out def was accepted".
DEF_START = re.compile(r"(?m)^(?:noncomputable\s+|private\s+|protected\s+)?def\s+(\w+)")


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
        # the shape test: a parameter-carrying type appears on BOTH sides of the arrow
        for m in DEF_START.finditer(src):
            tail = src[m.end():m.end() + 800]
            cut = tail.find(":=")
            wc = tail.find("\nwhere")
            if cut < 0 or (0 <= wc < cut):
                cut = wc
            sig = tail[:cut] if cut >= 0 else tail
            for T in PARAM_TYPES:
                # twice in one signature = argument side and return side
                if len(re.findall(r"\b%s\b" % re.escape(T), sig)) >= 2:
                    hits.append((rel, src[:m.start()].count("\n") + 1, m.group(1),
                                 "parameters-in/parameters-out (%s)" % T))
                    break
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
            # (c) the SHAPE test: an innocuously named training step. Its name is on no list, so only
            # the signature can catch it -- this is the case PARAM_TYPES exists for, and the case the
            # old unused `PARAM_NAMES` claimed to cover and did not.
            io.open(os.path.join(d, "C.lean"), "w", encoding="utf-8").write(
                "structure Params where\n  v : List Float\n\n"
                "def update (p : Params) : Params := p\n")
            # (d) a legitimate conversion: DIFFERENT types across the arrow, must be accepted
            io.open(os.path.join(d, "D.lean"), "w", encoding="utf-8").write(
                "structure Params where\n  v : List Float\n\n"
                "structure Layer where\n  w : List Float\n\n"
                "def ofParams (q : Params) : Layer := ⟨q.v⟩\n")
            found = scan({n: io.open(os.path.join(d, n), encoding="utf-8").read()
                          for n in ("A.lean", "B.lean", "C.lean", "D.lean")})
            names = {w for _, _, w, _ in found}
            if "trainStep" not in names:
                print("SELF-TEST FAILED: a training loop was accepted")
                return 2
            if "fomamlGrad" in names:
                print("SELF-TEST FAILED: a gradient FORMULA was rejected")
                return 2
            if "update" not in names:
                print("SELF-TEST FAILED: a parameters-in/parameters-out def was accepted"
                      " (the shape test did not fire)")
                return 2
            if "ofParams" in names:
                print("SELF-TEST FAILED: a type-changing conversion was rejected")
                return 2
        finally:
            import shutil
            shutil.rmtree(d, ignore_errors=True)
        print("SELF-TEST: training loops caught by name, parameters-in/parameters-out caught by"
              " shape, gradient formulas and type-changing conversions accepted")
        return 0

    if hits:
        print()
        print("SCOPE BOUNDARY: %d executable-framework marker(s) -- the objective forbids implementing"
              " an engine, model or training framework" % len(hits))
        return 1

    # Round 179, P2-7. The positioning has TWO halves and they must agree with each other:
    #   "it is a general infrastructure / certification layer"   and   "it does not implement a
    #   framework".
    # README's subtitle used to call it a "训练 / 后训练框架" while the positioning block four lines
    # below said it does NOT implement a training framework. Both sentences were in the same document,
    # nine lines apart, and nothing compared them -- the code half of the boundary was guarded and the
    # prose half was not.
    doc_problems = positioning_docs()
    for rel, line, text in doc_problems:
        print("  SELF-CONTRADICTION %s:%d  %s" % (rel, line, text))
    if doc_problems:
        print()
        print("SCOPE BOUNDARY: the documents call this a framework while also saying it does not"
              " implement one")
        return 1

    print("SCOPE BOUNDARY: no training loop, optimiser structure or Module-style forward;"
          " and no document calls it a framework while denying it implements one")
    return 0


#: Phrases that ASSERT the project IS a framework -- as an ASSERTION, not a mention.
#:
#: Round 179. The first version flagged any occurrence of the words, and reported two false positives in
#: a row: `STATE-FINAL` "目标排除的是「实现引擎/模型/训练框架」" (quoting the exclusion) and `README` "按
#: 「训练框架」衡量的分数" (quoting the phrase as a yardstick it rejects). Mentioning a phrase is not
#: claiming it, and chasing that with a regex over prose is a losing game.
#:
#: So the rule is now the narrow assertion shape: the words must appear as the PREDICATE of the project
#: -- "…的训练/后训练框架" with no quoting mark immediately before them, i.e. the README subtitle's
#: actual defect.
CLAIMS_TO_BE_FRAMEWORK = re.compile(r"(?<![「」\"'])(?:训练|后训练)\s*/\s*后训练框架|(?<![「」\"'])训练框架(?![」」\"'])\s*[，。,]$")

#: Phrases that DENY implementing a framework. If one of these is present, the document is claiming the
#: exclusion, and any `CLAIMS_TO_BE_FRAMEWORK` hit in the same document is a contradiction.
DENIES_FRAMEWORK = re.compile(r"不实现[^。\n]{0,20}(?:训练)?框架|不实现引擎、模型")


def positioning_docs():
    """Documents that both claim to be a framework and deny implementing one."""
    import glob
    out = []
    root = os.path.abspath(os.path.join(HERE, ".."))
    for p in sorted(glob.glob(os.path.join(root, "*.md"))):
        base = os.path.basename(p)
        if base.startswith("ROADMAP-v"):
            continue  # frozen: describes the tree at the time
        text = io.open(p, encoding="utf-8", errors="replace").read()
        if not DENIES_FRAMEWORK.search(text):
            continue
        for i, ln in enumerate(text.split("\n"), 1):
            if not CLAIMS_TO_BE_FRAMEWORK.search(ln):
                continue
            # A line that quotes the EXCLUSION ("the objective excludes implementing an engine / model
            # / training framework") names the phrase without claiming it. The first run flagged
            # exactly such a line in STATE-FINAL.md, so quotation context is excluded here rather than
            # by trying to make the regex clever about grammar.
            if QUOTES_EXCLUSION.search(ln):
                continue
            out.append((base, i, ln.strip()[:80]))
    return out


#: A line that mentions the excluded thing in order to EXCLUDE it -- quoting the objective's own
#: exclusion is not a claim to be that thing.
QUOTES_EXCLUSION = re.compile(r"排除|不实现|禁止|不得|不做|不可")


if __name__ == "__main__":
    sys.exit(main(sys.argv))
