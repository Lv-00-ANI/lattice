"""The body extraction is wrong: `(?=\\n(?:theorem|lemma|def|end)\\b|\\Z)` stops at the first
top-level `end` OR at a nested `end` of a `cases` block, so most bodies came out empty.

Correct approach: from `:=` take everything to the NEXT declaration at column 0, or EOF.
Nested blocks are indented, so an un-indented `theorem|lemma|def|structure|end` is the boundary.
"""
import io
import os
import re
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
LAT = _os.path.join(_REPO, "Lattice")

KEYWORDS = {
    "exact", "intro", "apply", "rw", "simp", "by", "fun", "have", "show", "refine",
    "constructor", "cases", "rcases", "obtain", "the", "and", "one", "zero", "that",
    "layer", "point", "this", "refl", "rfl", "at", "all", "first", "then", "with",
    "using", "from", "let", "in", "if", "else", "match", "do", "omega", "norm_num",
    "decide", "ring", "linarith", "nlinarith", "subst", "induction", "calc", "trans",
    "ext", "funext", "congr", "congrArg", "Or", "And", "Prop", "Type", "Nat", "Int",
    "Real", "List", "Set", "Finset", "Function",
}


def strip_comments(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if not depth:
            out.append(src[i])
        i += 1
    return "".join(out)


RUNGS = {
    "decodePayload_encodeForm": "Lift/L1L2Roundtrip.lean",
    "compileProgram_sound": "Lift/SymbolToWeight.lean",
    "extract_compile": "Lift/Extraction.lean",
    "converges_within": "Core/RepairConvergence.lean",
    "loss_eq_zero_of_poly_eq_zero": "Geo/Reinjection.lean",
    "residual_le_of_zero_on_dense": "Lift/VerificationSoundness.lean",
    "ladder_forward": "Lift/EndToEnd.lean",
    "sound_of_factors": "Lift/EncodingAbstraction.lean",
    "scheme_covers_all": "Lift/CompilerScheme.lean",
    "reinject_of_hold": "Geo/ReinjectionGeneral.lean",
    "decreases_of_one_step": "Audit/DecreasesRole.lean",
    "absorbs_not_derivable": "Audit/ObligationIndependence.lean",
}

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive|class)"
                  r"[ \t]+([A-Za-z0-9_'!?]+)")
all_names = set()
for root, _, fs in os.walk(LAT):
    if "Reference" in root:
        continue
    for f in fs:
        if not f.endswith(".lean"):
            continue
        t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
        for m in DECL.finditer(t):
            all_names.add(m.group(1))
all_names -= KEYWORDS

print("=== rung theorems: kernel declarations cited in their proofs ===\n")
total = 0
for name, f in RUNGS.items():
    p = os.path.join(*([LAT] + f.split("/")))
    t = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
    m = re.search(r"(?m)^(?:noncomputable\s+)?(?:theorem|lemma|def)\s+" + re.escape(name) + r"\b", t)
    if not m:
        print("%-32s DECL NOT FOUND" % name)
        continue
    rest = t[m.start():]
    # body runs to the next column-0 declaration or `end`
    nb = re.search(r"(?m)^(?:theorem|lemma|def|structure|abbrev|inductive|class|end|namespace)\b", rest[m.end() - m.start():])
    body = rest[m.end() - m.start(): m.end() - m.start() + (nb.start() if nb else len(rest))]
    cited = sorted({w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body)
                    if w in all_names and w != name})
    total += len(cited)
    print("%-32s cites %2d" % (name, len(cited)))
    for c in cited[:5]:
        print("      %s" % c)
print("\ntotal: %d" % total)
