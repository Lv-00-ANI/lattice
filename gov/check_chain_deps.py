"""gov/check_chain_deps.py -- guard the claim "the chain composes via FIELDS, not re-proof".

Round 36 measured that `compileProgram_sound`, `extract_compile`, `ladder_forward` cite ZERO
kernel declarations: their content IS a structure field. That is a design property, and it can
silently decay -- e.g. if someone rewrites `ladder_forward` to reason from scratch, the claim
"the obligation lives in the field" quietly becomes false.

This checker records the expected citation counts and FAILS on any drift, in both directions:
a field-backed theorem that starts citing others means composition changed; a composed theorem
that stops citing means a dependency was inlined.

It is a checker, so it must be able to fail. `--self-test` plants a wrong expectation and
asserts the checker reports it.
"""
import io

# Round 238. This table hardcodes paths, which is the SAME defect as the three path-keyed baselines
# (PROOF-DEBT, proof_strength, underscore_hypotheses): after a `git mv` the lookup reports MISSING even
# though the theorem is right there under the new path. Measured this round: `extract_compile` and
# `compileProgram_sound` went MISSING because their modules moved to `Runtime/`.
# Fixed the same way -- resolve through the shared map, never edit the table for a move.
import os as _os
import sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from _debt_path_map import PATH_MAP
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
LAKE = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(LAKE, "Lattice")

# theorem -> (file, expected number of kernel declarations cited in its proof)
_RAW_EXPECTED = {
    "decodePayload_encodeForm": ("Lift/L1L2Roundtrip.lean", 5),
    "compileProgram_sound": ("Lift/SymbolToWeight.lean", 0),
    "extract_compile": ("Lift/Extraction.lean", 0),
    # Round 92: `RepairConvergence.lean` MOVED into the `Core.Repair` plugin's directory, so the
    # chain table must name its current home. The theorem is the same theorem; only the path moved.
    "converges_within": ("Plugins/Core/Repair/RepairConvergence.lean", 1),
    "loss_eq_zero_of_poly_eq_zero": ("Reference/Geometry/Geometry/Reinjection.lean", 1),
    "residual_le_of_zero_on_dense": ("Lift/VerificationSoundness.lean", 1),
    "ladder_forward": ("Lift/EndToEnd.lean", 0),
    "sound_of_factors": ("Lift/EncodingAbstraction.lean", 2),
    "scheme_covers_all": ("Lift/CompilerScheme.lean", 3),
    "reinject_of_hold": ("Reference/Geometry/Geometry/ReinjectionGeneral.lean", 2),
    "decreases_of_one_step": ("Evidence/DecreasesRole.lean", 1),
    "absorbs_not_derivable": ("Evidence/ObligationIndependence.lean", 5),
}

KEYWORDS = {
    "exact", "intro", "apply", "rw", "simp", "by", "fun", "have", "show", "refine",
    "constructor", "cases", "rcases", "obtain", "the", "and", "one", "zero", "that",
    "layer", "point", "this", "refl", "rfl", "at", "all", "first", "then", "with",
    "using", "from", "let", "in", "if", "else", "match", "do", "omega", "norm_num",
    "decide", "ring", "linarith", "nlinarith", "subst", "induction", "calc", "trans",
    "ext", "funext", "congr", "congrArg", "Or", "And", "Prop", "Type", "Nat", "Int",
    "Real", "List", "Set", "Finset", "Function", "True", "False", "Iff", "Not",
}

DECL = re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                  r"noncomputable[ \t]+)*(?:theorem|lemma|def|structure|abbrev|inductive|class)"
                  r"[ \t]+([A-Za-z0-9_'!?]+)")


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


def build_name_index():
    names = set()
    for root, _, fs in os.walk(LAT):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            t = io.open(os.path.join(root, f), "rb").read().decode("utf-8", errors="replace")
            for m in DECL.finditer(t):
                names.add(m.group(1))
    return names - KEYWORDS


def count_citations(name, relpath, name_index):
    p = os.path.join(*([LAT] + relpath.split("/")))
    if not os.path.exists(p):
        return None
    t = strip_comments(io.open(p, "rb").read().decode("utf-8", errors="replace"))
    m = re.search(r"(?m)^(?:noncomputable\s+)?(?:theorem|lemma|def)\s+" + re.escape(name) + r"\b", t)
    if not m:
        return None
    rest = t[m.start():]
    offset = m.end() - m.start()
    nb = re.search(r"(?m)^(?:theorem|lemma|def|structure|abbrev|inductive|class|end|namespace)\b",
                   rest[offset:])
    body = rest[offset: offset + (nb.start() if nb else len(rest))]
    cited = {w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body)
             if w in name_index and w != name}
    return len(cited)


def main(argv):
    name_index = build_name_index()
    # Round 238. Resolve the hardcoded paths through the shared map, so a `git mv` no longer
    # reports MISSING. This table is the FOURTH path-keyed artifact found in the tree (after
    # PROOF-DEBT, the proof-strength baseline and the underscore baseline) -- all with the same
    # defect and all fixed the same way: map at lookup time, never edit the table for a move.
    expectations = {name: (PATH_MAP.get(rel, rel), want)
                    for name, (rel, want) in _RAW_EXPECTED.items()}
    self_test = "--self-test" in argv
    if self_test:
        # plant a wrong expectation: claim `ladder_forward` cites 3
        expectations["ladder_forward"] = ("Lift/EndToEnd.lean", 3)

    problems = 0
    print("chain dependency check: %d theorems\n" % len(expectations))
    print("%-32s %-8s %-8s %s" % ("theorem", "expected", "actual", "verdict"))
    for name, (rel, want) in expectations.items():
        got = count_citations(name, rel, name_index)
        if got is None:
            print("%-32s %-8s %-8s %s" % (name, want, "?", "MISSING"))
            problems += 1
            continue
        ok = (got == want)
        print("%-32s %-8d %-8d %s" % (name, want, got, "ok" if ok else "DRIFT"))
        if not ok:
            problems += 1

    print("\n" + "=" * 62)
    if self_test:
        # Round 238. This used to `return 1` on SUCCESS -- i.e. a working self-test looked like a
        # failing check, and a broken one looked like a pass. Nothing invoked it, which is why the
        # inversion survived; but `check_selftest_coverage.py` counts a `--self-test` by PRESENCE, so
        # "the gate can demonstrate its own red" was being claimed on the strength of a string.
        if problems > 0:
            print("SELF-TEST PASS: a wrong expectation is reported")
            return 0
        print("SELF-TEST FAIL: a wrong expectation was NOT reported")
        return 1
    print("CHAIN DEPS: %s" % ("consistent with the recorded structure"
                              if problems == 0 else "%d drift(s)" % problems))
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
