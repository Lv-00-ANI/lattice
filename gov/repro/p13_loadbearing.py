"""P13 load-bearing experiments.

For each rung, restate the carrier theorem with its hypotheses REMOVED and see whether the
weaker statement still typechecks. If it does, the hypothesis is decoration: the theorem
would be true regardless, and any prose claiming it is what makes the rung work is wrong.

This is the test the roadmap promises (`PROOF-CHAIN-RUNG.md` §4): evidence, not a claim.

Each case writes a probe file into the repo (so imports resolve), compiles it, deletes it,
and prints the result. A CLEAN exit means the hypothesis is NOT load-bearing.
"""
import io
import os
import subprocess
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _REPO
PROBE = os.path.join(NEW, "Lattice", "Lift", "GapProbeChain.lean")

CASES = []

# --- Rung L2->L3: Pipeline.token_to_weight, hypothesis `_hdec` ---
CASES.append((
    "L2->L3  token_to_weight  WITHOUT the decode hypothesis",
    """import Lattice.Geo.Pipeline

open Lattice.Geo
open scoped ContinuousLinearMap

example (n : ℕ) (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    (GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0) :=
  holds_ofLinearForm_iff c pts
""",
    "If this compiles, `_hdec` is decorative: the theorem says nothing about the token list.",
))

# --- Ladder T1: compileProgram_sound without the per-item `sound` field ---
CASES.append((
    "T1     compileProgram_sound  WITHOUT the `sound` obligation",
    """import Lattice.Lift.SymbolToWeight

example (P W : Type) (C : Lattice.Lift.Compiler P W) (p : P) (x : C.inputP) :
    C.satW (C.compile p) (C.encode x) → C.satW (C.compile p) (C.encode x) :=
  fun h => h
""",
    "Replacing the obligation by a tautology shows what the field contributes: it IS the content.",
))

# --- Ladder T3: extract_compile depends on Representation.roundtrip ---
CASES.append((
    "T3     extract_compile  WITHOUT `roundtrip`",
    """import Lattice.Lift.Extraction

example (P W : Type) (R : Lattice.Lift.Representation P W) (p : P) :
    R.extract (R.compile p) = p :=
  R.roundtrip p
""",
    "This uses the field, so it is the field's content restated. Whether an INSTANCE exists is the question.",
))

# --- EndToEnd: ladder_forward depends on l1l2's satSym -> satTok ---
CASES.append((
    "E2E    ladder_forward  WITHOUT `l1l2` field",
    """import Lattice.Lift.EndToEnd

example (Data Tok Sym W : Type) (L : Lattice.Lift.Ladder Data Tok Sym W)
    (s : Sym) :
    L.satW (L.l2l3 s) → L.satW (L.l2l3 s) :=
  fun h => h
""",
    "Tautology: shows the ladder theorem's content lives entirely in its fields.",
))


def run(name, src, note):
    io.open(PROBE, "w", encoding="utf-8", newline="\n").write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", PROBE], cwd=NEW, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        out = ((r.stdout or "") + (r.stderr or "")).strip()
        ok = r.returncode == 0
        print("\n--- %s" % name)
        print("    exit=%d  -> %s" % (r.returncode,
              "HYPOTHESIS NOT LOAD-BEARING (weaker statement still typechecks)" if ok
              else "does not typecheck without it"))
        print("    %s" % note)
        if not ok:
            for ln in out.split("\n")[:3]:
                print("      " + ln[:140])
    finally:
        if os.path.exists(PROBE):
            os.remove(PROBE)


for name, src, note in CASES:
    run(name, src, note)
print("\nprobe file removed:", not os.path.exists(PROBE))
