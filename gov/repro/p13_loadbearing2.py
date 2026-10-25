"""P13 load-bearing experiments, corrected.

The first attempt was invalid for three of four cases: it replaced the theorem by a
tautology (`fun h => h`), which proves nothing about the original. The valid form of the
test keeps the CONCLUSION identical and only removes a hypothesis. If it still typechecks,
the hypothesis was decoration.

For structural fields (`Compiler.sound`, `Representation.roundtrip`) the honest question is
different: does an INSTANCE exist? A field's content is real, but if no inhabitant is ever
constructed, the theorems about it say nothing about any compiler.
"""
import io
import os
import re
import subprocess
import sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _os.path.join(_REPO, "Lattice")
PROBE = os.path.join(NEW, "Lift", "GapProbeChain.lean")

# ---------------------------------------------------------------- part 1: instances
print("=" * 78)
print("PART 1 -- do instances of the ladder structures exist?")
print("=" * 78)

STRUCTS = ["Compiler", "Representation", "Tokenizer", "Ladder"]
for s in STRUCTS:
    found = []
    for root, _, fs in os.walk(NEW):
        if "Reference" in root:
            continue
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            t = io.open(p, "rb").read().decode("utf-8", errors="replace")
            # `def foo : Struct ... where`  or  `instance : Struct ... where`
            for m in re.finditer(r"(?m)^\s*(?:noncomputable\s+)?(?:def|instance|abbrev)\s+([A-Za-z0-9_.']+)"
                                 r"[^\n]*?:\s*(?:Lattice\.Lift\.)?" + s + r"\b[^\n]*\bwhere\b", t):
                found.append((os.path.relpath(p, NEW), m.group(1)))
    print("\n  %-16s instances: %d" % (s, len(found)))
    for rel, name in found:
        print("      %-44s %s" % (rel, name))

# ---------------------------------------------------------------- part 2: real removals
CASES = [
    (
        "L2->L3  token_to_weight: drop `_hdec` AND the `rs` argument",
        """import Lattice.Geo.Pipeline
open Lattice.Geo
example (n : ℕ) (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    (GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0) ∧
      ((ofLinearForm c).evalPts pts = c.b + ∑ i : Fin n, c.a i * pts 0 i) :=
  ⟨holds_ofLinearForm_iff c pts, ofLinearForm_evalPts c pts⟩
""",
    ),
    (
        "E2E     ladder_compose_soundness: drop the `satTok` half",
        """import Lattice.Lift.EndToEnd
example (Data Tok Sym W : Type) (L : Lattice.Lift.Ladder Data Tok Sym W)
    (s : Sym) (hsat : L.satSym s) :
    L.satW (L.l2l3 s) :=
  L.l2l3_sound s hsat
""",
    ),
]


def run(name, src):
    io.open(PROBE, "w", encoding="utf-8", newline="\n").write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", PROBE], cwd=os.path.dirname(NEW), capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
        out = ((r.stdout or "") + (r.stderr or "")).strip()
        print("\n  %s" % name)
        print("    exit=%d -> %s" % (r.returncode,
              "weaker statement accepted => hypothesis not load-bearing"
              if r.returncode == 0 else "weaker statement REFUSED => hypothesis is load-bearing"))
        if r.returncode != 0:
            for ln in out.split("\n")[:2]:
                print("      " + ln[:150])
    finally:
        if os.path.exists(PROBE):
            os.remove(PROBE)


print("\n" + "=" * 78)
print("PART 2 -- conclusions preserved, hypotheses removed")
print("=" * 78)
for name, src in CASES:
    run(name, src)
print("\nprobe removed:", not os.path.exists(PROBE))
