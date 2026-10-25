"""Verify the audit's most serious mathematical claim: that the G1 chain is vacuous.

`Geo/Pipeline.token_to_weight` takes `_hdec : decodePayload n rs = some c` and its
conclusion never mentions `rs` or the decode. If so, the hypothesis is not load-bearing:
the theorem holds with any `rs`, and the "four rungs" reduce to restating two facts about
one linear form.

Test: build two variants of the statement -- one that drops the hypothesis entirely, and
one that drops the `rs` argument -- and see whether Lean accepts them with the same proof.
If it does, the hypothesis is dead, and any claim that this theorem connects L0/L1 to L3
is false.
"""
import io, os, subprocess, sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = _REPO
PROBE = os.path.join(NEW, "Lattice", "Geo", "GapProbe.lean")

SRC = """import Lattice.Geo.Pipeline

namespace Lattice.Geo

-- (1) The published statement.
example (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) (rs : List ℝ)
    (h : Lattice.Lift.decodePayload n rs = some c) :
    (GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0) :=
  holds_ofLinearForm_iff c pts

-- (2) DROP the decode hypothesis entirely.
example (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    (GeoConstraint.Holds (.eqZero (ofLinearForm c)) pts ↔ (ofLinearForm c).evalPts pts = 0) :=
  holds_ofLinearForm_iff c pts

-- (3) DROP the token/material list too.
example (c : Lattice.Core.LinearForm ℝ n) (pts : ℕ → Pt n) :
    (ofLinearForm c).evalPts pts = c.b + ∑ i : Fin n, c.a i * pts 0 i :=
  ofLinearForm_evalPts c pts

end Lattice.Geo
"""

io.open(PROBE, "w", encoding="utf-8", newline="\n").write(SRC)
try:
    r = subprocess.run(["lake", "env", "lean", PROBE], cwd=NEW, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    print("exit:", r.returncode)
    out = (r.stdout or "") + (r.stderr or "")
    print(out.strip()[:1500] or "(no output = all three variants typecheck)")
finally:
    if os.path.exists(PROBE):
        os.remove(PROBE)
