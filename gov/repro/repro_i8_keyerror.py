import io, sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

# Minimal reproduction of the mapping gap in gate.py:622-626.
mapping = {"I1": "AXIOM", "I2": "SORRY", "I3": "DUP", "I4": "LAYER",
           "I5": "E2E", "I6": "HOLE", "I7": "ARTIFACT"}
for inv in ["I1", "I2", "I3", "I4", "I5", "I6", "I7", "I8"]:
    try:
        print(inv, "->", mapping[inv])
    except KeyError as e:
        print(inv, "-> KeyError", e, "  <-- gate would crash instead of reporting COMMENT(9)")
