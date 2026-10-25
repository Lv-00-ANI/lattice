import io, os, re, sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

NEW = _REPO
names = [
    "sound_not_exact", "constEmbedding", "const_not_levelB",
    "sq_penalty_exact", "sq_penalty_exact_finN", "sq_penalty_exact_matrix",
    "perpResid_localMin_of_nondegenerate",
    "verifier_reliable_clean", "verifier_error_vanishes",
    "quantized_chain_error_lipschitz", "accumulation_error_bound",
    "ce_compile_error_bound", "PenaltyExact", "PenaltySound",
    "markov_bound",
]
hits = {n: [] for n in names}
for root, _, files in os.walk(os.path.join(NEW, "Lattice")):
    if "Reference" in root:
        continue
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        t = io.open(p, "rb").read().decode("utf-8", errors="replace")
        for n in names:
            if re.search(r"(?m)^\s*(?:@\[[^\]]*\][ \t]*)*(?:theorem|lemma|def)\s+" + re.escape(n) + r"\b", t):
                hits[n].append(os.path.relpath(p, NEW))
for n in names:
    print("%-40s %s" % (n, ("OK  " + hits[n][0]) if hits[n] else "*** MISSING ***"))
