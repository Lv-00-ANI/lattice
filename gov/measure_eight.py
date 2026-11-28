# -*- coding: utf-8 -*-
"""One-shot re-measurement of the eight quantities the documents quote, from the tree as it stands.

Nothing here reads a recorded number; every value is computed now.
"""
import io
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
GOV = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.dirname(GOV)
sys.path.insert(0, GOV)
sys.path.insert(0, os.path.join(GOV, "tools"))

import audit_counts as A          # noqa: E402
import chain_connectors as C      # noqa: E402
import check_criterion_size as K  # noqa: E402
import gen_objective_map as G     # noqa: E402
import verify_all as V            # noqa: E402
from check_objective_coverage import CLAUSES  # noqa: E402

LAT = os.path.join(ZERO, "Lattice")

files = 0
lines = 0
for root, dirs, fs in os.walk(LAT):
    dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
    for f in fs:
        if f.endswith(".lean"):
            files += 1
            lines += io.open(os.path.join(root, f), "rb").read().count(b"\n")

crit, _ = K.count_conjuncts(io.open(os.path.join(LAT, "Plugins.lean"), encoding="utf-8").read())

print("1  modules (kernel)          : %d" % A.module_total())
print("2  theorems / declarations   : %d / %d" % (A.total_theorems(), A.total_declarations()))
print("3  .lean files / lines       : %d / %d" % (files, lines))
print("4  checks                    : %d = %d gating + %d reporters"
      % (len(V.CHECKS), len([1 for l, _ in V.CHECKS if l not in V.REPORT_ONLY]), len(V.REPORT_ONLY)))
print("5  reactivity probes         : %d" % len(V.SLOW_ONLY))
print("6  seams / connectors / budget: %d / %d / %d"
      % (len(G.END_OF_CHAIN), len(C.TERMINAL_CONNECTORS), C.UNREGISTERED_BUDGET))
print("7  clauses / carriers        : %d / %d" % (len(CLAUSES), sum(len(v) for v in CLAUSES.values())))
print("8  ProofComplete items       : %s" % crit)