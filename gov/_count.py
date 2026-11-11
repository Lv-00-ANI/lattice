# -*- coding: utf-8 -*-
"""Count the registered checks in verify_all.py by kind, for the doc-consistency numbers."""
import io
import os
import re

GOV = os.path.dirname(os.path.abspath(__file__))
src = io.open(os.path.join(GOV, "verify_all.py"), encoding="utf-8").read()

rows = re.findall(r'^\s{4}\("([^"]+)",\s*"([^"]+)"(,\s*True)?\)', src, re.M)
total = len(rows)
gating = sum(1 for r in rows if r[2])
print("  total=%d gating=%d reporter=%d" % (total, gating, total - gating))
