"""Which script guarantees which number? Derive it from the checkers themselves.

Round 38 established that drift happens where nothing measures. So the registry of "who
guarantees this number" must be derived from the checkers, not remembered.

Scan gov/*.py for EXPECTED-like constants and the doc they refer to, and scan the docs for
numbers, then pair them up where possible. Report what is GUARDED and what is NOT.
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
LAKE = _REPO
GOV = os.path.join(LAKE, "gov")

# 1. what each checker declares as its expectations
print("=== checkers and what they assert ===\n")
for f in sorted(os.listdir(GOV)):
    if not f.endswith(".py") or f.startswith("_"):
        continue
    p = os.path.join(GOV, f)
    t = io.open(p, "rb").read().decode("utf-8", errors="replace")
    # find EXPECTED/expect dicts or doc references
    exp = re.findall(r"EXPECTED\s*=\s*\{(.*?)\}", t, re.S)
    doc_refs = re.findall(r'([A-Z][A-Z0-9-]*\.md)', t)
    docs = sorted(set(doc_refs))
    # is it a gate (returns nonzero) or a reporter?
    fails = ("return 1" in t) or ("sys.exit(1" in t) or ("rep.add" in t)
    if exp or docs:
        print("%-30s asserts=%-4s docs=%s" % (f, "yes" if exp else "no",
                                              docs if docs else "-"))
        for e in exp:
            keys = re.findall(r'"([^"]+)"\s*:', e)
            if keys:
                print("      keys: %s" % keys[:8])

# 2. which docs contain numbers at all
print("\n=== docs containing explicit counts ===")
for f in sorted(os.listdir(LAKE)):
    if not f.endswith(".md"):
        continue
    t = io.open(os.path.join(LAKE, f), encoding="utf-8").read()
    n = len(re.findall(r"\b\d{2,}\b", t))
    print("  %-26s %3d multi-digit numbers" % (f, n))
