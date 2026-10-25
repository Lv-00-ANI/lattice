"""Verify the audit's central claim: which registered checks can never fail?

A check that always exits 0 is not a gate. The legacy project spent B1-B480 learning
this ("an always-red gate gets ignored"); the mirror failure -- an always-green one --
is worse, because it produces a PASS that means nothing.
"""
import io, os, re, sys
import os as _os
# Resolve paths relative to this file so the script runs on any machine:
#   gov/repro/<script>.py  ->  repo root is three levels up.
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_REPO = _os.path.abspath(_os.path.join(_HERE, "..", ".."))
_AGENT_TMP = _os.path.abspath(_os.path.join(_REPO, "..", "agent-tmp"))


sys.stdout.reconfigure(encoding="utf-8", errors="replace")
GOV = _os.path.join(_REPO, "gov")

src = io.open(os.path.join(GOV, "verify_all.py"), encoding="utf-8").read()
m = re.search(r"CHECKS = \[(.*?)\]", src, re.S)
entries = re.findall(r'\("([^"]+)",\s*"([^"]+)"\)', m.group(1))
print("registered checks:", len(entries))

constant_zero, real, unknown = [], [], []
for label, cmd in entries:
    script = cmd.split()[0]
    if not script.endswith(".py"):
        continue
    p = os.path.join(GOV, script)
    if not os.path.exists(p):
        unknown.append((label, script, "missing"))
        continue
    t = io.open(p, encoding="utf-8", errors="replace").read()
    mm = re.search(r"(?s)def main\([^)]*\).*?return\s+([^\n#]+)", t)
    if not mm:
        # generators without main() are allowed to be non-gating
        unknown.append((label, script, "no main()"))
        continue
    ret = mm.group(1).strip()
    if re.fullmatch(r"0", ret):
        constant_zero.append((label, script))
    else:
        real.append((label, script, ret[:60]))

print("\n=== ALWAYS EXIT 0 (cannot fail) : %d ===" % len(constant_zero))
for label, script in constant_zero:
    print("  %-34s %s" % (label, script))

print("\n=== can fail : %d ===" % len(real))
for label, script, ret in real:
    print("  %-34s %-28s return %s" % (label, script, ret))

print("\n=== no main() / missing : %d ===" % len(unknown))
for label, script, why in unknown:
    print("  %-34s %-28s (%s)" % (label, script, why))
