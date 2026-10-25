"""Reactivity for audit_tables: a check-marked README row citing a non-existent name must
make it exit 1.

The script always exited 0 before this round, so nothing had ever proven its unresolved-name
logic could fire. Plant a row that cites a name no declaration matches.
"""
import hashlib
import io
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
import os as _os
NEW = _os.path.abspath(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), ".."))
GOV = os.path.join(NEW, "gov")
README = os.path.join(NEW, "README.md")

orig = io.open(README, "rb").read()
digest = hashlib.sha256(orig).hexdigest()
text = orig.decode("utf-8")


def run():
    r = subprocess.run([sys.executable, "audit_tables.py"], cwd=GOV, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


base, _ = run()
print("baseline exit:", base, "(expect 0)")

# a table row with a check mark citing a name that cannot exist
# The scanner only looks at rows containing the U+2705 check mark; a row without it
# is skipped entirely, which is what made the first version of this test report a
# false MISSED.
PLANT = "\n| 注入测试 | \u2705 | `thisNameDefinitelyDoesNotExist_xyz` |\n"
mutated = text + PLANT

failures = 0
if base != 0:
    print("baseline red; cannot test")
    sys.exit(1)
try:
    io.open(README, "wb").write(mutated.encode("utf-8"))
    code, out = run()
    ok = code != 0 and "thisNameDefinitelyDoesNotExist_xyz" in out
    print("  planted unresolved citation -> exit %d %s" % (code, "OK (caught)" if ok else "** MISSED **"))
    if not ok:
        failures += 1
        print("    output excerpt:")
        for ln in out.split("\n")[:6]:
            print("      " + ln.strip()[:100])
finally:
    io.open(README, "wb").write(orig)

assert hashlib.sha256(io.open(README, "rb").read()).hexdigest() == digest, "restore failed"
code, _ = run()
print("restored -> exit %d (expect 0)" % code)
if code != 0:
    failures += 1

print("=" * 60)
print("REACTIVITY (audit_tables): %s" % ("PASS" if failures == 0 else "%d FAILURE(S)" % failures))
sys.exit(0 if failures == 0 else 1)
