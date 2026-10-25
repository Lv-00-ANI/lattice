"""Reactivity test that perturbs the EXACT cell the checker reads.

The previous attempt used `text.replace("52", "53", 1)`, which replaces the FIRST "52" in
the README -- possibly inside an unrelated sentence (e.g. a version, a percentage). The
checker then correctly saw no change in the Geo count and did not fire.

Fix: mutate the specific pattern the checker matches, so a MISSED result would be a real
defect in the gate rather than a bad test.
"""
import hashlib
import io
import os
import re
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
    r = subprocess.run([sys.executable, "audit_counts.py"], cwd=GOV, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


base, _ = run()
print("baseline exit:", base, "(expect 0)")

# the exact substrings the checker matches, with the number incremented
CASES = [
    ("Geo count",     r"(Geo/\s+)(\d+)",       lambda m: m.group(1) + str(int(m.group(2)) + 1)),
    ("Lib count",     r"(Lib/\s+)(\d+)",       lambda m: m.group(1) + str(int(m.group(2)) + 1)),
    ("LvFormal count", r"(LvFormal/\s+)(\d+)", lambda m: m.group(1) + str(int(m.group(2)) + 1)),
    ("escape count",  r"(\*\*)(\d+)(\*\* 处历史逃逸)",
     lambda m: m.group(1) + str(int(m.group(2)) + 1) + m.group(3)),
    ("registration",  r"(注册了 \*\*)(\d+)( 项\*\*)",
     lambda m: m.group(1) + str(int(m.group(2)) + 1) + m.group(3)),
]

failures = 0
if base != 0:
    print("baseline is red; cannot test")
    sys.exit(1)

for name, pat, repl in CASES:
    mutated, n = re.subn(pat, repl, text, count=1)
    if n == 0:
        print("  %-16s SKIPPED (pattern absent from README)" % name)
        failures += 1
        continue
    try:
        io.open(README, "wb").write(mutated.encode("utf-8"))
        code, out = run()
        ok = code != 0
        print("  %-16s exit=%-2d %s" % (name, code, "OK (caught)" if ok else "** MISSED **"))
        if not ok:
            failures += 1
    finally:
        io.open(README, "wb").write(orig)

assert hashlib.sha256(io.open(README, "rb").read()).hexdigest() == digest, "restore failed"
code, _ = run()
print("\nrestored -> exit %d (expect 0)" % code)
if code != 0:
    failures += 1

print("=" * 60)
print("REACTIVITY (audit_counts): %s" % ("ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures))
sys.exit(0 if failures == 0 else 1)
