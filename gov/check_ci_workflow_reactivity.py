"""Reactivity test for check_ci_workflow.py: prove the checker can FAIL.

A checker that has never been observed to fail is not evidence. This plants each defect the
previous workflow actually had, asserts the checker reports it, and restores the file.
"""
import hashlib
import io
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
NEW = r"C:\Users\xingg\Desktop\agent\lattice-new"
GOV = os.path.join(NEW, "gov")
WF = os.path.join(NEW, ".github", "workflows", "lattice.yml")
CHECK = os.path.join(GOV, "check_ci_workflow.py")

orig = io.open(WF, "rb").read()
digest = hashlib.sha256(orig).hexdigest()
text = orig.decode("utf-8")

CASES = [
    ("legacy manifest path", "lattice/lean/lake-manifest.json",
     text.replace('json.load(open("lake-manifest.json"))',
                  'json.load(open("lattice/lean/lake-manifest.json"))', 1)),
    ("no rev assertion", None, text.replace("len(rev) != 40", "len(rev) != 41", 1)),
    ("no HEAD verification", None, text.replace('test "$(git -C "$DEST" rev-parse HEAD)" = "$REV"',
                                                'true', 1)),
    ("no error gate", None, text.replace('if grep -qE \'^error\' build.log; then',
                                         'if false; then', 1)),
]


def run_check():
    r = subprocess.run([sys.executable, CHECK], cwd=GOV, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "")


failures = 0
for name, _unused, mutated in CASES:
    if mutated == text:
        print("  %-26s SKIPPED (mutation did not apply)" % name)
        failures += 1
        continue
    try:
        io.open(WF, "wb").write(mutated.encode("utf-8"))
        code, out = run_check()
        ok = code != 0
        print("  %-26s exit=%-2d %s" % (name, code, "OK (caught)" if ok else "** MISSED **"))
        if not ok:
            failures += 1
    finally:
        io.open(WF, "wb").write(orig)

assert hashlib.sha256(io.open(WF, "rb").read()).hexdigest() == digest, "restore failed"
code, _ = run_check()
print("\nrestored -> exit %d (expect 0)" % code)
if code != 0:
    failures += 1

print("=" * 60)
print("REACTIVITY (CI workflow): %s" % ("ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures))
sys.exit(0 if failures == 0 else 1)
