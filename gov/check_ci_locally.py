"""gov/check_ci_locally.py -- run what CI would run, and audit what cannot be run.

Round 116 context
=================
The README says, correctly, that CI has never actually run. That sentence has lived in the docs for
many rounds and made 'all guards green' a local claim rather than a CI claim. This checker narrows
that gap honestly instead of closing it falsely:

  JOB 1  `invariants` needs no Lean toolchain, so it is RUN here, step for step, exactly as the
         workflow specifies. If job 1 would be red on a Linux runner, this checker is red here.

  JOB 2  `build-and-verify` needs a Linux Lean toolchain and network. It CANNOT be run on the
         author's machine, and claiming otherwise is precisely the failure mode the project keeps
         recording. What this checker does instead is audit the parts that are machine-checkable
         without executing: the workflow file's own portability and integrity (line endings, BOM,
         referenced paths, Windows-only constructs).

What this does NOT establish
============================
A green run here does NOT mean job 2 passes on GitHub. It means job 1 passes and job 2's text is
sound. The README's statement that CI has never run is still true and must stay.
"""
import io
import json
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
WF = os.path.join(ROOT, ".github", "workflows", "lattice.yml")


def job1_steps():
    """The three steps of the `invariants` job, run exactly as the workflow runs them."""
    results = []

    script = (
        "import json, sys\n"
        "m = json.load(open('lake-manifest.json'))\n"
        "pkgs = [p for p in m['packages'] if p['name'] == 'mathlib']\n"
        "if len(pkgs) != 1:\n"
        "    sys.exit('expected exactly one mathlib entry, found %d' % len(pkgs))\n"
        "p = pkgs[0]\n"
        "if p.get('type') != 'git':\n"
        "    sys.exit('mathlib must be a git requirement, got type=%r' % p.get('type'))\n"
        "rev = p.get('rev') or ''\n"
        "if len(rev) != 40:\n"
        "    sys.exit('mathlib rev is not a 40-char SHA: %r' % rev)\n"
    )
    r = subprocess.run([sys.executable, "-c", script], cwd=ROOT,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    results.append(("mathlib revision is recorded", r.returncode == 0))

    r = subprocess.run([sys.executable, "gate.py"], cwd=HERE,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    results.append(("gate (I1-I8)", r.returncode == 0))

    r = subprocess.run([sys.executable, "gate.py", "--selftest"], cwd=HERE,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    results.append(("gate selftest", r.returncode == 0))
    return results


def job2_audit(root=None, wf=None):
    """Static audit of the parts of job 2 that can be checked without a Linux Lean toolchain."""
    root = root or ROOT
    wf = wf or os.path.join(root, ".github", "workflows", "lattice.yml")
    results = []
    if not os.path.exists(wf):
        return [("workflow file exists", False)]

    raw = io.open(wf, "rb").read()
    results.append(("no CRLF line endings", b"\r" not in raw))
    results.append(("no UTF-8 BOM", not raw.startswith(b"\xef\xbb\xbf")))

    text = raw.decode("utf-8")
    code = "\n".join(ln for ln in text.split("\n") if not ln.lstrip().startswith("#"))

    refs = set()
    for m in re.finditer(r"(?:open|cat|test -d|git -C)\s*\(?[\"']([\w./-]+)[\"']", text):
        refs.add(m.group(1))
    for m in re.finditer(r"python\s+(?:gov/)?(\w+\.py)", code):
        refs.add(m.group(1))
    for m in re.finditer(r"working-directory:\s*(\S+)", text):
        refs.add(m.group(1))

    missing = []
    for ref in sorted(refs):
        if ref in ("cm-rev.txt", "build.log") or ref.startswith("$"):
            continue
        if not (os.path.exists(os.path.join(root, ref))
                or os.path.exists(os.path.join(root, "gov", ref))):
            missing.append(ref)
    results.append(("referenced paths exist", not missing))

    for pat in ("powershell", "pwsh", ".ps1", "Select-String", "Get-ChildItem"):
        results.append(("no Windows-ism %r" % pat, pat not in code))
    return results


def main(argv):
    ok = True

    print("JOB 1  `invariants` (no toolchain) -- RUN, not simulated")
    for name, passed in job1_steps():
        print("  %-40s %s" % (name, "PASS" if passed else "FAIL"))
        ok = ok and passed

    print()
    print("JOB 2  `build-and-verify` -- statically audited (cannot run without Linux + network)")
    for name, passed in job2_audit():
        print("  %-40s %s" % (name, "PASS" if passed else "FAIL"))
        ok = ok and passed

    print()
    if "--self-test" in argv:
        # plant a workflow that would fail every audit, assert the audit reports it
        import shutil
        planted = "run: powershell -c 'Select-String'\nworking-directory: nowhere\n"
        tmp_dir = os.path.join(ROOT, ".ci-selftest")
        tmp_wf = os.path.join(tmp_dir, "wf.yml")
        os.makedirs(tmp_dir, exist_ok=True)
        try:
            with io.open(tmp_wf, "w", encoding="utf-8", newline="\r\n") as f:
                f.write(planted)
            planted_results = job2_audit(root=tmp_dir, wf=tmp_wf)
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)
        if all(p for _, p in planted_results):
            print("SELF-TEST FAILED: a broken workflow was audited clean")
            return 2
        print("SELF-TEST: a broken workflow is caught")
        return 0

    print("CI LOCAL SIMULATION: %s" % ("ok" if ok else "PROBLEM"))
    print("This does NOT mean CI passes on GitHub: job 2 has never run on a real runner.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
