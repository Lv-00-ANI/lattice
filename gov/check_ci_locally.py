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

    # Round 176, P2-10. THE MOST IMPORTANT LINE IN THIS FILE.
    #
    # `on.push.branches` listed only `main`, while this repository's default branch is `master` --
    # so **every push triggered nothing**. That is the concrete mechanism behind "CI has never run on
    # a real runner", and it is invisible from the outside: a workflow that matches no branch and a
    # workflow that passes both show a green (or absent) check.
    #
    # So the trigger list is now checked. Round 228 corrected HOW: not against "the branch that
    # actually exists" (that is the checked-out branch, which on a feature branch is not the default)
    # but against every plausible default name. If the default is renamed to a name outside that set,
    # this check goes red instead of quiet.
    branches = []
    m = re.search(r"(?ms)^on:.*?^\s+push:.*?^\s+branches:\s*\[([^\]]*)\]", text)
    if m:
        branches = [b.strip().strip("\"'") for b in m.group(1).split(",") if b.strip()]
    # Round 228. The claim is "a push to the DEFAULT branch triggers CI". The checked-out branch is
    # NOT the default when you are on a feature branch -- comparing against it made this check red on
    # EVERY branch, which does not fix anything and would force people to abandon the branch workflow.
    # (It is how this was found: the restructure is being done on `restructure-p0`, and the whole suite
    # went red for a reason that had nothing to do with the tree.)
    #
    # The check is now branch-INDEPENDENT: every plausible default name must be listed. That is what
    # the workflow's own comment claims ("Both names are listed so a future rename cannot silently...").
    plausible = {"main", "master"}
    missing = sorted(plausible - set(branches))
    results.append(("push trigger covers every plausible default branch %s" % sorted(plausible),
                    not missing))
    if missing:
        print("    the trigger omits %s -- a push to that branch would start nothing"
              % ", ".join(missing))
    # a workflow that cannot be triggered by hand cannot be checked by hand either
    results.append(("workflow_dispatch present", "workflow_dispatch" in code))
    # a `|| echo` around the cache fetch hides an outage behind a from-source build that will time out
    results.append(("mathlib cache failure is not silently swallowed",
                    "lake exe cache get ||" not in code))
    return results


def current_branch(root=None):
    """The repository's default branch, read from git; `None` if it cannot be determined.

    Using `git symbolic-ref refs/remotes/origin/HEAD` first would need a remote; this tree has none,
    so the checked-out branch is the honest answer on a developer machine. In CI the runner checks out
    a detached HEAD, where this returns `None` and the trigger check reports "not readable" rather
    than a false pass.
    """
    root = root or ROOT
    try:
        r = subprocess.run(["git", "-C", root, "branch", "--show-current"],
                           capture_output=True, text=True, encoding="utf-8", errors="replace")
    except (OSError, ValueError):
        return None
    if r.returncode != 0:
        return None
    name = (r.stdout or "").strip()
    return name or None


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
        # Round 176: this used to plant one broken workflow and assert only that SOMETHING failed,
        # which cannot show that any particular check works. Each rule is now planted on its own and
        # must be the one that fires.
        import shutil
        tmp_dir = os.path.join(ROOT, ".ci-selftest")
        os.makedirs(tmp_dir, exist_ok=True)

        def audit_text(t):
            p = os.path.join(tmp_dir, "wf.yml")
            io.open(p, "w", encoding="utf-8", newline="\n").write(t)
            return {name: ok for name, ok in job2_audit(root=ROOT, wf=p)}

        try:
            good = io.open(os.path.join(ROOT, ".github", "workflows", "lattice.yml"),
                           encoding="utf-8").read()
            base = audit_text(good)
            failures = []
            if not all(base.values()):
                failures.append("the real workflow is reported broken: %s"
                                % [n for n, ok in base.items() if not ok])

            # (a) the original defect: the push trigger names a branch that does not exist
            planted = good.replace("branches: [main, master]", "branches: [main]")
            if planted == good:
                failures.append("could not plant the branch defect (text changed?)")
            else:
                r = audit_text(planted)
                hit = [n for n, ok in r.items() if not ok and "push trigger" in n]
                if not hit:
                    failures.append("a push trigger naming no real branch was NOT caught")

            # (b) a silently swallowed cache failure. Appending the pattern is enough: the rule is
            # "this string must not appear", so a planted line is the most direct test of it and does
            # not depend on the exact wording of the real step.
            planted = good + "\n      - name: planted\n        run: lake exe cache get || echo swallowed\n"
            r = audit_text(planted)
            if not [n for n, ok in r.items() if not ok and "swallow" in n]:
                failures.append("a swallowed cache failure was NOT caught")

            # (c) no manual trigger
            planted = good.replace("  workflow_dispatch:\n", "")
            r = audit_text(planted)
            if not [n for n, ok in r.items() if not ok and "workflow_dispatch" in n]:
                failures.append("a workflow with no workflow_dispatch was NOT caught")
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

        if failures:
            for f in failures:
                print("SELF-TEST FAILED: %s" % f)
            return 2
        print("SELF-TEST: real workflow clean; branch trigger, swallowed cache and missing"
              " workflow_dispatch each caught on their own")
        return 0

    print("CI LOCAL SIMULATION: %s" % ("ok" if ok else "PROBLEM"))
    print("This does NOT mean CI passes on GitHub: job 2 has never run on a real runner.")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
