"""Pre-commit gate installer -- and an honest statement of why it is NOT installed.

## The finding

Both shims fail on this machine, and the failure is worse than "the hook does not run":

    sh.exe: *** fatal error - couldn't create signal pipe, Win32 error 5

Measured twice:
  * running `gov/pre-commit` by hand  -> same fatal error;
  * `git commit` with that hook in `.git/hooks/pre-commit` -> same fatal error, and
    **the commit is refused** (exit 1).

So a `/bin/sh` hook here does not "silently not run" -- it blocks every commit. That is
worse than having no hook: it makes the repository unusable, and the first person to hit
it will delete the hook and move on.

## What this installer does instead

It deliberately installs NOTHING by default, and prints the measurement. Leaving a hook
out is the honest state: the gate is not enforced on the commit path, and the README says
so. Installing a broken one would create the exact defect the legacy tree recorded
("installed" mistaken for "effective"), except louder.

## If you still want commit-time enforcement

Run the gate yourself, or wire it through an editor/task runner:

    python gov/gate.py

`--force` installs a Python-based hook anyway (git also honours a hook whose interpreter
line points at a real executable). Verify it by making a throwaway commit; if `git
commit` fails with the signal-pipe error, remove `.git/hooks/pre-commit` again.
"""
import os
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GATE = os.path.join(REPO, "gov", "gate.py")

SHIM = """#!/bin/sh
exec python "$(git rev-parse --show-toplevel)/gov/gate.py"
"""


def gate_runs():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=REPO,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    return r.returncode


def main():
    force = "--force" in sys.argv
    if not os.path.isdir(os.path.join(REPO, ".git")):
        print("no .git at", REPO)
        return 1

    print("gate exit (run directly):", gate_runs())

    if not force:
        print()
        print("NOT installing a commit hook. Measured reason:")
        print("  an sh hook fails here with 'couldn't create signal pipe, Win32 error 5',")
        print("  and git then REFUSES the commit. No hook is safer than a blocking one.")
        print("  Run `python gov/gate.py` yourself, or pass --force to install anyway.")
        return 0

    hooks = os.path.join(REPO, ".git", "hooks")
    os.makedirs(hooks, exist_ok=True)
    dst = os.path.join(hooks, "pre-commit")
    if os.path.exists(dst):
        shutil.copy2(dst, dst + ".bak")
        print("backed up existing hook")
    with open(dst, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(SHIM)
    os.chmod(dst, 0o755)
    print("installed (forced):", dst)
    print("VERIFY IT: run `git commit --allow-empty -m probe`; if it fails with the")
    print("signal-pipe error, delete .git/hooks/pre-commit again.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
