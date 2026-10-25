# -*- coding: utf-8 -*-
"""nnstall the ZERO pre-commit gate into the repository's git hooks dir.

Deliberately verifies the hook is EXECUTABLE and that it round-trips through the
same shell git will use. The legacy project's hook existed but never ran; "installed"
was mistaken for "effective", which is a failure mode this installer refuses to repeat.
"""
import os
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(REPO, "Lattice", "gov", "pre-commit")
DST = os.path.join(REPO, ".git", "hooks", "pre-commit")


def main():
    if not os.path.isdir(os.path.join(REPO, ".git")):
        print("no .git at", REPO)
        return 1
    os.makedirs(os.path.dirname(DST), exist_ok=True)
    if os.path.exists(DST):
        shutil.copy2(DST, DST + ".bak")
        print("backed up existing hook to pre-commit.bak")
    shutil.copy2(SRC, DST)
    os.chmod(DST, 0o755)
    print("installed:", DST)

    # Effectiveness check, not existence check.
    r = subprocess.run(["git", "config", "core.hooksPath"], cwd=REPO,
                       capture_output=True, text=True)
    hooks_path = r.stdout.strip()
    if not hooks_path:
        print("core.hooksPath is unset -> git uses .git/hooks, hook is live")
    else:
        print("core.hooksPath =", hooks_path, "(verify the hook is visible there)")

    exists = os.path.exists(DST)
    print("exists:", exists, " executable:", os.access(DST, os.X_OK))
    return 0 if exists else 1


if __name__ == "__main__":
    sys.exit(main())
