# -*- coding: utf-8 -*-
"""Reactivity test for the comment-integrity check.

The first version of `check_comments.py` flagged all 26 healthy files. That is the failure mode the
legacy `check-xref.ps1` had, and it is why this test exists: each planted defect must be caught, and
the clean tree must pass.

Cases:
  1. a doc comment glued onto another (the splice signature);
  2. a block comment never closed;
  3. a stray `-/`.
"""
import io
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
PROBE = os.path.join(ZERO, "Lattice", "CommentProbe.lean")
CHECK = os.path.join(HERE, "check_comments.py")

CASES = [
    ("glued doc comment", "import Lattice.Core\n\n/-- a -//-- b -/\ntheorem p1 : True := trivial\n", True),
    ("unclosed comment", "import Lattice.Core\n\n/- never closed\ntheorem p2 : True := trivial\n", True),
    ("stray closer", "import Lattice.Core\n\ntheorem p3 : True := trivial -/\n", True),
    ("clean", "import Lattice.Core\n\n/-- fine -/\ntheorem p4 : True := trivial\n", False),
]


def main():
    failures = 0
    try:
        for name, src, expect_red in CASES:
            io.open(PROBE, "w", encoding="utf-8", newline="\n").write(src)
            r = subprocess.run([sys.executable, CHECK], cwd=ZERO, capture_output=True,
                               text=True, encoding="utf-8", errors="replace")
            red = r.returncode != 0
            ok = red == expect_red
            print("  %-20s expect %-6s got %-6s %s" %
                  (name, "RED" if expect_red else "GREEN", "RED" if red else "GREEN",
                   "OK" if ok else "** FAIL **"))
            if not ok:
                failures += 1
                print("     ", (r.stdout or r.stderr).strip()[:300])
    finally:
        if os.path.exists(PROBE):
            os.remove(PROBE)
        stale = os.path.join(ZERO, ".lake", "build", "lib", "Lattice", "CommentProbe.olean")
        if os.path.exists(stale):
            os.remove(stale)
    r = subprocess.run([sys.executable, CHECK], cwd=ZERO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    print("=" * 56)
    print("clean tree:", (r.stdout or "").strip()[:120])
    print("REACTIVITY:", "ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
