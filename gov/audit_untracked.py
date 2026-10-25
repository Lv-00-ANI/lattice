#!/usr/bin/env python3
"""Audit: is any work sitting outside version control?

## Why this exists

Twice in this session a file had to be recovered by reconstruction rather than from git, and both times the cause
was the same: the file was **new** and therefore untracked.

* Round 97 -- an edit script truncated `gov/audit_reach.py` to zero bytes. `git status` reported `??` and there was
  nothing to restore from.
* Round 119 -- an edit script truncated `Zero/Geo/PathContinuity.lean` to 129 lines. Untracked again, so it was
  rewritten from memory. `verify_all` had gone to four failures in the meantime.

Neither incident was caused by a bad edit alone; both were made unrecoverable by an untracked file. And an untracked
file is invisible: nothing else in the audit suite looks at git at all, so "a batch of new work is not yet
committed" was a state with no reporter.

## What this checks, and what it deliberately does not

The report separates two things that are easy to confuse:

* **untracked files** -- work that exists only in the working tree. `.lean` files are listed first because they carry
  the proofs; `.py` and `.md` follow. This is the state that made the two incidents unrecoverable.
* **modified but tracked files** -- ordinary development. Reported as a count only, because a working tree with
  uncommitted edits is normal, whereas a working tree with uncommitted *new* files is the risk.

## Why exit 0

A working tree with untracked files is the normal state while work is in progress; making it a hard failure would
turn every step red and teach the reader to ignore this check. What is useful is not a verdict but a visible count,
placed next to the other audits so that "there is a batch not yet committed" stops being invisible. The gate still
exists for correctness (`gate.py`); this is inventory.

If git is unavailable -- not on `PATH`, or `zero/` is not inside a repository -- the script says so and exits 0. That
is not a pass; it is an explicit "cannot tell", which is the honest answer when the tool is missing.
"""
import io
import os
import subprocess
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))

CODE_EXT = {".lean": 0, ".py": 1, ".md": 2}


def git_status():
    try:
        out = subprocess.run(
            ["git", "status", "--porcelain", "--", "."],
            cwd=ZERO, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=120)
    except FileNotFoundError:
        return None, "git is not on PATH"
    except subprocess.TimeoutExpired:
        return None, "git status timed out"
    if out.returncode != 0:
        return None, "git status failed (is zero/ inside a repository?)"
    return out.stdout.splitlines(), None


def main():
    lines, err = git_status()

    print("=" * 78)
    print("Version-control inventory for zero/")
    print("=" * 78)

    if err is not None:
        print("  cannot tell: %s" % err)
        print()
        print("  This is not a pass. Without git there is no way to know whether new work is")
        print("  backed up, and the two reconstruction incidents in this session both began with")
        print("  an untracked file.")
        return 0

    untracked = {"lean": [], "other": []}
    modified = 0
    for line in lines:
        if len(line) < 4:
            continue
        code, path = line[:2], line[3:].strip()
        if code == "??":
            ext = os.path.splitext(path)[1].lower()
            if ext in CODE_EXT:
                untracked["lean" if ext == ".lean" else "other"].append(path)
            elif path.endswith("/"):
                # an untracked directory: list the files inside it
                full = os.path.join(ZERO, path)
                for root, dirs, fs in os.walk(full):
                    dirs[:] = [d for d in dirs if d not in (".lake", "__pycache__")]
                    for f in fs:
                        rel = os.path.join(root, f)
                        e = os.path.splitext(f)[1].lower()
                        if e in CODE_EXT:
                            bucket = "lean" if e == ".lean" else "other"
                            untracked[bucket].append(os.path.relpath(rel, ZERO).replace("\\", "/"))
        elif code.strip():
            modified += 1

    total = len(untracked["lean"]) + len(untracked["other"])

    print("  untracked .lean files : %d" % len(untracked["lean"]))
    for p in sorted(untracked["lean"]):
        print("      %s" % p)
    print("  untracked .py/.md      : %d" % len(untracked["other"]))
    for p in sorted(untracked["other"]):
        print("      %s" % p)
    print("  tracked but modified   : %d  (normal while working; not a warning)" % modified)
    print()

    if total == 0:
        print("  every source file in zero/ is committed.")
    else:
        print("  %d source file(s) exist only in the working tree. Two reconstruction incidents in" % total)
        print("  this session began exactly here: a script damaged a file, `git status` showed `??`,")
        print("  and there was nothing to restore from. Commit before the next edit.")

    print()
    print("=" * 78)
    print("Reading this report")
    print("=" * 78)
    print("  `audit_counts.py` checks numbers stated in the README; this checks whether the work")
    print("  exists anywhere other than this machine's working tree. They answer different questions")
    print("  and neither subsumes the other.")
    print()
    print("  Exit 0 is deliberate: uncommitted work is the normal state during a task, and a gate")
    print("  that is red every step teaches the reader to ignore it. The value here is visibility.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
