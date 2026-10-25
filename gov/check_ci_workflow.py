"""Check that the CI workflow only refers to things that exist in THIS repository.

The previous workflow failed on its first steps because it read
`lattice/lean/lake-manifest.json`, a path from the pre-migration layout. That defect
survived because nothing checked the workflow: YAML parsers accept any string, and the job
had never been run.

This check is cheap and deterministic: it looks at the EXECUTABLE text of the workflow (not
comments, which legitimately mention the old bug) and verifies that
  * no path under the legacy tree is referenced,
  * the mathlib revision is asserted to be a 40-char SHA,
  * the built log is checked for errors.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NEW = os.path.abspath(os.path.join(HERE, ".."))
WF = os.path.join(NEW, ".github", "workflows", "lattice.yml")


def executable_text(path):
    t = io.open(path, encoding="utf-8").read()
    blocks = re.findall(r"(?ms)^\s+run:\s*\|?\s*\n((?:\s{8,}.*\n)+)", t)
    blocks += re.findall(r"(?m)^\s+run:\s*(\S.*)$", t)
    return "\n".join(blocks)


def main():
    if not os.path.exists(WF):
        print("workflow missing:", WF)
        return 1
    ex = executable_text(WF)
    failures = []

    # 1. no reference to the legacy sibling tree
    for pat, desc in [
        (r"lattice/lean/", "path under the legacy lattice/ tree"),
        (r"lattice/zero/", "path under the legacy zero/ tree"),
        (r"verify\.ps1", "the legacy PowerShell entry point"),
    ]:
        if re.search(pat, ex):
            print("  FAIL: workflow references %s" % desc)
            failures.append(desc)

    # 2. the revision must be a pinned SHA, not a branch name
    if "len(rev) != 40" not in ex:
        print("  FAIL: workflow does not assert that the mathlib rev is a 40-char SHA")
        failures.append("rev assertion")

    # 3. the checkout must be verified against the rev
    if "rev-parse HEAD" not in ex:
        print("  FAIL: workflow does not verify the checked-out HEAD equals the pinned rev")
        failures.append("HEAD verification")

    # 4. build errors must fail the job.
    #    This has to match the GUARD ITSELF, not the presence of the words: a mutation from
    #    `if grep -qE '^error' build.log; then` to `if false; then` otherwise slips through,
    #    because `grep` and `^error` still occur elsewhere in the workflow.
    guard = re.search(r"if\s+grep\s+-q\w*\s+'\^error'\s+build\.log\s*;\s*then", ex)
    if not guard:
        print("  FAIL: no `if grep -qE '^error' build.log; then` guard around the build log")
        failures.append("error gate")
    elif not re.search(r"exit\s+1", ex):
        print("  FAIL: the error guard does not exit non-zero")
        failures.append("error gate exit")

    # 5. every working-directory must exist
    for line in io.open(WF, encoding="utf-8").read().split("\n"):
        if "working-directory:" in line:
            d = line.split("working-directory:", 1)[1].strip()
            if not os.path.isdir(os.path.join(NEW, d)):
                print("  FAIL: working-directory %r does not exist" % d)
                failures.append("wd " + d)

    print("=" * 60)
    if failures:
        print("CI WORKFLOW: %d problem(s)" % len(failures))
        return 1
    print("CI WORKFLOW: executable steps refer only to this repository")
    return 0


if __name__ == "__main__":
    sys.exit(main())
