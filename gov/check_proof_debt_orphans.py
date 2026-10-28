"""Fail if any proof-debt verdict points at a file that no longer exists.

## Why this exists

`DIRECTORY-DESIGN.md` §2.8 claims "`PROOF-DEBT` is regenerated with a `PATH_MAP`". **Round 234 measured
that the mechanism did not exist.** While piloting the P2 move it became clear why the omission is
dangerous: the 1369 verdicts are keyed on `(file, name)` with `file` relative to `Lattice/`. A `git mv`
therefore **silently orphans** every verdict for the moved file -- the inventory join misses,
`in_degree` falls back to 0, and the ledger quietly reports a reviewed file as unreviewed.

That is the same "silent empty" shape this project has hit four times (the `:=` vs `where` regex, the
`Input :=` reader, the greedy `: Primitive`, and the `%%` literal). **A ledger that loses entries without
saying so is worse than no ledger**, because the coverage table still claims 100% of the load-bearing set.

## What it checks

For every verdict: `Lattice/<file>` must exist, where `<file>` has been mapped through the SAME
`PATH_MAP` the generator uses. If a file is gone and unmapped, the move that removed it forgot the map.

## `--self-test`

`check_selftest_coverage.py` requires every gate to demonstrate its own failure. Here that means: build a
temporary review directory containing a verdict for a file that does not exist, and assert this checker
reports it. **Without that test, "0 orphans" is indistinguishable from "the scan found nothing to scan"**
-- which is the exact failure mode this file exists to catch, so it would be absurd to leave it untested.
"""

import io
import json
import os
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
LAT_DEFAULT = os.path.join(ROOT, "Lattice")
REV_DEFAULT = os.path.join(ROOT, "agent-tmp", "review")

sys.path.insert(0, HERE)
# single source of truth: do NOT copy the map, and do NOT import the generator either --
# `gen_proof_debt.py` writes `PROOF-DEBT.md` at module scope, so importing it would make this
# checker regenerate the very artifact it is checking (round 234's first attempt did exactly that).
from _debt_path_map import PATH_MAP


def collect(rev):
    """`{file: count}` over every verdict record in `rev`."""
    files = {}
    if not os.path.isdir(rev):
        return files
    for fn in sorted(os.listdir(rev)):
        if not (fn.startswith("verdicts_") and fn.endswith(".jsonl")):
            continue
        for line in io.open(os.path.join(rev, fn), encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            try:
                v = json.loads(line)
            except json.JSONDecodeError:
                continue
            f = v.get("file")
            if f:
                files[f] = files.get(f, 0) + 1
    return files


def scan(files, lat, path_map):
    """The orphaned `(file, count)` pairs, after applying `path_map`."""
    orphaned = []
    for f, n in sorted(files.items()):
        mapped = path_map.get(f, f)
        if not os.path.exists(os.path.join(lat, mapped.replace("/", os.sep))):
            orphaned.append((f, n))
    return orphaned


def main(argv):
    if "--self-test" in argv:
        # inject a defect: one verdict for a file that certainly does not exist,
        # plus one that DOES exist -- so the test also shows the scan is not "report everything"
        # The fixture goes INSIDE the workspace: the sandbox denies writes to the platform temp area
        # (round 234's first version used tempfile.mkdtemp and failed with PermissionError).
        tmp = os.path.join(HERE, "_selftest_debt_orphans")
        os.makedirs(tmp, exist_ok=True)
        try:
            with io.open(os.path.join(tmp, "verdicts_t1.jsonl"), "w", encoding="utf-8") as fh:
                fh.write(json.dumps({"file": "No/Such/Module.lean", "name": "phantom"}) + "\n")
            with io.open(os.path.join(tmp, "verdicts_t2.jsonl"), "w", encoding="utf-8") as fh:
                fh.write(json.dumps({"file": "Core/Net.lean", "name": "real"}) + "\n")
            got = [f for f, _ in scan(collect(tmp), LAT_DEFAULT, {})]
        finally:
            for fn in ("verdicts_t1.jsonl", "verdicts_t2.jsonl"):
                p = os.path.join(tmp, fn)
                if os.path.exists(p):
                    os.remove(p)
            try:
                os.rmdir(tmp)
            except OSError:
                pass
        if got == ["No/Such/Module.lean"]:
            print("SELFTEST OK: reports the phantom, ignores the real file")
            return 0
        print("SELFTEST FAILED: expected exactly ['No/Such/Module.lean'], got %r" % (got,))
        return 1

    files = collect(REV_DEFAULT)
    orphaned = scan(files, LAT_DEFAULT, PATH_MAP)
    if orphaned:
        print("PROOF-DEBT ORPHANS: %d file(s) with verdicts but no file in the tree" % len(orphaned))
        for f, n in orphaned:
            print("    %s  (%d verdict(s)) -- moved without a PATH_MAP entry?" % (f, n))
        return 1
    print("PROOF-DEBT ORPHANS: all %d reviewed file(s) still resolve (PATH_MAP covers the moved ones)"
          % len(files))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
