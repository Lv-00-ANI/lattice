# -*- coding: utf-8 -*-
"""Reactivity test for the slot cross-check, done by APPENDING to the registry.

The earlier draft edited existing slot literals with regex, which is fragile and did not
actually produce each defect. This version appends one deliberately broken slot per case
to `fullRegistry` -- additive edits are reversible and each defect is unambiguous.

Cases:
  1. a name not shaped `<domain>.<object>.<property>`;
  2. a duplicate of an existing name;
  3. a `discharged` status naming a declaration that does not exist.

The real file is backed up and restored around the experiment.
"""
import io
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SLOTS = os.path.join(ZERO, "Lattice", "Slots.lean")
BACKUP = SLOTS + ".reactivity.bak"
CHECK = os.path.join(HERE, "check_slots.py")

BROKEN = {
    "bad name": '  { name := "BadName", stmt := True, note := "", status := .open_ }',
    "duplicate": '  { name := "core.repair.atomic", stmt := True, note := "", status := .open_ }',
    "phantom discharge":
        '  { name := "lift.phantom.proof", stmt := True, note := "", '
        'status := .discharged "no_such_declaration_exists" }',
}
EXPECT = {
    "bad name": "not `<domain>",
    "duplicate": "duplicate slot name",
    "phantom discharge": "claims discharge by unknown declaration",
}


def run():
    r = subprocess.run([sys.executable, CHECK], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return (r.stdout or "") + (r.stderr or "")


def main():
    shutil.copy2(SLOTS, BACKUP)
    src = io.open(SLOTS, encoding="utf-8").read()
    failures = 0
    try:
        for label, literal in BROKEN.items():
            # Anchor on the closing bracket of `fullRegistry`, not on a particular slot name:
            # the registry is expected to grow, and a brittle anchor would make this test fail
            # for a reason unrelated to what it checks.
            head = src.index("def fullRegistry")
            close = src.index("]", head)
            text = src[:close] + "  , " + literal.strip() + "\n" + src[close:]
            assert text != src, "anchor for %s not found" % label
            io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(text)
            out = run()
            ok = EXPECT[label] in out
            print("  %-20s %s" % (label, "OK (fired)" if ok else "** FAIL (did not fire) **"))
            if not ok:
                failures += 1
                print("      output:", out.strip()[:500])
            io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(src)
    finally:
        shutil.copy2(BACKUP, SLOTS)
        os.remove(BACKUP)
    print("=" * 56)
    print("clean run:", run().strip()[:200])
    print("REACTIVITY:", "ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
