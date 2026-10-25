# -*- coding: utf-8 -*-
"""End-to-end proof that the *gate* now catches a lost definition.

`check_registry_reactivity.py` tests the checker in isolation. This tests the wiring: the gate itself
must exit non-zero when a definition vanishes, which is the path a future session would actually take.

The defect planted is the round-27 shape: delete a `def ... : Slot` (with its doc comment) while leaving
the registry entry that names it.
"""
import io
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SLOTS = os.path.join(ZERO, "Lattice", "Slots.lean")
BACKUP = SLOTS + ".gate_reactivity.bak"
GATE = os.path.join(HERE, "gate.py")


def gate_exit():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=ZERO, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, ((r.stdout or "") + (r.stderr or ""))


def main():
    src = io.open(SLOTS, encoding="utf-8").read()
    shutil.copy2(SLOTS, BACKUP)
    failures = 0
    try:
        base, _ = gate_exit()
        print("  baseline gate exit:", base)
        if base != 0:
            print("  ** baseline is already red; fix the tree before testing **")
            return 1

        dead = "def repairAtomic : Slot :="
        assert dead in src
        start = src.rindex("/--", 0, src.index(dead))
        end = src.index("/--", src.index(dead))
        io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(src[:start] + src[end:])
        code, out = gate_exit()
        ok = code != 0 and ("but no such defi" in out)
        print("  definition deleted -> gate exit %d %s" % (code, "OK (fired)" if ok else "** FAIL **"))
        if not ok:
            failures += 1
            print("     ", out.strip()[:400])
    finally:
        shutil.copy2(BACKUP, SLOTS)
        os.remove(BACKUP)

    code, _ = gate_exit()
    print("=" * 56)
    print("restored; gate exit:", code)
    print("GATE REACTIVITY:", "PASS" if failures == 0 and code == 0 else "FAILURE")
    return 0 if failures == 0 and code == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
