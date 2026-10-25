# -*- coding: utf-8 -*-
"""Reactivity test for the registry-consistency check.

The check exists because round 27 lost an entire `def` to a text splice and nothing noticed until the
next build. So the test plants exactly that defect, plus its two mirror images:

  1. a registry entry whose definition is gone (the round-27 shape);
  2. a definition that is never registered (silently excluded from the owed count);
  3. a name listed twice (inflates the count without adding a slot).

Each must fire; the untouched file must pass.
"""
import io
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
SLOTS = os.path.join(ZERO, "Lattice", "Slots.lean")
BACKUP = SLOTS + ".registry_reactivity.bak"
CHECK = os.path.join(HERE, "check_registry.py")


def run():
    r = subprocess.run([sys.executable, CHECK], cwd=ZERO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def main():
    src = io.open(SLOTS, encoding="utf-8").read()
    shutil.copy2(SLOTS, BACKUP)
    failures = 0
    try:
        # 1. delete a slot definition, keep the registry entry
        dead = "def repairAtomic : Slot :="
        assert dead in src
        start = src.rindex("/--", 0, src.index(dead))
        end = src.index("/--", src.index(dead))
        broken = src[:start] + src[end:]
        io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(broken)
        code, out = run()
        ok = code != 0 and "no such definition exists" in out
        print("  %-34s %s" % ("definition deleted", "OK (fired)" if ok else "** FAIL **"))
        failures += 0 if ok else 1
        if not ok:
            print("     ", out.strip()[:300])

        # 2. add a definition that is never registered
        added = src.replace("def repairAtomic : Slot :=",
                            "def unregisteredSlot : Slot :=\n"
                            "  { name := \"x.y.z\", stmt := True, note := \"\", status := .open_ }\n\n"
                            "def repairAtomic : Slot :=", 1)
        io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(added)
        code, out = run()
        ok = code != 0 and "is not listed in" in out
        print("  %-34s %s" % ("unregistered definition", "OK (fired)" if ok else "** FAIL **"))
        failures += 0 if ok else 1
        if not ok:
            print("     ", out.strip()[:300])

        # 3. list a name twice
        dup = src.replace("  , repairAtomic\n", "  , repairAtomic\n  , repairAtomic\n", 1)
        assert dup != src, "could not duplicate the entry"
        io.open(SLOTS, "w", encoding="utf-8", newline="\n").write(dup)
        code, out = run()
        ok = code != 0 and "listed 2 times" in out
        print("  %-34s %s" % ("duplicate registry entry", "OK (fired)" if ok else "** FAIL **"))
        failures += 0 if ok else 1
        if not ok:
            print("     ", out.strip()[:300])
    finally:
        shutil.copy2(BACKUP, SLOTS)
        os.remove(BACKUP)

    code, out = run()
    print("=" * 56)
    print("clean file:", out.strip()[:120], "(exit %d)" % code)
    print("REACTIVITY:", "ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
