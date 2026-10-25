"""Reactivity test for the I4 Geo-layer rule.

I4 previously skipped Geo files entirely (`layer_of` returned "top" for them), so a
`Lift -> Geo` import -- the reverse of the intended direction -- was invisible. The rule is
now in place; this test is what keeps it honest.

Planted defect: a `Lattice/Lift/*.lean` module importing `Lattice.Geo.*`. I4 must report it
(exit 4). The probe is removed and the tree rebuilt-free afterwards: an uncompiled `.lean`
would trip I7 before I4, exactly as in the I8 test, so the file is deleted rather than built.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NEW = os.path.abspath(os.path.join(HERE, ".."))
PROBE = os.path.join(NEW, "Lattice", "Lift", "LayeringProbe.lean")
GATE = os.path.join(HERE, "gate.py")

PROBE_SRC = "import Lattice.Geo.Dist\n\ntheorem layeringProbe : True := trivial\n"


def run_gate():
    r = subprocess.run([sys.executable, GATE], cwd=NEW, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def cleanup():
    if os.path.exists(PROBE):
        os.remove(PROBE)
    for ext in (".olean", ".ilean", ".trace",
                ".olean.hash", ".ilean.hash", ".trace.hash"):
        p = os.path.join(NEW, ".lake", "build", "lib", "Lattice", "Lift",
                         "LayeringProbe" + ext)
        if os.path.exists(p):
            os.remove(p)


def main():
    base, _ = run_gate()
    print("  baseline gate exit:", base, flush=True)
    if base != 0:
        print("  ** baseline is already red; fix the tree before testing **")
        return 1
    failures = 0
    try:
        os.makedirs(os.path.dirname(PROBE), exist_ok=True)
        with open(PROBE, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(PROBE_SRC)
        code, out = run_gate()
        ok = (code == 4) and ("I4" in out)
        print("  %-28s expect 4  got %-2d %s"
              % ("Lift imports Geo", code, "OK" if ok else "** FAIL **"), flush=True)
        if not ok:
            failures += 1
            for ln in out.split("\n"):
                if "I4" in ln or "layer" in ln:
                    print("        " + ln.strip()[:110])
    finally:
        cleanup()
    code, _ = run_gate()
    print("  restored gate exit: %d (expect 0)" % code, flush=True)
    if code != 0:
        failures += 1
    print("=" * 60)
    print("REACTIVITY (I4 geo layer): %s"
          % ("ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures))
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
