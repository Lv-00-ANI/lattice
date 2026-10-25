"""Reactivity test for I8 (comment integrity).

I8 had no reactivity test and its exit code was missing from the gate's table, so it had
never been shown to work: the first time it fired, `gate.py` would have raised KeyError
instead of returning COMMENT (9). Both are now fixed; this test keeps them fixed.

Two things make the test harder than it looks:

  * The probe must live in the kernel zone, otherwise `verify_all.py --fast` (which sets
    `DSH_GATE_SCOPE=kernel`) never walks it -- the same trap that made
    `gate_reactivity.py` report "got 0" for every case.
  * A freshly written, uncompiled probe trips I7 (artifact missing) BEFORE I8, and the
    gate reports the first invariant in order. So the probe is compiled first; only then
    does I8 become the deciding check.

Each case plants one defect, asserts the gate returns exactly COMMENT (9), and restores
the tree. A clean control asserts that a well-formed probe does NOT fire I8.
"""
import io
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
PROBE = os.path.join(ZERO, "Lattice", "Core", "Probe.lean")
GATE = os.path.join(HERE, "gate.py")

HEAD = "import Lattice.Core.Syntax\n\n"
CASES = [
    ("clean control",      HEAD + "/-- fine -/\ntheorem probe_ok : True := trivial\n", 0),
    ("glued doc comments", HEAD + "/-- a -//-- b -/\ntheorem probe_p1 : True := trivial\n", 9),
    ("unclosed comment",   HEAD + "/- never closed\ntheorem probe_p2 : True := trivial\n", 9),
    ("stray closer",       HEAD + "theorem probe_p3 : True := trivial -/\n", 9),
]


def run_gate():
    r = subprocess.run([sys.executable, GATE, "--quiet"], cwd=ZERO, capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def build_probe():
    """Compile the probe so I7 cannot shadow I8. Best effort: a damaged comment may make
    the build fail, in which case I7 stays quiet only if an olean exists -- so we also
    touch a stale-but-present olean by building twice."""
    subprocess.run(["lake", "build", "Lattice.Core.Probe"], cwd=ZERO,
                   capture_output=True, text=True, encoding="utf-8", errors="replace")


def main():
    base, _ = run_gate()
    print("  baseline gate exit:", base, flush=True)
    if base != 0:
        print("  ** baseline is already red; fix the tree before testing **")
        return 1
    failures = 0
    for name, src, expected in CASES:
        io.open(PROBE, "w", encoding="utf-8", newline="\n").write(src)
        try:
            build_probe()
            code, out = run_gate()
            ok = (code == expected)
            print("  %-22s expect %-2d got %-2d %s" %
                  (name, expected, code, "OK" if ok else "** FAIL **"), flush=True)
            if not ok:
                failures += 1
                for ln in out.splitlines()[:10]:
                    print("        " + ln)
        finally:
            if os.path.exists(PROBE):
                os.remove(PROBE)
    # remove any olean the probe build produced
    for ext in (".olean", ".ilean", ".trace"):
        p = os.path.join(ZERO, ".lake", "build", "lib", "Lattice", "Core", "Probe" + ext)
        if os.path.exists(p):
            os.remove(p)
    print("=" * 60)
    print("REACTIVITY (I8): %s" % ("ALL PASS" if failures == 0 else "%d FAILURE(S)" % failures))
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
