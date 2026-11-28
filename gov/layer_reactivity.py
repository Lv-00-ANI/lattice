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
# Round 242. This used to plant the probe in `Lattice/Lift/`, which is now EMPTY (the 66 modules moved
# to `Runtime/` in rounds 234-241). The test still worked -- writing a file recreates the directory --
# but it left `Lattice/Lift/` behind as an untracked empty directory after every `verify_all`.
#
# `Runtime` has the SAME rank as `Lift` (both 2), so the planted defect is unchanged: a rank-2 module
# importing `Lattice.Geo.*` (rank 4) must make I4 report exit 4. Only the location moved, into a
# layer that actually contains modules.
PROBE = os.path.join(NEW, "Lattice", "Runtime", "LayeringProbe.lean")
GATE = os.path.join(HERE, "gate.py")

# **第 1199 轮：植入的 import 必须指向**存活**的模块。**
# 旧值是 `Lattice.Geo.Dist`，而 `Lattice/Geo` **已不存在**（第 265 轮归档），
# 那个前缀又在 W0-2（第 1181 轮）从 `LAYER_OF` 里被当作死键删掉了。
# ⇒ 故从那一轮起，`layer_of` 对它返回不到任何层，I4 **根本不会触发**，
# 失败改由 I7（探针无 `.olean`）报出来——而 `--fast` 跳过探针，故这个回归**藏了十四轮**。
# ⇒ 现改用 `Lattice.Lib.Compiler.RealLayer`：它**存活**，且 `Lib`（秩 3）高于 `Runtime`（秩 2）。
PROBE_SRC = "import Lattice.Lib.Compiler.RealLayer\n\ntheorem layeringProbe : True := trivial\n"


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
              % ("Runtime imports Lib", code, "OK" if ok else "** FAIL **"), flush=True)
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
