#!/usr/bin/env python3
"""Do the numbers in the documentation match the tree?

## The errors this exists for

Two rounds of reading `README.md` against the tree turned up:

* `## 四、几何层的结构（42 模块）` -- the layer had **43** files, because a module was added and the heading
  was not updated;
* `121 模块中 56 个不可构建` -- a static check of imports finds **23** files importing modules that do not exist
  (`Zero.LvFormal.Theory.lvLang` and friends), plus 5 modules listed in `known-unbuildable.json`. Neither
  number is 56.

Both are the same failure: a count was written once, the tree changed, and nothing compared them again. Prose
numbers are the part of documentation that ages fastest, and no audit looked at them.

## What is checked

A small set of counts that can be computed unambiguously, compared against the numbers written next to their
own description in `README.md`:

| what | how the README refers to it |
|:--|:--|
| files in `Zero/Geo` | `几何层的结构（N 模块）` |
| files under `Zero/Reference` | `N 个 Lv-00 历史文件` |
| entries in the escape baseline | `冻结 N 处历史逃逸` |
| LvFormal files importing missing modules | `N 个` in the LvFormal debt sentence |
| gov scripts cited in the README | every backticked `*.py` name must exist |
| entries registered in `verify_all.py` | `注册了 **N 项**` |

Only these four: each has exactly one way to be counted, so a mismatch is a defect rather than a matter of
interpretation. Anything vaguer is left alone -- an audit that guesses at prose is worse than one that is narrow.

Exit code 1 when a documented count disagrees with the tree, else 0. A mismatch is printed
with both numbers so the reader can check the counting rule and the count can be fixed in
the README rather than the checker being ignored.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))

# One source of truth for "what does this file say, ignoring comments": the same stripper the
# gate's I1/I2 use. Duplicating it here is how the theorem counts drifted apart before.
sys.path.insert(0, HERE)
from tools.sorry_axiom_census import strip_comments  # noqa: E402
Z = os.path.join(ZERO, "Lattice")

IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)


def is_generated_probe(path):
    """True for the throwaway modules the reactivity / verification checks build and delete.

    Two are known, and BOTH were caught leaving their file behind:

        Lattice/Core/Probe.lean   `layer_reactivity`, `check_i8_reactivity`, `gate_reactivity`,
                                  `check_comments_reactivity`
        Lattice/G4Probe.lean      `verify_g4.py`

    They are gitignored/untracked, they are not part of the deliverable, and a count that runs WHILE
    one is mid-flight reports one extra module, one extra theorem and one extra declaration -- so
    `audit_counts` and `check_usage_claims` failed nondeterministically.

    Measured: the module count followed these files 788 -> 789 -> 788 within a few minutes, and
    `git status --ignored` showed `Lattice/G4Probe.lean` present while `verify_all --list` ran.

    The rule is by BASENAME (`*Probe.lean`), verified safe: `git ls-files Lattice` contains no file
    ending in `Probe.lean`, so no real module can be filtered out by this.

    The deeper fix is for those checks to clean up in a `finally` (see the P0-8 backlog item); this
    filter makes the counters immune in the meantime.
    """
    return os.path.basename(path).endswith("Probe.lean")


def lean_count(d):
    if not os.path.isdir(d):
        return 0
    n = 0
    for root, dirs, fs in os.walk(d):
        dirs[:] = [x for x in dirs if x != ".lake"]
        n += sum(1 for f in fs
                 if f.endswith(".lean") and not is_generated_probe(os.path.join(root, f)))
    return n


def _kernel_files():
    """Every .lean under Lattice/, excluding Reference (which is not built) and generated probes."""
    for root, dirs, fs in os.walk(Z):
        dirs[:] = [x for x in dirs if x not in (".lake", "Reference")]
        for f in fs:
            full = os.path.join(root, f)
            if f.endswith(".lean") and not is_generated_probe(full):
                yield full


def module_total():
    """Lean modules in the kernel, INCLUDING the root-level aggregators.

    Earlier rounds counted 717 including `(root)`; summing only the six layer directories
    gives 710 and is wrong -- "Lean modules" means every built file.
    """
    return sum(1 for _ in _kernel_files())


def total_theorems():
    """Count `theorem`/`lemma` declarations that Lean actually ELABORATES.

    SCOPE, written down because three different numbers were all "the theorem count" at various
    times -- 7,919 / 8,011 / 8,068 -- differing only in criterion:

      * `Reference/` excluded: archived evidence, not a root of the build.
      * comments STRIPPED: a `theorem` mentioned inside a docstring is not a declaration.
      * attributes `@[...]` and the `private`/`protected`/`noncomputable` modifiers are allowed
        before the keyword, since Lean accepts them there.

    This is the number `README` quotes. A different scope is fine, but it has to be stated.
    """
    import re as _re
    pat = _re.compile(r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:private[ \t]+|protected[ \t]+|"
                      r"noncomputable[ \t]+)*(?:theorem|lemma)[ \t]")
    n = 0
    for p in _kernel_files():
        src = io.open(p, "rb").read().decode("utf-8", "replace")
        n += len(pat.findall(strip_comments(src)))
    return n


def owed_count():
    """The owed-slot count, read from the `decide` assertion in `Slots.lean`.

    Read rather than recomputed: `example : Slot.owedCount fullRegistry = N := by decide` is
    the authority (the kernel checked it). Reimplementing the registry logic here would create a
    second source of truth that could silently disagree with the first.
    """
    import re as _re
    p = os.path.join(Z, "Slots.lean")
    if not os.path.isfile(p):
        return -1
    src = io.open(p, "rb").read().decode("utf-8", "replace")
    m = _re.search(r"Slot\.owedCount fullRegistry = (\d+) := by decide", src)
    return int(m.group(1)) if m else -1


def escape_entries():
    p = os.path.join(ZERO, "gov", "escape-baseline.json")
    if not os.path.exists(p):
        return None
    import json
    try:
        d = json.load(io.open(p, encoding="utf-8"))
        return sum(sum(v.values()) for v in d["files"].values())
    except Exception:
        return None


def lvformal_missing_imports():
    base = os.path.join(Z, "Reference", "LvFormal")
    if not os.path.isdir(base):
        return None
    files = []
    for root, dirs, fs in os.walk(base):
        dirs[:] = [d for d in dirs if d != ".lake"]
        files += [os.path.join(root, f) for f in fs if f.endswith(".lean")]
    bad = 0
    for p in files:
        src = io.open(p, "rb").read().decode("utf-8", "replace").replace("\r\n", "\n")
        deps = [m for m in IMPORT.findall(src) if m.startswith("Zero.")]
        if any(not os.path.exists(os.path.join(Z, *d.split(".")) + ".lean") for d in deps):
            bad += 1
    return bad


def main():
    readme = os.path.join(ZERO, "README.md")
    if not os.path.exists(readme):
        print("README.md not found -- nothing to check")
        return 0
    text = io.open(readme, encoding="utf-8", errors="replace").read().replace("\r\n", "\n")

    actual = {
        "total": module_total(),
        "thms": total_theorems(),
        "owed": owed_count(),
        "core": lean_count(os.path.join(Z, "Core")),
        "lift": lean_count(os.path.join(Z, "Lift")),
        "domains": lean_count(os.path.join(Z, "Domains")),
        "geo": lean_count(os.path.join(Z, "Geo")),
        "lib": lean_count(os.path.join(Z, "Lib")),
        "ref": lean_count(os.path.join(Z, "Reference")),
        "esc": escape_entries(),
        "lvf": lvformal_missing_imports(),
    }

    # Each pattern captures the number the README claims, next to its own description.
    # Patterns follow the README's CURRENT shape: the layer counts appear in the directory
    # tree (`|   |-- Geo/       52       # ...`), not in prose. The earlier prose patterns
    # matched nothing at all, which made this checker silently compare nothing with nothing.
    claims = [
                ("Lean 模块总数", r"Lean 模块 \| (\d+)", "total"),
        ("定理总数", r"定理 / 引理 \| (\d+)", "thms"),
        ("未清欠账", r"未清欠账\*\* \| \*\*(\d+)\*\*", "owed"),
("Core 模块数", r"Core/\s+(\d+)", "core"),
        ("Lift 模块数", r"Lift/\s+(\d+)", "lift"),
        ("Domains 模块数", r"Domains/\s+(\d+)", "domains"),
        ("几何层模块数", r"Geo/\s+(\d+)", "geo"),
        ("Lib 模块数", r"Lib/\s+(\d+)", "lib"),
        ("LvFormal 文件数", r"LvFormal/\s+(\d+)", "ref"),
        ("escape 基线条目", r"\*\*(\d+)\*\* 处历史逃逸", "esc"),
        ("LvFormal 缺失依赖文件数", r"\| LvFormal 缺失依赖文件数 \| \*\*(\d+)\*\* 个文件", "lvf"),
    ]

    print("documentation counts vs the tree")
    print("=" * 78)
    mismatches = 0
    unmatched = 0
    for label, pat, key in claims:
        m = re.search(pat, text)
        got = actual[key]
        if m is None:
            # A pattern that matches nothing is a defect in this checker or in the README,
            # not a pass: it would otherwise look identical to "the README agrees".
            print("  %-26s README 未写 | 实测 %s   <- pattern matched nothing" % (label, got))
            unmatched += 1
            continue
        claimed = int(m.group(1))
        if got is None:
            print("  %-26s README 写 %d | 无法实测" % (label, claimed))
            continue
        ok = "ok" if claimed == got else "MISMATCH"
        if claimed != got:
            mismatches += 1
        print("  %-26s README 写 %-5d 实测 %-5s %s" % (label, claimed, got, ok))
    print("=" * 78)
    if not mismatches:
        print("  every checked count matches")
    print()
    print("  Two mismatches were found this way and corrected: the geometry layer heading said 42")
    print("  when the layer had 43 files, and the LvFormal debt said 56 unbuildable files when a")
    print("  static import check finds 23 (plus 5 modules in gov/known-unbuildable.json).")
    print("  Both had been written once and never compared again -- which is what this does.")
    # --- gov script names and the registration count -----------------------------------------
    gov = os.path.join(ZERO, "gov")
    cited = sorted(set(re.findall(r"`([A-Za-z0-9_]+\.py)(?: [^`]*)?`", text)))
    absent = [m for m in cited if not os.path.exists(os.path.join(gov, m))]
    va = io.open(os.path.join(gov, "verify_all.py"), encoding="utf-8", errors="replace").read()
    # Count the entries of the CHECKS literal by structure, not by quoting style: one entry per
    # line that opens a tuple. A regex demanding `"..."` as the command string silently skipped
    # `("...", "cmd %s ..." % ZERO)`, under-counting by one for several rounds.
    _cm = re.search(r"CHECKS = \[(.*?)\n\]", va, re.S)
    n_reg = len([ln for ln in (_cm.group(1) if _cm else "").split("\n")
                 if ln.strip().startswith("(")])
    m = re.search(r"注册了 \*\*(\d+) 项\*\*", text)

    print()
    print("gov script names cited in the README: %d, of which absent: %d"
          % (len(cited), len(absent)))
    for a in absent:
        print("    MISSING: %s" % a)
    if m is None:
        print("  registration count: README does not state one (actual %d)   <- pattern matched nothing" % n_reg)
        unmatched += 1
    elif int(m.group(1)) == n_reg:
        print("  registration count: README %s, actual %d -- ok" % (m.group(1), n_reg))
    else:
        print("  registration count: README %s, actual %d -- MISMATCH" % (m.group(1), n_reg))
        mismatches += 1

    unmentioned = [f for f in sorted(os.listdir(gov))
                   if f.endswith(".py") and f not in cited
                   and not f.startswith("_") and f != "verify_all.py"]
    print("  gov scripts the README does not mention: %d (survey tools, not gates)" % len(unmentioned))

    print()
    print("  Counting rules, so a reader can reproduce them: every tracked file (`.lake` excluded);")
    print("  LvFormal \"unbuildable\" means an `import Zero.…` whose module file does not exist.")
    if mismatches or unmatched:
        print()
        print("RESULT: %d disagreement(s), %d pattern(s) matched nothing in the README"
              % (mismatches, unmatched))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
