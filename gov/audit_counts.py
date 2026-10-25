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

Exit code 0. A mismatch is printed with both numbers so the reader can check the counting rule.
"""
import io
import os
import re
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
Z = os.path.join(ZERO, "Lattice")

IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)


def lean_count(d):
    if not os.path.isdir(d):
        return 0
    n = 0
    for root, dirs, fs in os.walk(d):
        dirs[:] = [x for x in dirs if x != ".lake"]
        n += sum(1 for f in fs if f.endswith(".lean"))
    return n


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
        "geo": lean_count(os.path.join(Z, "Geo")),
        "ref": lean_count(os.path.join(Z, "Reference")),
        "esc": escape_entries(),
        "lvf": lvformal_missing_imports(),
    }

    # Each pattern captures the number the README claims, next to its own description.
    claims = [
        ("几何层模块数", r"几何层的结构（(\d+) 模块）", "geo"),
        ("Reference 文件数", r"（(\d+) 个 Lv-00 历史文件）", "ref"),
        ("escape 基线条目", r"冻结 (\d+) 处历史逃逸", "esc"),
        ("LvFormal 缺失依赖文件数", r"：\*\*(\d+) 个\*\* 文件引用了不存在的模块", "lvf"),
    ]

    print("documentation counts vs the tree")
    print("=" * 78)
    mismatches = 0
    for label, pat, key in claims:
        m = re.search(pat, text)
        got = actual[key]
        if m is None:
            print("  %-26s README 未写 | 实测 %s" % (label, got))
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
    n_reg = len(re.findall(r'\(\s*"[^"]+",\s*"[^"]+"\s*\)', va))
    m = re.search(r"注册了 \*\*(\d+) 项\*\*", text)

    print()
    print("gov script names cited in the README: %d, of which absent: %d"
          % (len(cited), len(absent)))
    for a in absent:
        print("    MISSING: %s" % a)
    if m is None:
        print("  registration count: README does not state one (actual %d)" % n_reg)
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
    return 0


if __name__ == "__main__":
    sys.exit(main())
