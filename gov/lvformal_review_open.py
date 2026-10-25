# -*- coding: utf-8 -*-
"""审查 open_bare 的改写决定：哪些会被改，改成什么。

21 处 `open X` 会被改。执行前必须核对这些 X 确实指向本地模块，
而不是 Mathlib 的命名空间（如 open Real 是 Mathlib 的，不能改）。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
ROOT = os.path.join(ZERO, "Lattice", "LvFormal")

from lvformal_fixns import build_module_map, FOREIGN, OPEN_BARE_RE  # noqa: E402


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    modmap = build_module_map()
    local_short = set(modmap.keys())
    print("=" * 74)
    print("open X 审查（共扫描 %d 个本地模块短名）" % len(local_short))
    print("=" * 74)

    will_change, will_skip_local, will_skip_foreign = [], [], []
    for base, dirs, fs in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ROOT).replace("\\", "/")
            s = io.open(p, encoding="utf-8").read()
            for m in OPEN_BARE_RE.finditer(s):
                name = m.group(2)
                if name in FOREIGN:
                    will_skip_foreign.append((rel, name))
                elif name in modmap:
                    will_change.append((rel, name, modmap[name]))
                else:
                    will_skip_local.append((rel, name))

    print("\n--- 将改写（指向本地模块）---  %d" % len(will_change))
    for rel, name, tgt in will_change:
        print("   %-46s %-24s -> %s" % (asc(rel), asc(name), asc(tgt)))

    print("\n--- 保持不变（Mathlib 命名空间）--- %d" % len(will_skip_foreign))
    seen = set()
    for rel, name in will_skip_foreign:
        if name in seen:
            continue
        seen.add(name)
        print("   %-24s (例: %s)" % (asc(name), asc(rel)))

    print("\n--- 保持不变（非本地、非白名单）--- %d" % len(will_skip_local))
    seen2 = set()
    for rel, name in will_skip_local:
        if name in seen2:
            continue
        seen2.add(name)
        print("   %-24s (例: %s)" % (asc(name), asc(rel)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
