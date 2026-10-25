#!/usr/bin/env python3
"""深度复核：`lift/` 之间的依赖、`core/` 的纯净性、`core` 声明的外部使用、未引用的定理。

## 性能修正

第一版对每个 `core_m` 的每个声明都在每个外部模块里做一次 `re.search`，
在 558 个文件的树上退化成立方复杂度，10 分钟跑不完。

本版改为：
1. 一次性提取所有模块的声明名 → 集合
2. 一次性把每个外部模块的源码变成 token 集合（用 `re.findall(r"[A-Za-z0-9_']+", src)`）
3. 求交，而不是逐个正则匹配

复杂度从 O(模块 × 声明 × 外部模块) 降到 O(总 token 数)。
"""
import io
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

DECL = re.compile(r"^\s*(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([A-Za-z0-9_']+)", re.M)
TOKEN = re.compile(r"[A-Za-z0-9_']+")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)



# ---------------------------------------------------------------- scope
# `DSH_GATE_SCOPE=kernel` restricts the walk to the code this project wrote, which is what makes the
# fast verification path affordable. Unset means "everything".
KERNEL_PREFIXES = ("Lattice/Core/", "Lattice/Lift/", "Lattice/Lib/", "Lattice/Slots", "Lattice/Geo/")


def _in_scope(relpath):
    scope = os.environ.get("DSH_GATE_SCOPE")
    if not scope or scope == "all":
        return True
    r = relpath.replace("\\", "/")
    if r.startswith("Lattice/"):
        r = r[len("Lattice/"):]
        r = "Lattice/" + r
    return any(p in r for p in KERNEL_PREFIXES)

def sources():
    out = []
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if f.endswith(".lean"):
                p = os.path.join(base, f)
                relp = os.path.relpath(p, ZERO).replace('\\', '/')
            if _in_scope(relp):
                out.append((p, relp[:-5].replace('/', '.')))
    return out


def main():
    files = sources()
    text = {}
    for p, m in files:
        text[m] = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))

    print("=" * 74)
    print("1. lift/ 模块之间的依赖")
    print("=" * 74)
    for m in sorted(text):
        if not m.startswith("Lattice.Lift"):
            continue
        imps = IMPORT.findall(text[m])
        sib = [i for i in imps if i.startswith("Lattice.Lift") and i != m]
        print("  %-32s siblings: %s" % (m, sib or "-"))

    print()
    print("=" * 74)
    print("2. core/ 是否导入上层")
    print("=" * 74)
    bad = []
    for m in sorted(text):
        if not m.startswith("Lattice.Core"):
            continue
        up = [i for i in IMPORT.findall(text[m])
              if i.startswith("Lattice.Lift") or i.startswith("Lattice.Lib") or i.startswith("Lattice.Geo")]
        if up:
            bad.append((m, up))
    print("  违规:", bad or "无")

    print()
    print("=" * 74)
    print("3. 被外部使用的 core/geo 声明（token 交集，非逐个正则）")
    print("=" * 74)
    # 收集 core/geo 声明
    core_decls = {}
    for m in sorted(text):
        if m.startswith(("Lattice.Core", "Lattice.Geo", "Lattice.Lib")):
            for kind, name in DECL.findall(text[m]):
                core_decls.setdefault(name, set()).add(m)
    # 外部模块的 token 集合
    used = collections.Counter()
    for m in sorted(text):
        if m.startswith(("Lattice.Core", "Lattice.Geo", "Lattice.Lib")):
            continue
        toks = set(TOKEN.findall(text[m]))
        for name in core_decls:
            if name in toks:
                used[name] += 1
    for name, n in used.most_common(25):
        srcs = sorted(core_decls[name])
        print("  %-30s 被 %2d 个文件引用  (定义于 %s)" % (name, n, srcs[0]))
    print("  共 %d 个 core/geo/lib 声明被外部使用" % len(used))

    print()
    print("=" * 74)
    print("4. 从未被引用的定理（限 kernel）")
    print("=" * 74)
    alltok = collections.Counter()
    for m in text:
        alltok.update(set(TOKEN.findall(text[m])))
    uncited = []
    for m in sorted(text):
        if not m.startswith(("Lattice.Core", "Lattice.Geo", "Lattice.Lib")):
            continue
        for kind, name in DECL.findall(text[m]):
            if kind not in ("theorem", "lemma"):
                continue
            if alltok[name] <= 1:
                uncited.append("%s.%s" % (m, name))
    for u in uncited[:30]:
        print("  ", u)
    print("  共 %d 条" % len(uncited))
    return 0


if __name__ == "__main__":
    sys.exit(main())
