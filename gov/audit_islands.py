# -*- coding: utf-8 -*-
"""把 `audit_reach.py` 的输出按模块汇总，找出「全部定理都没有消费者」的模块。

## 为什么做这个

`audit_reach` 按「条目」列出，读者看不到**模块级**的判断。
一个模块若它的所有定理都落入 `never-used-anywhere`，那它是**孤岛**：
可以编译、可以证明，但与任何其他模块无连接。

## 判据

只有**真正是孤岛**才报：该模块下**没有任何**定理被其他文件引用，
且**没有任何**定理被归类为 entry-point-by-design。
（entry-point 意味着「设计上就是终端陈述」，那不是孤岛。）

## 为什么不用改 audit_reach 本身

它的职责是「找出没有被引用的定理」。模块级汇总是一个**不同的阅读视角**，
放在独立的脚本里，两者各自单一职责。
"""
import io
import os
import re
import subprocess
import sys

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")

GOV = os.path.dirname(os.path.abspath(__file__)) if "__file__" in dir() else os.getcwd()

out = subprocess.run([sys.executable, os.path.join(GOV, "audit_reach.py")],
                     capture_output=True, text=True, encoding="utf-8", errors="replace")
text = out.stdout

SECTION = re.compile(r"^={10,}$")
ROW = re.compile(r"^\s{2}([A-Za-z0-9_.]+)\s+(.+)$")

sections = {}
current = None
for line in text.splitlines():
    if SECTION.match(line.strip()):
        continue
    low = line.strip()
    if low.startswith("never referenced outside"):
        current = "outside"
        sections[current] = {}
        continue
    if low.startswith("NEVER used anywhere"):
        current = "anywhere"
        sections[current] = {}
        continue
    if low.startswith("entry points by design"):
        current = "design"
        sections[current] = {}
        continue
    if low.startswith("Note on interpretation"):
        current = None
        continue
    if current:
        m = ROW.match(line)
        if m:
            mod, names = m.group(1), [x.strip() for x in m.group(2).split(",")]
            sections[current].setdefault(mod, set()).update(names)

outside = sections.get("outside", {})
anywhere = sections.get("anywhere", {})
design = sections.get("design", {})

all_mods = set(outside) | set(anywhere) | set(design)
print("模块数（有未被引用定理的）: %d" % len(all_mods))
print()

islands = []
for mod in sorted(all_mods):
    if mod in design:
        continue
    n_out = len(outside.get(mod, ()))
    n_any = len(anywhere.get(mod, ()))
    if n_out == 0 and n_any > 0:
        islands.append((mod, n_any, sorted(anywhere[mod])))

print("=" * 78)
print("模块级孤岛：全部定理都没有消费者，且无 entry-point -- %d 个" % len(islands))
print("=" * 78)
for mod, n, names in islands:
    print("  %-22s %2d 条: %s" % (mod, n, ", ".join(names[:6])))

print()
print("=" * 78)
print("按「未被引用定理数」排序的前 15 个模块")
print("=" * 78)
tot = {}
for mod in all_mods:
    tot[mod] = len(outside.get(mod, ())) + len(anywhere.get(mod, ()))
for mod, n in sorted(tot.items(), key=lambda kv: -kv[1])[:15]:
    tag = "design" if mod in design else ("ISLAND" if any(m == mod for m, _, _ in islands) else "")
    print("  %-22s %3d %s" % (mod, n, tag))

print()
print("=" * 78)
print("判据说明")
print("=" * 78)
print("  '模块级孤岛' 指：该模块的所有未被引用定理都落在 'NEVER used anywhere'，")
print("  且该模块没有任何 entry-point-by-design 的定理。")
print("  entry-point 意味着「设计上就是给外部读者引用的终端陈述」——它不是孤岛。")
print()
print("  这是 survey，exit 0。孤岛不一定是缺陷：终端陈述本就无需消费者。")
print("  但一个**中间步骤**若无消费者，说明链条在那里断了。")
