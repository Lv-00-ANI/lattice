#!/usr/bin/env python3
"""门禁的作用域：哪些目录适用 zero 的 8 条不变量。

## 问题

zzero/gov/gate.pyz 的 8 条不变量是为 **28 个精炼的内核模块**设计的：
- I1/I2 禁止 axiom/sorry
- I3 禁止重复定义
- I4 强制 core < slots < lift < lib 的分层
- I5 拒绝冒名 end-to-end

现在 zzero/z 下多了三类**性质完全不同**的代码：

| 目录 | 来源 | 性质 | 是否适用内核标准 |
|:--|:--|:--|:--|
| zZero/Core|Lift|Lib|Slotsz | 本项目原创 | 精炼、零逃逸 | ✅ 全部适用 |
| zZero/LvFormal/z | 旧项目资产 | 3,651 行零逃逸的编译链 + 若干历史 admit | **部分适用** |
| zZero/Legacy/z | 旧项目资产 | 437 个文件，已知有 36 处冒名 e2e | **部分适用** |
| zZero/LegacyConflicted/z | 待处理隔离区 | 已知冲突，暂不接入 | **不适用**（但要登记） |

## 判定

不能一刀切。正确做法是**分层作用域**：

1. **内核区**（Core/Lift/Lib/Slots）：8 条全部强制，一条不松。
2. **迁入区**（LvFormal/Legacy）：I1/I2（无 axiom/sorry）仍强制——但**冻结基线**：
   已经存在的逃逸登记在白名单里，新增的必须为 0。这防止「越迁越差」。
   I3/I5 **只对新文件生效**，历史文件登记基线。
3. **隔离区**（LegacyConflicted）：不检查内容，但**必须逐个登记**在封存清单里，
   且清单和目录必须双向一致（复用 I6 的 check_registry 思路）。

## 本脚本

只输出判定结果，不修改 gate.py。用于先看清规模，再决定怎么改门禁。

用法：
    python gov/gate_scope.py
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

ZONES = {
    "kernel": ["Lattice/Core", "Lattice/Lift", "Lattice/Lib", "Lattice/Slots"],
    "intake": ["Lattice/LvFormal", "Lattice/Legacy"],
    "quarantine": ["Lattice/LegacyConflicted"],
}

SORRY = re.compile(r"\bsorry\b")
ADMIT = re.compile(r"\badmit\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_']+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def zone_of(rel):
    """按目录段匹配，不做字符串前缀匹配。

    zZero/LegacyConflicted/x.leanz 以 zZero/Legacyz 开头，但它是隔离区而非迁入区。
    用 startswith 会把两者混为一谈——这正是第一版脚本 quarantine 统计为 0 的原因。
    """
    parts = rel.split("/")
    for z, prefixes in ZONES.items():
        for p in prefixes:
            seg = p.split("/")
            if parts[:len(seg)] == seg:
                return z
    return "root"


def main():
    stats = {z: {"files": 0, "lines": 0, "sorry": 0, "admit": 0, "axiom": 0}
             for z in list(ZONES) + ["root"]}
    offenders = {"kernel": [], "intake": []}

    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            z = zone_of(rel)
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            src = strip_comments(raw)
            s = len(SORRY.findall(src))
            a = len(ADMIT.findall(src))
            x = len(AXIOM.findall(src))
            d = stats[z]
            d["files"] += 1
            d["lines"] += raw.count("\n") + 1
            d["sorry"] += s
            d["admit"] += a
            d["axiom"] += x
            if (s or a or x) and z in offenders:
                offenders[z].append((rel, s, a, x))

    print("=" * 74)
    print("门禁作用域实测")
    print("=" * 74)
    print("%-12s %7s %9s %7s %7s %7s" % ("zone", "files", "lines", "sorry", "admit", "axiom"))
    print("-" * 74)
    for z in ("kernel", "intake", "quarantine", "root"):
        d = stats[z]
        print("%-12s %7d %9d %7d %7d %7d"
              % (z, d["files"], d["lines"], d["sorry"], d["admit"], d["axiom"]))

    print()
    print("=" * 74)
    print("迁入区（LvFormal + Legacy）里已存在的逃逸 —— 需登记为冻结基线")
    print("=" * 74)
    if not offenders["intake"]:
        print("  无")
    else:
        print("  共 %d 个文件:" % len(offenders["intake"]))
        for rel, s, a, x in offenders["intake"][:30]:
            print("   %-52s sorry=%d admit=%d axiom=%d" % (asc(rel), s, a, x))
        if len(offenders["intake"]) > 30:
            print("   ... 还有 %d 个" % (len(offenders["intake"]) - 30))

    print()
    print("=" * 74)
    print("判定")
    print("=" * 74)
    k = stats["kernel"]
    print("  内核区 %d 个文件、%d 行，逃逸 %d 处"
          % (k["files"], k["lines"], k["sorry"] + k["admit"] + k["axiom"]))
    if k["sorry"] == 0 and k["admit"] == 0 and k["axiom"] == 0:
        print("  => 内核区完全干净，I1/I2 可继续无条件强制。")
    else:
        print("  => 内核区出现逃逸，必须立即修复。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
