#!/usr/bin/env python3
"""门禁的作用域规则：哪些目录适用哪条不变量。

## 问题

`gate.py` 的 8 条不变量是为 **28 个精炼的内核模块** 写的：
I1/I2 禁逃逸、I3 禁重名、I4 强制分层、I5 拒绝冒名 end-to-end。

迁入 `Zero/Legacy/`（437）与 `Zero/LvFormal/`（121）后，全部红灯：

| 不变量 | 违规 | 来源 | 性质 |
|:--|--:|:--|:--|
| I1 axiom | 1 | LvFormal `LogicalFramework`（完备性定理） | 历史资产 |
| I2 admit | 68 | LvFormal 几何/密码学主题 | 历史资产 |
| I3 重名 | 32 | Legacy 内部同名 + 与内核同名 | 历史缺陷 |
| I5 冒名 e2e | 36 | Legacy 的 `e2e_*` | 历史缺陷 |

**这些都不是我们写的**，但如果不处理，门禁永远红，等于失效。

## 规则：三层作用域

1. **kernel**（`Core/` `Lift/` `Lib/` `Slots`）：**全部强制，一条不松**。
   这是我们自己的代码，必须零逃逸、零重名。
2. **intake**（`LvFormal/` `Legacy/`）：**冻结基线**。
   已存在的逃逸/重名登记在 `gov/intake-baseline.json`；
   门禁断言「当前 ⊆ 基线」，新增即红。这防止「越迁越差」。
3. **quarantine**（`LegacyConflicted/`）：**只登记不检查**。
   它是已知冲突的隔离区，按标准检查会永远红。但必须逐个登记，防止被当成垃圾桶。

## 这个脚本做什么

测量当前各个 zone 的实际违规数，输出基线文件，并给出 gate.py 应如何改的建议。
不改 gate.py（那是下一步，需要确认）。
"""
import io
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

ZONES = [
    ("kernel", ["Lattice/Core", "Lattice/Lift", "Lattice/Lib", "Lattice/Slots", "Lattice/Geo"]),
    ("reference", ["Lattice/Reference"]),
]

SORRY = re.compile(r"\bsorry\b")
ADMIT = re.compile(r"\badmit\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_']+)", re.M)
DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_']+)", re.M)


def zone_of(rel):
    """按目录段匹配，不做字符串前缀匹配（`LegacyConflicted` 以 `Legacy` 开头）。"""
    parts = rel.split("/")
    for z, prefixes in ZONES:
        for p in prefixes:
            seg = p.split("/")
            if parts[:len(seg)] == seg:
                return z
    return "root"


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def main():
    zones = {z: {"files": 0, "lines": 0, "sorry": 0, "admit": 0, "axiom": 0,
                 "axiom_files": [], "escape_files": []} for z, _ in ZONES}
    zones["root"] = {"files": 0, "lines": 0, "sorry": 0, "admit": 0, "axiom": 0,
                     "axiom_files": [], "escape_files": []}

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
            s_, a_, x_ = (len(SORRY.findall(src)), len(ADMIT.findall(src)),
                          len(AXIOM.findall(src)))
            d = zones[z]
            d["files"] += 1
            d["lines"] += raw.count("\n") + 1
            d["sorry"] += s_
            d["admit"] += a_
            d["axiom"] += x_
            if x_:
                d["axiom_files"].append(rel)
            if s_ or a_ or x_:
                d["escape_files"].append(rel)

    print("=" * 72)
    print("门禁作用域实测")
    print("=" * 72)
    print("%-12s %7s %9s %7s %7s %7s" % ("zone", "files", "lines", "sorry", "admit", "axiom"))
    print("-" * 72)
    for z in ("kernel", "reference", "root"):
        d = zones[z]
        print("%-12s %7d %9d %7d %7d %7d"
              % (z, d["files"], d["lines"], d["sorry"], d["admit"], d["axiom"]))

    print()
    print("=" * 72)
    print("判定")
    print("=" * 72)
    k = zones["kernel"]
    if k["sorry"] == 0 and k["admit"] == 0 and k["axiom"] == 0:
        print("  kernel 区零逃逸：%d 文件、%d 行 -> I1/I2 可无条件强制"
              % (k["files"], k["lines"]))
    else:
        print("  ** kernel 区有逃逸，必须立即修复 **")
        for f in k["escape_files"]:
            print("     ", asc(f))

    # 写 intake 基线
    baseline = {
        "intake": {
            "sorry": zones["intake"]["sorry"],
            "admit": zones["intake"]["admit"],
            "axiom": zones["intake"]["axiom"],
            "axiom_files": zones["intake"]["axiom_files"],
            "escape_files": zones["intake"]["escape_files"],
        },
        "quarantine": {
            "files": zones["quarantine"]["files"],
            "declared": True,
        },
    }
    out = os.path.join(HERE, "intake-baseline.json")
    io.open(out, "w", encoding="utf-8", newline="\n").write(
        json.dumps(baseline, ensure_ascii=False, indent=1, sort_keys=True))
    print()
    print("  已写基线:", os.path.relpath(out, ZERO))
    print("     intake 逃逸文件数:", len(zones["intake"]["escape_files"]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
