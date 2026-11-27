#!/usr/bin/env python3
"""冻结基线：把迁入区已存在的 axiomatic 逃逸登记为白名单，只禁止新增。

## 为什么

`Zero/LvFormal/` 带进来 68 处 admit + 1 处 axiom。它们都在几何/密码学主题上，
**不在目标链（lvLang→IR→Cv00）上**——目标链 8 个文件经实测是 0/0/0。

直接让 I1/I2 报错没有意义：这些是历史资产，不是我们写的。
直接豁免也不对：那就永远不知道有没有新增。

⇒ 冻结基线：登记现有逃逸的**精确位置**，门禁断言「当前集合 ⊆ 基线集合」。
新增一处就红，删除一处则提示可更新基线。

## 文件

`gov/escape-baseline.json`：
    { "files": { "Lattice/LvFormal/Theory/X.lean": {"admit": 8, "axiom": 0}, ... } }

## 用法

    python gov/escape_baseline.py --init     # 从当前树生成基线（首次或有意更新时）
    python gov/escape_baseline.py --check    # 断言当前 ⊆ 基线（门禁用）
"""
import io
import json
import os
import re
import sys

# 控制台可能是 GBK：任何非 ASCII 输出都不应让脚本崩溃。
try:
    sys.stdout.reconfigure(errors="replace")
except (AttributeError, ValueError):
    pass

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
BASE = os.path.join(HERE, "escape-baseline.json")
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

# 只有迁入区才允许有冻结逃逸；内核区必须恒为 0
FROZEN_ZONES = ("Lattice/Reference/",)

SORRY = re.compile(r"\bsorry\b")
ADMIT = re.compile(r"\badmit\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_']+)", re.M)


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def scan():
    found = {}
    for base, dirs, fs in os.walk(os.path.join(ZERO, "Lattice")):
        # **W0-3b (round 1173): this exclusion was the defect.** Round 265 skipped `Reference`
        # because the archive carried 111 `admit`s and counting them "would report the archival as a
        # regression". Measured now: the whole tree INCLUDING Reference has ZERO escape files, so
        # there is nothing left to exclude -- and excluding it meant the check compared an empty set
        # against a baseline of nine files, i.e. it could only ever return 0. It now walks the zone
        # it is named after.
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            src = strip_comments(raw)
            s, a, x = (len(SORRY.findall(src)), len(ADMIT.findall(src)),
                       len(AXIOM.findall(src)))
            if s or a or x:
                found[rel] = {"sorry": s, "admit": a, "axiom": x}
    return found


def main():
    if "--init" in sys.argv:
        cur = scan()
        frozen = {k: v for k, v in cur.items() if k.startswith(FROZEN_ZONES)}
        outside = {k: v for k, v in cur.items() if not k.startswith(FROZEN_ZONES)}
        io.open(BASE, "w", encoding="utf-8", newline="\n").write(
            json.dumps({"files": frozen}, ensure_ascii=False, indent=1, sort_keys=True))
        print("基线已写入:", os.path.relpath(BASE, ZERO))
        print("  冻结文件数:", len(frozen))
        tot = sum(v["sorry"] + v["admit"] + v["axiom"] for v in frozen.values())
        print("  冻结逃逸总数:", tot)
        if outside:
            print("  ** 警告：内核区/其他区也有逃逸，必须立即修复 **")
            for k, v in outside.items():
                print("     ", asc(k), v)
            return 1
        return 0

    # --check
    if not os.path.exists(BASE):
        print("基线不存在，先跑 --init")
        return 1
    base = json.load(io.open(BASE, encoding="utf-8"))["files"]
    cur = scan()

    new = {k: v for k, v in cur.items() if k not in base}
    grown = {k: v for k, v in cur.items()
             if k in base and any(v[t] > base[k][t] for t in ("sorry", "admit", "axiom"))}
    shrunk = {k for k in base if k not in cur}

    if new:
        print("** 新增逃逸文件（必须修复）**")
        for k, v in new.items():
            print("   ", asc(k), v)
    if grown:
        print("** 逃逸数量增长（必须修复）**")
        for k, v in grown.items():
            print("   ", asc(k), "now", v, "was", base[k])
    if shrunk:
        print("提示：以下文件不再有逃逸，可更新基线：")
        for k in sorted(shrunk):
            print("   ", asc(k))

    if new or grown:
        return 1
    print("escape set is a subset of the frozen baseline: no new escapes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
