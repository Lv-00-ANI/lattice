# -*- coding: utf-8 -*-
"""任务 C：扫描 Legacy 的通配分支空壳（只读）。

背景：目标链上的 `exec_stmt` 用 `| _ => .normal m env` 静默丢弃 7 个构造子。
本脚本检查这种模式在 Legacy 的 437 个文件里有多普遍。

检测的形态（全部要求「通配模式 + 无信息返回」）：
  1. `| _ => <常量/恒等>`  —— 通配分支直接返回一个固定值或原值
  2. `| _ => .normal ...`  —— 状态机空转
  3. `| _ => (m, env)` 之类的原样返回

判定：
  * 先剥注释，避免把文档里的示例算进来
  * 要求 `| _ =>` 或 `| _ : _ =>` 出现在 match 分支位置
  * 统计同一文件里这种分支的数量

分级：
  A. 危险：通配分支返回一个 `.normal`/`pure`/`some` 之类的「没事发生」值
  B. 可疑：通配分支返回字面常量或变量本身
  C. 无害：通配分支返回 `False`/`0` 用于完备性填充（如 `else` 分支）
"""
import io
import json
import os
import re
import sys

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEG = os.path.join(ZERO, "Lattice", "Legacy")
PLAN = os.path.join(ZERO, "gov", "legacy_isolation_set.json")
OUT = os.path.join(ZERO, "gov", "legacy_shellscan.json")

sys.path.insert(0, os.path.join(ZERO, "gov", "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

# 通配分支
WILD = re.compile(r"^\s*\|\s*_\s*(?::[^=]*)?=>\s*(.+)$", re.M)

# A 类：返回「什么都没发生」的信号
NOOP = re.compile(r"^\.\s*(normal|ok|success|pure|skip|nil|none|id)\b|"
                  r"\bpure\b|\bskip\b|\bnoop\b", re.I)


def classify(rhs):
    r = rhs.strip()
    if NOOP.search(r):
        return "A_noop"
    # 返回单个标识符（原样返回）
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", r):
        return "B_identity"
    # 返回字面量
    if re.fullmatch(r"[0-9]+|true|false|\(\)", r, re.I):
        return "C_literal"
    return "D_other"


def main():
    plan = json.loads(io.open(PLAN, encoding="utf-8").read())
    keep = [k for k in plan["keep_final"] if re.match(r"^[A-Za-z][A-Za-z0-9_]*$", k)]

    results = []
    for k in keep:
        p = os.path.join(LEG, k + ".lean")
        raw = io.open(p, "rb").read().decode("utf-8", "replace")
        s = strip_comments(raw)
        hits = []
        for m in WILD.finditer(s):
            rhs = m.group(1).strip()
            line = s[:m.start()].count("\n") + 1
            hits.append({"line": line, "kind": classify(rhs), "rhs": rhs[:90]})
        if hits:
            results.append({"file": k, "hits": hits})

    from collections import Counter
    kinds = Counter()
    for r in results:
        for h in r["hits"]:
            kinds[h["kind"]] += 1

    print("=" * 70)
    print("Legacy 通配分支扫描（%d 个保留目标）" % len(keep))
    print("=" * 70)
    print("含通配分支的文件数 :", len(results))
    print("通配分支总数       :", sum(kinds.values()))
    print()
    print("按类型：")
    label = {
        "A_noop": "A 危险：返回 no-op / .normal / pure",
        "B_identity": "B 可疑：原样返回一个标识符",
        "C_literal": "C 无害：返回字面量（多为填充）",
        "D_other": "D 其他：有实际表达式",
    }
    for kk in ("A_noop", "B_identity", "C_literal", "D_other"):
        print("   %-44s %4d" % (label[kk], kinds[kk]))

    print()
    print("--- A 类（危险）明细，按文件聚合 ---")
    a_files = []
    for r in results:
        a = [h for h in r["hits"] if h["kind"] == "A_noop"]
        if a:
            a_files.append((r["file"], a))
    a_files.sort(key=lambda t: -len(t[1]))
    for f, a in a_files[:20]:
        print("   %-44s %d 处" % (f, len(a)))
        for h in a[:2]:
            print("        L%-5d %s" % (h["line"], h["rhs"]))
    print("   A 类文件总数:", len(a_files))

    io.open(OUT, "w", encoding="utf-8", newline="\n").write(
        json.dumps(results, ensure_ascii=False, indent=1))
    print()
    print("明细写出:", OUT)


if __name__ == "__main__":
    main()
