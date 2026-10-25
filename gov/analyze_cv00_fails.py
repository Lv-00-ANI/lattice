# -*- coding: utf-8 -*-
"""只读分析 1：Cv00Memory 失败行用了哪些 simp 引理 / 依赖什么。

## 目的

不实际编译，而是判断失败是「mathlib 版本漂移」还是「源文件逻辑问题」。

## 做法

打印每个失败行及其后 1-2 行（证明体），列出：
- 该行用了什么 tactic（simp / unfold / rfl）
- 涉及的引理名
- 该引理是否可能不在 v4.14.0 中
"""
import os
import io
import os
import re

P = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "reference", "LvFormal", "Theory", "Cv00Memory.lean")
FAIL_LINES = [109, 131, 133, 139, 141, 169]


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


s = io.open(P, encoding="utf-8", errors="replace").read()
lines = s.splitlines()

print("=" * 78)
print("Cv00Memory.lean 失败行分析（共 %d 行）" % len(lines))
print("=" * 78)

for ln in FAIL_LINES:
    print("\n" + "-" * 78)
    print("失败行 %d" % ln)
    print("-" * 78)
    # 往上找到定理名
    thm = None
    for k in range(ln - 1, max(-1, ln - 25), -1):
        m = re.match(r"^(theorem|lemma)\s+([A-Za-z0-9_']+)", lines[k])
        if m:
            thm = (k + 1, m.group(1), m.group(2))
            break
    if thm:
        print("  定理: %s %s (行 %d)" % (thm[1], thm[2], thm[0]))
        # 打印定理完整签名与证明体
        for j in range(thm[0] - 1, min(ln + 2, len(lines))):
            mark = "  >>" if (j + 1) in FAIL_LINES else "    "
            print("%s%4d %s" % (mark, j + 1, asc(lines[j])[:100]))
    else:
        print("  (未找到定理名)")
        for j in range(max(0, ln - 4), min(ln + 2, len(lines))):
            print("    %4d %s" % (j + 1, asc(lines[j])[:100]))

    # 提取引理名
    window = "\n".join(lines[max(0, ln - 6):min(len(lines), ln + 2)])
    lemmas = re.findall(r"\b([a-z][A-Za-z0-9_']*_(?:le|eq|iff|pos|nonneg|zero|add|mul|one|sub|ssub)[A-Za-z0-9_']*)", window)
    tactics = set(re.findall(r"\b(simp|unfold|rfl|omega|linarith|nlinarith|ring|norm_num|positivity|decide|exact|apply|rw)\b", window))
    if lemmas:
        print("  涉及引理: %s" % ", ".join(sorted(set(lemmas))[:8]))
    if tactics:
        print("  tactics: %s" % ", ".join(sorted(tactics)))

print()
print("=" * 78)
print("头部 import 与 open")
print("=" * 78)
for i, l in enumerate(lines[:30]):
    t = l.strip()
    if re.match(r"^(import|open|namespace)\b", t):
        print("  %4d %s" % (i + 1, asc(t)[:95]))
