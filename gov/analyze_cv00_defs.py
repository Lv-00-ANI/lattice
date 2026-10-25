# -*- coding: utf-8 -*-
"""只读分析：解析 Cv00Memory 失败的真实原因。

## 症状

```
theorem points_to_env_correct_x (pts : List lvPoint) (p : lvPoint) (h : p ∈ pts) :
    (points_to_env pts) (p.name ++ "_x") = some (.fval (0 : Float)) := by
  induction h with
  | head => unfold points_to_env; simp      -- 失败: simp made no progress
```

`simp` 无进展 + 目标说 `= some (.fval 0)`。

## 要查什么

1. `points_to_env` 的定义 —— 它是否真的把 x 坐标设为 0？
2. `lvPoint` 的结构 —— 有什么字段？
3. `.fval` 是哪个类型的构造子？
4. `Mem` 的类型（`points_to_env` 返回 `Option (State)` 还是有 `Mem`？）

如果 `points_to_env` 用的是**实际坐标值**而非 0，那么定理本身是**假**的，
`simp made no progress` 是因为目标陈述错误，不是 mathlib 漂移。
"""
import os
import io
import os
import re

P = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "reference", "LvFormal", "Theory", "Cv00Memory.lean")


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


s = io.open(P, encoding="utf-8", errors="replace").read()
lines = s.splitlines()

TARGETS = ["points_to_env", "lvPoint", "fval", "Env", "Mem", "State", "satisfiable"]

print("=" * 78)
print("定义定位")
print("=" * 78)

for name in TARGETS:
    found = False
    for i, l in enumerate(lines):
        if re.match(r"\s*(?:noncomputable\s+)?(?:def|abbrev|structure|inductive)\s+"
                    + re.escape(name) + r"\b", l):
            found = True
            print("\n--- %s (行 %d) ---" % (asc(name), i + 1))
            for j in range(i, min(i + 16, len(lines))):
                print("  %4d %s" % (j + 1, asc(lines[j])[:100]))
                if j > i and lines[j].strip() == "":
                    break
            break
    if not found:
        print("\n--- %s : 本文件未定义（来自 import） ---" % asc(name))

# 额外：找 points_to_env 的所有相关定理
print()
print("=" * 78)
print("所有涉及 points_to_env 的定理")
print("=" * 78)
for i, l in enumerate(lines):
    if "points_to_env" in l and re.match(r"\s*(theorem|lemma)\s", l):
        print("  %4d %s" % (i + 1, asc(l.strip())[:100]))
