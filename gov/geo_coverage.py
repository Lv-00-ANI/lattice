# -*- coding: utf-8 -*-
"""把 `GeoConstraint` 的 Layer 分类写进文档，并统计覆盖率。

## 意义

子代理指出：Lv-00 的 IR 有 15 个约束，`GeoConstraint` 只有 7 个。
本轮补到 12 个，并引入 `Layer` 枚举让「能否到达权重」成为**可计算的事实**。

本文档记录覆盖率与每一个未覆盖项的原因。
"""
import io
import os
import re

ZERO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# 从 Constraint.lean 读实际构造子与 layer
src = io.open(os.path.join(ZERO, "Lattice", "Geo", "Constraint.lean"), encoding="utf-8").read()
m = re.search(r"inductive GeoConstraint.*?(?=namespace GeoConstraint)", src, re.S)
ctors = re.findall(r"^\s+\| (\w+)", m.group(0), re.M)

lm = re.search(r"def layer : GeoConstraint n → Layer(.*?)\n\n", src, re.S)
layer_map = dict(re.findall(r"\| \.(\w+)[^=]*=> \.(\w+)", lm.group(1) if lm else ""))

# Lv-00 的 15 个
LV00 = ["distance", "collinear", "perpendicular", "parallel", "angle", "eq_expr", "lt_expr",
        "gt_expr", "radius", "tangent", "midpoint", "rightAngle", "equalLength", "equalAngle",
        "ratioDivision"]

# Geo 构造子到 Lv-00 的映射
COVER = {
    "sqDistEq": ["distance", "radius"],
    "equalLength": ["equalLength"],
    "collinear": ["collinear"],
    "perpendicular": ["perpendicular", "rightAngle"],
    "parallel": ["parallel"],
    "rightAngle": ["rightAngle"],
    "midpoint": ["midpoint"],
    "samePoint": [],
    "eqZero": ["eq_expr"],
    "leZero": ["lt_expr"],
    "ltZero": ["lt_expr"],
    "gtZero": ["gt_expr"],
}

covered = set()
for c in ctors:
    covered |= set(COVER.get(c, []))
missing = [x for x in LV00 if x not in covered]

lines = ["# `GeoConstraint` 对 `Lv-00` IR 的覆盖", "",
         "> 由 `gov/geo_coverage.py` 生成。", "",
         "## 一、构造子", "",
         "| `GeoConstraint` 构造子 | 对应 `Lv-00` 谓词 | 代数层 |",
         "|:--|:--|:--|"]
for c in ctors:
    lines.append("| `%s` | %s | `%s` |"
                 % (c, ", ".join("`%s`" % x for x in COVER.get(c, [])) or "—（新增）",
                    layer_map.get(c, "?")))
lines.append("")

lines += ["## 二、覆盖率", "",
          "| 指标 | 值 |", "|:--|--:|",
          "| `Lv-00` IR 谓词数 | %d |" % len(LV00),
          "| 已覆盖 | **%d** |" % len(covered),
          "| 未覆盖 | **%d** |" % len(missing),
          "| `GeoConstraint` 构造子数 | %d |" % len(ctors), ""]

lines += ["## 三、未覆盖项及原因", "",
          "| 谓词 | 原因 |", "|:--|:--|"]
REASON = {
    "angle": "含 `Real.cos`（角度由点积与模长之比定义），不是任何多项式的零点集，"
             "`Layer.transc` 记录了这一点",
    "equalAngle": "同上，两个角的余弦之比相等",
    "tangent": "需要 Skolem 化存在量词（切点参数 `t`）后才能成为多项式；"
               "当前 `midpoint` 等已完成，`tangent` 留待后续",
    "ratioDivision": "同 `tangent`，含 `∃ t, ...`",
    "radius": "已由 `sqDistEq` 泛化覆盖（半径即到圆心的距离）",
    "distance": "已由 `sqDistEq` 覆盖（平方后）",
}
for x in missing:
    lines.append("| `%s` | %s |" % (x, REASON.get(x, "待定")))
lines.append("")

lines += ["## 四、代数层的意义", "",
          "`Layer` 让「这个约束能否到达权重」成为**可计算**的问题，而不是注释里的说明：",
          "",
          "| 层 | 含义 | 能否构造 `f²` 惩罚 |",
          "|:--|:--|:--|",
          "| `poly` | 已是多项式 | ✅ 直接 |",
          "| `square` | 平方后可化 | ✅ 直接 |",
          "| `existential` | 需消去存在量词 | ⚠️ 消元后 |",
          "| `transc` | 含超越函数 | ❌ 不可能 |", "",
          "这正是目标「可逆性必须分层陈述」的要求在**可代数化性**上的对应："
          "不仅可逆性要分层，可编译性也要分层。"]

out = os.path.join(ZERO, "_archive", "GEO-COVERAGE.md")
io.open(out, "w", encoding="utf-8", newline="\n").write("\n".join(lines))
print("GeoConstraint 构造子:", len(ctors))
print("覆盖 Lv-00 谓词:", len(covered), "/", len(LV00))
print("未覆盖:", missing)
print("已写:", os.path.relpath(out, ZERO))
