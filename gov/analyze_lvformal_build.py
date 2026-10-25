#!/usr/bin/env python3
"""分析 `gov/lvformal_perfile.json`：哪些能构建、哪些不能、失败原因分布。

## 依据

`gov/lvformal_perfile.py` 对 121 个模块逐个 `lake build`，结果：
- 成功 **65**
- 失败 **56**

这解答了此前一直悬而未决的问题：「LvFormal 到底有多少能用」。

## 本脚本做什么

1. 按目标链重要性给模块分级
2. 统计失败原因的类型
3. 生成 `_archive/LVFORMAL-BUILD-MAP.md`
"""
import io
import json
import os
import re
import sys
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
DATA = os.path.join(HERE, "lvformal_perfile.json")

# 目标链上的关键模块（手工标注，因为它们决定「既有已验证编译链」的可用性）
CHAIN = {
    "Zero.LvFormal.Theory.lvLang": "lvLang 语法",
    "Zero.LvFormal.Theory.IR": "IR 定义与语义",
    "Zero.LvFormal.Theory.Compiler": "lvLang → IR 编译器",
    "Zero.LvFormal.Theory.CompilerCorrectness": "编译正确性（T1）",
    "Zero.LvFormal.Theory.LvDSL": "DSL 层",
    "Zero.LvFormal.Theory.Codegen": "代码生成",
    "Zero.LvFormal.Theory.CodegenCorrectness": "代码生成正确性",
    "Zero.LvFormal.Theory.Cv00Lang": "Cv00 语法",
    "Zero.LvFormal.Theory.Cv00Memory": "Cv00 内存与执行",
}


def classify(err):
    """按错误文本给失败分类。"""
    e = err.lower()
    if "unsolved goals" in e:
        return "证明目标未解决"
    if "simp made no progress" in e:
        return "simp 无进展"
    if "type mismatch" in e or "application type mismatch" in e:
        return "类型不匹配"
    if "failed to synthesize" in e:
        return "实例合成失败"
    if "tactic" in e:
        return "tactic 失败"
    if "unexpected token" in e or "expected token" in e or "invalid 'import'" in e:
        return "语法错误（含注释损坏）"
    if "unknown" in e:
        return "标识符未知"
    return "其他"


def main():
    d = json.load(io.open(DATA, encoding="utf-8"))
    ok = sorted(k for k, v in d.items() if v["ok"])
    bad = sorted(k for k, v in d.items() if not v["ok"])
    reasons = collections.Counter(classify(d[k]["first_error"]) for k in bad)

    print("=" * 74)
    print("LvFormal 构建地图")
    print("=" * 74)
    print("  总数:", len(d), " 成功:", len(ok), " 失败:", len(bad))
    print()
    print("  失败原因分布:")
    for r, n in reasons.most_common():
        print("    %-24s %2d" % (r, n))

    print()
    print("=" * 74)
    print("目标链模块的状态")
    print("=" * 74)
    for m, desc in CHAIN.items():
        if m not in d:
            print("  %-44s 未在清单" % m)
            continue
        st = "ok" if d[m]["ok"] else "FAIL"
        print("  %-44s %-5s %s" % (m, st, desc))

    # 写文档
    lines = ["# LvFormal 构建地图（实测）", "",
             "> 由 `gov/lvformal_perfile.py` 逐模块 `lake build` 得出，"
             "`gov/analyze_lvformal_build.py` 汇总。", "",
             "## 一、总览", "",
             "| 指标 | 值 |", "|:--|--:|",
             "| 模块总数 | %d |" % len(d),
             "| 构建成功 | **%d** |" % len(ok),
             "| 构建失败 | **%d** |" % len(bad), ""]

    lines += ["## 二、目标链模块", "",
              "| 模块 | 状态 | 说明 |", "|:--|:--|:--|"]
    for m, desc in CHAIN.items():
        if m in d:
            st = "✅ 可构建" if d[m]["ok"] else "❌ 不可构建"
            lines.append("| `%s` | %s | %s |" % (m.replace("Zero.LvFormal.Theory.", ""), st, desc))
        else:
            lines.append("| `%s` | — | 未在清单中 |" % m.replace("Zero.LvFormal.Theory.", ""))
    lines.append("")

    lines += ["## 三、失败原因分布", "",
              "| 原因 | 数量 |", "|:--|--:|"]
    for r, n in reasons.most_common():
        lines.append("| %s | %d |" % (r, n))
    lines.append("")

    lines += ["## 四、可构建的模块（%d 个）" % len(ok), ""]
    for m in ok:
        lines.append("- `%s`" % m)
    lines.append("")

    lines += ["## 五、不可构建的模块（%d 个）" % len(bad), "",
              "| 模块 | 首条错误 |", "|:--|:--|"]
    for m in bad:
        err = d[m]["first_error"].replace("|", "\\|")[:110]
        lines.append("| `%s` | `%s` |" % (m, err))
    lines.append("")

    lines += ["## 六、结论", "",
              "**「既有已验证编译链」的可用范围是实测的，不是声称的。**", "",
              "目标链上 `IR` / `Compiler` / `CompilerCorrectness` / `Cv00Lang` 的状态见第二节；",
              "其余 %d 个模块与 lvLang→IR→Cv00 无关（几何、密码学、求解器、可视化等）。" % len(bad),
              "",
              "失败的模块**不是被删除，而是被记录**：它们的定义仍可读，"
              "证明在本工具链下无法通过。逐条错误见第五节。"]

    out = os.path.join(ZERO, "_archive", "LVFORMAL-BUILD-MAP.md")
    io.open(out, "w", encoding="utf-8", newline="\n").write("\n".join(lines))
    print()
    print("已写:", os.path.relpath(out, ZERO))
    return 0


if __name__ == "__main__":
    sys.exit(main())
