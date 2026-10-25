# -*- coding: utf-8 -*-
"""精读与目标缺口直接相关的四个文件的定理陈述。

目标缺口：
  G5 符号引擎        -> Engine.lean / Semantic.lean
  G3 闭环（提取再注入）-> Pipeline.lean / Compile.lean / Extract.lean
  G2 编译成权重      -> Compile.lean / Pipeline.lean

打印这些文件里每条定理的**完整陈述**（不只是名字），用于判断它们是否真的
对应目标语义，而不是名字看起来像。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
sys.path.insert(0, os.path.join(HERE, "tools"))
from sorry_axiom_census import strip_comments  # noqa: E402

FILES = ["Engine.lean", "Semantic.lean", "Pipeline.lean", "Compile.lean", "Extract.lean"]


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def statements(text):
    """抓出每条 theorem/def 的签名（到 := 或 where 为止）。"""
    out = []
    for m in re.finditer(r"^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z0-9_']+)",
                         text, re.M):
        start = m.start()
        # 从声明行到 `:=` 或顶格 `where`
        rest = text[start:]
        endm = re.search(r":=|^\s*where\b", rest, re.M)
        sig = rest[:endm.start()] if endm else rest[:300]
        sig = " ".join(sig.split())
        out.append((m.group(1), m.group(2), sig))
    return out


def main():
    geo = os.path.join(ZERO, "Lattice", "Geo")
    for fname in FILES:
        p = os.path.join(geo, fname)
        if not os.path.exists(p):
            print("\n### %s : 不存在" % fname)
            continue
        s = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
        print("\n" + "=" * 80)
        print("### %s" % fname)
        print("=" * 80)
        for kind, name, sig in statements(s):
            print("\n  [%s] %s" % (kind, asc(name)))
            print("     %s" % asc(sig)[:290])
    return 0


if __name__ == "__main__":
    sys.exit(main())
