# -*- coding: utf-8 -*-
"""修正 lvFormal 迁移：同时改写 import / namespace / open / 限定引用。

## 根因

第一版只改了 `import lvFormal.` -> `import Zero.LvFormal.`，
但 `namespace lvFormal.Theory.Cv00Memory` 和 `open Cv00Lang` 没动。

`open Cv00Lang` 相对于当前命名空间解析。命名空间仍是 lvFormal.Theory.Cv00Memory，
而被 import 的模块已改名 Zero.LvFormal.Theory.Cv00Lang，所以 open 找不到目标，
随后 dist/dot/cross 等名字未定义 -> `simp made no progress`。

## 改写规则

对 Zero/LvFormal/ 下每个 .lean：

1. `import lvFormal.X`        -> `import Zero.LvFormal.X`
2. `namespace lvFormal.X`     -> `namespace Zero.LvFormal.X`
3. `end lvFormal.X`           -> `end Zero.LvFormal.X`
4. `open lvFormal.X`          -> `open Zero.LvFormal.X`
5. `open X`（X 是 lvFormal 模块的短名）-> `open Zero.LvFormal.<路径>.X`

规则 5 需要知道短名 -> 模块路径的映射，从文件系统建立。

## 为什么 open 要改而不是靠相对解析

Lean 的 `open` 会在当前命名空间前缀下查找，而当前命名空间是 `Zero.LvFormal.Theory.Cv00Memory`，
待找模块是 `Zero.LvFormal.Theory.Cv00Lang`。两者公共前缀是 `Zero.LvFormal.Theory`，
所以理论上 `open Cv00Lang` 有希望能解析。但实测失败——因为实际命名空间写在文件里仍是
`lvFormal.Theory.Cv00Memory`（第 2 条修好后才会变成 `Zero.LvFormal.Theory.Cv00Memory`）。

两条必须同时改才有意义。本脚本一次改全。
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
ROOT = os.path.join(ZERO, "Lattice", "LvFormal")


def asc(s):
    return "".join(c if c.isascii() else "?" for c in s)


def build_module_map():
    """短名 -> 完整模块名。eg. 'Cv00Lang' -> 'Zero.LvFormal.Theory.Cv00Lang'"""
    m = {}
    for base, dirs, fs in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            rel = os.path.relpath(p, ZERO).replace("\\", "/")[:-5]
            mod = rel.replace("/", ".")
            m[f[:-5]] = mod
    return m


IMPORT_RE = re.compile(r"^(import\s+)(lvFormal\.)", re.M)
NS_RE = re.compile(r"^(namespace\s+)(lvFormal\.)", re.M)
END_RE = re.compile(r"^(end\s+)(lvFormal\.)", re.M)
OPEN_QUALIFIED_RE = re.compile(r"^(\s*open\s+(?:scoped\s+)?)(lvFormal\.)", re.M)
OPEN_BARE_RE = re.compile(r"^(\s*open\s+(?:scoped\s+)?)([A-Za-z0-9_']+)\s*$", re.M)

# 这些是 Mathlib/Std 的命名空间，绝不能当成本地模块改名
FOREIGN = {
    "BigOperators", "Classical", "Finset", "Function", "List", "Matrix", "Nat", "Real",
    "Set", "Polynomial", "Topology", "MeasureTheory", "Filter", "Complex", "Int", "Rat",
    "ContinuousLinearMap", "InnerProductSpace", "Metric", "Fintype", "Module", "Algebra",
}


def transform(src, modmap):
    n = {"import": 0, "ns": 0, "end": 0, "open_q": 0, "open_bare": 0}

    def count_and_sub(pat, repl, key, s):
        n_hits = len(pat.findall(s))
        if n_hits:
            n[key] += n_hits
            s = pat.sub(repl, s)
        return s

    src = count_and_sub(IMPORT_RE, r"\1Zero.LvFormal.", "import", src)
    src = count_and_sub(NS_RE, r"\1Zero.LvFormal.", "ns", src)
    src = count_and_sub(END_RE, r"\1Zero.LvFormal.", "end", src)
    src = count_and_sub(OPEN_QUALIFIED_RE, r"\1Zero.LvFormal.", "open_q", src)

    def open_bare(m):
        prefix, name = m.group(1), m.group(2)
        if name in FOREIGN or name not in modmap:
            return m.group(0)
        n["open_bare"] += 1
        return "%s%s" % (prefix, modmap[name])

    src = OPEN_BARE_RE.sub(open_bare, src)
    return src, n


def main():
    apply = "--apply" in sys.argv
    if not os.path.isdir(ROOT):
        print("目录不存在:", ROOT)
        return 1

    modmap = build_module_map()
    print("本地模块映射数:", len(modmap))

    totals = {"import": 0, "ns": 0, "end": 0, "open_q": 0, "open_bare": 0}
    changed = 0
    for base, dirs, fs in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(base, f)
            s = io.open(p, encoding="utf-8").read()
            new, n = transform(s, modmap)
            if new != s:
                changed += 1
                for k in totals:
                    totals[k] += n[k]
                if apply:
                    io.open(p, "w", encoding="utf-8", newline="\n").write(new)

    print("%s文件:" % ("已改写" if apply else "将改写"), changed)
    for k in ("import", "ns", "end", "open_q", "open_bare"):
        print("  %-10s %d" % (k, totals[k]))
    if not apply:
        print("\n干跑。用 --apply 执行。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
