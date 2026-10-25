#!/usr/bin/env python3
"""逐个构建 `Zero/LvFormal/` 的每个模块，记录真实成败。

## 为什么需要

先前只知道 6 个文件的成败（手工测的）。整包构建报出更多失败。
要把「哪些能编、哪些不能」变成可复算的事实，必须逐个测。

## 方法

对每个 `Zero/LvFormal/**.lean`，单独 `lake build <module>`，记录：
- 成功 / 失败
- 失败的首条错误信息（截断到 160 字符）

结果写 `gov/lvformal_perfile.json`。

## 注意

- 逐个构建很慢（118 个模块），用后台作业
- 必须串行，避免 `bad_alloc`（子代理实测过并发会导致内存溢出）
"""
import io
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
OUT = os.path.join(HERE, "lvformal_perfile.json")


def modules():
    base = os.path.join(ZERO, "Lattice", "LvFormal")
    out = []
    for b, dirs, fs in os.walk(base):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(b, f), os.path.join(ZERO, "Lattice"))
            mod = "Zero." + rel[:-5].replace(os.sep, ".").replace("\\", ".")
            if mod != "Zero.LvFormal":
                out.append(mod)
    return sorted(out)


def main():
    mods = modules()
    print("待测模块:", len(mods))
    result = {}
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)

    for i, m in enumerate(mods, 1):
        r = subprocess.run(["lake", "build", m], cwd=ZERO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace", env=env)
        ok = r.returncode == 0
        err = ""
        if not ok:
            for line in (r.stdout or "").splitlines():
                if "error" in line:
                    err = line.strip()[:160]
                    break
        result[m] = {"ok": ok, "first_error": err}
        print("  [%d/%d] %-52s %s" % (i, len(mods), m, "ok" if ok else "FAIL"))

    io.open(OUT, "w", encoding="utf-8", newline="\n").write(
        json.dumps(result, ensure_ascii=False, indent=1, sort_keys=True))

    ok_n = sum(1 for v in result.values() if v["ok"])
    print()
    print("=" * 60)
    print("成功:", ok_n, "/", len(mods))
    print("失败:", len(mods) - ok_n)
    print("已写:", os.path.relpath(OUT, ZERO))
    return 0


if __name__ == "__main__":
    sys.exit(main())
