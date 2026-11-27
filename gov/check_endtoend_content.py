"""gov/check_endtoend_content.py -- how much of the library is cross-layer BY CONTENT.

## Why this exists

`gate.py`'s I5 already does content analysis: it builds a transitive reference graph and resolves short
names to layers. **But it only runs that analysis on theorems whose NAME matches `e2e` / `end_to_end`.**

Measured at round 219: **36 of 8,501 theorems** match by name, **all in `Lib/`, none in `Geo`** -- so the
chain's actual cross-layer work (`NetLoss`, `PenaltyLoss`, `ConstraintDescent`) was entirely outside I5's
coverage, not because it is layer-local but because nobody named it `e2e`.

This script applies the SAME analysis to EVERY theorem and reports the distribution. It is a **census**, not
a gate: a theorem that only touches one layer is not a defect. What would be a defect is claiming otherwise,
and I5 already catches that.

## What it measures

For each theorem/lemma, the layers reached by the identifiers in its block, walked transitively through the
declaration reference graph. `0` means the statement mentions no library declaration at all (pure `Mathlib`);
that is legal but means the theorem says nothing about this library's objects.

## Boundaries

- **Layer is read off the defining module's top-level directory.** A declaration moved between layers
  changes the census; that is intended.
- **Transitivity means "depends on", not "states about".** A theorem can reach 3 layers through a helper
  while its own statement is about one. This is an UPPER bound on how cross-layer its content is.
- **Not a gate.** Do not wire it as one: `0`-layer theorems are legitimate.
"""
import io
import artifact_guard
SYNCED = []
sync = artifact_guard.sync
import os
import re
import sys
from collections import Counter, defaultdict

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")
OUT = os.path.join(HERE, "ENDTOEND-CENSUS.md")

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive)\s+([\w'.ᵢ-₉]+)")
THM = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([\w'.ᵢ-₉]+)")
TOKEN = re.compile(r"[A-Za-z_\u03b1-\u03c9][\w'ᵢ-₉]*")

LAYERS = ["Core", "Slots", "Lift", "Runtime", "Domains", "Compose", "Lib", "Geo", "Audit", "Semantics", "Usage"]
# Round 245. `Runtime` (66 modules), `Domains` (99) and `Compose` (8) were created by the P2/P3
# migration, and this list was never extended -- so this audit silently IGNORED 173 modules, more
# than a fifth of the tree. The census that I5 rests on (`check_endtoend_content.py`) was among the
# blind ones, which is the worst place for a blind spot: it measures coverage.



def strip_comments(src):
    out = []
    i, n = 0, len(src)
    while i < n:
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                break
            out.append(" " * (j - i))
            i = j
            continue
        if src.startswith("/-", i):
            j = src.find("-/", i + 2)
            if j < 0:
                out.append(" " * (n - i))
                break
            out.append("".join(c if c == "\n" else " " for c in src[i:j + 2]))
            i = j + 2
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def build_index():
    """decl name -> set of layers it is defined in; decl name -> body text."""
    layer = defaultdict(set)
    body = {}
    for dp, dirs, files in os.walk(LAT):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            top = rel.split("/")[0] if "/" in rel else "root"
            lay = top if top in LAYERS else "root"
            code = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            starts = [(m.start(), m.group(1)) for m in DECL.finditer(code)]
            for idx, (pos, name) in enumerate(starts):
                end = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
                layer[name].add(lay)
                body.setdefault(name, "")
                body[name] += " " + code[pos:end]
    return layer, body


def layers_of(tokens, layer, body, seen):
    out = set()
    stack = list(tokens)
    while stack:
        t = stack.pop()
        if t in seen:
            continue
        seen.add(t)
        out |= layer.get(t, set())
        if t in body:
            stack.extend(TOKEN.findall(body[t]))
    return out


def main():
    layer, body = build_index()
    dist = Counter()
    per_file = defaultdict(Counter)
    cross = []
    total = 0
    for dp, dirs, files in os.walk(LAT):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            code = strip_comments(io.open(p, "rb").read().decode("utf-8", "replace"))
            starts = [(m.start(), m.group(1)) for m in THM.finditer(code)]
            for idx, (pos, name) in enumerate(starts):
                end = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
                block = code[pos:end]
                # the statement is up to the first top-level `:=`
                depth, cut = 0, len(block)
                for i in range(len(block) - 1):
                    ch = block[i]
                    if ch in "([{":
                        depth += 1
                    elif ch in ")]}":
                        depth -= 1
                    elif depth == 0 and block.startswith(":=", i):
                        cut = i
                        break
                toks = set(TOKEN.findall(block[:cut]))
                lays = layers_of(toks, layer, body, set())
                # the theorem's own layer does not count towards "cross-layer"
                own = rel.split("/")[0] if "/" in rel else "root"
                lays.discard(own)
                k = len(lays)
                total += 1
                dist[k] += 1
                per_file[rel][k] += 1
                if k >= 2:
                    cross.append((k, rel, name, sorted(lays)))

    lines = []
    A = lines.append
    A("# 端到端普查（**按内容**，不是按名字）")
    A("")
    A("> 由 `gov/check_endtoend_content.py` 生成。**这是普查，不是门禁**：")
    A("> 只碰一层的定理**不是缺陷**；声称跨层而没跨才是，那由 `gate.py` 的 I5 抓。")
    A("")
    A("## 为什么需要它")
    A("")
    A("I5 **已经**做内容分析（传递解析短名到层），**但它只对名字匹配 `e2e` / `end_to_end` 的定理跑**。")
    A("第 219 轮实测：8,501 条里 **36 条**按名字命中，**全在 `Lib`，`Geo` 零条**——")
    A("所以链路真正的跨层工作**不在 I5 的覆盖内**，不是因为它是层内的，而是**因为没人给它起那个名字**。")
    A("")
    A("本脚本对**每条**定理跑同一套分析，给出分布。")
    A("")
    A("## 分布（去掉定理自己所在的那一层）")
    A("")
    A("| 触及的其他层数 | 定理数 | 占比 |")
    A("|--:|--:|--:|")
    for k in sorted(dist):
        A("| %d | %d | %.1f%% |" % (k, dist[k], 100.0 * dist[k] / max(total, 1)))
    A("| **合计** | **%d** | |" % total)
    A("")
    A("## 跨 ≥ 2 层（按层数降序，最多 60 条）")
    A("")
    A("| 层数 | 定理 | 触及的层 |")
    A("|--:|:--|:--|")
    for k, rel, name, lays in sorted(cross, key=lambda x: (-x[0], x[1]))[:60]:
        A("| %d | `%s` (`%s`) | %s |" % (k, name, rel, ", ".join(lays)))
    A("")
    A("## ⚠ 层数高**不等于**更端到端")
    A("")
    A("按层数排在最前面的那批是**审计自指**（`census_length`、`repair_is_densest`、`total_obligations`……），")
    A("它们经由审计自己的依赖图传递触及四层。**审计已经把它们判为 `register` 债**，理由正是")
    A("「这是审计**自指**，不是审计结果」。")
    A("")
    A("**所以本表不能按层数排序当作「链路完整度」读。** 它度量的是「依赖图的深度」，")
    A("而审计机器本身会人为加深依赖图。**真正的链路内容要看具体定理在说什么，不是看它的 `k`。**")
    A("")
    A("## 这份普查自己的边界")
    A("")
    A("- **层取自定义模块的顶层目录**。声明在层间移动会改变普查——那是有意的。")
    A("- **传递性意味着「依赖」而不是「陈述关于」**。一条定理可以通过辅助引理触及三层，")
    A("  而它自己的陈述只关于一层。**这是跨层程度的上界。**")
    A("- **不要按它的计数设门禁**：0 层定理是合法的（纯 `Mathlib` 陈述）。")
    A("")
    A("⚠ **第 26 轮补充**：上面那条说的是**不要按绝对计数**设门禁。**下降**是另一件事——")
    A("`gov/check_endtoend_floor.py` 只对「某条定理**不再**跨 >= 2 层」失败，")
    A("而对「新增跨层定理」放行。**增长是改进，下降是回归**，两者不该用同一把尺子。")
    A("")
    # **W0-3c: compare, do not overwrite.**
    SYNCED.append(("gov/ENDTOEND-CENSUS.md", sync(OUT, "\n".join(lines), allow_write="--write" in sys.argv)))

    # Round 26, L4-7. A FLOOR gate needs the NAME SET, and it must not re-implement this scan -- two
    # implementations would be two authorities. So the census emits the list and the gate reads it.
    tsv = os.path.join(HERE, "endtoend-cross.tsv")
    io.open(tsv, "w", encoding="utf-8", newline="\n").write(
        "# theorems touching >= 2 layers BY CONTENT -- written by check_endtoend_content.py\n"
        + "".join("%s\t%s\n" % (rel, name) for _k, rel, name, _lays in cross))

    print("END-TO-END CENSUS (by content)")
    for k in sorted(dist):
        print("  layers=%d : %d" % (k, dist[k]))
    print("  total    : %d" % total)
    print("  cross (>=2): %d" % len(cross))
    print("  written to gov/ENDTOEND-CENSUS.md")
    return artifact_guard.require_synced(SYNCED, "ENDTOEND-CENSUS") or 0


if __name__ == "__main__":
    sys.exit(main())
