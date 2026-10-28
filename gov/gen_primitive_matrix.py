"""Generate `PRIMITIVE-MATRIX.md`: what is actually registered, and what needs an adapter.

## What this is, and what it is NOT

It is a **text-level** matrix. Python cannot see Lean types, so it reads each `Primitive`'s
`Input := ...` / `Output := ...` **source text** and compares it. Two consequences, both stated in the
generated document:

1. **"same text" is a sufficient, not necessary, condition for "no adapter needed".** `ℝ` written once
   and `ℝ` written again are the same text and the same type; but a type synonym, a reducible `abbrev`
   or an unfolded definition would be the *same type* with *different text*, and the matrix would ask
   for an adapter that §6 does not actually require.
2. **It says nothing about whether a composition is *proved*.** It says what the types allow.

That is still worth generating, because the thing it measures is exactly the thing §6 got wrong: the
design's `compose` signature assumes `f.Output = g.Input` while nothing enforces it.

## Why report-only

It cannot fail. It is a census, like `check_endtoend_content.py`. Registered as `reported`, not `ok`, so
a reader cannot mistake it for a gate that passed.
"""

import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, ".."))
OUT = os.path.join(ROOT, "PRIMITIVE-MATRIX.md")
COMPOSE = os.path.join(ROOT, "Lattice", "Compose")

# `def ... : Primitive A B where` -- round 232: A/B are PARAMETERS, read from the signature.
# The first version looked for `Input := ...` fields, which no longer exist; it silently produced an
# empty matrix -- the same silent-empty failure mode as the earlier `:=` vs `where` bug, which is why
# the generated file now prints the count instead of just saying "ok".
DEF = re.compile(
    r"(?m)^(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z_][\w'.]*)[^\n]*:\s*Primitive\b(.*?)"
    r"(?:where|:=)(.*?)(?=\n(?:noncomputable\s+)?(?:def|theorem|abbrev|structure|inductive|end)\b|\Z)",
    re.S)
FIELD = re.compile(r"(?m)^\s{2,}(strength|coverage)\s*:=\s*(.+?)\s*$")


def split_params(s):
    """Split `A B` or `(I1 x I2) (O1 x O2)` into two type texts, respecting parentheses."""
    s = s.strip()
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
            cur += ch
        elif ch == ")":
            depth -= 1
            cur += ch
        elif ch == " " and depth == 0:
            if cur.strip():
                out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


POLY = re.compile(r"^[\u03b1-\u03c9][\w']*$")


def is_poly(s):
    """True if the source text is a single bare type variable (Greek letter), e.g. `α`.

    A polymorphic `Primitive` can be INSTANTIATED by the caller, so a mismatched pair is not
    necessarily an adapter burden. This is the concrete case of caveat 1 in the header.
    """
    return bool(POLY.match(s.strip()))


def primitives():
    found = []
    for fn in sorted(os.listdir(COMPOSE)):
        if not fn.endswith(".lean"):
            continue
        src = io.open(os.path.join(COMPOSE, fn), encoding="utf-8").read()
        for m in DEF.finditer(src):
            name, params, body = m.group(1), m.group(2), m.group(3)
            # Round 232 second bug. `[^\n]*:\s*Primitive` is GREEDY, so for
            #   `def MatrixRow.ofPrim ... (p : Primitive I O) : MatrixRow where`
            # it matched the PARAMETER's `: Primitive` and then swallowed ` O) : MatrixRow` as the
            # "output". Fix: the RETURN type is the LAST `: Primitive` in the header, and a header
            # whose return type is not `Primitive` must be rejected outright.
            # Normalize whitespace FIRST: signatures span multiple lines
            # (def parallel ... : <newline> Primitive (I1 x I2) (O1 x O2) where), and a raw
            # rsplit on the un-normalized text matches the PARAMETER's : Primitive instead.
            head = " ".join(m.group(0).split())
            head = head.split(" where ")[0].split(" := ")[0]
            tail = head.rsplit(": Primitive", 1)
            if len(tail) != 2:
                continue
            params = tail[1]
            if "." in name:
                continue
            types = split_params(params)
            if len(types) != 2:
                continue
            fields = {}
            for fm in FIELD.finditer(body):
                fields[fm.group(1)] = fm.group(2).strip()
            if True:
                found.append({
                    "name": name,
                    "file": "Lattice/Compose/" + fn,
                    "line": src[:m.start()].count("\n") + 1,
                    "Input": types[0],
                    "Output": types[1],
                    "strength": fields.get("strength", "—"),
                    "coverage": fields.get("coverage", "—"),
                })
    return found


def main():
    ps = primitives()
    L = []
    A = L.append

    A("# PRIMITIVE-MATRIX：已登记的 `Primitive` 与适配器需求")
    A("")
    A("> **本文件由 `gov/gen_primitive_matrix.py` 生成，勿手改。**")
    A("> **它是「报数」，不是门禁**：`verify_all.py` 把它登记为 `reported`，不是 `ok`。")
    A("")
    A("## 这份矩阵是什么，**不是**什么")
    A("")
    A("它是**文本层**矩阵。Python 看不见 Lean 的类型，所以它读每个 `Primitive` 的")
    A("`Input := …` / `Output := …` **源码文本**再比较。两个后果，下面都写清：")
    A("")
    A("1. **「文本相同」是「不需要适配器」的充分条件，不是必要条件。**")
    A("   `ℝ` 写两次是同一类型；但类型同义词、可归约的 `abbrev`、需要展开的定义会")
    A("   是**同一类型而文本不同**，矩阵会要求一个 §6 实际上并不需要的适配器。")
    A("2. **它完全不说明组合是否被证明过。** 它只说明类型允许什么。")
    A("")
    A("**仍然值得生成**，因为它量的正是 §6 出错的那件事：")
    A("`compose` 的签名假定 `f.Output = g.Input`，而结构里没有任何东西强制它。")
    A("")
    A("## 一、已登记的 `Primitive`")
    A("")
    if not ps:
        A("**没有找到任何 `Primitive` 实例。** 这不是错误——`Compose/` 目前只有契约、")
        A("`compose`/`parallel`/`identity`/`descentStep` 与 `Registry`。**空矩阵是诚实的读数。**")
    else:
        A("| # | 名称 | 位置 | `Input` | `Output` | 强度 | 覆盖 |")
        A("|--:|:--|:--|:--|:--|:--|:--|")
        for i, p in enumerate(ps, 1):
            A("| %d | `%s` | `%s:%d` | `%s` | `%s` | `%s` | `%s` |"
              % (i, p["name"], p["file"], p["line"], p["Input"], p["Output"],
                 p["strength"], p["coverage"]))
        A("")
        A("## 二、适配器矩阵")
        A("")
        A("行 = 先跑的，列 = 后跑的。三态：")
        A("")
        A("- **`—`**：文本相同，适配器可取 `id`；")
        A("- **`POLY`**：至少一侧是**裸类型变量**（如 `α`），调用方可**实例化**它，所以原则上不需要适配器；")
        A("- **`ADAPT`**：文本不同且没有可实例化的变量，**必须**提供适配器。")
        A("")
        hdr = "| 先 \\\\ 后 | " + " | ".join("`%s`" % p["name"] for p in ps) + " |"
        A(hdr)
        A("|:--|" + "|".join([":--:"] * len(ps)) + "|")
        need = 0
        total = 0
        poly = 0
        for a in ps:
            row = ["`%s`" % a["name"]]
            for b in ps:
                total += 1
                if a["Output"] == b["Input"]:
                    row.append("—")
                elif is_poly(a["Output"]) or is_poly(b["Input"]):
                    # one side is a bare type variable: the caller can INSTANTIATE it, so no adapter
                    # is needed in principle. Reporting this as ADAPT would overstate the burden --
                    # `identity ℝ` composes with `descentStep` using `id`.
                    row.append("POLY")
                    poly += 1
                else:
                    row.append("ADAPT")
                    need += 1
            A("| " + " | ".join(row) + " |")
        A("")
        A("## 三、读数")
        A("")
        A("| 指标 | 值 |")
        A("|:--|--:|")
        A("| 已登记的 `Primitive` | %d |" % len(ps))
        A("| 有序对总数 | %d |" % total)
        A("| **`—` 文本相同** | **%d** |" % (total - need - poly))
        A("| **`POLY` 可实例化** | **%d** |" % poly)
        A("| **`ADAPT` 必须给适配器** | **%d** |" % need)
        A("")
        A("**这三行就是 §6 那个签名的错误规模**：`ADAPT` 的比例越高，")
        A("原签名（`compose (f g : Primitive) (h : ∀ x y, f.post x y → g.pre y)`）")
        A("假定的 `f.Output = g.Input` 就越不成立——**而结构里没有任何东西强制它**。")
        A("")
        A("**注意 `ADAPT` 里包含自组合**：`parallel` 的 `Input` 是 `f.Input × g.Input`、")
        A("`Output` 是 `f.Output × g.Output`，**文本永不相等**，所以 `parallel` 连与自身组合都要适配器。")
        A("这不是矩阵的缺陷，是 `parallel` 的定义决定的。")
        A("")
        A("⚠ **不要把 `—` 读成「已证明可组合」**：它只说明类型文本一致，")
        A("`compose` 仍需要 `adapt : f.Output → g.Input`（此时可取 `id`）")
        A("**与兼容性证明 `h : ∀ x y, f.post x y → g.pre (adapt y)`**。")
        A("**后者是真正的工作量，本矩阵不测量它。**")
    A("")

    io.open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")
    print("PRIMITIVE-MATRIX: %d primitive(s), %d ordered pair(s) written to PRIMITIVE-MATRIX.md"
          % (len(ps), len(ps) ** 2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
