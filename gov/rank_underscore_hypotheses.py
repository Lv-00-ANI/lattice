"""Rank the baselined underscore hypotheses by in-degree.

In-degree = how many OTHER modules mention the theorem name in code (comments stripped) **and** import
the defining module. That gate matters: an earlier inventory counted same-named lemmas across namespaces.

The point of the ranking is that 130 entries cannot all be paid in the rounds available, so the ones that
downstream code actually consumes should be paid first.
"""
import io
import os
import re
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")
BASE = os.path.join(HERE, "underscore_hypotheses_baseline.txt")
MOD = re.compile(r"(?m)^import\s+Lattice\.([\w.]+)\s*$")


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


def main():
    entries = []
    for ln in io.open(BASE, encoding="utf-8"):
        ln = ln.rstrip("\n")
        if not ln or ln.startswith("#"):
            continue
        p = ln.split("\t")
        if len(p) >= 2:
            entries.append((p[0].strip(), p[1].strip(), p[2].strip() if len(p) > 2 else ""))

    # module path -> (rel file, code, imports)
    files = {}
    for dp, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in fs:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            code = strip_comments(raw)
            imports = {"Lattice." + m.group(1) for m in MOD.finditer(raw)}
            files[rel] = (code, imports)

    rows = []
    for loc, name, var in entries:
        if loc not in files:
            rows.append((0, loc, name, var, "file missing"))
            continue
        # the module that defines it, in import form
        definer = "Lattice." + loc[:-5].replace("/", ".")
        users = 0
        for rel, (code, imports) in files.items():
            if rel == loc:
                continue
            if definer not in imports:
                continue
            if re.search(r"(?<![\w'.])%s(?![\w'])ŋ?" % re.escape(name), code):
                users += 1
        rows.append((users, loc, name, var, ""))

    rows.sort(key=lambda r: (-r[0], r[1]))
    print("%-5s %-6s %s" % ("in", "binder", "theorem"))
    for users, loc, name, var, note in rows:
        if users >= 2:
            print("%-5d %-6s %s :: %s %s" % (users, var, name, loc, note))
    print()
    hi = sum(1 for r in rows if r[0] >= 2)
    mid = sum(1 for r in rows if r[0] == 1)
    lo = sum(1 for r in rows if r[0] == 0)
    print("TOTAL %d -- in-degree >=2: %d, ==1: %d, ==0: %d" % (len(rows), hi, mid, lo))


if __name__ == "__main__":
    main()
