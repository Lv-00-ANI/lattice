"""gov/gen_review_inventory.py -- every kernel declaration, with the context a reviewer needs.

## Why

`check_proof_strength.py` finds only three *syntactically* decidable shapes. The judgements that
matter -- "is this strong enough", "what is still missing for its PURPOSE", "which hypotheses could be
discharged", "can exactness be honestly downgraded to an error bound" -- cannot be mechanised.

So this generator does the mechanical half: enumerate **every** declaration, with its statement, its
docstring, its proof body and -- crucially -- its **in-degree** (who references it). The in-degree is
the anchor for "看用途": a theorem nothing references cannot be judged by its usage, and a theorem
referenced by twenty files must be judged by those twenty.

Output: one JSON object per line, in `agent-tmp/review/inv.jsonl`, plus per-batch slices.

## What it does NOT do

It does not judge. It records.
"""
import io
import json
import os
import re
import sys
from collections import defaultdict

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

HERE = os.path.dirname(os.path.abspath(__file__))
ZERO = os.path.abspath(os.path.join(HERE, ".."))
LAT = os.path.join(ZERO, "Lattice")
OUT = os.path.join(ZERO, "agent-tmp", "review")

DECL = re.compile(
    r"(?m)^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([\w'.ᵢ-₉]+)")

DOC_BEFORE = re.compile(r"/--((?:(?!-/).)*)-/\s*$", re.S)


def strip_comments_keep_docs(src):
    """Blank out ALL comments but KEEP docstring text, preserving offsets exactly.

    Used only to recover a declaration's own docstring. It must NOT be used to find declarations --
    a ```lean block inside a docstring would then look like code.
    """
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                out.append(" " * (n - i))
                break
            out.append(" " * (j - i))
            i = j
            continue
        if src.startswith("/--", i):
            j = src.find("-/", i)
            if j < 0:
                out.append(src[i:])
                break
            out.append(src[i:j + 2])
            i = j + 2
            continue
        if src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        out.append(src[i] if depth == 0 else ("\n" if src[i] == "\n" else " "))
        i += 1
    return "".join(out)


def strip_everything(src):
    """Blank out every comment INCLUDING docstrings, preserving offsets.

    This is the text used for (a) locating declarations and (b) counting references. A `theorem`
    inside a docstring is prose, not a declaration; a `#print axioms foo` in a comment is prose, not a
    use of `foo`.
    """
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j < 0:
                out.append(" " * (n - i))
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


def module_of(rel):
    """`Lib/Optim/RealSGD.lean` -> `Lattice.Lib.Optim.RealSGD`."""
    return "Lattice." + rel[:-5].replace("/", ".")


def load_corpus():
    """Return `rel -> (code_only, with_docstrings, imported_modules)`.

    `code_only` has every comment blanked: it is where declarations live and where references count.
    `with_docstrings` keeps docstring text so a reviewer can read the author's own claim.
    `imported_modules` is the set of `Lattice.*` modules the file imports, which is what makes a
    reference *possible*.
    """
    files = {}
    for dp, dirs, fs in os.walk(LAT):
        dirs[:] = [d for d in dirs if d not in (".lake", "Reference")]
        for f in sorted(fs):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, LAT).replace("\\", "/")
            raw = io.open(p, "rb").read().decode("utf-8", "replace")
            code = strip_everything(raw)
            with_doc = strip_comments_keep_docs(raw)
            imports = set()
            for m in re.finditer(r"(?m)^import\s+([\w.]+)", code):
                imports.add(m.group(1))
            files[rel] = (code, with_doc, imports)
    return files


def main():
    os.makedirs(OUT, exist_ok=True)
    corpus = load_corpus()

    # ---- in-degree: code-only occurrences, and only from files that can import the definition ----
    word = re.compile(r"[\w'.ᵢ-₉]+")
    refs = defaultdict(set)          # name -> set of files mentioning it in CODE
    for rel, (code, _wd, _imp) in corpus.items():
        for m in word.finditer(code):
            refs[m.group(0)].add(rel)

    records = []
    for rel, (code, with_doc, imports) in sorted(corpus.items()):
        # declarations are located in CODE ONLY -- a `theorem` inside a docstring is prose
        starts = [(m.start(), m.group(1), m.group(2)) for m in DECL.finditer(code)]
        for idx, (pos, kind, name) in enumerate(starts):
            end = starts[idx + 1][0] if idx + 1 < len(starts) else len(code)
            block = code[pos:end]
            line = code[:pos].count("\n") + 1
            # docstring recovered from the doc-preserving text at the same offset
            head = with_doc[:pos].rstrip()
            dm = DOC_BEFORE.search(head)
            doc = dm.group(1).strip() if dm else ""
            # split statement / proof at first top-level :=
            depth, split = 0, -1
            for i in range(len(block) - 1):
                ch = block[i]
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif depth == 0 and block.startswith(":=", i):
                    split = i
                    break
            stmt = block[:split] if split >= 0 else block
            proof = block[split + 2:] if split >= 0 else ""
            # a reference from a file that cannot import this module is not a use
            mine = module_of(rel)
            users = sorted(u for u in refs.get(name, set()) - {rel}
                           if mine in corpus[u][2])
            records.append({
                "file": rel,
                "line": line,
                "kind": kind,
                "name": name,
                "doc": doc[:1200],
                "stmt": stmt.strip()[:1500],
                "proof": proof.strip()[:1500],
                "in_degree": len(users),
                "users": users[:12],
            })

    inv = os.path.join(OUT, "inv.jsonl")
    with io.open(inv, "w", encoding="utf-8", newline="\n") as f:
        for r in records:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")

    # ---- batches: group by file so a reviewer sees a coherent topic ----
    by_file = defaultdict(list)
    for r in records:
        by_file[r["file"]].append(r)

    BATCH_TARGET = 28
    batches, cur, cur_n = [], [], 0
    for rel in sorted(by_file):
        recs = by_file[rel]
        if cur and cur_n + len(recs) > BATCH_TARGET:
            batches.append(cur)
            cur, cur_n = [], 0
        cur.extend(recs)
        cur_n += len(recs)
    if cur:
        batches.append(cur)

    for i, b in enumerate(batches):
        p = os.path.join(OUT, "batch_%03d.jsonl" % i)
        with io.open(p, "w", encoding="utf-8", newline="\n") as f:
            for r in b:
                f.write(json.dumps(r, ensure_ascii=False) + "\n")

    print("declarations: %d" % len(records))
    print("batches: %d  (target %d decls each)" % (len(batches), BATCH_TARGET))
    print("written: %s" % inv)
    tot = len(records)
    for k in ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "instance"):
        n = sum(1 for r in records if r["kind"] == k)
        if n:
            print("  %-10s %5d" % (k, n))
    zero = sum(1 for r in records if r["in_degree"] == 0)
    print("  in-degree 0: %d / %d" % (zero, tot))


if __name__ == "__main__":
    main()
