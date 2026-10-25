#!/usr/bin/env python3
"""Compile a Lean file with the project's OWN toolchain and import graph.

This is the ONLY authoritative oracle for two questions:
  (a) does a file compile?
  (b) which module does a given declaration live in?

It deliberately shells out to `lake env lean` instead of hand-assembling LEAN_PATH.
A hand-built LEAN_PATH was tried first and produced a misleading
"unknown module prefix 'Mathlib'" that looked like a missing dependency.

Usage
-----
    python lake_lean.py check  <project_dir> <relative.lean> [--import MODULE]
    python lake_lean.py find   <project_dir> <Namespace.ClassName>
    python lake_lean.py build  <project_dir> [--target Name]

`find` greps every `.lean` under the project for a `class`/`structure`/`inductive`/
`def` declaration with that name, because LEAN_PATH alone cannot resolve
namespace-qualified names whose module you do not know.
"""
import argparse
import json
import os
import re
import subprocess
import sys


def run_lake_env_lean(project: str, rel_path: str, extra_import: str = None) -> dict:
    if extra_import:
        src = "import %s\n" % extra_import
        r = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=project,
                           input=src, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
    else:
        r = subprocess.run(["lake", "env", "lean", rel_path], cwd=project,
                           capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
    out = (r.stdout or "") + (r.stderr or "")
    errors = [ln for ln in out.splitlines() if ": error" in ln or ln.startswith("error")]
    warnings = [ln for ln in out.splitlines() if ": warning" in ln]
    return {
        "target": rel_path if not extra_import else ("import " + extra_import),
        "exit": r.returncode,
        "ok": r.returncode == 0,
        "errors": errors,
        "n_errors": len(errors),
        "n_warnings": len(warnings),
        "raw_tail": out[-4000:],
    }


def find_decl(project: str, name: str) -> dict:
    pat = re.compile(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*"
                     r"(class|structure|inductive|def|abbrev|theorem|lemma)[ \t]+"
                     + re.escape(name) + r"\b", re.M)
    hits = []
    for root, _d, files in os.walk(project):
        if ".lake" in root.split(os.sep):
            continue
        for f in files:
            if not f.endswith(".lean"):
                continue
            p = os.path.join(root, f)
            try:
                src = open(p, "rb").read().decode("utf-8", errors="replace")
            except OSError:
                continue
            for m in pat.finditer(src):
                hits.append({
                    "file": os.path.relpath(p, project),
                    "line": src[: m.start()].count("\n") + 1,
                    "kind": m.group(1),
                    "name": name,
                })
    return {"name": name, "hits": hits, "count": len(hits)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("command", choices=["check", "find", "build"])
    ap.add_argument("project")
    ap.add_argument("target", nargs="?")
    ap.add_argument("--import", dest="imp", default=None)
    ap.add_argument("--target", dest="build_target", default=None, help="for build")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if args.command == "check":
        res = run_lake_env_lean(os.path.abspath(args.project), args.target, args.imp)
        if args.json:
            print(json.dumps(res, ensure_ascii=False, indent=1))
        else:
            print("target : %s" % res["target"])
            print("exit   : %d  (%s)" % (res["exit"], "OK" if res["ok"] else "FAIL"))
            print("errors : %d   warnings: %d" % (res["n_errors"], res["n_warnings"]))
            for e in res["errors"][:20]:
                print("   " + e)
        return 0 if res["ok"] else 1

    if args.command == "find":
        res = find_decl(os.path.abspath(args.project), args.target)
        if args.json:
            print(json.dumps(res, ensure_ascii=False, indent=1))
        else:
            print("declaration `%s` found in %d place(s):" % (res["name"], res["count"]))
            for h in res["hits"]:
                print("  %-45s :%-6d (%s)" % (h["file"], h["line"], h["kind"]))
        return 0 if res["count"] else 1

    cmd = ["lake", "build"]
    if args.build_target:
        cmd.append(args.build_target)
    r = subprocess.run(cmd, cwd=os.path.abspath(args.project), capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    print((r.stdout or "")[-4000:])
    print((r.stderr or "")[-2000:])
    print("exit:", r.returncode)
    return r.returncode


if __name__ == "__main__":
    sys.exit(main())
