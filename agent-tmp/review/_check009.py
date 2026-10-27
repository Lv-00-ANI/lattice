import re, io, json

p = r"C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Lib\Chain\RealN2AxiomDischargeJia.lean"
s = io.open(p, encoding="utf-8").read()

def block(defname):
    m = re.search(r"def " + defname + r"[^\n]*:=\s*\n?(.*?)\n\n", s, re.S)
    if not m:
        m = re.search(r"def " + defname + r"[^\n]*:=\s*(.*?)\n\n", s, re.S)
    return m.group(1) if m else ""

def names(txt):
    return re.findall(r'"([^"]+)"', txt)

pkgs = ["computabilityTheory","modalLogic","zfcSetTheory","graphTheory","measureTheory",
        "functionalAnalysis","probabilityTheory","informationTheory","linearAlgebra",
        "projectiveGeometry","orderTheory","affineGeometry"]

for p0 in pkgs:
    tpl = names(block(p0 + "TemplateNames"))
    unc = block(p0 + "Unconstructibles")
    # each record line: dependencies := [ ... ]
    deps = []
    for m in re.finditer(r"dependencies := \[(.*?)\]", unc, re.S):
        deps += re.findall(r'"([^"]+)"', m.group(1))
    ext = names(block(p0 + "Extra"))
    dset, tset, eset = set(deps), set(tpl), set(ext)
    padding = sorted(eset - dset)
    uncovered = sorted(dset - tset - eset)
    useless = sorted(eset & tset)
    print(f"{p0:20s} tpl={len(tpl):3d} extra={len(ext):2d} deps={len(deps):3d} distinct_deps={len(dset):2d} "
          f"| uncovered={uncovered} padding={padding} extra_in_templates={useless} nodup={len(ext)==len(eset)}")
