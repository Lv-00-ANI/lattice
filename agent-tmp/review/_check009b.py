import re, io

p = r"C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Lib\Chain\RealN2AxiomDischargeJia.lean"
s = io.open(p, encoding="utf-8").read()

def block(defname):
    m = re.search(r"def " + defname + r"[^\n]*:=\s*\n?(.*?)\n\n", s, re.S)
    return m.group(1) if m else ""

def names(txt):
    return re.findall(r'"([^"]+)"', txt)

pkgs = ["computabilityTheory","modalLogic","zfcSetTheory","graphTheory","measureTheory",
        "functionalAnalysis","probabilityTheory","informationTheory","linearAlgebra",
        "projectiveGeometry","orderTheory","affineGeometry"]

tot_edges = 0
allnames = set()
for p0 in pkgs:
    tpl = names(block(p0 + "TemplateNames"))
    unc = block(p0 + "Unconstructibles")
    deps = []
    for m in re.finditer(r"dependencies := \[(.*?)\]", unc, re.S):
        deps += re.findall(r'"([^"]+)"', m.group(1))
    tset = set(tpl)
    cross = [d for d in deps if d not in tset]
    tot_edges += len(cross)
    allnames |= set(cross)
    print(f"{p0:20s} edges_total={len(deps):3d} cross_edges={len(cross):2d} cross_names={len(set(cross)):2d} :: {sorted(set(cross))}")
print("TOTAL cross edges =", tot_edges, " distinct cross names =", len(allnames))
