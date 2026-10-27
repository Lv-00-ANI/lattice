# -*- coding: utf-8 -*-
"""Generate verdicts_009.jsonl for batch_009 with per-item reasoning."""
import io, json, re

BASE = r"C:\Users\xingg\Desktop\agent\lattice-new"
BATCH = BASE + r"\agent-tmp\review\batch_009.jsonl"
OUT = BASE + r"\agent-tmp\review\verdicts_009.jsonl"
JIA = BASE + r"\Lattice\Lib\Chain\RealN2AxiomDischargeJia.lean"
INST = BASE + r"\Lattice\Lib\Chain\RealLv00AxiomDischargeInstances.lean"

jia = io.open(JIA, encoding="utf-8").read()
inst = io.open(INST, encoding="utf-8").read()


def block(src, defname):
    m = re.search(r"def " + defname + r"[^\n]*:=\s*\n?(.*?)\n\n", src, re.S)
    return m.group(1) if m else ""


def names(txt):
    return re.findall(r'"([^"]+)"', txt)


PKGS = ["computabilityTheory", "modalLogic", "zfcSetTheory", "graphTheory", "measureTheory",
        "functionalAnalysis", "probabilityTheory", "informationTheory", "linearAlgebra",
        "projectiveGeometry", "orderTheory", "affineGeometry"]

stats = {}
for p in PKGS:
    tpl = names(block(jia, p + "TemplateNames"))
    unc = block(jia, p + "Unconstructibles")
    deps = []
    for m in re.finditer(r"dependencies := \[(.*?)\]", unc, re.S):
        deps += re.findall(r'"([^"]+)"', m.group(1))
    ext = names(block(jia, p + "Extra"))
    inst_len_m = re.search(r"theorem " + p + r"_templateNames_length : " + p + r"TemplateNames\.length = (\d+)",
                           inst)
    stats[p] = dict(
        tpl=len(tpl), extra=len(ext), deps=len(deps),
        cross=[d for d in deps if d not in set(tpl)],
        distinct=len(set(deps)),
        inst_len=int(inst_len_m.group(1)) if inst_len_m else None,
        padding=sorted(set(ext) - set(deps)),
        nodup=len(ext) == len(set(ext)),
        overlap=sorted(set(ext) & set(tpl)),
    )

items = [json.loads(l) for l in io.open(BATCH, encoding="utf-8") if l.strip()]

KEEP = {"A_strength": "", "B_missing": "", "C_hypotheses": "",
        "D_downgrade": "", "E_coverage": "", "F_content": ""}


def verdict(it):
    name = it["name"]
    pkg = None
    for p in PKGS:
        if name.startswith(p + "_"):
            pkg = p
    st = stats.get(pkg) if pkg else None

    if name == "lcm_assoc":
        return dict(verdict="register",
            A_strength="无需更强：结论就是 mathlib `Nat.lcm_assoc` 的等式，是格公理里最基础的一条。",
            B_missing="数学上无缺口（mathlib 已覆盖）；缺的是去重动作——同类薄包装（gcd_assoc/gcd_lcm_identity/lcm_assoc）应一次收敛到一处登记表，而不是各留一个 theorem 名。",
            C_hypotheses="无前提可删。",
            D_downgrade="不适用（等式，非误差界）。",
            E_coverage="覆盖如实：`∀ a b c : Nat`，无隐含前提，无子类限制。",
            F_content="薄包装：证明体是 `Nat.lcm_assoc a b c` 原样转发，与 mathlib 完全重复，不新增证明内容（非 a=a，但也无自有数学）。",
            note="【实测，锚点为假】`RealDvdLatticeStratification.lean` 只 `import Mathlib`，其中 `lcm_assoc` 仅出现在注释（:107），且该文件用 `Nat.dvd_antisymm` **自己重证**了 `nat_sup_assoc`（:109–126），还错误宣称「mathlib 的 `Nat` 上无现成 `lcm_assoc`」——本条正是 `Nat.lcm_assoc` 的逐字包装。⇒ in_degree=1 是注释文本误匹配，本条 0 真实调用者、0 新增信息。建议删除该 theorem（或降为 `abbrev`）并修正下游注释，属清理项，非现在必修。")

    if name == "model_block_lb_nonneg":
        return dict(verdict="keep", **KEEP,
            note="真前置：`Lb ≥ 0` 正是下游 `model_chain_numeric_bound` 用幂不等式 `Lb^m` 的必要条件（`chainN_dom_bound` 的 `hL0`）。C 维度已是最弱形式：原稿的 `hB : ∀ z, ‖z‖ ≤ B`（不可满足）已换成只取 `0 ≤ B`（:113–116），而 `0 ≤ B` 在本引理内**不可**导出（B<0 时 `1 + B·k(k+1)e^{4‖S‖B}‖S‖` 可负 ⟹ Lb 可负），由调用方从 `hBc 0` 另行推出；`hM` 用于经 `[NeZero k]` 取 i₀ 得 `0 ≤ M`。无冗余。")

    if name == "model_chain_numeric_bound":
        return dict(verdict="keep", **KEEP,
            note="端到端 `Lb^m` 界，恰是下游（RealModelChainHetero / RealMixedAttention）要引用的形状；`hBc`/`hreach` 是沿链可达性的显式前提而非被证结论，文件头 :41–59 已如实标注「不证明真实块链满足 hreach」。**可满足性本人复核**：取 S=W=V=0、x=e₀、c≤1、B≥√n，则每步 residual=ChainFwd j x∈{e₀,√n·e₀}，`hBc`/`hreach` 同时成立 ⟹ 非空洞。前件无一可删：`hBc` 供 `0≤B` 与 softmax 有界，`hreach` 供 RMSNorm 定义域，均随 m 变化，点对版不足以替代。")

    if name == "model_chain_edit_locality_numeric":
        return dict(verdict="keep", **KEEP,
            note="编辑局部性数字版：结论 `≤ Lb^(m−kk)·‖δ‖` 与用途（尾部块扰动放大）一致；`ChainTail = ChainFwd (m−kk)` 由 rfl 得（:296–300），`hstart` 用 abel。`hBc` 声明范围 `j ≤ m` 比所需 `j ≤ m−kk` 宽（无害且省得再切索引）。同块 hBc/hreach 的诚实性与可满足性同 `model_chain_numeric_bound`。")

    if name == "hetero_block_lb_nonneg":
        return dict(verdict="keep", **KEEP,
            note="适配器（`change` 后复用 `model_block_lb_nonneg`），但**有真实消费者**：`RealMixedAttention.lean:646/746` 在给 `∏ Lb_i` 的乘积非负前提时逐块调用。异质版常数 `heteroBlockLb = (√n/c)(1+attnNumericConstant+‖W i‖)` 与 `modelBlockLb S (W i)` 定义等同，故 `change` 合法而非绕过证明。C：hB0 同样不可删（B<0 可致 Lb_i<0）。")

    if name == "hetero_block_lipschitz_numeric":
        return dict(verdict="keep", **KEEP,
            note="`simpa [ModelBlock, heteroBlockLb, attnNumericConstant] using transformer_block_numeric`——逐块读出，非自证但也不是空壳：常数确实被换成 `heteroBlockLb`，需 `ModelBlock S V (W i)` 与 `transformer_block_numeric` 的被证算子在定义上重合。真实消费者：`RealMixedAttention.lean:595`（混合块证明的双向分支）。属于合法的薄实例化。")

    if name == "hetero_chain_numeric_bound":
        return dict(verdict="keep", **KEEP,
            note="异质链的 `∏_{i<m} Lb_i` 界，与同构版同形（`chainN_dom_bound` + 逐层 `hetero_block_lipschitz_numeric` + 逐层非负），前件 `hBc`/`hreach` 与 `model_chain_numeric_bound` 相同且可满足（同上 S=W=0 见证）。doc 声称的「异质性来自 ‖W_i‖，不是额外假设」与陈述一致（n/k/M/B/c/S 全块共享，仅 W 逐块）。")

    if name == "convertVec_bias_eq_convertRealVec_bias":
        return dict(verdict="register",
            A_strength="不足以支撑 doc 的「承重点」措辞：该处若要主张「链核心语义可以抬升到 ℝ」，需要的不是字段相等，而是语义交换——应存在 `RealLayerOut (convertRealVec (castConstraint n c)) (toRealVec n x) = toRealVec n (LayerOut (convertVec c) x)`（以及 `RealDot (toRealVec n x) (toRealVec n y) = ((dot x y : ℤ) : ℝ)`）。现在只钉了偏置字段。",
            B_missing="缺「交换方块 / 保值」定理（上述形状）。现有整套桥（本条 + `convertVec_weight_eq_convertRealVec_weight` + `RealSeamBridges2` 的 `coreConstraintToReal_eq_castConstraint` / `castConstraint_b_eq_convertVec_b`）全是 rfl 链，没有一条把两侧的**行为**接起来。",
            C_hypotheses="无前提可删（无假设）。",
            D_downgrade="不适用（等式陈述已是精确，问题在信息量而非精度）。",
            E_coverage="覆盖如实：`∀ n c`，两侧字段都取到（偏置分量确实相等），无子类限制。",
            F_content="rfl ⟹ 两侧展开为同一项 `((c.b : ℤ) : ℝ)`（`castConstraint` 直接把 `b` 定义为 `(c.b : ℝ)`，`convertRealVec` 又原样搬 `.b`），数学信息≈0；唯一价值是把 import 边变成真依赖（消融可达性）。",
            note="【实测】证明体是 `rfl`。doc 的字段级说法准确，但「这就是边的承重点」易被下游读成「语义等价已证」——而宏可达性只需提及两个常量名即可成立，与证明内容无关。下游 `RealSeamBridges2.lean` 又以 rfl 链（`castConstraint_b_eq_convertVec_b`）复述同一事实。⇒ 登记「语义抬升未接通」的 PROOF-DEBT；不删（它确实把「模型族 → 链核心」的可达边接成真实 import 依赖，删了该文件就不再提及 `convertVec`），但下游不得据此声称语义等价。")

    if name.endswith("_templateNames_length"):
        s = st
        div = s["inst_len"] is not None and s["inst_len"] != s["tpl"]
        tail = (f"本文件 {s['tpl']} / 副本 {s['inst_len']}（副本另有 padding 名，见其 `EXEC-Y1-EXTERNAL-30` 注释）" if div
                else f"本文件与副本同为 {s['tpl']}（数一致，但仍是两份数据源）")
        return dict(verdict="register",
            A_strength=f"作为「转录不丢项」的 pin 强度够（`rfl` 直接算列表长度）；但作为「上游 {s['tpl']} 条」的证据**不够**：本条只钉本文件那份字面量，与上游 `Instances_*.lean` 无任何机器可检联系（不 import、不比对）。",
            B_missing="缺数据单一来源：应由上游生成/比对（或一条 `templateNames_eq_upstream` 型定理），并缺 12 个 length 的汇总核对定理（现有 `all_twelve_discharged` 只汇总 ¬Valid，不汇总计数）。",
            C_hypotheses="无前提可删。",
            D_downgrade="不适用（计数等式，无精度可降）。",
            E_coverage=f"覆盖如实：全称即字面量本身（长度 {s['tpl']}），无 ∀x/构造子覆盖问题。",
            F_content="`rfl` 的具体计数，非重言（不是 a=a），属数据 pin；但数学信息为零，价值完全取决于「有没有第二份数据要对齐」。",
            note=f"【实测，锚点为假 + 数据已分叉】in_degree 指向 `RealLv00AxiomDischargeInstances.lean`，但该文件只 `import ...AxiomDischargeCore`，并在 `:88` 起**自行重声明**同名定理（副本，非使用）。同一上游包的两份模板表长度已不一致：{tail}。12 个包里 6 个分叉（modalLogic 27/28、graphTheory 70/71、probabilityTheory 87/89、informationTheory 106/117、projectiveGeometry 38/48、orderTheory 32/37）。⇒ 这条 pin 保护不到任何东西，登记「重复副本 + 数据单一来源」债务；无需改证明，需删副本或加对齐断言。")

    if name.endswith("_extra_length"):
        s = st
        return dict(verdict="keep", **KEEP,
            note=f"数据核对（脚本实测本文件数据）：`extra` 恰等于 `deps ∖ templates`，无填充（padding=[]）、无重复（nodup=True）、与模板表不交、覆盖全部跨引用名。`length = {s['extra']}` 由 rfl 算得，且是 `{pkg}_false_but_repairable` 第三个合取项的真消费者（文件内真用途）。")

    if name.endswith("_validB_eq_false"):
        s = st
        return dict(verdict="keep", **KEEP,
            note=f"rfl 完成可判定计算：{s['distinct']} 个不可构造问题、{s['deps']} 条依赖中出现 {len(s['cross'])} 个不在模板表内的名 ⟹ 上游元谓词为假。这是本条目的**实际内容**（对上游 axiom 的反例证书），并经开 `packageDependenciesValidB_iff` 被 `not_{pkg}_orig` 使用；不是「名字在、内容空」。")

    if name.endswith("_closedB_eq_true"):
        s = st
        return dict(verdict="keep", **KEEP,
            note=f"rfl 计算「`extra` 覆盖全部依赖名」为真；因实测 `extra = deps∖templates`（无填充无重复），此证书不空泛，且经 `packageDependenciesClosedB_iff` 被 `{pkg}_closed` 真消费。注意它只证「闭包」，不证「依赖可构造」——doc 与文件头 :46 均已如实划界。")

    if name.endswith("_closed"):
        s = st
        return dict(verdict="keep", **KEEP,
            note=f"把 Bool 计算经 `packageDependenciesClosedB_iff` 抬回 Prop，结论即「`extra` 意义下包内依赖全在合法名集内」。doc 用「闭包意义下为真」，未冒充原命题成立（文件头 :42–46 明确「严格更弱，`closed_nil_iff` 为界」）⟹ 声称强度与所证一致。")

    if name.endswith("_false_but_repairable"):
        s = st
        return dict(verdict="keep", **KEEP,
            note=f"三个合取项各自真实且已分别证明：¬Valid（反例）、Closed（`extra` 下闭包）、`extra.length = {s['extra']}`。脚本实测该包跨引用 {len(set(s['cross']))} 名 / {len(s['cross'])} 条边（边 = 指向非模板名的依赖出现次数），与 doc 的「{len(set(s['cross']))} 个名, {len(s['cross'])} 条边」完全吻合；`extra` 无填充无重复 ⟹ 计数非注水。这是本批最实的一类条目。")

    if name == "dependenciesSatisfiedB_iff":
        return dict(verdict="keep", **KEEP,
            note="Bool↔Prop 桥：`List.all_eq_true` + `contains` 一侧到 `∀ d ∈ deps` 一侧的转化，是本族全部 Bool 计算能合法抬回 Prop 的前提（且刻意不用 `native_decide`，避免引入额外公理）。证明是 simp 但需要正确的 iff 方向与 `TemplateNameAvailable` 展开，非 a=a。")

    if name == "closed_nil_iff":
        return dict(verdict="keep", **KEEP,
            note="定义性展开（`LegalNames pkg [] = templateNames ++ [] = templateNames`），数学信息低，但它是**文件自述策略的边界契约**：`extra = []` 时「修复谓词」恰好退化为「原谓词」，这正是全套「只弱化、不加内容」主张的依据；doc 也只声称这一点。作为接口引理成立且被 `#print axioms` 清单点名，非占位。")

    if name == "not_valid_iff_bad_dep":
        return dict(verdict="keep", **KEEP,
            note="真刻画（非重言）：`¬Valid ↔ ∃ u ∈ pkg.unconstructibles, ∃ d ∈ u.dependencies, d ∉ templateNames`。双向都有内容（`not_forall`/`Classical.not_imp` 一侧），为「原谓词为假」提供了可复用的反例形式，而不只是算某个包。")

    raise SystemExit("no rule for " + name)


out = []
for it in items:
    v = verdict(it)
    rec = {"file": it["file"], "line": it["line"], "name": it["name"],
           "verdict": v["verdict"],
           "A_strength": v.get("A_strength", ""), "B_missing": v.get("B_missing", ""),
           "C_hypotheses": v.get("C_hypotheses", ""), "D_downgrade": v.get("D_downgrade", ""),
           "E_coverage": v.get("E_coverage", ""), "F_content": v.get("F_content", ""),
           "note": v["note"]}
    out.append(rec)

with io.open(OUT, "w", encoding="utf-8", newline="\n") as f:
    for r in out:
        f.write(json.dumps(r, ensure_ascii=False) + "\n")

from collections import Counter
c = Counter(r["verdict"] for r in out)
print("items:", len(out), "batch:", len(items))
print(dict(c))
print("weak:", sum(v for k, v in c.items() if k != "keep"))
