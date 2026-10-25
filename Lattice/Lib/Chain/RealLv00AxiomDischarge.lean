import Mathlib

import Lattice.Lib.Chain.RealLv00AxiomDischargeCore
import Lattice.Lib.Chain.RealLv00AxiomDischargeInstances
import Lattice.Lib.Chain.RealLv00AxiomDischargeClosure
import Lattice.Lib.Chain.RealLv00AxiomDischargePerPackage
import Lattice.Lib.Chain.RealLv00AxiomDischargeSummary
/-!
# LATTICE / Lv-00 -- 12 tiao *Package_dependencies_valid axiom de qingsuan
（其中 graph_theory 经 EXEC-Y1 补外名后原谓词改判为真，见 `graphTheory_orig_true`）

Shangyou Lv-00 (level0000x/Lv-00, fenzhi lv-merged) de
lvFormal/Theory/Axioms/ xia you **12 tiao zhen axiom**, xing ru

    axiom <X>Package_dependencies_valid : PackageDependenciesValid <X>Package

Ben wenjian ba zhe 12 tiao **zhu tiao qingsuan**:

1. **Banyun zhenshi shuju** (muban biao + buke gouzao wenti biao,
   zhu zi lai zi shangyou Instances_*.lean),
   er bu shi xiang RealLv00AxiomPackages.lean S4 nayang zhi yong yige wanju refPackage.
2. **Zhengming yuan mingti wei jia**: not_<X>_orig.
3. **Zhengming xiufu mingti wei zhen**: <X>_closed.

## Caining: **gai weici**（bing bu dengji EXEC-Y1 wai ming shuju）, bu shi gai shuju

Shangyou 12 tiao duanyan de weici shi

    PackageDependenciesValid pkg := forall u, u ∈ pkg.unconstructibles -> forall d, d ∈ u.dependencies ->
                                  d ∈ templateNames pkg.templates

Ta yaoqiu **meige yilai dou mingzhong benbao muban biao**.
Shice: 12 ge bao de yilai biao li gong you 98 tiao kua yinyong bian.

**Weishenme bu shi gai shuju**: zhexie kua yinyong zai yuyi shang shi **zhengque** de --
continuum_hypothesis que shi shi ZFC bao li de xiongdi buke gouzao wenti;
halting_problem que shi shi computability bao li de xiongdi;
zfc_set_theory / measure_theory / computability_theory que shi shi bie de zhenshi bao.
Shan diao huo gai ming zhexie yilai jiushi cuangai shuju yi qianjiu guo ruo de weici.

**Suoyi chulu shi gai weici**: ba yilai bixu mingzhong benbao muban biao fangkuan wei
yilai bixu mingzhong benbao muban biao UNION xianshi dengji de kua yinyong ming jihe extra.
extra shi **zhengju weizhi**: ta ba zhexie mingzi you ju ke yi zhe jian shi bian cheng
ke jian, ke shenji de shuru.

**Bu chong shuoming (EXEC-Y1 she ji mu ban biao shuju)**: chu gai weici wai, EXEC-Y1 hai
**xiang benbao mu ban biao zhui jia le 30 ge zhen wai ming**（ji bu shi kua yinyong ming de
wai bu mingzi）, fen bie wei modalLogic +1、graphTheory +1、probabilityTheory +2、
informationTheory +11、projectiveGeometry +10、orderTheory +5, ge chu jun biao you
`EXEC-Y1-EXTERNAL-30` zhu shi. Suoyi ben wenjian bing fei **wanquan** bu dong shuju;
zhunque de shuo shi: **bu shan gai / bu chong ming** renhe yi lai ming, zhi **zhui jia**
yi lei 「zhen wai ming」shuju.

Zhe lei zhui jia **hufan yingxiang le yuan weici de zhen zhi**: `graph_theory` de wei yi
queshi yilai `three_colorability` zheng hao bei bu jin le benbao mu ban biao, gu qi
**yuan weici you jia bian zhen**（jian `graphTheory_orig_true` / `graphTheory_repaired`
yu xia fang de EXEC-Y1 gai pan shuoming）。Ji **bu shuju ben shen jiu shi xiufu shouduan
zhi yi**, er bu jin jin shi weici fangkuan.

## Chengshi bianjie

- Ben wenjian **bu chengsheng** xiufu hou de mingti he yuan mingti yiyang qiang.
  Ta yange geng ruo: closed_nil_iff.
- Ben wenjian **bu chengsheng** kua yinyong ming ben shen ke gouzao huo you yiyi.
- 0 axiom / 0 sorry / 0 admit.
- Shangyou na 12 tiao axiom shi **jia mingti**, bu shi zheng bu chulai.
-/

/-!
> **拆分说明（2026-10-14）**：本文件原含 **168 个声明**（93 theorem + 72 def + 3 structure）、
> 1366 行。声明已按原有分节（1～6）拆入 5 个模块，本文件**改为 re-export 门面**：
>
> | 子模块 | 原行范围 | 声明数 |
> |:--|:--|--:|
> | `RealLv00AxiomDischargeCore` | 70–118 | 8 |
> | `RealLv00AxiomDischargeInstances` | 119–769 | 60 |
> | `RealLv00AxiomDischargeClosure` | 770–878 | 14 |
> | `RealLv00AxiomDischargePerPackage` | 879–1303 | 84 |
> | `RealLv00AxiomDischargeSummary` | 1304–1335 | 2 |
> | **合计** | | **168** |
>
> 采用**连续切分**（每模块覆盖连续行区间并 import 紧邻前驱），实测本文件**零前向引用**，
> 故文件顺序即拓扑序，无需手写依赖表。
>
> 下方 `#print axioms` 清单保留在本文件：它原本就在 namespace **之外**（:1340–:1366），
> 且引用 §4/§5/§6 的名字；门面 import 了全部子模块，故行为不变。
>
> 子模块已注册进 `lakefile.toml` 的 `roots`——`roots` 是显式白名单，不注册则
> `lake build lattice` 会以 `unknown module prefix` 失败。
-/

/-! ## 7. Axiom qingdan -/

#print axioms Lattice.Lv00.AxiomDischarge.not_computabilityTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.computabilityTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_modalLogic_orig
#print axioms Lattice.Lv00.AxiomDischarge.modalLogic_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_zfcSetTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.zfcSetTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.graphTheory_orig_true
#print axioms Lattice.Lv00.AxiomDischarge.graphTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_measureTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.measureTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_functionalAnalysis_orig
#print axioms Lattice.Lv00.AxiomDischarge.functionalAnalysis_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_probabilityTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.probabilityTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_informationTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.informationTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_linearAlgebra_orig
#print axioms Lattice.Lv00.AxiomDischarge.linearAlgebra_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_projectiveGeometry_orig
#print axioms Lattice.Lv00.AxiomDischarge.projectiveGeometry_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_orderTheory_orig
#print axioms Lattice.Lv00.AxiomDischarge.orderTheory_closed
#print axioms Lattice.Lv00.AxiomDischarge.not_affineGeometry_orig
#print axioms Lattice.Lv00.AxiomDischarge.affineGeometry_closed
#print axioms Lattice.Lv00.AxiomDischarge.closed_nil_iff
#print axioms Lattice.Lv00.AxiomDischarge.dependenciesClosed_mono
#print axioms Lattice.Lv00.AxiomDischarge.not_forall_packageDependenciesValid
