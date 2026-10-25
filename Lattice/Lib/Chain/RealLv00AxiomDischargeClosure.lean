import Mathlib
import Lattice.Lib.Chain.RealLv00AxiomDischargeInstances
/-! # RealLv00AxiomDischargeClosure

拆分自 `RealLv00AxiomDischarge.lean`（第 770–878 行），2026-10-14。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00AxiomDischarge` 仍有效。

本模块重新声明了原文件的三项模块级设置（缺一不可）：
`noncomputable section`（:64）、`set_option maxHeartbeats 1000000`（:66）、
`namespace Lattice.Lv00.AxiomDischarge`（:68）。
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Lattice.Lv00.AxiomDischarge

/-! ## 4. Xiufu weici: yi lai bi bao (dependency closure)

He fa ming ji he = ben bao mu ban biao UNION xianshi dengji de kua yinyong ming extra.
extra shi **zhengju weizhi**.

注意 **Ke jueding xing she ji**: `String` shi **wu xian** yu, suo yi
`forall d : String, d ∈ l -> P d` zai Lean li **mei you** `Decidable` shili,
`decide` hui bao unable to synthesize Decidable.
Yin ci ben wenjian ba he xin pan ding xie cheng **Bool ban** (`*B`),
zai yong `*_iff` yin li **qiao jie** hui Prop ban.
Zhe yang: (a) pan ding bi ding ke jueding; (b) bu yi lai `native_decide`;
(c) qiao jie yin li jin yong `List.all_eq_true` + `List.contains`, bu yin ru gongli. -/

/-- He fa ming ji he (Prop ban). -/
def LegalNames (pkg : AxiomPackageInstance) (extra : List String) : List String :=
  templateNames pkg.templates ++ extra

/-- **Bao zai `extra` xia de yi lai bi he xing**（dan ge wen ti）。

注意 **2026-10 ben ci bu chong**：`DependenciesClosed` yu `PackageDependenciesClosed`
yin `RealLv00AxiomPackages.lean` ding yi，er ben wen jian zhi `import Mathlib`，
gu er **wei ding yi** —— 31 + 61 chu yin yong quan bu wu fa jie xi。
Ben ci **jiu di bu qi**（zi han han），er fei xin zeng kua mo kuai import。 -/
def DependenciesClosed (pkg : AxiomPackageInstance) (extra : List String)
    (u : UnconstructibleProblem) : Prop :=
  ∀ d ∈ u.dependencies, d ∈ LegalNames pkg extra

/-- **Bao zai `extra` xia de yi lai bi he xing**（zheng ge bao）。 -/
def PackageDependenciesClosed (pkg : AxiomPackageInstance) (extra : List String) : Prop :=
  ∀ u ∈ pkg.unconstructibles, DependenciesClosed pkg extra u


/-- **Bool he xin**: mu ban ming biao shi fou han mou ming. -/
def templateNameAvailableB (ts : List PackageTemplate) (name : String) : Bool :=
  (templateNames ts).contains name

/-- **Bool he xin**: dan ge wen ti de yi lai shi fou bei mu ban biao manzu. -/
def dependenciesSatisfiedB (ts : List PackageTemplate) (u : UnconstructibleProblem) : Bool :=
  u.dependencies.all (templateNameAvailableB ts)

/-- **Bool he xin**: shangyou yuan weici de Bool ban. -/
def packageDependenciesValidB (pkg : AxiomPackageInstance) : Bool :=
  pkg.unconstructibles.all (dependenciesSatisfiedB pkg.templates)

/-- **Bool he xin**: xiufu weici (bi bao) de Bool ban. -/
def packageDependenciesClosedB (pkg : AxiomPackageInstance) (extra : List String) : Bool :=
  pkg.unconstructibles.all (fun u => u.dependencies.all (fun d => (LegalNames pkg extra).contains d))

/-- **Qiao jie 1**: dan ge wen ti, Bool ban <-> Prop ban. -/
theorem dependenciesSatisfiedB_iff (ts : List PackageTemplate) (u : UnconstructibleProblem) :
    dependenciesSatisfiedB ts u = true <-> DependenciesSatisfied ts u := by
  simp [dependenciesSatisfiedB, DependenciesSatisfied, TemplateNameAvailable,
    templateNameAvailableB]

/-- **Qiao jie 2**: shangyou yuan weici, Bool ban <-> Prop ban. -/
theorem packageDependenciesValidB_iff (pkg : AxiomPackageInstance) :
    packageDependenciesValidB pkg = true <-> PackageDependenciesValid pkg := by
  simp [packageDependenciesValidB, PackageDependenciesValid, dependenciesSatisfiedB_iff]

/-- **Qiao jie 3**: xiufu weici, Bool ban <-> Prop ban. -/
theorem packageDependenciesClosedB_iff (pkg : AxiomPackageInstance) (extra : List String) :
    packageDependenciesClosedB pkg extra = true <-> PackageDependenciesClosed pkg extra := by
  simp [packageDependenciesClosedB, PackageDependenciesClosed, DependenciesClosed, LegalNames]

/-- **Jie kou ding li**: extra = [] shi, xiufu weici tui hua wei shangyou yuan weici.
Ba liang ge weici de guan xi ding si, shi hou xu 12 tiao dui zhao de yiju. -/
theorem closed_nil_iff (pkg : AxiomPackageInstance) :
    PackageDependenciesClosed pkg [] <-> PackageDependenciesValid pkg := by
  simp only [PackageDependenciesClosed, PackageDependenciesValid, DependenciesClosed,
    DependenciesSatisfied, TemplateNameAvailable, LegalNames, List.append_nil]

/-- **Dan diao xing**: kuo da extra dan diao baochi bi bao zi qia. -/
theorem dependenciesClosed_mono {pkg : AxiomPackageInstance} {extra extra2 : List String}
    (hsub : ∀ n, n ∈ extra → n ∈ extra2)
    (h : PackageDependenciesClosed pkg extra) :
    PackageDependenciesClosed pkg extra2 := by
  intro u hu d hd
  have hd2 : d ∈ LegalNames pkg extra := h u hu d hd
  show d ∈ LegalNames pkg extra2
  simp only [LegalNames, List.mem_append] at hd2 ⊢
  rcases hd2 with hd2 | hd2
  · exact Or.inl hd2
  · exact Or.inr (hsub d hd2)

/-- **Bu deng yin li**: ruo mou bao de yi lai ji zheng ti bao han yu extra, ze bi bao zi qia. -/
theorem dependenciesClosed_of_subset {pkg : AxiomPackageInstance} {extra : List String}
    (h : ∀ u, u ∈ pkg.unconstructibles → ∀ d, d ∈ u.dependencies → d ∈ extra) :
    PackageDependenciesClosed pkg extra := by
  intro u hu d hd
  show d ∈ LegalNames pkg extra
  simp only [LegalNames, List.mem_append]
  exact Or.inr (h u hu d hd)

/-- **Fan li pan ju**: mou bao yuan weici wei jia, dang qie jin dang
cun zai yi tiao bu zai mu ban biao zhong de yi lai. -/
theorem not_valid_iff_bad_dep (pkg : AxiomPackageInstance) :
    (¬ PackageDependenciesValid pkg) ↔
      ∃ u, u ∈ pkg.unconstructibles ∧ ∃ d, d ∈ u.dependencies ∧
        d ∉ templateNames pkg.templates := by
  unfold PackageDependenciesValid DependenciesSatisfied TemplateNameAvailable
  constructor
  · intro h
    push_neg at h
    exact h
  · intro h hv
    obtain ⟨u, hu, d, hd, hnd⟩ := h
    exact hnd (hv u hu d hd)



end Lattice.Lv00.AxiomDischarge
