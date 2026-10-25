import Mathlib

/-! # RealLv00AxiomDischargeCore

拆分自 `RealLv00AxiomDischarge.lean`（第 70–118 行），2026-10-14。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00AxiomDischarge` 仍有效。

本模块重新声明了原文件的三项模块级设置（缺一不可）：
`noncomputable section`（:64）、`set_option maxHeartbeats 1000000`（:66）、
`namespace Lattice.Lv00.AxiomDischarge`（:68）。
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Lattice.Lv00.AxiomDischarge

/-! ## 1. Shu ju jie gou -/

/-- Gongli bao mu ban. -/
structure PackageTemplate where
  name : String
  paramCount : Nat
  group : String
  deriving DecidableEq, Repr

/-- Bu ke gou zao wen ti. -/
structure UnconstructibleProblem where
  name : String
  reducesTo : String
  dependencies : List String
  externalRef : String
  greenVerified : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Gongli bao shi li. -/
structure AxiomPackageInstance where
  name : String
  version : String
  templates : List PackageTemplate
  unconstructibles : List UnconstructibleProblem
  deriving Repr

/-- Mu ban ming biao. -/
def templateNames (ts : List PackageTemplate) : List String := ts.map (fun t => t.name)

/-- You luo ming biao gou zao mu ban biao. -/
def mkTemplates (ns : List String) (p : Nat) (g : String) : List PackageTemplate :=
  ns.map (fun n => { name := n, paramCount := p, group := g })


/-! ## 2. Shangyou yuan weici (ben wenjian zhengming ta dui 12 ge bao quan wei jia) -/

/-- Mu ban ming shi fou ke yong. -/
def TemplateNameAvailable (templates : List PackageTemplate) (name : String) : Prop :=
  name ∈ templateNames templates

/-- Dan ge bu ke gou zao wen ti de yi lai shi fou bei mu ban biao manzu. -/
def DependenciesSatisfied (templates : List PackageTemplate) (u : UnconstructibleProblem) : Prop :=
  ∀ d ∈ u.dependencies, TemplateNameAvailable templates d

/-- **Shangyou yuan weici**. -/
def PackageDependenciesValid (pkg : AxiomPackageInstance) : Prop :=
  ∀ u ∈ pkg.unconstructibles, DependenciesSatisfied pkg.templates u



end Lattice.Lv00.AxiomDischarge
