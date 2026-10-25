import Mathlib

/-!
# LATTICE / Lv-00 -- 12 tiao *Package_dependencies_valid axiom de qingsuan

Shangyou Lv-00 (level0000x/Lv-00, fenzhi lv-merged) de
lvFormal/Theory/Axioms/ xia you **12 tiao zhen axiom**, xing ru

    axiom <X>Package_dependencies_valid : PackageDependenciesValid <X>Package

Ben wenjian ba zhe 12 tiao **zhu tiao qingsuan**
(12 tiao axiom dui ying 12 ge bao, `all_twelve_discharged` de he qu xiang shu wei 12):

1. **Banyun zhenshi shuju** (muban biao + buke gouzao wenti biao,
   zhu zi lai zi shangyou Instances_*.lean),
   er bu shi xiang RealLv00AxiomPackages.lean S4 nayang zhi yong yige wanju refPackage.
2. **Zhengming yuan mingti wei jia**: not_<X>_orig.
3. **Zhengming xiufu mingti wei zhen**: <X>_closed.

## Caining: **gai weici**, bu shi gai shuju

Shangyou 12 tiao duanyan de weici shi

    PackageDependenciesValid pkg := forall u, u ∈ pkg.unconstructibles -> forall d, d ∈ u.dependencies ->
                                  d ∈ templateNames pkg.templates

Ta yaoqiu **meige yilai dou mingzhong benbao muban biao**.
Shice: 12 ge bao de yilai biao li gong you 95 tiao kua yinyong bian;
zhe xie bian qu fen ming ji zhi hou wei 60 ge bu tong de kua yinyong ming.

**Weishenme bu shi gai shuju**: zhexie kua yinyong zai yuyi shang shi **zhengque** de --
continuum_hypothesis que shi shi ZFC bao li de xiongdi buke gouzao wenti;
halting_problem que shi shi computability bao li de xiongdi;
zfc_set_theory / measure_theory / computability_theory que shi shi bie de zhenshi bao.
Shan diao huo gai ming zhexie yilai jiushi cuangai shuju yi qianjiu guo ruo de weici.

**Suoyi chulu shi gai weici**: ba yilai bixu mingzhong benbao muban biao fangkuan wei
yilai bixu mingzhong benbao muban biao UNION xianshi dengji de kua yinyong ming jihe extra.
extra shi **zhengju weizhi**: ta ba zhexie mingzi you ju ke yi zhe jian shi bian cheng
ke jian, ke shenji de shuru.

## Chengshi bianjie

- Ben wenjian **bu chengsheng** xiufu hou de mingti he yuan mingti yiyang qiang.
  Ta yange geng ruo: closed_nil_iff.
- Ben wenjian **bu chengsheng** kua yinyong ming ben shen ke gouzao huo you yiyi.
- 0 axiom / 0 sorry / 0 admit.
- Shangyou na 12 tiao axiom shi **jia mingti**, bu shi zheng bu chulai.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Lattice.Lv00.AxiomDischargeJia

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
  forall d, d ∈ u.dependencies -> TemplateNameAvailable templates d

/-- **Shangyou yuan weici**. -/
def PackageDependenciesValid (pkg : AxiomPackageInstance) : Prop :=
  forall u, u ∈ pkg.unconstructibles -> DependenciesSatisfied pkg.templates u

/-- He fa ming ji he = ben bao mu ban biao UNION extra. -/
def LegalNames (pkg : AxiomPackageInstance) (extra : List String) : List String :=
  templateNames pkg.templates ++ extra

/-- Dan ge wen ti zai bi bao yi yi xia zi qia. -/
def DependenciesClosed (pkg : AxiomPackageInstance) (extra : List String)
    (u : UnconstructibleProblem) : Prop :=
  forall d, d ∈ u.dependencies -> d ∈ LegalNames pkg extra

/-- Bao zai bi bao yi yi xia yi lai zi qia. -/
def PackageDependenciesClosed (pkg : AxiomPackageInstance) (extra : List String) : Prop :=
  forall u, u ∈ pkg.unconstructibles -> DependenciesClosed pkg extra u



/-! ## 3. 12 ge zhenshi bao de shuju (zhu zi lai zi shangyou Instances_*.lean)

Bu ke gou zao wen ti biao zhu tiao banyun, dependencies liebiao **zhu zi baoliu**,
**bu zuo renhe shan gai** -- zhe zheng shi gai weici er fei gai shuju de tixian. -/
/-- computability_theory de 55 tiao mu ban ming (shangyou computabilityTheoryTemplateNames). -/
def computabilityTheoryTemplateNames : List String :=
  [ "zero_function", "successor_function", "projection_function", "composition",
    "primitive_recursion", "minimization_operator", "universal_turing_machine", "kleene_T_predicate",
    "result_extraction", "kleene_normal_form", "smn_theorem", "kleene_recursion_theorem",
    "rice_theorem", "computable_set", "computably_enumerable_set", "halting_set_K",
    "complement_halting_set", "many_one_reducibility", "turing_reducibility", "turing_equivalence",
    "turing_degree", "turing_jump", "sigma_1_set", "pi_1_set",
    "sigma_n_set", "pi_n_set", "delta_n_set", "post_theorem",
    "cantor_pairing", "cantor_unpairing", "godel_numbering", "program_enumeration",
    "diagonalization", "oracle_turing_machine", "relative_computability", "finite_injury_priority",
    "infinite_injury_priority", "primitive_addition", "primitive_multiplication", "primitive_exponentiation",
    "primitive_factorial", "primitive_predecessor", "primitive_subtraction", "primitive_sign",
    "primitive_absolute_difference", "bounded_minimization", "bounded_existential", "bounded_universal",
    "ackermann_function", "busy_beaver_function", "kolmogorov_complexity", "martin_lof_randomness_test",
    "friedberg_muchnik_theorem", "computable_real_number", "computable_function_on_reals" ]

/-- computability_theory de mu ban biao. -/
def computabilityTheoryTemplates : List PackageTemplate := mkTemplates computabilityTheoryTemplateNames 2 "computability_theory"

/-- computability_theory de 14 tiao bu ke gou zao wen ti. -/
def computabilityTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "halting_problem", reducesTo := "unspecified", dependencies := ["universal_turing_machine", "diagonalization", "godel_numbering"],
      externalRef := "upstream", greenVerified := true },
    { name := "rice_theorem_undecidability", reducesTo := "unspecified", dependencies := ["kleene_recursion_theorem", "program_enumeration", "halting_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "totality_problem", reducesTo := "unspecified", dependencies := ["rice_theorem_undecidability", "sigma_n_set"],
      externalRef := "upstream", greenVerified := true },
    { name := "program_equivalence_problem", reducesTo := "unspecified", dependencies := ["rice_theorem_undecidability", "program_enumeration"],
      externalRef := "upstream", greenVerified := true },
    { name := "post_correspondence_problem", reducesTo := "unspecified", dependencies := ["universal_turing_machine", "halting_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "hilberts_tenth_problem", reducesTo := "unspecified", dependencies := ["minimization_operator", "primitive_recursion", "halting_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "word_problem_for_groups", reducesTo := "unspecified", dependencies := ["universal_turing_machine", "halting_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "kolmogorov_complexity_exact", reducesTo := "unspecified", dependencies := ["diagonalization", "universal_turing_machine", "program_enumeration"],
      externalRef := "upstream", greenVerified := true },
    { name := "busy_beaver_values", reducesTo := "unspecified", dependencies := ["halting_problem", "universal_turing_machine"],
      externalRef := "upstream", greenVerified := true },
    { name := "entscheidungsproblem", reducesTo := "unspecified", dependencies := ["halting_problem", "godel_numbering"],
      externalRef := "upstream", greenVerified := true },
    { name := "tiling_problem", reducesTo := "unspecified", dependencies := ["halting_problem", "post_correspondence_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "mortal_matrix_problem", reducesTo := "unspecified", dependencies := ["halting_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "posts_problem_uniform_solution", reducesTo := "unspecified", dependencies := ["finite_injury_priority", "turing_degree", "halting_set_K"],
      externalRef := "upstream", greenVerified := true },
    { name := "zero_of_computable_function", reducesTo := "unspecified", dependencies := ["rice_theorem_undecidability", "halting_problem"],
      externalRef := "upstream", greenVerified := true } ]

/-- computability_theory bao. -/
def computabilityTheoryPackage : AxiomPackageInstance :=
  { name := "computability_theory", version := "1.0.0", templates := computabilityTheoryTemplates,
    unconstructibles := computabilityTheoryUnconstructibles }

theorem computabilityTheory_templateNames_length : computabilityTheoryTemplateNames.length = 55 := rfl

/-- modal_logic de 27 tiao mu ban ming (shangyou modalLogicTemplateNames). -/
def modalLogicTemplateNames : List String :=
  [ "classical_tautology", "modus_ponens", "kripke_schema", "necessitation",
    "possibility_dual", "necessity_dual", "reflexivity_T", "transitivity_4",
    "symmetry_B", "euclidean_5", "seriality_D", "lob_axiom",
    "kripke_frame", "kripke_model", "satisfaction_at_world", "validity_in_frame",
    "modal_modus_tollens", "box_distributes_over_and", "diamond_monotonicity", "modal_negation",
    "knowledge_axiom", "positive_introspection", "negative_introspection", "always_operator",
    "eventually_operator", "next_operator", "until_operator" ]

/-- modal_logic de mu ban biao. -/
def modalLogicTemplates : List PackageTemplate := mkTemplates modalLogicTemplateNames 2 "modal_logic"

/-- modal_logic de 7 tiao bu ke gou zao wen ti. -/
def modalLogicUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "modal_satisfiability_K", reducesTo := "unspecified", dependencies := ["classical_propositional_logic"],
      externalRef := "upstream", greenVerified := true },
    { name := "modal_satisfiability_S4", reducesTo := "unspecified", dependencies := ["modal_satisfiability_K"],
      externalRef := "upstream", greenVerified := true },
    { name := "modal_satisfiability_S5", reducesTo := "unspecified", dependencies := ["classical_propositional_logic"],
      externalRef := "upstream", greenVerified := true },
    { name := "modal_uniform_interpolation", reducesTo := "unspecified", dependencies := ["modal_logic"],
      externalRef := "upstream", greenVerified := true },
    { name := "modal_logic_with_propositional_quantifiers", reducesTo := "unspecified", dependencies := ["second_order_logic"],
      externalRef := "upstream", greenVerified := true },
    { name := "global_satisfiability_S4", reducesTo := "unspecified", dependencies := ["modal_satisfiability_S4"],
      externalRef := "upstream", greenVerified := true },
    { name := "modal_mu_calculus_model_checking", reducesTo := "unspecified", dependencies := ["modal_logic"],
      externalRef := "upstream", greenVerified := true } ]

/-- modal_logic bao. -/
def modalLogicPackage : AxiomPackageInstance :=
  { name := "modal_logic", version := "1.0.0", templates := modalLogicTemplates,
    unconstructibles := modalLogicUnconstructibles }

theorem modalLogic_templateNames_length : modalLogicTemplateNames.length = 27 := rfl

/-- zfc_set_theory de 29 tiao mu ban ming (shangyou zfcSetTheoryTemplateNames). -/
def zfcSetTheoryTemplateNames : List String :=
  [ "extensionality", "pairing", "union", "power_set",
    "infinity", "regularity", "specification", "replacement",
    "choice", "empty_set", "singleton", "ordered_pair",
    "cartesian_product", "binary_union", "binary_intersection", "set_difference",
    "big_intersection", "subset_relation", "epsilon_induction", "transitive_closure",
    "ordinal_successor", "relation", "function", "function_application",
    "image", "inverse_image", "equinumerous", "cardinality",
    "well_order" ]

/-- zfc_set_theory de mu ban biao. -/
def zfcSetTheoryTemplates : List PackageTemplate := mkTemplates zfcSetTheoryTemplateNames 2 "zfc_set_theory"

/-- zfc_set_theory de 10 tiao bu ke gou zao wen ti. -/
def zfcSetTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "continuum_hypothesis", reducesTo := "unspecified", dependencies := ["infinity", "power_set", "cardinality", "choice"],
      externalRef := "upstream", greenVerified := true },
    { name := "generalized_continuum_hypothesis", reducesTo := "unspecified", dependencies := ["continuum_hypothesis", "cardinality", "replacement"],
      externalRef := "upstream", greenVerified := true },
    { name := "axiom_of_choice_independence", reducesTo := "unspecified", dependencies := ["choice", "well_order"],
      externalRef := "upstream", greenVerified := true },
    { name := "inaccessible_cardinal_existence", reducesTo := "unspecified", dependencies := ["cardinality", "power_set", "regularity"],
      externalRef := "upstream", greenVerified := true },
    { name := "suslin_hypothesis", reducesTo := "unspecified", dependencies := ["well_order", "cartesian_product", "infinity"],
      externalRef := "upstream", greenVerified := true },
    { name := "whitehead_problem", reducesTo := "unspecified", dependencies := ["function", "cardinality", "choice"],
      externalRef := "upstream", greenVerified := true },
    { name := "zfc_consistency", reducesTo := "unspecified", dependencies := ["specification", "replacement", "infinity"],
      externalRef := "upstream", greenVerified := true },
    { name := "measurable_cardinal_existence", reducesTo := "unspecified", dependencies := ["cardinality", "power_set", "choice"],
      externalRef := "upstream", greenVerified := true },
    { name := "axiom_of_constructibility", reducesTo := "unspecified", dependencies := ["power_set", "replacement", "infinity"],
      externalRef := "upstream", greenVerified := true },
    { name := "martins_axiom", reducesTo := "unspecified", dependencies := ["choice", "continuum_hypothesis", "cardinality"],
      externalRef := "upstream", greenVerified := true } ]

/-- zfc_set_theory bao. -/
def zfcSetTheoryPackage : AxiomPackageInstance :=
  { name := "zfc_set_theory", version := "1.0.0", templates := zfcSetTheoryTemplates,
    unconstructibles := zfcSetTheoryUnconstructibles }

theorem zfcSetTheory_templateNames_length : zfcSetTheoryTemplateNames.length = 29 := rfl

/-- graph_theory de 70 tiao mu ban ming (shangyou graphTheoryTemplateNames). -/
def graphTheoryTemplateNames : List String :=
  [ "vertex_set", "edge_set", "incidence", "adjacency",
    "vertex_degree", "handshaking_lemma", "maximum_degree", "minimum_degree",
    "walk", "path", "path_length", "distance",
    "connected", "connected_component", "component_count", "vertex_connectivity",
    "cycle", "girth", "circumference", "acyclic",
    "tree", "forest", "spanning_tree", "leaf",
    "subgraph", "induced_subgraph", "complement", "graph_union",
    "graph_intersection", "vertex_deletion", "edge_deletion", "edge_contraction",
    "line_graph", "cartesian_product", "graph_join", "disjoint_union",
    "complete_graph", "empty_graph", "path_graph", "cycle_graph",
    "bipartite", "complete_bipartite", "regular", "planar",
    "eulerian", "hamiltonian", "matching", "maximum_matching",
    "perfect_matching", "vertex_cover", "minimum_vertex_cover", "independent_set",
    "maximum_independent_set", "dominating_set", "vertex_coloring", "chromatic_number",
    "chromatic_polynomial", "edge_coloring", "chromatic_index", "clique",
    "euler_formula_planar", "konigs_theorem", "mengers_theorem", "kuratowskis_theorem",
    "four_color_theorem", "graph_isomorphism", "graph_automorphism", "treewidth",
    "graph_minor", "spectral_properties" ]

/-- graph_theory de mu ban biao. -/
def graphTheoryTemplates : List PackageTemplate := mkTemplates graphTheoryTemplateNames 2 "graph_theory"

/-- graph_theory de 14 tiao bu ke gou zao wen ti. -/
def graphTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "graph_3_coloring", reducesTo := "unspecified", dependencies := ["vertex_coloring", "chromatic_number", "three_colorability"],
      externalRef := "upstream", greenVerified := true },
    { name := "hamiltonian_cycle", reducesTo := "unspecified", dependencies := ["cycle", "hamiltonian", "path"],
      externalRef := "upstream", greenVerified := true },
    { name := "subgraph_isomorphism", reducesTo := "unspecified", dependencies := ["subgraph", "graph_isomorphism", "induced_subgraph"],
      externalRef := "upstream", greenVerified := true },
    { name := "graph_isomorphism_problem", reducesTo := "unspecified", dependencies := ["graph_isomorphism", "graph_automorphism"],
      externalRef := "upstream", greenVerified := true },
    { name := "treewidth_computation", reducesTo := "unspecified", dependencies := ["treewidth", "subgraph", "vertex_deletion"],
      externalRef := "upstream", greenVerified := true },
    { name := "maximum_clique", reducesTo := "unspecified", dependencies := ["clique", "complement", "independent_set"],
      externalRef := "upstream", greenVerified := true },
    { name := "maximum_independent_set_problem", reducesTo := "unspecified", dependencies := ["independent_set", "maximum_independent_set", "vertex_cover"],
      externalRef := "upstream", greenVerified := true },
    { name := "minimum_vertex_cover_problem", reducesTo := "unspecified", dependencies := ["vertex_cover", "minimum_vertex_cover", "maximum_matching"],
      externalRef := "upstream", greenVerified := true },
    { name := "minimum_dominating_set", reducesTo := "unspecified", dependencies := ["dominating_set", "adjacency"],
      externalRef := "upstream", greenVerified := true },
    { name := "graph_k_coloring", reducesTo := "unspecified", dependencies := ["vertex_coloring", "chromatic_number", "bipartite"],
      externalRef := "upstream", greenVerified := true },
    { name := "steiner_tree", reducesTo := "unspecified", dependencies := ["spanning_tree", "tree", "path"],
      externalRef := "upstream", greenVerified := true },
    { name := "feedback_vertex_set", reducesTo := "unspecified", dependencies := ["acyclic", "cycle", "vertex_deletion"],
      externalRef := "upstream", greenVerified := true },
    { name := "graph_homomorphism", reducesTo := "unspecified", dependencies := ["vertex_coloring", "complete_graph", "adjacency"],
      externalRef := "upstream", greenVerified := true },
    { name := "bandwidth_minimization", reducesTo := "unspecified", dependencies := ["adjacency", "path_length"],
      externalRef := "upstream", greenVerified := true } ]

/-- graph_theory bao. -/
def graphTheoryPackage : AxiomPackageInstance :=
  { name := "graph_theory", version := "1.0.0", templates := graphTheoryTemplates,
    unconstructibles := graphTheoryUnconstructibles }

theorem graphTheory_templateNames_length : graphTheoryTemplateNames.length = 70 := rfl

/-- measure_theory de 66 tiao mu ban ming (shangyou measureTheoryTemplateNames). -/
def measureTheoryTemplateNames : List String :=
  [ "sigma_algebra_contains_X", "sigma_algebra_complement", "sigma_algebra_countable_union", "sigma_algebra_countable_intersection",
    "sigma_algebra_contains_empty", "sigma_algebra_set_difference", "sigma_algebra_symmetric_difference", "measure_null_empty_set",
    "measure_non_negativity", "measure_countable_additivity", "measure_finite_additivity", "measure_monotonicity",
    "measure_countable_subadditivity", "measure_continuity_from_below", "measure_continuity_from_above", "outer_measure_null_empty",
    "outer_measure_monotonicity", "outer_measure_countable_subadditivity", "caratheodory_measurability", "measurable_sets_form_sigma_algebra",
    "outer_measure_restriction_complete", "null_set", "null_set_subset_measurable", "almost_everywhere",
    "measure_completion", "sigma_finite_measure", "semifinite_measure", "localizable_measure",
    "signed_measure", "hahn_decomposition", "jordan_decomposition", "total_variation_measure",
    "complex_measure", "absolute_continuity", "mutual_singularity", "radon_nikodym_theorem",
    "lebesgue_decomposition", "product_sigma_algebra", "product_measure", "fubini_theorem",
    "tonelli_theorem", "monotone_convergence_theorem", "fatou_lemma", "dominated_convergence_theorem",
    "uniform_integrability", "pre_measure", "caratheodory_outer_measure_construction", "caratheodory_extension_theorem",
    "dynkin_pi_lambda_theorem", "counting_measure", "dirac_measure", "lebesgue_measure_interval",
    "lebesgue_measure_rn", "borel_sigma_algebra", "hausdorff_measure", "hausdorff_dimension",
    "pushforward_measure", "measure_restriction", "lp_norm", "linf_norm",
    "holder_inequality", "minkowski_inequality", "jensen_inequality", "probability_measure",
    "conditional_expectation", "sigma_algebra_independence" ]

/-- measure_theory de mu ban biao. -/
def measureTheoryTemplates : List PackageTemplate := mkTemplates measureTheoryTemplateNames 2 "measure_theory"

/-- measure_theory de 9 tiao bu ke gou zao wen ti. -/
def measureTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "vitali_set_non_measurable", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "lebesgue_measure_rn"],
      externalRef := "upstream", greenVerified := true },
    { name := "banach_tarski_paradox", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "lebesgue_measure_rn"],
      externalRef := "upstream", greenVerified := true },
    { name := "universal_measure_on_all_subsets", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "lebesgue_measure_rn"],
      externalRef := "upstream", greenVerified := true },
    { name := "all_sets_measurable_consistency", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "measure_null_empty_set"],
      externalRef := "upstream", greenVerified := true },
    { name := "hausdorff_dimension_computation", reducesTo := "unspecified", dependencies := ["computability_theory", "hausdorff_measure"],
      externalRef := "upstream", greenVerified := true },
    { name := "measure_space_isomorphism_classification", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "measure_countable_additivity"],
      externalRef := "upstream", greenVerified := true },
    { name := "measure_extension_uniqueness_without_sigma_finite", reducesTo := "unspecified", dependencies := ["caratheodory_extension_theorem", "sigma_finite_measure"],
      externalRef := "upstream", greenVerified := true },
    { name := "riemann_integrability_decision", reducesTo := "unspecified", dependencies := ["lebesgue_measure_rn", "null_set"],
      externalRef := "upstream", greenVerified := true },
    { name := "non_measurable_set_existence", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "lebesgue_measure_rn"],
      externalRef := "upstream", greenVerified := true } ]

/-- measure_theory bao. -/
def measureTheoryPackage : AxiomPackageInstance :=
  { name := "measure_theory", version := "1.0.0", templates := measureTheoryTemplates,
    unconstructibles := measureTheoryUnconstructibles }

theorem measureTheory_templateNames_length : measureTheoryTemplateNames.length = 66 := rfl

/-- functional_analysis de 37 tiao mu ban ming (shangyou functionalAnalysisTemplateNames). -/
def functionalAnalysisTemplateNames : List String :=
  [ "normed_vector_space", "banach_space", "dual_space", "hahn_banach_theorem",
    "separation_theorem", "inner_product_space", "hilbert_space", "orthonormal_basis",
    "projection_theorem", "riesz_representation", "parseval_identity", "bounded_linear_operator",
    "operator_norm", "operator_adjoint", "compact_operator", "self_adjoint_operator",
    "unitary_operator", "spectrum_of_operator", "spectral_radius", "resolvent_set",
    "spectral_theorem", "eigenvalue_problem", "spectral_decomposition", "banach_algebra",
    "c_star_algebra", "von_neumann_algebra", "gel_fand_naimark", "functional_calculus",
    "sobolev_space", "weak_derivative", "trace_theorem", "embedding_theorem",
    "test_function_space", "distribution_theory", "fourier_transform", "convolution",
    "singularity_theorem" ]

/-- functional_analysis de mu ban biao. -/
def functionalAnalysisTemplates : List PackageTemplate := mkTemplates functionalAnalysisTemplateNames 2 "functional_analysis"

/-- functional_analysis de 7 tiao bu ke gou zao wen ti. -/
def functionalAnalysisUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "invariant_subspace_problem", reducesTo := "unspecified", dependencies := ["bounded_linear_operator", "hilbert_space", "banach_space"],
      externalRef := "upstream", greenVerified := true },
    { name := "approximation_property", reducesTo := "unspecified", dependencies := ["banach_space", "bounded_linear_operator", "operator_norm"],
      externalRef := "upstream", greenVerified := true },
    { name := "komornik_loreti_constant", reducesTo := "unspecified", dependencies := ["banach_space", "fourier_transform", "operator_norm"],
      externalRef := "upstream", greenVerified := true },
    { name := "boundedness_of_singular_integrals", reducesTo := "unspecified", dependencies := ["operator_norm", "bounded_linear_operator", "lp_space"],
      externalRef := "upstream", greenVerified := true },
    { name := "spectral_theorem_self_adjoint", reducesTo := "unspecified", dependencies := ["spectral_theorem", "self_adjoint_operator", "spectral_decomposition"],
      externalRef := "upstream", greenVerified := true },
    { name := "existence_of_complement", reducesTo := "unspecified", dependencies := ["banach_space", "projection_theorem", "dual_space"],
      externalRef := "upstream", greenVerified := true },
    { name := "continuous_function_algebra", reducesTo := "unspecified", dependencies := ["c_star_algebra", "banach_algebra", "functional_calculus"],
      externalRef := "upstream", greenVerified := true } ]

/-- functional_analysis bao. -/
def functionalAnalysisPackage : AxiomPackageInstance :=
  { name := "functional_analysis", version := "1.0.0", templates := functionalAnalysisTemplates,
    unconstructibles := functionalAnalysisUnconstructibles }

theorem functionalAnalysis_templateNames_length : functionalAnalysisTemplateNames.length = 37 := rfl

/-- probability_theory de 87 tiao mu ban ming (shangyou probabilityTheoryTemplateNames). -/
def probabilityTheoryTemplateNames : List String :=
  [ "kolmogorov_non_negativity", "kolmogorov_unit_measure", "kolmogorov_sigma_additivity", "prob_empty_set_zero",
    "prob_bounds", "prob_complement_rule", "prob_monotonicity", "prob_union_two",
    "boole_inequality", "bonferroni_inequality", "prob_continuity_below", "prob_continuity_above",
    "inclusion_exclusion", "partition_formula", "prob_finite_additivity", "conditional_prob_def",
    "multiplication_rule", "chain_rule", "law_total_probability", "bayes_theorem",
    "bayes_theorem_partition", "independence_pairwise", "independence_mutual", "independence_conditional",
    "independence_complement", "independence_trivial", "independence_pairwise_not_mutual", "independence_sigma_algebras",
    "independence_random_variables", "random_variable_def", "distribution_function", "random_variable_discrete",
    "random_variable_continuous", "pmf_def", "pdf_def", "indicator_random_variable",
    "random_variable_function", "joint_distribution", "marginal_distribution", "random_variable_transformation",
    "quantile_function", "expected_value_def", "expected_value_linearity", "expected_value_indicator",
    "expected_value_nonnegativity", "expected_value_monotonicity", "variance_def", "variance_linear_transform",
    "covariance_def", "correlation_coefficient", "cauchy_schwarz_inequality", "convergence_almost_sure",
    "convergence_probability", "convergence_Lp", "convergence_distribution", "monotone_convergence",
    "dominated_convergence", "fatou_lemma", "convergence_hierarchy", "weak_law_large_numbers",
    "strong_law_large_numbers", "kolmogorov_three_series", "borel_cantelli", "central_limit_theorem",
    "lindeberg_feller_clt", "berry_esseen_theorem", "characteristic_function_convergence", "distribution_bernoulli",
    "distribution_binomial", "distribution_poisson", "distribution_geometric", "distribution_uniform_continuous",
    "distribution_exponential", "distribution_normal", "distribution_gamma", "distribution_beta",
    "distribution_chi_squared", "stochastic_process_def", "filtration_def", "martingale_def",
    "markov_property", "stopping_time_def", "optional_stopping_theorem", "characteristic_function_def",
    "characteristic_function_properties", "characteristic_function_uniqueness", "characteristic_function_inversion" ]

/-- probability_theory de mu ban biao. -/
def probabilityTheoryTemplates : List PackageTemplate := mkTemplates probabilityTheoryTemplateNames 2 "probability_theory"

/-- probability_theory de 8 tiao bu ke gou zao wen ti. -/
def probabilityTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "non_measurable_set_existence", reducesTo := "unspecified", dependencies := ["zfc_set_theory", "measure_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "vitali_set_non_measurable", reducesTo := "unspecified", dependencies := ["axiom_of_choice"],
      externalRef := "upstream", greenVerified := true },
    { name := "banach_tarski_paradox", reducesTo := "unspecified", dependencies := ["axiom_of_choice"],
      externalRef := "upstream", greenVerified := true },
    { name := "solovay_all_sets_measurable", reducesTo := "unspecified", dependencies := ["zfc_set_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "slln_without_sigma_additivity", reducesTo := "unspecified", dependencies := ["kolmogorov_sigma_additivity"],
      externalRef := "upstream", greenVerified := true },
    { name := "exact_continuous_simulation", reducesTo := "unspecified", dependencies := [],
      externalRef := "upstream", greenVerified := true },
    { name := "exact_probability_computation", reducesTo := "unspecified", dependencies := ["computational_complexity_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "regular_conditional_probability_general", reducesTo := "unspecified", dependencies := ["measure_theory"],
      externalRef := "upstream", greenVerified := true } ]

/-- probability_theory bao. -/
def probabilityTheoryPackage : AxiomPackageInstance :=
  { name := "probability_theory", version := "1.0.0", templates := probabilityTheoryTemplates,
    unconstructibles := probabilityTheoryUnconstructibles }

theorem probabilityTheory_templateNames_length : probabilityTheoryTemplateNames.length = 87 := rfl

/-- information_theory de 106 tiao mu ban ming (shangyou informationTheoryTemplateNames). -/
def informationTheoryTemplateNames : List String :=
  [ "entropy_non_negativity", "entropy_continuity", "entropy_maximum_uniform", "entropy_additivity",
    "entropy_expansibility", "shannon_entropy", "binary_entropy", "entropy_deterministic_zero",
    "entropy_concavity", "entropy_schur_concavity", "entropy_grouping_property", "fano_inequality",
    "data_processing_inequality", "joint_entropy", "conditional_entropy", "entropy_chain_rule",
    "joint_entropy_bounds", "conditional_entropy_non_negativity", "conditioning_reduces_entropy", "independence_entropy_equivalence",
    "mutual_information", "mutual_information_symmetry", "mutual_information_non_negativity", "mutual_information_independence",
    "mutual_information_kl_divergence", "conditional_mutual_information", "mutual_information_chain_rule", "interaction_information",
    "kl_divergence", "kl_divergence_non_negativity", "kl_divergence_asymmetry", "kl_divergence_convexity",
    "cross_entropy", "cross_entropy_lower_bound", "jensen_shannon_divergence", "source_coding_theorem",
    "kraft_inequality", "optimal_code_length", "huffman_optimality", "shannon_fano_coding",
    "arithmetic_coding", "asymptotic_equipartition_property", "typical_set", "noisy_channel_coding_theorem",
    "channel_capacity", "channel_capacity_converse", "bsc_capacity", "bec_capacity",
    "shannon_hartley_theorem", "awgn_channel_capacity", "feedback_no_capacity_increase", "fano_channel_coding",
    "rate_distortion_function", "rate_distortion_theorem", "rate_distortion_convexity", "distortion_rate_function",
    "shannon_lower_bound", "binary_rate_distortion", "gaussian_rate_distortion", "differential_entropy",
    "differential_entropy_can_be_negative", "gaussian_maximizes_differential_entropy", "gaussian_differential_entropy", "joint_differential_entropy",
    "conditional_differential_entropy", "continuous_mutual_information", "discrete_memoryless_channel", "binary_symmetric_channel",
    "binary_erasure_channel", "z_channel", "awgn_channel", "broadcast_channel",
    "multiple_access_channel", "relay_channel", "network_coding", "max_flow_min_cut_information",
    "slepian_wolf_coding", "wyner_ziv_coding", "gelfand_pinsker_theorem", "kolmogorov_complexity",
    "kolmogorov_uncomputability", "kolmogorov_incompressibility", "kolmogorov_entropy_relation", "algorithmic_mutual_information",
    "solomonoff_induction", "compute_entropy", "compute_joint_entropy", "compute_conditional_entropy",
    "compute_mutual_information", "compute_kl_divergence", "compute_cross_entropy", "compute_channel_capacity",
    "compute_rate_distortion", "compute_differential_entropy", "construct_typical_set", "construct_huffman_code",
    "construct_channel_code", "entropy_power_inequality", "log_sum_inequality", "shearers_lemma",
    "hans_inequality", "mrs_gerbers_lemma", "csiszar_sum_identity", "viterbi_decoding",
    "bcjr_decoding", "blahut_arimoto_algorithm" ]

/-- information_theory de mu ban biao. -/
def informationTheoryTemplates : List PackageTemplate := mkTemplates informationTheoryTemplateNames 2 "information_theory"

/-- information_theory de 8 tiao bu ke gou zao wen ti. -/
def informationTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "kolmogorov_complexity_computation", reducesTo := "unspecified", dependencies := ["turing_machine_universality", "program_termination"],
      externalRef := "upstream", greenVerified := true },
    { name := "channel_capacity_general_channel", reducesTo := "unspecified", dependencies := ["channel_model_specification"],
      externalRef := "upstream", greenVerified := true },
    { name := "optimal_prefix_code_construction", reducesTo := "unspecified", dependencies := ["source_distribution"],
      externalRef := "upstream", greenVerified := true },
    { name := "rate_distortion_function_computation", reducesTo := "unspecified", dependencies := ["source_distribution", "distortion_measure"],
      externalRef := "upstream", greenVerified := true },
    { name := "minimum_entropy_decoding", reducesTo := "unspecified", dependencies := ["channel_model", "received_signal"],
      externalRef := "upstream", greenVerified := true },
    { name := "network_coding_capacity_general", reducesTo := "unspecified", dependencies := ["network_topology", "channel_models"],
      externalRef := "upstream", greenVerified := true },
    { name := "information_theoretic_security_verification", reducesTo := "unspecified", dependencies := ["cryptographic_protocol", "adversary_model"],
      externalRef := "upstream", greenVerified := true },
    { name := "solomonoff_prior_approximation", reducesTo := "unspecified", dependencies := ["universal_turing_machine"],
      externalRef := "upstream", greenVerified := true } ]

/-- information_theory bao. -/
def informationTheoryPackage : AxiomPackageInstance :=
  { name := "information_theory", version := "1.0.0", templates := informationTheoryTemplates,
    unconstructibles := informationTheoryUnconstructibles }

theorem informationTheory_templateNames_length : informationTheoryTemplateNames.length = 106 := rfl

/-- linear_algebra de 90 tiao mu ban ming (shangyou linearAlgebraTemplateNames). -/
def linearAlgebraTemplateNames : List String :=
  [ "vector_addition_associativity", "vector_addition_commutativity", "vector_additive_identity", "vector_additive_inverse",
    "scalar_multiplication_compatibility", "scalar_identity", "scalar_distributivity_vector", "scalar_distributivity_field",
    "zero_scalar_annihilates", "zero_vector_annihilates", "negation_via_scalar", "zero_divisor_property",
    "vector_subtraction", "scalar_subtraction", "subspace_test", "span",
    "linear_independence", "linear_dependence", "quotient_space", "direct_sum",
    "basis", "dimension", "finite_dimensional", "infinite_dimensional",
    "dimension_theorem", "rank_nullity_theorem", "basis_extension", "steinitz_exchange",
    "linear_map", "linear_map_composition", "kernel", "image",
    "injectivity_criterion", "surjectivity_criterion", "isomorphism", "hom_space",
    "endomorphism_ring", "general_linear_group", "matrix", "matrix_addition",
    "matrix_multiplication", "scalar_matrix_multiplication", "matrix_transpose", "identity_matrix",
    "zero_matrix", "matrix_inverse", "matrix_trace", "matrix_rank",
    "determinant", "determinant_multiplicative", "determinant_transpose", "cofactor_expansion",
    "cramers_rule", "adjugate_matrix", "eigenvalue", "eigenvector",
    "characteristic_polynomial", "eigenspace", "algebraic_multiplicity", "geometric_multiplicity",
    "diagonalizability", "cayley_hamilton", "inner_product", "conjugate_symmetry",
    "inner_product_linearity", "positive_definiteness", "norm_from_inner_product", "orthogonality",
    "orthogonal_complement", "gram_schmidt", "dual_space", "dual_basis",
    "double_dual", "annihilator", "tensor_product", "tensor_universal_property",
    "exterior_product", "symmetric_product", "jordan_normal_form", "rational_canonical_form",
    "singular_value_decomposition", "qr_decomposition", "lu_decomposition", "spectral_theorem",
    "direct_product", "external_direct_sum", "induced_quotient_map", "pullback",
    "pushout", "multilinear_map" ]

/-- linear_algebra de mu ban biao. -/
def linearAlgebraTemplates : List PackageTemplate := mkTemplates linearAlgebraTemplateNames 2 "linear_algebra"

/-- linear_algebra de 8 tiao bu ke gou zao wen ti. -/
def linearAlgebraUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "matrix_mortality_problem", reducesTo := "unspecified", dependencies := ["matrix_multiplication", "zero_matrix", "matrix"],
      externalRef := "upstream", greenVerified := true },
    { name := "matrix_semigroup_membership", reducesTo := "unspecified", dependencies := ["matrix_multiplication", "matrix", "identity_matrix"],
      externalRef := "upstream", greenVerified := true },
    { name := "matrix_semigroup_equality", reducesTo := "unspecified", dependencies := ["matrix_multiplication", "matrix"],
      externalRef := "upstream", greenVerified := true },
    { name := "matrix_nilpotency_problem", reducesTo := "unspecified", dependencies := ["matrix_multiplication", "zero_matrix", "matrix", "matrix_mortality_problem"],
      externalRef := "upstream", greenVerified := true },
    { name := "basis_existence_infinite_dimensional", reducesTo := "unspecified", dependencies := ["basis", "infinite_dimensional", "basis_extension"],
      externalRef := "upstream", greenVerified := true },
    { name := "vector_space_isomorphism_problem", reducesTo := "unspecified", dependencies := ["isomorphism", "dimension", "basis", "linear_map"],
      externalRef := "upstream", greenVerified := true },
    { name := "tensor_rank_problem", reducesTo := "unspecified", dependencies := ["tensor_product", "multilinear_map"],
      externalRef := "upstream", greenVerified := true },
    { name := "eigenvalue_sensitivity_nonnormal", reducesTo := "unspecified", dependencies := ["eigenvalue", "characteristic_polynomial", "algebraic_multiplicity", "geometric_multiplicity"],
      externalRef := "upstream", greenVerified := true } ]

/-- linear_algebra bao. -/
def linearAlgebraPackage : AxiomPackageInstance :=
  { name := "linear_algebra", version := "1.0.0", templates := linearAlgebraTemplates,
    unconstructibles := linearAlgebraUnconstructibles }

theorem linearAlgebra_templateNames_length : linearAlgebraTemplateNames.length = 90 := rfl

/-- projective_geometry de 38 tiao mu ban ming (shangyou projectiveGeometryTemplateNames). -/
def projectiveGeometryTemplateNames : List String :=
  [ "join_of_two_points", "meet_of_two_lines", "existence_of_triangle_projective", "existence_of_complete_quadrangle",
    "line_has_three_points", "point_has_three_lines", "veblen_axiom", "desargues_theorem",
    "pappus_hexagon_theorem", "line_through_point_meeting_line", "harmonic_conjugate", "intersection_of_line_with_line",
    "cross_ratio", "perspectivity", "diagonal_triangle_of_quadrangle", "dual_configuration",
    "pole_polar_construction", "projectivity", "fundamental_theorem_uniqueness", "collineation",
    "correlation", "elation", "conic_through_five_points", "tangent_to_conic",
    "pascal_theorem", "brianchon_theorem", "field_addition_geometric", "field_multiplication_geometric",
    "field_additive_inverse", "field_multiplicative_inverse", "join_point_line_to_plane", "meet_of_two_planes",
    "desargues_provable_in_3d", "dual_desargues_theorem", "harmonic_conjugate_uniqueness", "complete_quadrilateral_theorem",
    "projectivity_uniqueness", "cross_ratio_invariance" ]

/-- projective_geometry de mu ban biao. -/
def projectiveGeometryTemplates : List PackageTemplate := mkTemplates projectiveGeometryTemplateNames 2 "projective_geometry"

/-- projective_geometry de 7 tiao bu ke gou zao wen ti. -/
def projectiveGeometryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "existence_of_finite_projective_plane_non_prime_power", reducesTo := "unspecified", dependencies := ["combinatorial_design_theory", "finite_field_theory", "bruck_ryser_chowla_theorem"],
      externalRef := "upstream", greenVerified := true },
    { name := "classification_of_finite_projective_planes", reducesTo := "unspecified", dependencies := ["non_desarguesian_plane_construction", "translation_plane_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "coordinate_field_of_non_desarguesian_plane", reducesTo := "unspecified", dependencies := ["desargues_theorem_failure", "alternative_division_ring"],
      externalRef := "upstream", greenVerified := true },
    { name := "constructing_midpoint_with_straightedge_only", reducesTo := "unspecified", dependencies := ["harmonic_conjugate", "projective_to_euclidean_specialization"],
      externalRef := "upstream", greenVerified := true },
    { name := "trisection_of_angle_projective", reducesTo := "unspecified", dependencies := ["cross_ratio", "field_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "pappus_implies_field_commutativity", reducesTo := "unspecified", dependencies := ["desargues_theorem", "coordinate_field_construction", "pappus_hexagon_theorem"],
      externalRef := "upstream", greenVerified := true },
    { name := "order_of_largest_unknown_finite_projective_plane", reducesTo := "unspecified", dependencies := ["bruck_ryser_chowla_theorem", "computational_search"],
      externalRef := "upstream", greenVerified := true } ]

/-- projective_geometry bao. -/
def projectiveGeometryPackage : AxiomPackageInstance :=
  { name := "projective_geometry", version := "1.0.0", templates := projectiveGeometryTemplates,
    unconstructibles := projectiveGeometryUnconstructibles }

theorem projectiveGeometry_templateNames_length : projectiveGeometryTemplateNames.length = 38 := rfl

/-- order_theory de 32 tiao mu ban ming (shangyou orderTheoryTemplateNames). -/
def orderTheoryTemplateNames : List String :=
  [ "reflexivity", "antisymmetry", "transitivity", "least_element",
    "greatest_element", "minimal_element", "maximal_element", "upper_bound",
    "lower_bound", "least_upper_bound", "greatest_lower_bound", "totality",
    "well_foundedness", "well_order", "monotone_function", "antitone_function",
    "order_embedding", "order_isomorphism", "dual_order", "product_order",
    "induced_suborder", "ordinal_sum", "strict_order", "covering_relation",
    "chain", "antichain", "interval", "hasse_diagram",
    "zorn_lemma", "dilworth_decomposition", "knaster_tarski_fixed_point", "szpilrajn_extension" ]

/-- order_theory de mu ban biao. -/
def orderTheoryTemplates : List PackageTemplate := mkTemplates orderTheoryTemplateNames 2 "order_theory"

/-- order_theory de 8 tiao bu ke gou zao wen ti. -/
def orderTheoryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "poset_dimension", reducesTo := "unspecified", dependencies := ["partial_order", "realizer"],
      externalRef := "upstream", greenVerified := true },
    { name := "counting_linear_extensions", reducesTo := "unspecified", dependencies := ["partial_order", "topological_sort"],
      externalRef := "upstream", greenVerified := true },
    { name := "poset_isomorphism", reducesTo := "unspecified", dependencies := ["partial_order", "graph_isomorphism"],
      externalRef := "upstream", greenVerified := true },
    { name := "infinite_poset_width", reducesTo := "unspecified", dependencies := ["partial_order", "antichain", "zfc_set_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "order_automorphism_group", reducesTo := "unspecified", dependencies := ["partial_order", "group_theory"],
      externalRef := "upstream", greenVerified := true },
    { name := "poset_convex_realizability", reducesTo := "unspecified", dependencies := ["partial_order", "convex_geometry"],
      externalRef := "upstream", greenVerified := true },
    { name := "poset_dimension_at_least_4", reducesTo := "unspecified", dependencies := ["partial_order", "poset_dimension"],
      externalRef := "upstream", greenVerified := true },
    { name := "chain_partition_minimization", reducesTo := "unspecified", dependencies := ["partial_order", "dilworth_theorem"],
      externalRef := "upstream", greenVerified := true } ]

/-- order_theory bao. -/
def orderTheoryPackage : AxiomPackageInstance :=
  { name := "order_theory", version := "1.0.0", templates := orderTheoryTemplates,
    unconstructibles := orderTheoryUnconstructibles }

theorem orderTheory_templateNames_length : orderTheoryTemplateNames.length = 32 := rfl

/-- affine_geometry de 56 tiao mu ban ming (shangyou affineGeometryTemplateNames). -/
def affineGeometryTemplateNames : List String :=
  [ "line_through_two_points", "line_has_two_points", "existence_of_triangle", "existence_of_affine_frame_3d",
    "parallel_through_point", "parallelism_reflexive", "parallelism_transitive", "parallelism_no_intersection",
    "point_subtraction", "point_translation", "vector_addition_associative", "vector_addition_commutative",
    "zero_vector_exists", "vector_negation", "scalar_multiplication", "scalar_distributivity_vectors",
    "scalar_distributivity_scalars", "scalar_multiplication_associative", "scalar_unit", "subtraction_identity",
    "subtraction_chain", "translation_subtraction_compat", "subtraction_translation_compat", "affine_combination_two",
    "midpoint", "centroid_three_points", "general_barycenter", "affine_combination_associative",
    "affine_combination_commutative", "affine_combination_idempotent", "affine_map_preserves_combination", "translation_map",
    "affine_map_decomposition", "affine_map_preserves_parallelism", "affine_map_preserves_ratio", "affine_map_preserves_midpoint",
    "affine_map_preserves_centroid", "affine_map_preserves_barycenter", "desargues_theorem_affine", "pappus_theorem_affine",
    "affine_subspace_check", "affine_span_two_points", "affine_span_three_points", "affine_subspace_dimension",
    "affine_subspaces_parallel", "simple_ratio", "thales_intercept_theorem", "ceva_theorem",
    "menelaus_theorem", "parallelogram_fourth_vertex", "parallelogram_law", "parallelogram_diagonal_bisect",
    "affine_map_preserves_parallelogram", "projective_completion", "line_at_infinity", "affine_patch_from_projective" ]

/-- affine_geometry de mu ban biao. -/
def affineGeometryTemplates : List PackageTemplate := mkTemplates affineGeometryTemplateNames 2 "affine_geometry"

/-- affine_geometry de 7 tiao bu ke gou zao wen ti. -/
def affineGeometryUnconstructibles : List UnconstructibleProblem :=
  [
    { name := "perpendicular_bisector", reducesTo := "unspecified", dependencies := ["affine_geometry", "euclidean_plane"],
      externalRef := "upstream", greenVerified := true },
    { name := "angle_trisection", reducesTo := "unspecified", dependencies := ["affine_geometry", "euclidean_plane"],
      externalRef := "upstream", greenVerified := true },
    { name := "circle_construction", reducesTo := "unspecified", dependencies := ["affine_geometry", "euclidean_plane"],
      externalRef := "upstream", greenVerified := true },
    { name := "finite_affine_plane_non_prime_power", reducesTo := "unspecified", dependencies := ["affine_geometry", "combinatorics", "projective_geometry"],
      externalRef := "upstream", greenVerified := true },
    { name := "non_desarguesian_classification", reducesTo := "unspecified", dependencies := ["affine_geometry", "projective_geometry"],
      externalRef := "upstream", greenVerified := true },
    { name := "metric_recovery_from_affine", reducesTo := "unspecified", dependencies := ["affine_geometry", "euclidean_plane"],
      externalRef := "upstream", greenVerified := true },
    { name := "area_computation", reducesTo := "unspecified", dependencies := ["affine_geometry", "euclidean_plane"],
      externalRef := "upstream", greenVerified := true } ]

/-- affine_geometry bao. -/
def affineGeometryPackage : AxiomPackageInstance :=
  { name := "affine_geometry", version := "1.0.0", templates := affineGeometryTemplates,
    unconstructibles := affineGeometryUnconstructibles }

theorem affineGeometry_templateNames_length : affineGeometryTemplateNames.length = 56 := rfl


/-! ## 4. Xiufu weici: yi lai bi bao (dependency closure)

He fa ming ji he = ben bao mu ban biao UNION xianshi dengji de kua yinyong ming extra.
extra shi **zhengju weizhi**.

Zhu yi **Ke jueding xing she ji**: `String` shi **wu xian** yu, suo yi
`forall d : String, d ∈ l -> P d` zai Lean li **mei you** `Decidable` shili,
`decide` hui bao unable to synthesize Decidable.
Yin ci ben wenjian ba he xin pan ding xie cheng **Bool ban** (`*B`),
zai yong `*_iff` yin li **qiao jie** hui Prop ban.
Zhe yang: (a) pan ding bi ding ke jueding; (b) bu yi lai `native_decide`;
(c) qiao jie yin li jin yong `List.all_eq_true` + `List.contains`, bu yin ru gongli. -/

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
  simp [PackageDependenciesClosed, PackageDependenciesValid, DependenciesClosed, DependenciesSatisfied, TemplateNameAvailable, LegalNames]

/-- **Dan diao xing**: kuo da extra dan diao baochi bi bao zi qia. -/
theorem dependenciesClosed_mono {pkg : AxiomPackageInstance} {extra extra2 : List String}
    (hsub : ∀ n, n ∈ extra → n ∈ extra2)
    (h : PackageDependenciesClosed pkg extra) :
    PackageDependenciesClosed pkg extra2 := by
  intro u hu d hd
  have h1 : d ∈ LegalNames pkg extra := h u hu d hd
  have h2 : d ∈ templateNames pkg.templates ∨ d ∈ extra :=
    List.mem_append.mp h1
  have h3 : d ∈ templateNames pkg.templates ∨ d ∈ extra2 :=
    h2.elim (fun hx => Or.inl hx) (fun hx => Or.inr (hsub d hx))
  exact List.mem_append.mpr h3

/-- **Bu deng yin li**: ruo mou bao de yi lai ji zheng ti bao han yu extra, ze bi bao zi qia. -/
theorem dependenciesClosed_of_subset {pkg : AxiomPackageInstance} {extra : List String}
    (h : ∀ u, u ∈ pkg.unconstructibles → ∀ d, d ∈ u.dependencies → d ∈ extra) :
    PackageDependenciesClosed pkg extra := by
  intro u hu d hd
  exact List.mem_append.mpr (Or.inr (h u hu d hd))

/-- **Fan li pan ju**: mou bao yuan weici wei jia, dang qie jin dang
cun zai yi tiao bu zai mu ban biao zhong de yi lai. -/
theorem not_valid_iff_bad_dep (pkg : AxiomPackageInstance) :
    (¬ PackageDependenciesValid pkg) ↔
      ∃ u, u ∈ pkg.unconstructibles ∧ ∃ d, d ∈ u.dependencies ∧
        d ∉ templateNames pkg.templates := by
  simp [PackageDependenciesValid, DependenciesSatisfied, TemplateNameAvailable, not_forall, Classical.not_imp]


/-! ## 5. 12 tiao axiom de zhu tiao qingsuan

Dui mei ge bao <X>:

- `not_<X>_orig` : **yuan weici wei jia** (ji shangyou na tiao axiom duanyan de shi jia mingti).
- `<X>_closed`   : **xiufu weici wei zhen**, extra = gai bao de kua yinyong ming ji.
- `<X>_false_but_repairable` : dui zhao + extra fei kong.

Lu jing: xian zai **Bool he xin** shang suan chu jie guo, zai jing `*_iff` qiao jie hui Prop.
**Bu yong `native_decide`.** -/


/-! ### computabilityTheory (computability_theory) -- kua yinyong 3 ge ming, 13 tiao bian

`13 tiao bian` shi shangyou yilai biao li *chu xian ci shu* (13 tiao dependencies tiao mu),
bu shi extra de chang du; extra zhi you 3 ge ming (jian `computabilityTheory_extra_length`). -/

/-- computability_theory de kua yinyong ming ji (ji extra). -/
def computabilityTheoryExtra : List String :=
  [ "halting_problem", "post_correspondence_problem", "rice_theorem_undecidability" ]

theorem computabilityTheory_extra_length : computabilityTheoryExtra.length = 3 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem computabilityTheory_validB_eq_false : packageDependenciesValidB computabilityTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem computabilityTheory_closedB_eq_true : packageDependenciesClosedB computabilityTheoryPackage computabilityTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `computabilityTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_computabilityTheory_orig : ¬ (PackageDependenciesValid computabilityTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [computabilityTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem computabilityTheory_closed : PackageDependenciesClosed computabilityTheoryPackage computabilityTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact computabilityTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem computabilityTheory_false_but_repairable :
    (¬ (PackageDependenciesValid computabilityTheoryPackage)) ∧
      PackageDependenciesClosed computabilityTheoryPackage computabilityTheoryExtra ∧
      computabilityTheoryExtra.length = 3 := by
  exact And.intro not_computabilityTheory_orig (And.intro computabilityTheory_closed computabilityTheory_extra_length)


/-! ### modalLogic (modal_logic) -- kua yinyong 5 ge ming, 7 tiao bian -/

/-- modal_logic de kua yinyong ming ji (ji extra). -/
def modalLogicExtra : List String :=
  [ "classical_propositional_logic", "modal_logic", "modal_satisfiability_K",
    "modal_satisfiability_S4", "second_order_logic" ]

theorem modalLogic_extra_length : modalLogicExtra.length = 5 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem modalLogic_validB_eq_false : packageDependenciesValidB modalLogicPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem modalLogic_closedB_eq_true : packageDependenciesClosedB modalLogicPackage modalLogicExtra = true := rfl

/-- **Qingsuan**: shangyou `modalLogicPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_modalLogic_orig : ¬ (PackageDependenciesValid modalLogicPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [modalLogic_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem modalLogic_closed : PackageDependenciesClosed modalLogicPackage modalLogicExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact modalLogic_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem modalLogic_false_but_repairable :
    (¬ (PackageDependenciesValid modalLogicPackage)) ∧
      PackageDependenciesClosed modalLogicPackage modalLogicExtra ∧
      modalLogicExtra.length = 5 := by
  exact And.intro not_modalLogic_orig (And.intro modalLogic_closed modalLogic_extra_length)


/-! ### zfcSetTheory (zfc_set_theory) -- kua yinyong 1 ge ming, 2 tiao bian -/

/-- zfc_set_theory de kua yinyong ming ji (ji extra). -/
def zfcSetTheoryExtra : List String :=
  [ "continuum_hypothesis" ]

theorem zfcSetTheory_extra_length : zfcSetTheoryExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem zfcSetTheory_validB_eq_false : packageDependenciesValidB zfcSetTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem zfcSetTheory_closedB_eq_true : packageDependenciesClosedB zfcSetTheoryPackage zfcSetTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `zfcSetTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_zfcSetTheory_orig : ¬ (PackageDependenciesValid zfcSetTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [zfcSetTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem zfcSetTheory_closed : PackageDependenciesClosed zfcSetTheoryPackage zfcSetTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact zfcSetTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem zfcSetTheory_false_but_repairable :
    (¬ (PackageDependenciesValid zfcSetTheoryPackage)) ∧
      PackageDependenciesClosed zfcSetTheoryPackage zfcSetTheoryExtra ∧
      zfcSetTheoryExtra.length = 1 := by
  exact And.intro not_zfcSetTheory_orig (And.intro zfcSetTheory_closed zfcSetTheory_extra_length)


/-! ### graphTheory (graph_theory) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- graph_theory de kua yinyong ming ji (ji extra). -/
def graphTheoryExtra : List String :=
  [ "three_colorability" ]

theorem graphTheory_extra_length : graphTheoryExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem graphTheory_validB_eq_false : packageDependenciesValidB graphTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem graphTheory_closedB_eq_true : packageDependenciesClosedB graphTheoryPackage graphTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `graphTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_graphTheory_orig : ¬ (PackageDependenciesValid graphTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [graphTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem graphTheory_closed : PackageDependenciesClosed graphTheoryPackage graphTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact graphTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem graphTheory_false_but_repairable :
    (¬ (PackageDependenciesValid graphTheoryPackage)) ∧
      PackageDependenciesClosed graphTheoryPackage graphTheoryExtra ∧
      graphTheoryExtra.length = 1 := by
  exact And.intro not_graphTheory_orig (And.intro graphTheory_closed graphTheory_extra_length)


/-! ### measureTheory (measure_theory) -- kua yinyong 2 ge ming, 7 tiao bian -/

/-- measure_theory de kua yinyong ming ji (ji extra). -/
def measureTheoryExtra : List String :=
  [ "computability_theory", "zfc_set_theory" ]

theorem measureTheory_extra_length : measureTheoryExtra.length = 2 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem measureTheory_validB_eq_false : packageDependenciesValidB measureTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem measureTheory_closedB_eq_true : packageDependenciesClosedB measureTheoryPackage measureTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `measureTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_measureTheory_orig : ¬ (PackageDependenciesValid measureTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [measureTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem measureTheory_closed : PackageDependenciesClosed measureTheoryPackage measureTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact measureTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem measureTheory_false_but_repairable :
    (¬ (PackageDependenciesValid measureTheoryPackage)) ∧
      PackageDependenciesClosed measureTheoryPackage measureTheoryExtra ∧
      measureTheoryExtra.length = 2 := by
  exact And.intro not_measureTheory_orig (And.intro measureTheory_closed measureTheory_extra_length)


/-! ### functionalAnalysis (functional_analysis) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- functional_analysis de kua yinyong ming ji (ji extra). -/
def functionalAnalysisExtra : List String :=
  [ "lp_space" ]

theorem functionalAnalysis_extra_length : functionalAnalysisExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem functionalAnalysis_validB_eq_false : packageDependenciesValidB functionalAnalysisPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem functionalAnalysis_closedB_eq_true : packageDependenciesClosedB functionalAnalysisPackage functionalAnalysisExtra = true := rfl

/-- **Qingsuan**: shangyou `functionalAnalysisPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_functionalAnalysis_orig : ¬ (PackageDependenciesValid functionalAnalysisPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [functionalAnalysis_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem functionalAnalysis_closed : PackageDependenciesClosed functionalAnalysisPackage functionalAnalysisExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact functionalAnalysis_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem functionalAnalysis_false_but_repairable :
    (¬ (PackageDependenciesValid functionalAnalysisPackage)) ∧
      PackageDependenciesClosed functionalAnalysisPackage functionalAnalysisExtra ∧
      functionalAnalysisExtra.length = 1 := by
  exact And.intro not_functionalAnalysis_orig (And.intro functionalAnalysis_closed functionalAnalysis_extra_length)


/-! ### probabilityTheory (probability_theory) -- kua yinyong 4 ge ming, 7 tiao bian -/

/-- probability_theory de kua yinyong ming ji (ji extra). -/
def probabilityTheoryExtra : List String :=
  [ "axiom_of_choice", "computational_complexity_theory", "measure_theory",
    "zfc_set_theory" ]

theorem probabilityTheory_extra_length : probabilityTheoryExtra.length = 4 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem probabilityTheory_validB_eq_false : packageDependenciesValidB probabilityTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem probabilityTheory_closedB_eq_true : packageDependenciesClosedB probabilityTheoryPackage probabilityTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `probabilityTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_probabilityTheory_orig : ¬ (PackageDependenciesValid probabilityTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [probabilityTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem probabilityTheory_closed : PackageDependenciesClosed probabilityTheoryPackage probabilityTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact probabilityTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem probabilityTheory_false_but_repairable :
    (¬ (PackageDependenciesValid probabilityTheoryPackage)) ∧
      PackageDependenciesClosed probabilityTheoryPackage probabilityTheoryExtra ∧
      probabilityTheoryExtra.length = 4 := by
  exact And.intro not_probabilityTheory_orig (And.intro probabilityTheory_closed probabilityTheory_extra_length)


/-! ### informationTheory (information_theory) -- kua yinyong 12 ge ming, 13 tiao bian

Tong computabilityTheory: `13 tiao bian` shi shangyou yilai biao li de chu xian ci shu,
extra ben shen wei 12 ge ming (jian `informationTheory_extra_length`). -/

/-- information_theory de kua yinyong ming ji (ji extra). -/
def informationTheoryExtra : List String :=
  [ "adversary_model", "channel_model", "channel_model_specification",
    "channel_models", "cryptographic_protocol", "distortion_measure",
    "network_topology", "program_termination", "received_signal",
    "source_distribution", "turing_machine_universality", "universal_turing_machine" ]

theorem informationTheory_extra_length : informationTheoryExtra.length = 12 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem informationTheory_validB_eq_false : packageDependenciesValidB informationTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem informationTheory_closedB_eq_true : packageDependenciesClosedB informationTheoryPackage informationTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `informationTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_informationTheory_orig : ¬ (PackageDependenciesValid informationTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [informationTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem informationTheory_closed : PackageDependenciesClosed informationTheoryPackage informationTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact informationTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem informationTheory_false_but_repairable :
    (¬ (PackageDependenciesValid informationTheoryPackage)) ∧
      PackageDependenciesClosed informationTheoryPackage informationTheoryExtra ∧
      informationTheoryExtra.length = 12 := by
  exact And.intro not_informationTheory_orig (And.intro informationTheory_closed informationTheory_extra_length)


/-! ### linearAlgebra (linear_algebra) -- kua yinyong 1 ge ming, 1 tiao bian -/

/-- linear_algebra de kua yinyong ming ji (ji extra). -/
def linearAlgebraExtra : List String :=
  [ "matrix_mortality_problem" ]

theorem linearAlgebra_extra_length : linearAlgebraExtra.length = 1 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem linearAlgebra_validB_eq_false : packageDependenciesValidB linearAlgebraPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem linearAlgebra_closedB_eq_true : packageDependenciesClosedB linearAlgebraPackage linearAlgebraExtra = true := rfl

/-- **Qingsuan**: shangyou `linearAlgebraPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_linearAlgebra_orig : ¬ (PackageDependenciesValid linearAlgebraPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [linearAlgebra_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem linearAlgebra_closed : PackageDependenciesClosed linearAlgebraPackage linearAlgebraExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact linearAlgebra_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem linearAlgebra_false_but_repairable :
    (¬ (PackageDependenciesValid linearAlgebraPackage)) ∧
      PackageDependenciesClosed linearAlgebraPackage linearAlgebraExtra ∧
      linearAlgebraExtra.length = 1 := by
  exact And.intro not_linearAlgebra_orig (And.intro linearAlgebra_closed linearAlgebra_extra_length)


/-! ### projectiveGeometry (projective_geometry) -- kua yinyong 11 ge ming, 12 tiao bian -/

/-- projective_geometry de kua yinyong ming ji (ji extra). -/
def projectiveGeometryExtra : List String :=
  [ "alternative_division_ring", "bruck_ryser_chowla_theorem", "combinatorial_design_theory",
    "computational_search", "coordinate_field_construction", "desargues_theorem_failure",
    "field_theory", "finite_field_theory", "non_desarguesian_plane_construction",
    "projective_to_euclidean_specialization", "translation_plane_theory" ]

theorem projectiveGeometry_extra_length : projectiveGeometryExtra.length = 11 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem projectiveGeometry_validB_eq_false : packageDependenciesValidB projectiveGeometryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem projectiveGeometry_closedB_eq_true : packageDependenciesClosedB projectiveGeometryPackage projectiveGeometryExtra = true := rfl

/-- **Qingsuan**: shangyou `projectiveGeometryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_projectiveGeometry_orig : ¬ (PackageDependenciesValid projectiveGeometryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [projectiveGeometry_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem projectiveGeometry_closed : PackageDependenciesClosed projectiveGeometryPackage projectiveGeometryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact projectiveGeometry_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem projectiveGeometry_false_but_repairable :
    (¬ (PackageDependenciesValid projectiveGeometryPackage)) ∧
      PackageDependenciesClosed projectiveGeometryPackage projectiveGeometryExtra ∧
      projectiveGeometryExtra.length = 11 := by
  exact And.intro not_projectiveGeometry_orig (And.intro projectiveGeometry_closed projectiveGeometry_extra_length)


/-! ### orderTheory (order_theory) -- kua yinyong 9 ge ming, 16 tiao bian -/

/-- order_theory de kua yinyong ming ji (ji extra). -/
def orderTheoryExtra : List String :=
  [ "convex_geometry", "dilworth_theorem", "graph_isomorphism",
    "group_theory", "partial_order", "poset_dimension",
    "realizer", "topological_sort", "zfc_set_theory" ]

theorem orderTheory_extra_length : orderTheoryExtra.length = 9 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem orderTheory_validB_eq_false : packageDependenciesValidB orderTheoryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem orderTheory_closedB_eq_true : packageDependenciesClosedB orderTheoryPackage orderTheoryExtra = true := rfl

/-- **Qingsuan**: shangyou `orderTheoryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_orderTheory_orig : ¬ (PackageDependenciesValid orderTheoryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [orderTheory_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem orderTheory_closed : PackageDependenciesClosed orderTheoryPackage orderTheoryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact orderTheory_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem orderTheory_false_but_repairable :
    (¬ (PackageDependenciesValid orderTheoryPackage)) ∧
      PackageDependenciesClosed orderTheoryPackage orderTheoryExtra ∧
      orderTheoryExtra.length = 9 := by
  exact And.intro not_orderTheory_orig (And.intro orderTheory_closed orderTheory_extra_length)


/-! ### affineGeometry (affine_geometry) -- kua yinyong 4 ge ming, 15 tiao bian -/

/-- affine_geometry de kua yinyong ming ji (ji extra). -/
def affineGeometryExtra : List String :=
  [ "affine_geometry", "combinatorics", "euclidean_plane",
    "projective_geometry" ]

theorem affineGeometry_extra_length : affineGeometryExtra.length = 4 := rfl

/-- Bool he xin pan ju: yuan weici wei **jia**. -/
theorem affineGeometry_validB_eq_false : packageDependenciesValidB affineGeometryPackage = false := rfl

/-- Bool he xin pan ju: xiufu weici wei **zhen**. -/
theorem affineGeometry_closedB_eq_true : packageDependenciesClosedB affineGeometryPackage affineGeometryExtra = true := rfl

/-- **Qingsuan**: shangyou `affineGeometryPackage_dependencies_valid` duanyan de mingti wei **jia**. -/
theorem not_affineGeometry_orig : ¬ (PackageDependenciesValid affineGeometryPackage) := by
  rw [<- packageDependenciesValidB_iff]
  simp [affineGeometry_validB_eq_false]

/-- **Xiufu**: tong yi ge bao, zai bi bao yi yi xia **wei zhen**. -/
theorem affineGeometry_closed : PackageDependenciesClosed affineGeometryPackage affineGeometryExtra := by
  rw [<- packageDependenciesClosedB_iff]
  exact affineGeometry_closedB_eq_true

/-- Dui zhao: yuan wei jia, xiufu wei zhen, extra fei kong. -/
theorem affineGeometry_false_but_repairable :
    (¬ (PackageDependenciesValid affineGeometryPackage)) ∧
      PackageDependenciesClosed affineGeometryPackage affineGeometryExtra ∧
      affineGeometryExtra.length = 4 := by
  exact And.intro not_affineGeometry_orig (And.intro affineGeometry_closed affineGeometry_extra_length)


/-! ## 6. Zong biao -/

/-- Shangyou yuan weici zuo wei quan cheng schema shi jia de. -/
theorem not_forall_packageDependenciesValid :
    ¬ (forall pkg : AxiomPackageInstance, PackageDependenciesValid pkg) :=
  fun h => not_zfcSetTheory_orig (h zfcSetTheoryPackage)

/-- Zong he ming ti: 12 ge bao, yuan weici quan jia.

Zhu yi (ming ming li shi): `all_twelve_discharged` de ming zi bao liu zi shangyou
「12 tiao axiom」de shuo fa, dan qi he qu xiang shi ji wei 12 xiang, qia hao dui ying
shangyou 12 tiao `Package_dependencies_valid` axiom.

Yi xia tong ji (yi ben wenjian sheng ming wei zhun):

* 12 ge bao: `computabilityTheory`/`modalLogic`/`zfcSetTheory`/`graphTheory`/
  `measureTheory`/`functionalAnalysis`/`probabilityTheory`/`informationTheory`/
  `linearAlgebra`/`projectiveGeometry`/`orderTheory`/`affineGeometry`.
* `Shice` nan duan ceng xie zuo 98; an di 3 jie shuju zhu tiao zhong suan wei 95
  (qu fen ming ji hou 60 ge bu tong kua yinyong ming). 95 <= 98, you ci ke jian
  yuan wen de 98 shi gao gu, bu shi lin shi kou chu.
* 12 ge `*_extra_length` zhi he = 3+5+1+1+2+1+4+12+1+11+9+4 = 54. -/
theorem all_twelve_discharged :
    (¬ (PackageDependenciesValid computabilityTheoryPackage)) ∧
    (¬ (PackageDependenciesValid modalLogicPackage)) ∧
    (¬ (PackageDependenciesValid zfcSetTheoryPackage)) ∧
    (¬ (PackageDependenciesValid graphTheoryPackage)) ∧
    (¬ (PackageDependenciesValid measureTheoryPackage)) ∧
    (¬ (PackageDependenciesValid functionalAnalysisPackage)) ∧
    (¬ (PackageDependenciesValid probabilityTheoryPackage)) ∧
    (¬ (PackageDependenciesValid informationTheoryPackage)) ∧
    (¬ (PackageDependenciesValid linearAlgebraPackage)) ∧
    (¬ (PackageDependenciesValid projectiveGeometryPackage)) ∧
    (¬ (PackageDependenciesValid orderTheoryPackage)) ∧
    (¬ (PackageDependenciesValid affineGeometryPackage)) := by
  exact ⟨not_computabilityTheory_orig, ⟨not_modalLogic_orig, ⟨not_zfcSetTheory_orig, ⟨not_graphTheory_orig, ⟨not_measureTheory_orig, ⟨not_functionalAnalysis_orig, ⟨not_probabilityTheory_orig, ⟨not_informationTheory_orig, ⟨not_linearAlgebra_orig, ⟨not_projectiveGeometry_orig, ⟨not_orderTheory_orig, not_affineGeometry_orig⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end Lattice.Lv00.AxiomDischargeJia

/-! ## 7. Axiom qingdan -/

#print axioms Lattice.Lv00.AxiomDischargeJia.not_computabilityTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.computabilityTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_modalLogic_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.modalLogic_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_zfcSetTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.zfcSetTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_graphTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.graphTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_measureTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.measureTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_functionalAnalysis_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.functionalAnalysis_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_probabilityTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.probabilityTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_informationTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.informationTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_linearAlgebra_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.linearAlgebra_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_projectiveGeometry_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.projectiveGeometry_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_orderTheory_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.orderTheory_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.not_affineGeometry_orig
#print axioms Lattice.Lv00.AxiomDischargeJia.affineGeometry_closed
#print axioms Lattice.Lv00.AxiomDischargeJia.closed_nil_iff
#print axioms Lattice.Lv00.AxiomDischargeJia.dependenciesClosed_mono
#print axioms Lattice.Lv00.AxiomDischargeJia.not_forall_packageDependenciesValid
