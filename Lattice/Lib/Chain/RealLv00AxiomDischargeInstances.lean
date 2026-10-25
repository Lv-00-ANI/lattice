import Mathlib
import Lattice.Lib.Chain.RealLv00AxiomDischargeCore
/-! # RealLv00AxiomDischargeInstances

拆分自 `RealLv00AxiomDischarge.lean`（第 119–769 行），2026-10-14。
声明内容未改动。原文件已改为 re-export 门面，`import RealLv00AxiomDischarge` 仍有效。

本模块重新声明了原文件的三项模块级设置（缺一不可）：
`noncomputable section`（:64）、`set_option maxHeartbeats 1000000`（:66）、
`namespace Lattice.Lv00.AxiomDischarge`（:68）。
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace Lattice.Lv00.AxiomDischarge

/-! ## 3. 12 ge zhenshi bao de shuju (zhu zi lai zi shangyou Instances_*.lean)

Bu ke gou zao wen ti biao zhu tiao banyun, dependencies liebiao **zhu zi baoliu**,
**bu zuo renhe shan gai**。Shang shu shengming **jin dui `dependencies` liebiao** you xiao:
mei tiao yilai ming dou mei bei shan diao huo gai ming（ji bu cai qu「shan/gai yilai yi
qianjiu ruo weici」de zuo fa）。

**Zhu yi**: ben jie de **mu ban ming biao** bu zai gai shengming fan wei nei --
EXEC-Y1 yi an `EXEC-Y1-EXTERNAL-30` fen bie xiang modalLogic / graphTheory /
probabilityTheory / informationTheory / projectiveGeometry / orderTheory de mu ban biao
**zhui jia le wai ming**（gong 30 ge）。Suoyi「zhu zi baoliu、bu zuo renhe shan gai」
zhi cheng li yu yilai liebiao, bu neng du zuo **zheng pi caiji shuju** wei gai dong de yi ju. -/
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
    "eventually_operator", "next_operator", "until_operator",
    -- EXEC-Y1-EXTERNAL-30 (modalLogic): 1 true-external name(s)
    "second_order_logic"
    ]

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

theorem modalLogic_templateNames_length : modalLogicTemplateNames.length = 28 := rfl

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
    "graph_minor", "spectral_properties",
    -- EXEC-Y1-EXTERNAL-30 (graphTheory): 1 true-external name(s)
    "three_colorability"
    ]

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

theorem graphTheory_templateNames_length : graphTheoryTemplateNames.length = 71 := rfl

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
    "characteristic_function_properties", "characteristic_function_uniqueness", "characteristic_function_inversion",
    -- EXEC-Y1-EXTERNAL-30 (probabilityTheory): 2 true-external name(s)
    "axiom_of_choice",
    "computational_complexity_theory"
    ]

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

theorem probabilityTheory_templateNames_length : probabilityTheoryTemplateNames.length = 89 := rfl

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
    "bcjr_decoding", "blahut_arimoto_algorithm",
    -- EXEC-Y1-EXTERNAL-30 (informationTheory): 11 true-external name(s)
    "turing_machine_universality",
    "program_termination",
    "channel_model_specification",
    "source_distribution",
    "distortion_measure",
    "channel_model",
    "received_signal",
    "network_topology",
    "channel_models",
    "cryptographic_protocol",
    "adversary_model"
    ]

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

theorem informationTheory_templateNames_length : informationTheoryTemplateNames.length = 117 := rfl

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
    "projectivity_uniqueness", "cross_ratio_invariance",
    -- EXEC-Y1-EXTERNAL-30 (projectiveGeometry): 10 true-external name(s)
    "combinatorial_design_theory",
    "finite_field_theory",
    "bruck_ryser_chowla_theorem",
    "non_desarguesian_plane_construction",
    "translation_plane_theory",
    "desargues_theorem_failure",
    "alternative_division_ring",
    "projective_to_euclidean_specialization",
    "coordinate_field_construction",
    "computational_search"
    ]

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

theorem projectiveGeometry_templateNames_length : projectiveGeometryTemplateNames.length = 48 := rfl

/-- order_theory de 32 tiao mu ban ming (shangyou orderTheoryTemplateNames). -/
def orderTheoryTemplateNames : List String :=
  [ "reflexivity", "antisymmetry", "transitivity", "least_element",
    "greatest_element", "minimal_element", "maximal_element", "upper_bound",
    "lower_bound", "least_upper_bound", "greatest_lower_bound", "totality",
    "well_foundedness", "well_order", "monotone_function", "antitone_function",
    "order_embedding", "order_isomorphism", "dual_order", "product_order",
    "induced_suborder", "ordinal_sum", "strict_order", "covering_relation",
    "chain", "antichain", "interval", "hasse_diagram",
    "zorn_lemma", "dilworth_decomposition", "knaster_tarski_fixed_point", "szpilrajn_extension",
    -- EXEC-Y1-EXTERNAL-30 (orderTheory): 5 true-external name(s)
    "partial_order",
    "realizer",
    "topological_sort",
    "convex_geometry",
    "dilworth_theorem"
    ]

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

theorem orderTheory_templateNames_length : orderTheoryTemplateNames.length = 37 := rfl

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



end Lattice.Lv00.AxiomDischarge
