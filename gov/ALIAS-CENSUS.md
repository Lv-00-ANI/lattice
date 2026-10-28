# 别名清册（谁的证明只是转发）

> 由 `gov/audit_aliases.py` 生成。**不要手改。**

**别名不是缺陷**；它是「增加了一个名字、没有增加数学」的形状。
有的是**词汇桥**（九条 `compileIR_*_exact` 指向一条一般引理，那是好设计），
有的是**重复的副本**（`audit_duplicates.py` 按**名字**分组，看不见后者）。

**本清册的作用**：让每一个别名被**决定过一次**，并记在 `alias-baseline.txt` 里。

| 指标 | 值 |
|:--|--:|
| 别名总数 | 706 |

## 被转发最多的声明

> 一个声明被 **≥3** 条别名指向，通常意味着「一条一般引理 + 一族词汇」；
> 被**只有 1 条**指向，则更像重复副本，值得单独看。

| 声明 | 别名条数 |
|:--|--:|
| `le_trans` | 31 |
| `exact` | 18 |
| `compileIR_penalty_exact_of` | 9 |
| `ladder_forward` | 8 |
| `preserves_of_sat` | 7 |
| `symbolToWeight_correct` | 7 |
| `roundtrip_extractVec` | 7 |
| `softMasked_is_gated` | 6 |
| `selState_norm_bound_contracting` | 6 |
| `intent_closure_idempotent` | 5 |
| `reg_softMasked_coverage` | 5 |
| `converges_within` | 4 |
| `progress` | 4 |
| `localMin_implies_zero` | 4 |
| `convComb_norm_bound` | 4 |
| `galois_connection` | 4 |
| `subset_extent_intent` | 4 |
| `comp` | 4 |
| `extent_antitone` | 4 |
| `sound` | 4 |
| `glu_lipschitz` | 4 |
| `samples_sound` | 3 |
| `decode_encode` | 3 |
| `glu_mask_bound` | 3 |
| `glu_is_gated` | 3 |
| `gated_ffn_effective` | 3 |
| `attention_output_bound` | 3 |
| `maskedSoftmax_sum_one` | 3 |
| `masked_attention_output_bound` | 3 |
| `sphereGD_mem_sphere` | 3 |
| `hoeffding_lemma_measure` | 3 |
| `intent_antitone` | 3 |
| `extractLayer_compileToLayer` | 3 |
| `every_function_is_quotient_reversible` | 3 |
| `roundTripAddsNothing_of_factorsThrough` | 3 |
| `le_antisymm` | 3 |
| `cauchy_schwarz_finset` | 3 |
| `spectral_radius_le_opNorm` | 3 |
| `dot_eq_dotProduct` | 3 |
| `sgd_rate_bound` | 3 |
| `roundtrip` | 3 |
| `compose_chain` | 2 |
| `flattenEquiv` | 2 |
| `loss_le_sq_of_resid_le` | 2 |
| `reinject_loss_eq_zero` | 2 |
| `loop_fixed_point_stable` | 2 |
| `loss_nonneg` | 2 |
| `pluckerNorm_nonneg` | 2 |
| `sqDistConst_one` | 2 |
| `loss_eq_zero_of_poly_eq_zero` | 2 |
| `twoValuedPenalty_nonneg` | 2 |
| `samplesOf_sound` | 2 |
| `gated_abs_le` | 2 |
| `contracting_of_lipschitz` | 2 |
| `maskedSoftmax_nonneg` | 2 |
| `complex_softmax_pmf` | 2 |
| `topK_sum_max` | 2 |
| `subset_intent_extent` | 2 |
| `suspend_preserves_base` | 2 |
| `extent_intent_extent` | 2 |
| `format_error_bound` | 2 |
| `format_round_idempotent` | 2 |
| `isometry_preserves_norm_scalar` | 2 |
| `GD_contraction_step` | 2 |
| `compileToLayer_injective` | 2 |
| `tokenize_collision` | 2 |
| `semantic_not_injective` | 2 |
| `gaussian_curvature_eq_zero` | 2 |
| `convertVec_bias_eq_convertRealVec_bias` | 2 |
| `simulation_reflTransGen` | 2 |
| `eym_symmetric` | 2 |
| `uniformExpectation_eq_zero_of_sum_eq_zero` | 2 |
| `jensen_concave_finset_of_mem` | 2 |
| `hoeffding_two_sided` | 2 |
| `canonicalize_section_pos` | 2 |
| `canonicalize_idempotent` | 2 |
| `fibre_singleton_of_injective` | 2 |
| `rowEdit_commute_of_orthogonal_keys` | 2 |
| `roundTrip_perturbation_id` | 2 |
| `strictMonoOn_injOn` | 2 |
| `induction` | 2 |
| `roundTripAddsNothing_of_leftInverse` | 2 |
| `closure_idempotent` | 2 |
| `kl_as_sum_log_sub_log` | 2 |
| `gen_GD_contraction_step` | 2 |
| `exists_decrease` | 2 |
| `gelfand_radius_le_opNorm` | 2 |
| `softThresh_is_min` | 2 |
| `gd_sharpness` | 2 |
| `Expect_nonneg` | 2 |
| `triangle_combine` | 2 |
| `loss_bound_gives_resid_bound` | 2 |
| `post_train_preserves` | 2 |
| `E` | 1 |
| `sqDist_eq_of_dist_eq` | 1 |
| `sqNorm_nonneg` | 1 |
| `subst` | 1 |
| `loss_eq_zero_expr` | 1 |
| `loss_eq_zero_samePoint` | 1 |
| `weightLadder_forward` | 1 |
| `loop_fixed_point` | 1 |
| `netLoss_stepN_tendsto` | 1 |
| `equalLengthFix_reaches` | 1 |
| `sq_eq_zero_of_localMin` | 1 |
| `unflatten_flatten` | 1 |
| `flatten_unflatten` | 1 |
| `loop_converges_in_one` | 1 |
| `fixPerp_holds` | 1 |
| `fixPerp_absorbs` | 1 |
| `parallel_skolemized` | 1 |
| `parallelFix_reaches` | 1 |
| `bilinearSum_lipschitz` | 1 |
| `evalPts_localMin_implies_zero` | 1 |
| `repair_iff_satisfiable` | 1 |
| `reinject_perpendicular` | 1 |
| `reinject_of_hold` | 1 |
| `repair_success_is_penalty_zero` | 1 |
| `fixSamePoint_other` | 1 |
| `fixSamePoint_self` | 1 |
| `fixPerp_other` | 1 |
| `localMin_implies_penalty_zero` | 1 |
| `infer_bn_is_affine` | 1 |
| `bn_train_eq_infer` | 1 |
| `gnorm_scale_invariant` | 1 |
| `normalize_scale_invariant` | 1 |
| `unit_normalize_lipschitz` | 1 |
| `unit_normalize_lipschitz_sharp` | 1 |
| `normSq_nonneg` | 1 |
| `oneHot_lookup` | 1 |
| `msgPass_equivariant` | 1 |
| `regular_uniform_aggregate_eq` | 1 |
| `normalize_translation_invariant` | 1 |
| `invariant_preserves_iteration` | 1 |
| `contraction_fixed_point_existsUnique` | 1 |
| `sigmoid_monotone` | 1 |
| `softmax_monotone` | 1 |
| `balanced_no_drop` | 1 |
| `droppedCount_eq_zero_iff` | 1 |
| `imbalance_forces_drop` | 1 |
| `rms_scale` | 1 |
| `exists_norm_eq` | 1 |
| `P2a_nonstationary_when_unsatisfied` | 1 |
| `ssd_row_succ_eq` | 1 |
| `ssdMatVec_eq_selState` | 1 |
| `selState_explicit` | 1 |
| `selState_succ` | 1 |
| `sel_is_LTI_special` | 1 |
| `gnnFeat_eq_of_wlEq` | 1 |
| `gnnFeat_eq_of_wlEq_of_constOn_zero` | 1 |
| `abs_pos_relative_shift` | 1 |
| `block_sparse_lipschitz` | 1 |
| `block_sparse_output_bound` | 1 |
| `full_mask_eq_softmax` | 1 |
| `maskedDenom_pos` | 1 |
| `convComb_lipschitz_prob` | 1 |
| `maskCount_le_total` | 1 |
| `windowMaskCount_general` | 1 |
| `complex_attention_bound` | 1 |
| `complex_rope_phase_shift` | 1 |
| `lipschitz_comp` | 1 |
| `topk_one_is_argmax` | 1 |
| `routeSelect_spec` | 1 |
| `head_redundancy_bound` | 1 |
| `topk_output_bound` | 1 |
| `block_rotate_preserves_normSq` | 1 |
| `block_rotate_preserves_dot` | 1 |
| `sharpness_witness_uniform` | 1 |
| `causalSoftmax_eq_zero_of_gt` | 1 |
| `linear_attn_associativity` | 1 |
| `mla_absorb_key` | 1 |
| `hetero_chain_numeric_bound` | 1 |
| `period_multiple_witness` | 1 |
| `subset_gazeUp_gazeDown` | 1 |
| `subset_gazeDown_gazeUp` | 1 |
| `split_immediately_confers_concept` | 1 |
| `split_iff_all` | 1 |
| `up_gaze_content_is_passive` | 1 |
| `upGaze_within_given_space` | 1 |
| `mul` | 1 |
| `alibi_bias_translation_equivariant` | 1 |
| `distBias_equivariant` | 1 |
| `relPhaseAbs_translation_equivariant` | 1 |
| `rope_score_translation_equivariant` | 1 |
| `gelu_is_soft_masked` | 1 |
| `hardSwish_is_soft_masked` | 1 |
| `relu_is_soft_masked` | 1 |
| `silu_is_soft_masked` | 1 |
| `swiglu_is_soft_masked` | 1 |
| `supporting_hyperplane_real` | 1 |
| `exists_optimal_plan` | 1 |
| `reg_roundOp_coverage` | 1 |
| `sphereGD_retr_bound` | 1 |
| `supporting_hyperplane_of_boundary_point` | 1 |
| `b194_counterexamples_intact_holds` | 1 |
| `reachL_le_of_edge_le` | 1 |
| `order_unique_of_same_cone` | 1 |
| `P0_normal_equation_scalar` | 1 |
| `affine_edit_output_bound_scalar` | 1 |
| `edit_output_bound_scalar` | 1 |
| `edit_preserves_constraint_scalar` | 1 |
| `edit_verify_tolerance_scalar` | 1 |
| `edit_verify_tolerance_scalar_affine` | 1 |
| `complex_edit_output_bound` | 1 |
| `complex_inner_conj_symm` | 1 |
| `complex_inner_self_norm_sq_instance` | 1 |
| `complex_isometry_preserves_norm` | 1 |
| `complex_P0_normal_equation` | 1 |
| `inner_self_norm_sq_scalar` | 1 |
| `isometry_scalar_compose` | 1 |
| `normSq_eq_norm_sq` | 1 |
| `residual_edit_local_scalar` | 1 |
| `residual_error_isolation_scalar` | 1 |
| `GD_converges` | 1 |
| `GD_error_identity` | 1 |
| `GD_iterate_contraction` | 1 |
| `GD_sq_contraction_step` | 1 |
| `complex_GD_converges` | 1 |
| `complex_GD_error_identity` | 1 |
| `cgd_re` | 1 |
| `cgd_im` | 1 |
| `wirtinger_decomposition` | 1 |
| `infinite_sum_bound` | 1 |
| `modSinLoss_zero_iff_vectorConstraintSat_of_lt` | 1 |
| `w3_clm_eq_layerOut_cast` | 1 |
| `realDot_eq_symDot_cast` | 1 |
| `int_dvd_not_antisymmetric` | 1 |
| `gcd_assoc` | 1 |
| `encode_injective` | 1 |
| `tokenize_not_injective` | 1 |
| `trivialProofTrace_passes` | 1 |
| `go_hypotheses_pushes` | 1 |
| `length_le` | 1 |
| `natToReal_refl_lt` | 1 |
| `natToReal_monotone` | 1 |
| `natToReal_strictMono` | 1 |
| `natToReal_le_of_le` | 1 |
| `zmod_homogeneous_structure` | 1 |
| `rs_unique_decoding` | 1 |
| `min` | 1 |
| `add` | 1 |
| `dvd_add_int` | 1 |
| `soundAbstract_alpha_le` | 1 |
| `fixpoint_transfer_le` | 1 |
| `point_le_iff_contains` | 1 |
| `point_contains` | 1 |
| `gamma_monotone` | 1 |
| `roundDownN_le` | 1 |
| `star_refl` | 1 |
| `bigstep_to_smallstep` | 1 |
| `bigstep_deterministic` | 1 |
| `edit_seq_comm` | 1 |
| `families_satisfiable` | 1 |
| `ofDB_toDB` | 1 |
| `confluent_of_wf` | 1 |
| `newman` | 1 |
| `compile_program_go_contains` | 1 |
| `decide_eq_true_iff_alt` | 1 |
| `flat_eval_inr` | 1 |
| `simulation_comp` | 1 |
| `clique_lower_bound` | 1 |
| `iso_iff_eq` | 1 |
| `size_pos` | 1 |
| `size_pos_aux` | 1 |
| `preservation` | 1 |
| `triple_iff_wpT` | 1 |
| `wpT_while_fixpoint` | 1 |
| `wpT_while_least` | 1 |
| `abs_cube_expectation_le_secondMoment` | 1 |
| `finrank_add_finrank_gt_implies_inf_ne_bot` | 1 |
| `eigenvalues_antitone_imp_ge` | 1 |
| `trans` | 1 |
| `condExpFiber_mul_of_adapted_mem` | 1 |
| `uniformExpectation_le_of_fibreBound` | 1 |
| `uniformExpectation_mgf_iterate` | 1 |
| `hoeffding_lemma_bounded` | 1 |
| `condexp_mono` | 1 |
| `hoeffding_inequality_measure` | 1 |
| `hoeffding_inequality_measure_sq` | 1 |
| `mgf_bound_of_coordinate_bounds` | 1 |
| `hoeffding_lemma_measure_interval` | 1 |
| `indep_mgf_sum` | 1 |
| `sum_fiber_eq_row` | 1 |
| `doob_maximal_azuma_max` | 1 |
| `submartingale_of_condexp_le` | 1 |
| `martingale_expected_stoppedValue_eq_last` | 1 |
| `martingale_expected_stoppedValue_min_eq` | 1 |
| `martingale_expected_stoppedValue_eq_of_le` | 1 |
| `mcdiarmid_additive_two_sided` | 1 |
| `martingale_expected_stoppedValue_eq` | 1 |
| `rad_complexity_nonneg_of` | 1 |
| `union_bound_finite` | 1 |
| `exp_neg_div_lt_exp_neg_sq_quarter` | 1 |
| `exp_neg_div_lt_exp_neg_sq_of_lt` | 1 |
| `linearFunctional_gradSq_eq_fderiv` | 1 |
| `fenchelConjAll_infConv_eq` | 1 |
| `rcq_multiplier_uniqueness_false_for_any_dim` | 1 |
| `licq_multiplier_unique` | 1 |
| `ccx_affine_comp` | 1 |
| `proj_nonexpansive_of_variational` | 1 |
| `proj_unique_variational` | 1 |
| `convex_proj_variational` | 1 |
| `fenchelConjAllEReal_le` | 1 |
| `fenchelConjAllEReal_toReal` | 1 |
| `le_kr_pairValue` | 1 |
| `kp_lipschitz_bound` | 1 |
| `pareto_optimal_of_scalarization` | 1 |
| `subgradient_step_decrease` | 1 |
| `subgradient_exists_of_convex` | 1 |
| `supporting_hyperplane_of_not_mem_interior` | 1 |
| `canonicalize_scaleVec_sign` | 1 |
| `canonicalize_of_content_one` | 1 |
| `ft2L2L3Norm` | 1 |
| `ft2L2L3Norm_idem_apply` | 1 |
| `no_left_inverse_at_all` | 1 |
| `spec_retract_without_rep` | 1 |
| `dot_representation_agreement` | 1 |
| `linearization_global_fails` | 1 |
| `natTransform_compile` | 1 |
| `weightFunctor_compileToLayer` | 1 |
| `image_galoisConnection_general` | 1 |
| `append_assoc` | 1 |
| `compileToLayer_bijective` | 1 |
| `scaleVec_mul_param` | 1 |
| `layerOut_perturbation_bound` | 1 |
| `compileToLayer_extractLayer` | 1 |
| `roundTripFixed_append_singleton_iff` | 1 |
| `scaleVec_preserves` | 1 |
| `kl_zero_iff_eq` | 1 |
| `safe_normalize_bound` | 1 |
| `safe_normalize_lipschitz_on` | 1 |
| `chain_split_at` | 1 |
| `dot_zipWith_add_of_length` | 1 |
| `layerOut_cast_eq_clm` | 1 |
| `layerOut_zero_iff_clm` | 1 |
| `roundtrip_extractVec_rfl` | 1 |
| `roundtrip_convertVec_rfl` | 1 |
| `preimage_subsingleton` | 1 |
| `canonicalize_cNegVec` | 1 |
| `canonicalize_preserves_sat` | 1 |
| `canonicalize_scaleVec_neg_cNegVec` | 1 |
| `scaleClassB_iff` | 1 |
| `geluTanh_injOn_of_gate` | 1 |
| `no_fiber_of_extractVec_has_two_points` | 1 |
| `decode_drops_trailing_partial` | 1 |
| `gramEdit_eq_batchClosed` | 1 |
| `convertVec_respects_semEq` | 1 |
| `t1_decompose` | 1 |
| `detokenize_left_inverse_on_quotient` | 1 |
| `repairTo_lands` | 1 |
| `closed_loop_adds_nothing` | 1 |
| `roundtrip_extract` | 1 |
| `roundtrip_error_bound` | 1 |
| `roundtrip_under_quantization` | 1 |
| `dot_append_zero_d21` | 1 |
| `dot_append_replicate_d21` | 1 |
| `map_extractVec_compileToLayer_eq_self` | 1 |
| `no_nontrivial_roundtrip_subset` | 1 |
| `ratSemanticallyParallel_of_scaleVecQ` | 1 |
| `dot_append_additive_iff` | 1 |
| `E8_later_ring_inert` | 1 |
| `no_upper_iff_no_split` | 1 |
| `up_gaze_element_or_concept` | 1 |
| `suspend_dissolves_identity` | 1 |
| `suspend_idempotent` | 1 |
| `constraint_entailment_closure` | 1 |
| `tcl_triExtent_monotone` | 1 |
| `netAct_deviation_le_devB` | 1 |
| `log_derivative_identity` | 1 |
| `fisherMatrix_zero_direction_score` | 1 |
| `fisherMatrix_psd` | 1 |
| `log_concave_pair` | 1 |
| `mul_log_convex_pair` | 1 |
| `kleeneChain_monotone` | 1 |
| `unique_theta_for_moment` | 1 |
| `gibbs_ineq` | 1 |
| `dual_weak` | 1 |
| `rnDerivLog_integral_nonpos` | 1 |
| `bayesRisk_le_worstCase` | 1 |
| `constrainedSoftmax_support_iff_allowed` | 1 |
| `constrained_agrees_with_constraint_set` | 1 |
| `obsClosure_id_of_injective` | 1 |
| `closure_fixedPoints_eq_range` | 1 |
| `distill_excess_of_uniform_distance` | 1 |
| `kernelGramMatrix_psd_iff_exists_featureMap` | 1 |
| `noiseMatrix_mulVec_alpha` | 1 |
| `chord_hull_abs` | 1 |
| `boost_confidence` | 1 |
| `sq_add_le_two_mul_sq_add_sq` | 1 |
| `weighted_cauchy_schwarz` | 1 |
| `coupling_accept_bound` | 1 |
| `meanField_isProb` | 1 |
| `contraction_converges` | 1 |
| `zeroFixingR_iff_unique_zero` | 1 |
| `zeroFixingR_iff_of_monotone` | 1 |
| `zeroFixing_of_strictMono` | 1 |
| `reluZ_not_zeroFixing` | 1 |
| `step_residual` | 1 |
| `sqNorm_eq_zero_iff` | 1 |
| `linearFix_residual` | 1 |
| `exact_implies_sound` | 1 |
| `cspec_hermitian_eigenvalue_im_zero` | 1 |
| `cspec_eigenvalue_isRoot_charpoly` | 1 |
| `frobeniusNorm_nonneg` | 1 |
| `frobenius_add_eq` | 1 |
| `strict_min_of_quadratic_lower_bound` | 1 |
| `compBound_monotone` | 1 |
| `bound_monotone_in_length` | 1 |
| `rotate_preserves_dot` | 1 |
| `op_norm_pow_apply_le_of_le` | 1 |
| `op_norm_pow_le` | 1 |
| `matvecE_mul` | 1 |
| `spectral_concentration_of_markov` | 1 |
| `markov_counting` | 1 |
| `metric_eq_kernel_expansion` | 1 |
| `normalizedKernel_self` | 1 |
| `reproducing_property` | 1 |
| `metric_kernel_nonneg` | 1 |
| `kernel_metric_zero_iff` | 1 |
| `kernel_diag_nonneg` | 1 |
| `prune_magnitude_bound` | 1 |
| `proj_fixed` | 1 |
| `ce_not_joint_convex` | 1 |
| `silu_lipschitz_on` | 1 |
| `slater_not_sufficient_discrete` | 1 |
| `unit_normalize_two_div_not_attained` | 1 |
| `toVec_not_injective_without_length` | 1 |
| `audit_is_contentful_iff_not_all` | 1 |
| `compileFailed_not_refutes` | 1 |
| `extractVec_convertVec_rfl` | 1 |
| `congruent_to_modEq` | 1 |
| `modEq_to_congruent` | 1 |
| `extract_idempotent` | 1 |
| `mono_le_of_le` | 1 |
| `async_bounded_delay_converges` | 1 |
| `neighborhood_scope` | 1 |
| `async_random_delay_converges` | 1 |
| `gated_lipschitz` | 1 |
| `one_dim_lower_witness_core` | 1 |
| `newton_step_quadratic` | 1 |
| `prox_linear` | 1 |
| `normsq_sub` | 1 |
| `no_faster_than_geometric` | 1 |
| `projSphere_norm` | 1 |
| `unique_bayes_admissible` | 1 |
| `toIsLocalMax` | 1 |
| `exists_modulus_of_posDef` | 1 |
| `second_order_necessary_multidim` | 1 |
| `second_order_taylor` | 1 |
| `isLocalMin_of_forall_le` | 1 |
| `op_error_propagation` | 1 |
| `round_close` | 1 |
| `clampTo_eq_self` | 1 |
| `clampTo_mono` | 1 |
| `accumulation_error_bound` | 1 |
| `fp16_round_abs_bound` | 1 |
| `fp16_underflow_dominated` | 1 |
| `loss_scaling_no_overflow` | 1 |
| `mixed_layer_error` | 1 |
| `mixed_matrix_frobenius_error` | 1 |
| `mixed_matrix_op_error` | 1 |
| `mixed_vs_full_precision` | 1 |
| `format_add_error` | 1 |
| `format_mul_error` | 1 |
| `channel_op_bound` | 1 |
| `channel_pruning_bound` | 1 |
| `approx_ladder_forward` | 1 |
| `abs_resid_le_of_loss_le_sq` | 1 |
| `compileProgram_sound` | 1 |
| `backend_sound` | 1 |
| `toFinVec` | 1 |
| `idempotentOn_of_leftInverse` | 1 |
| `iterate_comp_of_leftInverse` | 1 |
| `residual_le_of_zero_on_dense_of_d` | 1 |
| `payload_getElem` | 1 |
| `foldGo_idem` | 1 |
| `foldGo_length_le` | 1 |
| `tokenizeRaw_detok` | 1 |
| `clamp_error` | 1 |
| `le_succ_of_pred_le` | 1 |
| `classify_total` | 1 |
| `iterateRepair_eq_self` | 1 |
| `holdsSet_member` | 1 |
| `holdsSet_mem` | 1 |
| `holdsSet_of_sublist` | 1 |
| `merge_error_bound` | 1 |
| `vocab_edit_permutation_exact` | 1 |

## 全部别名

| 文件 | 定理 | 转发到 |
|:--|:--|:--|
| `Audit/MultiComposition.lean` | `chain_single` | `compose_chain` |
| `Audit/MultiComposition.lean` | `chain_two` | `compose_chain` |
| `Audit/PredicateWitnesses.lean` | `isometryScalar_id` | `E` |
| `Core/OneStepBridge.lean` | `natCountdownAsRepair_converges` | `converges_within` |
| `Core/OneStepBridge.lean` | `oneStepRepair_converges` | `converges_within` |
| `Core/Repair.lean` | `parity_terminates` | `progress` |
| `Domains/Constraints/Dist.lean` | `sqDist_eq_of_dist_eq_same` | `sqDist_eq_of_dist_eq` |
| `Domains/Constraints/Dist.lean` | `sqDist_nonneg` | `sqNorm_nonneg` |
| `Domains/Constraints/ExprDeriv.lean` | `maxPoint_lt_of_coord` | `subst` |
| `Domains/Constraints/Flatten.lean` | `flattenRepresentation_compile_extract` | `flattenEquiv` |
| `Domains/Constraints/Flatten.lean` | `flattenRepresentation_roundtrip` | `flattenEquiv` |
| `Domains/Constraints/Loss.lean` | `loss_eq_zero_toGeo_expr` | `loss_eq_zero_expr` |
| `Domains/Constraints/Loss.lean` | `loss_eq_zero_toGeo_samePoint` | `loss_eq_zero_samePoint` |
| `Domains/Geometry/ApproxEmbedding.lean` | `eqConstraint_loss_le_sq_of_resid_le` | `loss_le_sq_of_resid_le` |
| `Domains/Geometry/ClauseComposition.lean` | `init_then_weight` | `weightLadder_forward` |
| `Domains/Geometry/ClauseComposition.lean` | `rate_then_repair` | `converges_within` |
| `Domains/Geometry/ClauseComposition.lean` | `repair_then_reinject` | `reinject_loss_eq_zero` |
| `Domains/Geometry/ClauseComposition.lean` | `synthesis_then_verify` | `samples_sound` |
| `Domains/Geometry/ClosedLoop.lean` | `conj_loop_is_stable` | `loop_fixed_point_stable` |
| `Domains/Geometry/ClosedLoop.lean` | `geometric_loop_fixed_point` | `loop_fixed_point` |
| `Domains/Geometry/ClosedLoop.lean` | `geometric_loop_is_stable` | `loop_fixed_point_stable` |
| `Domains/Geometry/CodegenLadder.lean` | `codegenLadder_forward` | `ladder_forward` |
| `Domains/Geometry/ConstraintDescent.lean` | `netLoss_tendsto_zero` | `netLoss_stepN_tendsto` |
| `Domains/Geometry/EqualLengthRepair.lean` | `repair_coverage_geometric` | `equalLengthFix_reaches` |
| `Domains/Geometry/Exact.lean` | `geo_penalty_exact` | `sq_eq_zero_of_localMin` |
| `Domains/Geometry/Exact.lean` | `perpendicular_loss_nonneg` | `loss_nonneg` |
| `Domains/Geometry/Exact.lean` | `samePoint_loss_nonneg` | `loss_nonneg` |
| `Domains/Geometry/ExprLocalMin.lean` | `evalPts_localMin_implies_zero` | `localMin_implies_zero` |
| `Domains/Geometry/Exterior.lean` | `collinearPenalty_nonneg` | `pluckerNorm_nonneg` |
| `Domains/Geometry/Exterior.lean` | `parallelPenalty_nonneg` | `pluckerNorm_nonneg` |
| `Domains/Geometry/Extract.lean` | `configOf_inv` | `unflatten_flatten` |
| `Domains/Geometry/Extract.lean` | `configOf_roundtrip` | `flatten_unflatten` |
| `Domains/Geometry/GeoLadder.lean` | `geoLadder_forward` | `ladder_forward` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_collinear_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_distance_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_eqExpr_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_equalLength_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_midpoint_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_parallel_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_perpendicular_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_radius_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/IRBridge.lean` | `compileIR_rightAngle_exact` | `compileIR_penalty_exact_of` |
| `Domains/Geometry/LadderInstance.lean` | `linearLadder_forward` | `ladder_forward` |
| `Domains/Geometry/LadderInstance.lean` | `linearLadder_l1l2_roundtrip` | `decode_encode` |
| `Domains/Geometry/Loop.lean` | `reinject_sound` | `loop_converges_in_one` |
| `Domains/Geometry/LoopPerp.lean` | `perp_loop_converges_in_one` | `fixPerp_holds` |
| `Domains/Geometry/LoopPerp.lean` | `perp_loop_preserves` | `fixPerp_absorbs` |
| `Domains/Geometry/Nondegenerate.lean` | `perpResid_localMin_implies_zero` | `localMin_implies_zero` |
| `Domains/Geometry/Nondegenerate.lean` | `perpResid_localMin_of_nondegenerate` | `localMin_implies_zero` |
| `Domains/Geometry/ParallelRepair.lean` | `parallel_gap_closed` | `parallel_skolemized` |
| `Domains/Geometry/ParallelRepair.lean` | `parallel_skolemized` | `parallelFix_reaches` |
| `Domains/Geometry/PartialReinjection.lean` | `exact_reinject_zero` | `reinject_loss_eq_zero` |
| `Domains/Geometry/PartialReinjection.lean` | `loss_le_of_le` | `le_trans` |
| `Domains/Geometry/PartialReinjection.lean` | `partial_reinject_bound` | `loss_le_sq_of_resid_le` |
| `Domains/Geometry/PolyAssemble.lean` | `poly_lipschitz_perpendicular` | `bilinearSum_lipschitz` |
| `Domains/Geometry/PolyConstants.lean` | `poly_const_perpendicular` | `sqDistConst_one` |
| `Domains/Geometry/PolyConstants.lean` | `poly_const_samePoint` | `sqDistConst_one` |
| `Domains/Geometry/PolyNondegenerate.lean` | `poly_expr_localMin_implies_zero` | `evalPts_localMin_implies_zero` |
| `Domains/Geometry/PolyRepair.lean` | `poly_gap_is_not_a_gap` | `repair_iff_satisfiable` |
| `Domains/Geometry/QualityBridge.lean` | `copy_preserves_at_sat` | `preserves_of_sat` |
| `Domains/Geometry/QualityBridge.lean` | `linear_repair_preserves_at_sat` | `preserves_of_sat` |
| `Domains/Geometry/QualityBridge.lean` | `project_preserves_at_sat` | `preserves_of_sat` |
| `Domains/Geometry/ReinjectionGeneral.lean` | `reinject_generic` | `loss_eq_zero_of_poly_eq_zero` |
| `Domains/Geometry/ReinjectionGeneral.lean` | `reinject_of_hold` | `loss_eq_zero_of_poly_eq_zero` |
| `Domains/Geometry/ReinjectionGeneral.lean` | `reinject_perpRepair` | `reinject_perpendicular` |
| `Domains/Geometry/ReinjectionGeneral.lean` | `reinject_perpendicular` | `reinject_of_hold` |
| `Domains/Geometry/RepairBridge.lean` | `converges` | `progress` |
| `Domains/Geometry/RepairPenalty.lean` | `samePoint_loop_reaches_penalty_zero` | `repair_success_is_penalty_zero` |
| `Domains/Geometry/RepairQuality.lean` | `copy_keeps_a` | `fixSamePoint_other` |
| `Domains/Geometry/RepairQuality.lean` | `copy_writes_b` | `fixSamePoint_self` |
| `Domains/Geometry/RepairQuality.lean` | `project_keeps_a` | `fixPerp_other` |
| `Domains/Geometry/Square.lean` | `equalLengthPenalty_nonneg` | `twoValuedPenalty_nonneg` |
| `Domains/Geometry/Square.lean` | `sqDistEqPenalty_nonneg` | `twoValuedPenalty_nonneg` |
| `Domains/Geometry/Synthesis.lean` | `synthesize_perpendicular_samples` | `samples_sound` |
| `Domains/Geometry/SynthesisConnection.lean` | `synthesis_connects_to_chain` | `ladder_forward` |
| `Domains/Geometry/SynthesisConnection.lean` | `synthesize_for` | `samples_sound` |
| `Domains/Geometry/SynthesisConnection.lean` | `synthesize_for_multi` | `samplesOf_sound` |
| `Domains/Geometry/SynthesisMulti.lean` | `synthesize_perpendicular_multi` | `samplesOf_sound` |
| `Domains/Geometry/Unconditional.lean` | `localMin_ofLinearForm_implies_loss_zero` | `localMin_implies_penalty_zero` |
| `Domains/Geometry/Unconditional.lean` | `localMin_ofLinearForm_implies_zero` | `localMin_implies_zero` |
| `Domains/Geometry/Unified.lean` | `every_repair_preserves_at_sat` | `preserves_of_sat` |
| `Domains/Geometry/Unified.lean` | `linearRepair_unified` | `preserves_of_sat` |
| `Domains/Geometry/Unified.lean` | `perpRepair_unified` | `preserves_of_sat` |
| `Domains/Geometry/Unified.lean` | `samePointRepair_unified` | `preserves_of_sat` |
| `Lib/Architectures/RealBatchNorm.lean` | `infer_bn_slope_intercept` | `infer_bn_is_affine` |
| `Lib/Architectures/RealBatchNormConsistency.lean` | `bn_train_eq_infer_of_const` | `bn_train_eq_infer` |
| `Lib/Architectures/RealBatchNormConsistency.lean` | `gnorm_scale_invariant_reuse` | `gnorm_scale_invariant` |
| `Lib/Architectures/RealBatchNormConsistency.lean` | `normalize_scale_invariant_reuse` | `normalize_scale_invariant` |
| `Lib/Architectures/RealBatchNormConsistency.lean` | `varNormalize_unit_lipschitz` | `unit_normalize_lipschitz` |
| `Lib/Architectures/RealBatchNormConsistency.lean` | `varNormalize_unit_lipschitz_sharp` | `unit_normalize_lipschitz_sharp` |
| `Lib/Architectures/RealComplexNorm.lean` | `complexNormSq_nonneg` | `normSq_nonneg` |
| `Lib/Architectures/RealEmbedding.lean` | `oneHot_represents_token` | `oneHot_lookup` |
| `Lib/Architectures/RealGLUVariants.lean` | `geglu_bound` | `glu_mask_bound` |
| `Lib/Architectures/RealGLUVariants.lean` | `geglu_is_gated` | `glu_is_gated` |
| `Lib/Architectures/RealGLUVariants.lean` | `glu_mask_bound` | `gated_abs_le` |
| `Lib/Architectures/RealGLUVariants.lean` | `reglu_bound` | `glu_mask_bound` |
| `Lib/Architectures/RealGLUVariants.lean` | `reglu_is_gated` | `glu_is_gated` |
| `Lib/Architectures/RealGLUVariants.lean` | `siluGLU_bound` | `glu_mask_bound` |
| `Lib/Architectures/RealGLUVariants.lean` | `siluGLU_is_gated` | `glu_is_gated` |
| `Lib/Architectures/RealGNNEquivariance.lean` | `msgPass_equivariant_one` | `msgPass_equivariant` |
| `Lib/Architectures/RealGatingGeneral.lean` | `gelu_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGatingGeneral.lean` | `hardSwish_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGatingGeneral.lean` | `relu_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGatingGeneral.lean` | `silu_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGatingGeneral.lean` | `softMask_ffn_effective_via_gated` | `gated_ffn_effective` |
| `Lib/Architectures/RealGatingGeneral.lean` | `swigluPair_ffn_effective` | `gated_ffn_effective` |
| `Lib/Architectures/RealGatingGeneral.lean` | `swiglu_ffn_effective_via_gated` | `gated_ffn_effective` |
| `Lib/Architectures/RealGatingGeneral.lean` | `swiglu_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGeluExact.lean` | `geluExact_bound` | `gated_abs_le` |
| `Lib/Architectures/RealGeluExact.lean` | `geluExact_is_gated` | `softMasked_is_gated` |
| `Lib/Architectures/RealGeneralNormalEquation.lean` | `normal_eq_consistent` | `exact` |
| `Lib/Architectures/RealGraphExpressivity.lean` | `oneWL_first_round_blind` | `regular_uniform_aggregate_eq` |
| `Lib/Architectures/RealLayerNormComplete.lean` | `layernorm_translation_invariant` | `normalize_translation_invariant` |
| `Lib/Architectures/RealLayerwiseStability.lean` | `resJac_chain_le_inv_one_sub_sum` | `le_trans` |
| `Lib/Architectures/RealLoop.lean` | `satisfaction_loop_invariant` | `invariant_preserves_iteration` |
| `Lib/Architectures/RealLoopFixedPointExistence.lean` | `affineStep_contracting` | `contracting_of_lipschitz` |
| `Lib/Architectures/RealLoopFixedPointExistence.lean` | `contraction_derivative_fixed_point_existsUnique` | `contraction_fixed_point_existsUnique` |
| `Lib/Architectures/RealLoopFixedPointExistence.lean` | `loopStepMap_contracting` | `contracting_of_lipschitz` |
| `Lib/Architectures/RealMoE.lean` | `sigmoid_gate_preserves_order` | `sigmoid_monotone` |
| `Lib/Architectures/RealMoE.lean` | `softmax_gate_preserves_order` | `softmax_monotone` |
| `Lib/Architectures/RealMoERouteCapacity.lean` | `balanced_route_no_drop` | `balanced_no_drop` |
| `Lib/Architectures/RealMoERouteCapacity.lean` | `routeLoad_drop_eq_zero_iff` | `droppedCount_eq_zero_iff` |
| `Lib/Architectures/RealMoERouteCapacity.lean` | `route_over_capacity_drops` | `imbalance_forces_drop` |
| `Lib/Architectures/RealNormFamily.lean` | `rms_is_homogeneous` | `rms_scale` |
| `Lib/Architectures/RealRMSNormGeneral.lean` | `exists_norm_eq_general` | `exists_norm_eq` |
| `Lib/Architectures/RealReLUStationarity.lean` | `P2a_relu_sq_summary` | `P2a_nonstationary_when_unsatisfied` |
| `Lib/Architectures/RealSSDBridge.lean` | `ssd_row_succ_extra` | `ssd_row_succ_eq` |
| `Lib/Architectures/RealSSDBridge.lean` | `ssd_scan_compose` | `ssdMatVec_eq_selState` |
| `Lib/Architectures/RealSSM.lean` | `ssm_contraction_rho` | `le_trans` |
| `Lib/Architectures/RealSSMContinuous.lean` | `selStateGated_explicit` | `selState_explicit` |
| `Lib/Architectures/RealSSMContinuous.lean` | `selStateGated_norm_bound` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealSSMContinuous.lean` | `sel_LTI_zoh_spectral_criterion` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealSSMContinuous.lean` | `sel_spectral_eigen_criterion` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealSSMContinuous.lean` | `sel_spectral_norm_criterion` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealSSMContinuous.lean` | `zoh_recurrence_eq_selState` | `selState_succ` |
| `Lib/Architectures/RealSSMContinuous.lean` | `zoh_state_explicit` | `sel_is_LTI_special` |
| `Lib/Architectures/RealSSMContinuous.lean` | `zoh_state_norm_bound` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealSelectiveSSM.lean` | `sel_LTI_norm_bound` | `selState_norm_bound_contracting` |
| `Lib/Architectures/RealWLRefinement.lean` | `gnnFeat_eq_of_wlEq_of_constOn_zero` | `gnnFeat_eq_of_wlEq` |
| `Lib/Architectures/RealWLRefinement.lean` | `gnnFeat_zero_comp_eq` | `gnnFeat_eq_of_wlEq_of_constOn_zero` |
| `Lib/Attention/RealALiBi.lean` | `alibi_attention_output_bound` | `attention_output_bound` |
| `Lib/Attention/RealAbsPosEncoding.lean` | `abs_pos_relative_shift_no_denom` | `abs_pos_relative_shift` |
| `Lib/Attention/RealAttention.lean` | `attention_output_bound` | `convComb_norm_bound` |
| `Lib/Attention/RealAttentionCoreBridge.lean` | `convComb_coreValue_norm_bound` | `convComb_norm_bound` |
| `Lib/Attention/RealBlockSparse.lean` | `block_causal_lipschitz` | `block_sparse_lipschitz` |
| `Lib/Attention/RealBlockSparse.lean` | `block_causal_output_bound` | `block_sparse_output_bound` |
| `Lib/Attention/RealBlockSparse.lean` | `block_causal_row_random` | `maskedSoftmax_sum_one` |
| `Lib/Attention/RealBlockSparse.lean` | `block_sparse_all_blocks_eq_softmax` | `full_mask_eq_softmax` |
| `Lib/Attention/RealBlockSparse.lean` | `block_sparse_denom_pos` | `maskedDenom_pos` |
| `Lib/Attention/RealBlockSparse.lean` | `block_sparse_lipschitz` | `convComb_lipschitz_prob` |
| `Lib/Attention/RealBlockSparse.lean` | `block_sparse_nonneg` | `maskedSoftmax_nonneg` |
| `Lib/Attention/RealBlockSparse.lean` | `block_sparse_output_bound` | `masked_attention_output_bound` |
| `Lib/Attention/RealBlockSparseExact.lean` | `maskCount_le_total_nb` | `maskCount_le_total` |
| `Lib/Attention/RealBlockSparseExact.lean` | `windowMaskCount_general_zero` | `windowMaskCount_general` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_abs_attention_bound` | `attention_output_bound` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_abs_score_softmax_pmf` | `complex_softmax_pmf` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_attention_bound` | `attention_output_bound` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_attention_bound_expanded` | `complex_attention_bound` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_rope_score_phase_relation` | `complex_rope_phase_shift` |
| `Lib/Attention/RealComplexAttention.lean` | `complex_score_softmax_pmf` | `complex_softmax_pmf` |
| `Lib/Attention/RealCrossAttention.lean` | `encoder_decoder_comp_bound` | `lipschitz_comp` |
| `Lib/Attention/RealDynamicRoute.lean` | `routeSelectOne_is_argmax` | `topk_one_is_argmax` |
| `Lib/Attention/RealDynamicRoute.lean` | `routeSelectOne_spec` | `routeSelect_spec` |
| `Lib/Attention/RealGQA.lean` | `gqa_preserves_pmf` | `exact` |
| `Lib/Attention/RealHeadMerge.lean` | `head_output_bound` | `convComb_norm_bound` |
| `Lib/Attention/RealHeadMerge.lean` | `head_pairwise_redundancy_bound` | `head_redundancy_bound` |
| `Lib/Attention/RealHeadMerge.lean` | `pruned_head_output_bound` | `topk_output_bound` |
| `Lib/Attention/RealHeadPruningOptimal.lean` | `headMass_le_topSum` | `topK_sum_max` |
| `Lib/Attention/RealHighDimRoPE.lean` | `block_rope_isometry` | `block_rotate_preserves_normSq` |
| `Lib/Attention/RealHighDimRoPE.lean` | `block_rotate_preserves_normSq` | `block_rotate_preserves_dot` |
| `Lib/Attention/RealKVBudget.lean` | `retainedMass_le_topSum` | `topK_sum_max` |
| `Lib/Attention/RealKVBudget.lean` | `sharpness_witness_const_weights` | `sharpness_witness_uniform` |
| `Lib/Attention/RealKVCache.lean` | `cache_weights_supported_on_prefix` | `causalSoftmax_eq_zero_of_gt` |
| `Lib/Attention/RealLinearAttention.lean` | `linear_attn_output_bound` | `convComb_norm_bound` |
| `Lib/Attention/RealLinearAttention.lean` | `linear_attn_state_form` | `linear_attn_associativity` |
| `Lib/Attention/RealMLA.lean` | `absorb_requires_image` | `mla_absorb_key` |
| `Lib/Attention/RealMaskFamily.lean` | `refl_mask_output_bound` | `masked_attention_output_bound` |
| `Lib/Attention/RealMaskFamily.lean` | `refl_mask_sum_one` | `maskedSoftmax_sum_one` |
| `Lib/Attention/RealMaskFamily.lean` | `sliding_window_nonneg` | `maskedSoftmax_nonneg` |
| `Lib/Attention/RealMaskFamily.lean` | `sliding_window_output_bound` | `masked_attention_output_bound` |
| `Lib/Attention/RealMaskFamily.lean` | `sliding_window_row_random` | `maskedSoftmax_sum_one` |
| `Lib/Attention/RealMixedAttention.lean` | `mixed_to_encoder` | `hetero_chain_numeric_bound` |
| `Lib/Attention/RealRoPEExtrapolationFailure.lean` | `window_no_coincidence_outside_grid` | `period_multiple_witness` |
| `Lib/Attention/RealTemporalLayer.lean` | `galois_connection_temporal` | `galois_connection` |
| `Lib/Attention/RealTemporalLayer.lean` | `split_exposes_parts_to_upward_gaze` | `subset_gazeUp_gazeDown` |
| `Lib/Attention/RealTemporalLayer.lean` | `subset_gazeDown_gazeUp` | `subset_extent_intent` |
| `Lib/Attention/RealTemporalLayer.lean` | `subset_gazeUp_gazeDown` | `subset_intent_extent` |
| `Lib/Attention/RealTemporalLayer.lean` | `suspend_not_decomposition` | `suspend_preserves_base` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `downGaze_opens_new_space` | `subset_gazeDown_gazeUp` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `down_gaze_content_is_constrained` | `split_immediately_confers_concept` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `down_gaze_outcome_is_passive` | `split_iff_all` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `passivity_is_internal_texture` | `up_gaze_content_is_passive` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `upGaze_does_not_open_object` | `extent_intent_extent` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `upGaze_saturates_depth` | `upGaze_within_given_space` |
| `Lib/Attention/RealTemporalLayerExt.lean` | `upGaze_within_given_space` | `intent_closure_idempotent` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_gated_coverage_comp` | `comp` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_gated_coverage_mul` | `mul` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_gated_gelu` | `reg_softMasked_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_gated_hardSwish` | `reg_softMasked_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_gated_relu` | `reg_softMasked_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_gated_silu` | `reg_softMasked_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_gated_swiglu` | `reg_softMasked_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_ite_alibi` | `alibi_bias_translation_equivariant` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_ite_distBias` | `distBias_equivariant` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_ite_relPhaseAbs` | `relPhaseAbs_translation_equivariant` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_ite_rope` | `rope_score_translation_equivariant` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_softMasked_gelu` | `gelu_is_soft_masked` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_softMasked_hardSwish` | `hardSwish_is_soft_masked` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_softMasked_relu` | `relu_is_soft_masked` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_softMasked_silu` | `silu_is_soft_masked` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_softMasked_swiglu` | `swiglu_is_soft_masked` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_sphere_mem` | `sphereGD_mem_sphere` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_inst_support_scalar` | `supporting_hyperplane_real` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_ot_coverage_optimal` | `exists_optimal_plan` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_roundOp_coverage` | `format_error_bound` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_roundOp_coverage_idempotent` | `format_round_idempotent` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_roundOp_identity_applies` | `reg_roundOp_coverage` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_sphere_coverage_retr` | `sphereGD_retr_bound` |
| `Lib/Chain/RealAbstractionRegistry.lean` | `reg_support_coverage` | `supporting_hyperplane_of_boundary_point` |
| `Lib/Chain/RealChainAxioms3.lean` | `b194_anchor_consumer` | `b194_counterexamples_intact_holds` |
| `Lib/Chain/RealChainLiftGeneral.lean` | `reachL_image_le_max_of_edge_le` | `reachL_le_of_edge_le` |
| `Lib/Chain/RealClosedFieldAxiomatic.lean` | `cone_unique_of_same_squares` | `order_unique_of_same_cone` |
| `Lib/Chain/RealComplex.lean` | `complex_P0_normal_equation` | `P0_normal_equation_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_affine_edit_output_bound` | `affine_edit_output_bound_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_edit_output_bound` | `edit_output_bound_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_edit_preserves_constraint` | `edit_preserves_constraint_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_edit_verify_tolerance` | `edit_verify_tolerance_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_edit_verify_tolerance_affine` | `edit_verify_tolerance_scalar_affine` |
| `Lib/Chain/RealComplex.lean` | `complex_euclid_edit_output_bound` | `complex_edit_output_bound` |
| `Lib/Chain/RealComplex.lean` | `complex_euclid_inner_conj_symm` | `complex_inner_conj_symm` |
| `Lib/Chain/RealComplex.lean` | `complex_euclid_inner_self_norm_sq` | `complex_inner_self_norm_sq_instance` |
| `Lib/Chain/RealComplex.lean` | `complex_euclid_isometry_preserves_norm` | `complex_isometry_preserves_norm` |
| `Lib/Chain/RealComplex.lean` | `complex_euclid_normal_equation` | `complex_P0_normal_equation` |
| `Lib/Chain/RealComplex.lean` | `complex_inner_self_norm_sq_instance` | `inner_self_norm_sq_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_isometry_preserves_norm` | `isometry_preserves_norm_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_isometry_scalar_compose` | `isometry_scalar_compose` |
| `Lib/Chain/RealComplex.lean` | `complex_normSq_eq_norm_sq` | `normSq_eq_norm_sq` |
| `Lib/Chain/RealComplex.lean` | `complex_residual_edit_local` | `residual_edit_local_scalar` |
| `Lib/Chain/RealComplex.lean` | `complex_residual_error_isolation` | `residual_error_isolation_scalar` |
| `Lib/Chain/RealComplexGD.lean` | `complex_GD_contraction_step` | `GD_contraction_step` |
| `Lib/Chain/RealComplexGD.lean` | `complex_GD_converges` | `GD_converges` |
| `Lib/Chain/RealComplexGD.lean` | `complex_GD_error_identity` | `GD_error_identity` |
| `Lib/Chain/RealComplexGD.lean` | `complex_GD_iterate_contraction` | `GD_iterate_contraction` |
| `Lib/Chain/RealComplexGD.lean` | `complex_GD_sq_contraction_step` | `GD_sq_contraction_step` |
| `Lib/Chain/RealComplexGD.lean` | `complex_euclid_GD_converges` | `complex_GD_converges` |
| `Lib/Chain/RealComplexGD.lean` | `complex_euclid_GD_error_identity` | `complex_GD_error_identity` |
| `Lib/Chain/RealComplexWirtinger.lean` | `complex_GD_matches_real_fst` | `cgd_re` |
| `Lib/Chain/RealComplexWirtinger.lean` | `complex_GD_matches_real_snd` | `cgd_im` |
| `Lib/Chain/RealComplexWirtinger.lean` | `wirtinger_decomposition_apply_I` | `wirtinger_decomposition` |
| `Lib/Chain/RealCountableSum.lean` | `finset_bound_to_tsum` | `infinite_sum_bound` |
| `Lib/Chain/RealCrossUniverseApplication.lean` | `modSinLoss_zero_iff_vectorConstraintSat` | `modSinLoss_zero_iff_vectorConstraintSat_of_lt` |
| `Lib/Chain/RealCrossUniverseApplication.lean` | `w3_clm_plus_b_eq_cast` | `w3_clm_eq_layerOut_cast` |
| `Lib/Chain/RealCrossUniverseConsumer.lean` | `realDot_symW_concrete` | `realDot_eq_symDot_cast` |
| `Lib/Chain/RealDvdLatticeStratification.lean` | `int_dvd_not_partial_order` | `int_dvd_not_antisymmetric` |
| `Lib/Chain/RealDvdLatticeStratification.lean` | `nat_inf_assoc` | `gcd_assoc` |
| `Lib/Chain/RealE2EComposite.lean` | `semantic_loss_is_not_structural` | `compileToLayer_injective` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_L1L2_is_lossless` | `encode_injective` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_extract_hypothesis_is_not_load_bearing` | `symbolToWeight_correct` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_loss_at_L0L1` | `tokenize_collision` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_loss_at_L2L3` | `semantic_not_injective` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_not_injective` | `tokenize_not_injective` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_sound` | `symbolToWeight_correct` |
| `Lib/Chain/RealEndToEnd.lean` | `e2e_vacuous_composition` | `symbolToWeight_correct` |
| `Lib/Chain/RealEndToEndNontrivial.lean` | `d41_T2_shell_hypothesis_free` | `symbolToWeight_correct` |
| `Lib/Chain/RealEndToEndNontrivial.lean` | `d41_e2e_semantic_soundness_at_data_level_shell` | `symbolToWeight_correct` |
| `Lib/Chain/RealEndToEndStrict.lean` | `e2e_L0L1_loss_exists` | `tokenize_collision` |
| `Lib/Chain/RealEndToEndStrict.lean` | `e2e_sameLayer_comp_is_wellTyped` | `decode_encode` |
| `Lib/Chain/RealErf.lean` | `continuous_exp_neg_sq` | `comp` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/A.lean` | `computabilityTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/A.lean` | `modalLogic_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/B.lean` | `graphTheory_repaired` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/B.lean` | `measureTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/B.lean` | `zfcSetTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean` | `functionalAnalysis_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean` | `informationTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/C.lean` | `probabilityTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean` | `affineGeometry_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean` | `linearAlgebra_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean` | `orderTheory_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00AxiomDischargePerPackage_parts/D.lean` | `projectiveGeometry_false_but_repairable` | `exact` |
| `Lib/Chain/RealLv00GeometryDifferential.lean` | `cylinder_gaussian_curvature_zero_degenerate` | `gaussian_curvature_eq_zero` |
| `Lib/Chain/RealLv00GeometryDifferential.lean` | `plane_gaussian_curvature_zero_degenerate` | `gaussian_curvature_eq_zero` |
| `Lib/Chain/RealLv00Systems.lean` | `evidenceCheck_accepts_unsatisfiable` | `trivialProofTrace_passes` |
| `Lib/Chain/RealLv00Systems.lean` | `go_hypotheses_eq` | `go_hypotheses_pushes` |
| `Lib/Chain/RealModelFamilyChainWiring.lean` | `core_semantics_lifts_to_real_bias` | `convertVec_bias_eq_convertRealVec_bias` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `comp_apply_strictMono` | `comp` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `comp_strictMono_of_strictMono` | `comp` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `covers_mono` | `le_trans` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `length_le_of_prefix` | `length_le` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `lt_of_natToReal_lt` | `natToReal_refl_lt` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `natToReal_le_of_le` | `natToReal_monotone` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `natToReal_length_lt` | `natToReal_strictMono` |
| `Lib/Chain/RealNumericChainOrder_parts/C.lean` | `natToReal_length_monotone` | `natToReal_le_of_le` |
| `Lib/Chain/RealPrimeFieldExt.lean` | `zmod_linear_system_homogeneous_bridge` | `zmod_homogeneous_structure` |
| `Lib/Chain/RealReedSolomon.lean` | `rs_decoding_unique_plus_reconstruction` | `rs_unique_decoding` |
| `Lib/Chain/RealScalarField.lean` | `edit_verify_tolerance_scalar` | `le_trans` |
| `Lib/Chain/RealSimpleExtensionDegree.lean` | `degree_minpoly_le_of_monic_aeval` | `min` |
| `Lib/Chain/RealTaylorMultivariate.lean` | `contDiff_pathMap` | `add` |
| `Lib/Compiler/ModConstraint.lean` | `dvd_sub_int` | `dvd_add_int` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `bestAbstract_le_of_sound` | `soundAbstract_alpha_le` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `fixpoint_transfer_le_of_fixed` | `fixpoint_transfer_le` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `galoisConnection_interval_pointwise` | `point_le_iff_contains` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `interval_expansive` | `point_contains` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `mem_gamma_of_le` | `gamma_monotone` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `roundDownN_lower_safe` | `roundDownN_le` |
| `Lib/Compiler/RealAbstractInterpretation.lean` | `transfer_of_sound_abstraction` | `le_trans` |
| `Lib/Compiler/RealBetaConfluence.lean` | `omegaStar_self` | `star_refl` |
| `Lib/Compiler/RealBigStepSmallStep.lean` | `bigstep_implies_final` | `bigstep_to_smallstep` |
| `Lib/Compiler/RealBigStepSmallStep.lean` | `smallstep_final_unique` | `bigstep_deterministic` |
| `Lib/Compiler/RealCompileFloatCorrectness.lean` | `mag_nonneg` | `le_trans` |
| `Lib/Compiler/RealConcurrentSemantics.lean` | `editSeq_commuting_instance` | `edit_seq_comm` |
| `Lib/Compiler/RealFirstOrderLogic.lean` | `finite_subset_satisfiable` | `families_satisfiable` |
| `Lib/Compiler/RealFirstOrderLogic.lean` | `ofDB_toDB_witness` | `ofDB_toDB` |
| `Lib/Compiler/RealGlobalConfluence.lean` | `newman` | `confluent_of_wf` |
| `Lib/Compiler/RealGlobalConfluence.lean` | `prec_confluent` | `newman` |
| `Lib/Compiler/RealLv00CompilerReal.lean` | `compile_program_contains_compiled_constraints` | `compile_program_go_contains` |
| `Lib/Compiler/RealMutualRecursion_parts/C.lean` | `decEq_eq_iff_decide` | `decide_eq_true_iff_alt` |
| `Lib/Compiler/RealMutualRecursion_parts/C.lean` | `flat_guard_agrees` | `flat_eval_inr` |
| `Lib/Compiler/RealRefinementCalculus.lean` | `fidelity_spec_multistep` | `simulation_reflTransGen` |
| `Lib/Compiler/RealRefinementCalculus.lean` | `simulation_comp_reflTransGen` | `simulation_reflTransGen` |
| `Lib/Compiler/RealRefinementCalculus.lean` | `simulation_comp_three` | `simulation_comp` |
| `Lib/Compiler/RealRegisterAllocation.lean` | `loop_lower_bound` | `clique_lower_bound` |
| `Lib/Compiler/RealTreeDecidable.lean` | `iso_self_iff` | `iso_iff_eq` |
| `Lib/Compiler/RealTreeRecursion.lean` | `eval_size_pos` | `size_pos` |
| `Lib/Compiler/RealTreeRecursion.lean` | `size_pos` | `size_pos_aux` |
| `Lib/Compiler/RealTypeSoundness.lean` | `type_preservation_add` | `preservation` |
| `Lib/Compiler/RealWPWhile.lean` | `triple_while_iff_wpT_while` | `triple_iff_wpT` |
| `Lib/Compiler/RealWPWhile.lean` | `wpT_while_isFixpoint` | `wpT_while_fixpoint` |
| `Lib/Compiler/RealWPWhile.lean` | `wpT_while_least_agrees` | `wpT_while_least` |
| `Lib/Concentration/RealBernsteinCondition.lean` | `bernstein_moment_recurrence` | `abs_cube_expectation_le_secondMoment` |
| `Lib/Concentration/RealEYM.lean` | `eym_dimension_crossing` | `finrank_add_finrank_gt_implies_inf_ne_bot` |
| `Lib/Concentration/RealEYM.lean` | `eym_general_via_gram` | `eym_symmetric` |
| `Lib/Concentration/RealEYM.lean` | `eym_k_full` | `eym_symmetric` |
| `Lib/Concentration/RealEYM.lean` | `tail_le_head_pointwise` | `eigenvalues_antitone_imp_ge` |
| `Lib/Concentration/RealEYM.lean` | `trace_sq_eq_sum_eigSq` | `trans` |
| `Lib/Concentration/RealFiltrationIteration.lean` | `condExpFiber_mul_of_adapted_of_ne` | `condExpFiber_mul_of_adapted_mem` |
| `Lib/Concentration/RealFiltrationIteration.lean` | `uniformExpectation_mgf_iterate` | `uniformExpectation_le_of_fibreBound` |
| `Lib/Concentration/RealFiltrationIteration.lean` | `uniformExpectation_mgf_iterate_of_condZeroMean` | `uniformExpectation_mgf_iterate` |
| `Lib/Concentration/RealHoeffding.lean` | `hoeffding_lemma_shifted` | `hoeffding_lemma_bounded` |
| `Lib/Concentration/RealHoeffding.lean` | `uniformExpectation_sub_mean_eq_zero` | `uniformExpectation_eq_zero_of_sum_eq_zero` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `condexp_le_of_ae_le` | `condexp_mono` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `hoeffding_inequality_measure_const_bound` | `hoeffding_inequality_measure` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `mcdiarmid_measure_of_differences` | `hoeffding_inequality_measure_sq` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `mgf_bound_of_bounded_zero_mean` | `mgf_bound_of_coordinate_bounds` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `mgf_le_of_bounded_zero_mean` | `hoeffding_lemma_measure` |
| `Lib/Concentration/RealHoeffdingInequality.lean` | `mgf_le_of_interval_zero_mean` | `hoeffding_lemma_measure_interval` |
| `Lib/Concentration/RealHoeffdingLemmaMeasure.lean` | `hoeffding_lemma_measure_symmetric` | `hoeffding_lemma_measure` |
| `Lib/Concentration/RealHoeffdingMeasureGeneral.lean` | `mgf_coord_bound_of_bounded_mean_zero` | `hoeffding_lemma_measure` |
| `Lib/Concentration/RealHoeffdingMeasureGeneral.lean` | `mgf_factor_sum` | `indep_mgf_sum` |
| `Lib/Concentration/RealJensenGeneral.lean` | `jensen_concave_finset` | `jensen_concave_finset_of_mem` |
| `Lib/Concentration/RealJensenGeneral.lean` | `jensen_log` | `jensen_concave_finset_of_mem` |
| `Lib/Concentration/RealMartingaleConcentration.lean` | `azuma_difference_nonvacuous` | `sum_fiber_eq_row` |
| `Lib/Concentration/RealMartingaleOptionalStopping.lean` | `azuma_max_tail_of_cond_mgf` | `doob_maximal_azuma_max` |
| `Lib/Concentration/RealMartingaleOptionalStopping.lean` | `exp_submartingale_of_cond` | `submartingale_of_condexp_le` |
| `Lib/Concentration/RealMartingaleOptionalStopping.lean` | `optional_stopping_eq_last` | `martingale_expected_stoppedValue_eq_last` |
| `Lib/Concentration/RealMartingaleOptionalStopping.lean` | `optional_stopping_min` | `martingale_expected_stoppedValue_min_eq` |
| `Lib/Concentration/RealMartingaleOptionalStopping.lean` | `optional_stopping_tower` | `martingale_expected_stoppedValue_eq_of_le` |
| `Lib/Concentration/RealMcDiarmid.lean` | `mcdiarmid_example` | `mcdiarmid_additive_two_sided` |
| `Lib/Concentration/RealOptionalStopping.lean` | `martingale_expected_stoppedValue_min_eq` | `martingale_expected_stoppedValue_eq` |
| `Lib/Concentration/RealRademacher.lean` | `radSign_uniformExpectation_zero` | `uniformExpectation_eq_zero_of_sum_eq_zero` |
| `Lib/Concentration/RealRademacher.lean` | `rad_complexity_nonneg` | `rad_complexity_nonneg_of` |
| `Lib/Concentration/RealRademacher.lean` | `rad_generalization_bound` | `union_bound_finite` |
| `Lib/Concentration/RealRademacher.lean` | `rad_hoeffding_event` | `hoeffding_two_sided` |
| `Lib/Concentration/RealSubExponentialTail.lean` | `subExponential_strictly_stronger_than_bernstein_subGaussian` | `exp_neg_div_lt_exp_neg_sq_quarter` |
| `Lib/Concentration/RealSubExponentialTail.lean` | `subGaussian_strictly_weaker_than_subExponential_at_small_t` | `exp_neg_div_lt_exp_neg_sq_of_lt` |
| `Lib/Concentration/RealTalagrandConcentration.lean` | `linearFunctional_gradSq_one_eq` | `linearFunctional_gradSq_eq_fderiv` |
| `Lib/Concentration/RealTalagrandConcentration.lean` | `variance_le_one_of_poincare` | `le_trans` |
| `Lib/Convex/RealConjugateDuality.lean` | `fenchelConjAll_infConv_le` | `fenchelConjAll_infConv_eq` |
| `Lib/Convex/RealConstraintQualification.lean` | `rcq_multiplier_uniqueness_false_2x2` | `rcq_multiplier_uniqueness_false_for_any_dim` |
| `Lib/Convex/RealConstraintQualification.lean` | `rcq_zero_combo_coeff_unique` | `licq_multiplier_unique` |
| `Lib/Convex/RealConvexCalculus.lean` | `ccx_affine_comp_of_nonneg` | `ccx_affine_comp` |
| `Lib/Convex/RealConvexProjection.lean` | `projOn_nonexpansive` | `proj_nonexpansive_of_variational` |
| `Lib/Convex/RealConvexProjection.lean` | `projOn_unique_of_min` | `proj_unique_variational` |
| `Lib/Convex/RealConvexProjection.lean` | `projOn_variational` | `convex_proj_variational` |
| `Lib/Convex/RealDualTheory.lean` | `weak_duality` | `le_trans` |
| `Lib/Convex/RealFCADuality.lean` | `adjoint_holds` | `galois_connection` |
| `Lib/Convex/RealFCADuality.lean` | `extent_antitone_here` | `extent_antitone` |
| `Lib/Convex/RealFCADuality.lean` | `extent_intent_extent_here` | `extent_intent_extent` |
| `Lib/Convex/RealFCADuality.lean` | `extent_intent_monotone` | `extent_antitone` |
| `Lib/Convex/RealFCADuality.lean` | `fca_antitone_adjoint` | `galois_connection` |
| `Lib/Convex/RealFCADuality.lean` | `intent_antitone_here` | `intent_antitone` |
| `Lib/Convex/RealFCADuality.lean` | `intent_extent_intent_here` | `intent_closure_idempotent` |
| `Lib/Convex/RealFCADuality.lean` | `intent_extent_monotone` | `intent_antitone` |
| `Lib/Convex/RealFenchelEReal.lean` | `fenchelConjAllEReal_le_of_bddAbove` | `fenchelConjAllEReal_le` |
| `Lib/Convex/RealFenchelEReal.lean` | `fenchelConjAllEReal_toReal_of_bddAbove` | `fenchelConjAllEReal_toReal` |
| `Lib/Convex/RealKRDuality.lean` | `krPairValue_le_absCost` | `le_kr_pairValue` |
| `Lib/Convex/RealKRDuality.lean` | `le_kr_pairValue` | `kp_lipschitz_bound` |
| `Lib/Convex/RealPareto.lean` | `weighted_optimal_is_pareto` | `pareto_optimal_of_scalarization` |
| `Lib/Convex/RealSubgradientCalculus.lean` | `subdiff_mem_step_decrease` | `subgradient_step_decrease` |
| `Lib/Convex/RealSubgradientExistence.lean` | `subdifferential_nonempty` | `subgradient_exists_of_convex` |
| `Lib/Convex/RealSupportingHyperplane.lean` | `supporting_hyperplane_of_finite_convexHull` | `supporting_hyperplane_of_not_mem_interior` |
| `Lib/Editing/RealCanonicalCompileComm.lean` | `canonicalize_absorbs_scale_pos` | `canonicalize_section_pos` |
| `Lib/Editing/RealCanonicalCompileComm.lean` | `canonicalize_scaleVec_sign_law` | `canonicalize_scaleVec_sign` |
| `Lib/Editing/RealCanonicalForm.lean` | `canonicalize_idempotent` | `canonicalize_of_content_one` |
| `Lib/Editing/RealClosureReversibility.lean` | `ft2L2L3Norm_idem_apply` | `canonicalize_idempotent` |
| `Lib/Editing/RealClosureReversibility.lean` | `ft2L2L3_failure_identifiable` | `ft2L2L3Norm` |
| `Lib/Editing/RealClosureReversibility.lean` | `ft2L2L3_norm_idempotent` | `canonicalize_idempotent` |
| `Lib/Editing/RealClosureReversibility.lean` | `ft2L2L3_quotient_reversible` | `ft2L2L3Norm_idem_apply` |
| `Lib/Editing/RealClosureReversibility.lean` | `l1l2_only_one_direction` | `no_left_inverse_at_all` |
| `Lib/Editing/RealClosureReversibility.lean` | `spec_retract_minimal` | `spec_retract_without_rep` |
| `Lib/Editing/RealCompileExtractClosed.lean` | `closed_loop_dot_representation_unambiguous` | `dot_representation_agreement` |
| `Lib/Editing/RealCompileExtractClosed.lean` | `global_linearization_fails` | `linearization_global_fails` |
| `Lib/Editing/RealConstraintEdit.lean` | `edit_roundtrip_through_weights` | `roundtrip_extractVec` |
| `Lib/Editing/RealConstraintEdit.lean` | `edited_closure_interface` | `symbolToWeight_correct` |
| `Lib/Editing/RealConversionCategorical.lean` | `natTransform_equiv` | `natTransform_compile` |
| `Lib/Editing/RealConversionCategoryNew.lean` | `compileImage_syntacticFunctor_eq_weightFunctor` | `weightFunctor_compileToLayer` |
| `Lib/Editing/RealConversionCategoryNew.lean` | `compile_galoisConnection_is_general_instance` | `image_galoisConnection_general` |
| `Lib/Editing/RealConversionComposition.lean` | `compileToLayer_append_assoc_layer` | `append_assoc` |
| `Lib/Editing/RealConversionComposition.lean` | `compile_extract_bijective` | `compileToLayer_bijective` |
| `Lib/Editing/RealConversionComposition.lean` | `scaleLayer_inverse_iff` | `scaleVec_mul_param` |
| `Lib/Editing/RealConversionInformation.lean` | `compileFibre_card_le_one` | `fibre_singleton_of_injective` |
| `Lib/Editing/RealConversionInformation.lean` | `extractFibre_card_le_one` | `fibre_singleton_of_injective` |
| `Lib/Editing/RealConversionInformation.lean` | `fibre_card_le_image_card` | `le_trans` |
| `Lib/Editing/RealConversionRobustness.lean` | `compileToLayer_perturbation` | `layerOut_perturbation_bound` |
| `Lib/Editing/RealConversionRoundTrip.lean` | `compiled_roundTrip_fixed` | `compileToLayer_extractLayer` |
| `Lib/Editing/RealConversionRoundTrip.lean` | `roundTripFixed_singleton_iff` | `roundTripFixed_append_singleton_iff` |
| `Lib/Editing/RealConversionRoundTrip.lean` | `roundTrip_eq_self` | `extractLayer_compileToLayer` |
| `Lib/Editing/RealConversionRoundTrip.lean` | `scaleVec_semantically_equal` | `scaleVec_preserves` |
| `Lib/Editing/RealConversionStabilityInformation.lean` | `conversion_kl_lossless_iff` | `kl_zero_iff_eq` |
| `Lib/Editing/RealConversionStabilityReversibility.lean` | `extract_normalize_bounded` | `safe_normalize_bound` |
| `Lib/Editing/RealConversionStabilityReversibility.lean` | `extract_normalize_lipschitz` | `safe_normalize_lipschitz_on` |
| `Lib/Editing/RealEditBound.lean` | `edit_verify_tolerance` | `le_trans` |
| `Lib/Editing/RealEditCommute.lean` | `rowEdit_commute_of_orthogonal_support` | `rowEdit_commute_of_orthogonal_keys` |
| `Lib/Editing/RealEditCommute.lean` | `same_row_orthogonal_keys_commute` | `rowEdit_commute_of_orthogonal_keys` |
| `Lib/Editing/RealEditCostPropagation.lean` | `chain_fwd_step` | `chain_split_at` |
| `Lib/Editing/RealEditLocality.lean` | `rowEdit_not_depends_only_counterexample` | `exact` |
| `Lib/Editing/RealEditSemantics.lean` | `dot_zipWith_add` | `dot_zipWith_add_of_length` |
| `Lib/Editing/RealEditSemantics.lean` | `editSemantics_layer_bridge` | `layerOut_cast_eq_clm` |
| `Lib/Editing/RealEditSemantics.lean` | `editSemantics_layer_zero_iff` | `layerOut_zero_iff_clm` |
| `Lib/Editing/RealEditSymbolAgreement.lean` | `agreement_coeffDist_zero` | `roundTrip_perturbation_id` |
| `Lib/Editing/RealEditSymbolAgreement.lean` | `extract_convert_id` | `roundtrip_extractVec` |
| `Lib/Editing/RealEditToSymbol.lean` | `extractVec_blind_to_scale` | `roundtrip_extractVec_rfl` |
| `Lib/Editing/RealEditToSymbol.lean` | `extractVec_mem_preimage` | `roundtrip_convertVec_rfl` |
| `Lib/Editing/RealEditToSymbol.lean` | `preimage_eq_extractVec` | `preimage_subsingleton` |
| `Lib/Editing/RealEditToSymbol.lean` | `roundtrip_extractVec_rfl` | `roundtrip_extractVec` |
| `Lib/Editing/RealEditToSymbol.lean` | `toSymbol_coeffDist_zero` | `roundTrip_perturbation_id` |
| `Lib/Editing/RealEditVerdict.lean` | `edit_verdict_pass` | `le_trans` |
| `Lib/Editing/RealExtractCanonical.lean` | `R02_canonicalize_already_exists` | `canonicalize_cNegVec` |
| `Lib/Editing/RealExtractCanonical.lean` | `R02_correctness_already_exists` | `canonicalize_preserves_sat` |
| `Lib/Editing/RealExtractCanonical.lean` | `R02_sign_obstruction_already_exists` | `canonicalize_scaleVec_neg_cNegVec` |
| `Lib/Editing/RealExtractCanonical.lean` | `R02_uniqueness_already_exists` | `canonicalize_section_pos` |
| `Lib/Editing/RealExtractDecidability.lean` | `scaleClassLayerB_iff` | `scaleClassB_iff` |
| `Lib/Editing/RealExtractInvertibility.lean` | `geluTanh_injOn` | `strictMonoOn_injOn` |
| `Lib/Editing/RealExtractInvertibility.lean` | `geluTanh_injOn_of_analytic` | `geluTanh_injOn_of_gate` |
| `Lib/Editing/RealExtractInvertibility.lean` | `geluTanh_injOn_of_strictMono` | `strictMonoOn_injOn` |
| `Lib/Editing/RealExtractNonInjective.lean` | `convertVec_mem_fiber` | `roundtrip_extractVec` |
| `Lib/Editing/RealExtractNonInjective.lean` | `r03_claim_is_false` | `no_fiber_of_extractVec_has_two_points` |
| `Lib/Editing/RealExtractSurjectivity.lean` | `extractVec_convertVec_rfl` | `roundtrip_extractVec` |
| `Lib/Editing/RealExtractSurjectivity.lean` | `symbol_preimage_unique` | `compileToLayer_injective` |
| `Lib/Editing/RealExtractionDirection.lean` | `extract_drops_unterminated` | `decode_drops_trailing_partial` |
| `Lib/Editing/RealExtractionDirection.lean` | `extract_render_left_inverse` | `decode_encode` |
| `Lib/Editing/RealExtractionDirection.lean` | `extract_to_weights` | `symbolToWeight_correct` |
| `Lib/Editing/RealGramEdit.lean` | `gram_vs_closed_residual` | `gramEdit_eq_batchClosed` |
| `Lib/Editing/RealLayerSemanticQuotient.lean` | `r04_convertVec_semEq_scaled` | `convertVec_respects_semEq` |
| `Lib/Editing/RealLayerSemanticQuotient.lean` | `semQuotient_merges_scale_orbit` | `sound` |
| `Lib/Editing/RealNonlinearExtract.lean` | `closureOperator_extensive` | `subset_extent_intent` |
| `Lib/Editing/RealOperatorSplit.lean` | `t1_pointwise` | `t1_decompose` |
| `Lib/Editing/RealQuotientReversibility.lean` | `constant_map_is_quotient_reversible` | `every_function_is_quotient_reversible` |
| `Lib/Editing/RealQuotientReversibility.lean` | `decode_is_quotient_reversible` | `every_function_is_quotient_reversible` |
| `Lib/Editing/RealQuotientReversibility.lean` | `detokenize_is_section` | `detokenize_left_inverse_on_quotient` |
| `Lib/Editing/RealQuotientReversibility.lean` | `tokenize_is_quotient_reversible` | `every_function_is_quotient_reversible` |
| `Lib/Editing/RealRepairMetric.lean` | `iterate_id_apply` | `induction` |
| `Lib/Editing/RealRepairMetric.lean` | `repairTo_preserves` | `repairTo_lands` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `factorsThrough_and_leftInverse_gives_factorsThrough` | `roundTripAddsNothing_of_factorsThrough` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `roundTripAddsNothing_of_factorsThrough_of_fiberPreds` | `roundTripAddsNothing_of_factorsThrough` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `rt1_is_instance_of_branch_B` | `roundTripAddsNothing_of_leftInverse` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `rt1_leftInverse` | `extractLayer_compileToLayer` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `rt1_matches_existing` | `closed_loop_adds_nothing` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `rt2_is_instance_of_branch_B` | `roundTripAddsNothing_of_leftInverse` |
| `Lib/Editing/RealRoundTripVacuity.lean` | `rt2_leftInverse` | `roundtrip_extractVec` |
| `Lib/Editing/RealRoundtripBound.lean` | `extract_compile_identity_int` | `roundtrip_extract` |
| `Lib/Editing/RealRoundtripBound.lean` | `extract_compile_identity_vec` | `roundtrip_extractVec` |
| `Lib/Editing/RealRoundtripBound.lean` | `roundtrip_error_bound_uniform` | `roundtrip_error_bound` |
| `Lib/Editing/RealRoundtripBound.lean` | `roundtrip_under_pruning` | `roundtrip_under_quantization` |
| `Lib/Editing/RealRoundtripNondegenerate.lean` | `dot_append_zero_left_d21` | `dot_append_zero_d21` |
| `Lib/Editing/RealRoundtripNondegenerate.lean` | `dot_of_append_zeros_d21` | `dot_append_replicate_d21` |
| `Lib/Editing/RealRoundtripNontrivial.lean` | `map_extractVec_compileToLayer_rfl` | `map_extractVec_compileToLayer_eq_self` |
| `Lib/Editing/RealRoundtripNontrivial.lean` | `roundTripNeedsProof_is_false` | `no_nontrivial_roundtrip_subset` |
| `Lib/Editing/RealRoundtripRat.lean` | `ratSemanticallyParallel_scaleVecQ_iff` | `ratSemanticallyParallel_of_scaleVecQ` |
| `Lib/Editing/RealSparseEdit.lean` | `sparse_edit_op_bound` | `le_trans` |
| `Lib/Editing/RealSymbolDomainWidening.lean` | `d31_dot_additive_iff_no_truncation` | `dot_append_additive_iff` |
| `Lib/Editing/RealTwoSidedEditEquiv.lean` | `E8_e2e_kernel_inert` | `E8_later_ring_inert` |
| `Lib/FCA/RealFCAAbstractionSoundness.lean` | `fcaClosure_idempotent` | `closure_idempotent` |
| `Lib/FCA/RealFCAAbstractionSoundness.lean` | `fcaClosure_mono` | `extent_antitone` |
| `Lib/FCA/RealFCAAbstractionSoundness.lean` | `subset_fcaClosure` | `subset_extent_intent` |
| `Lib/FCA/RealFCAElementApplication.lean` | `constraint_element_iff_no_split` | `no_upper_iff_no_split` |
| `Lib/FCA/RealFCAElementApplication.lean` | `constraint_element_or_concept` | `up_gaze_element_or_concept` |
| `Lib/FCA/RealFCAElementApplication.lean` | `constraint_suspend_dissolves_identity` | `suspend_dissolves_identity` |
| `Lib/FCA/RealFCAElementApplication.lean` | `constraint_suspend_idempotent` | `suspend_idempotent` |
| `Lib/FCA/RealFCAElementApplication.lean` | `constraint_suspend_preserves_base` | `suspend_preserves_base` |
| `Lib/FCA/RealFCAElementApplication.lean` | `entailmentSet_eq_closure` | `constraint_entailment_closure` |
| `Lib/FCA/RealFCAImplicationBasis.lean` | `implClosure_extensive` | `subset_intent_extent` |
| `Lib/FCA/RealFCAImplicationBasis.lean` | `implClosure_idempotent` | `intent_closure_idempotent` |
| `Lib/FCA/RealFCAImplicationBasis.lean` | `impl_of_subset` | `extent_antitone` |
| `Lib/FCA/RealFCAInstance.lean` | `entailment_closure_idempotent` | `intent_closure_idempotent` |
| `Lib/FCA/RealFCATokenization.lean` | `closure_idempotent_isPrefixRel` | `closure_idempotent` |
| `Lib/FCA/RealFCATokenization.lean` | `galois_connection_isPrefixRel` | `galois_connection` |
| `Lib/FCA/RealFCATokenization.lean` | `intent_antitone_isPrefixRel` | `intent_antitone` |
| `Lib/FCA/RealFCATokenization.lean` | `intent_closure_idempotent_isPrefixRel` | `intent_closure_idempotent` |
| `Lib/FCA/RealFCATriadicCompleteLattice.lean` | `tcl_triExtent_extensive` | `subset_extent_intent` |
| `Lib/FCA/RealFCATriadicCompleteLattice.lean` | `tcl_triExtent_mono_restated` | `tcl_triExtent_monotone` |
| `Lib/FloatStackRefinement.lean` | `float_stack_refinement` | `netAct_deviation_le_devB` |
| `Lib/InfoTheory/RealFisherInfo.lean` | `score_log_derivative` | `log_derivative_identity` |
| `Lib/InfoTheory/RealInformationGeometry.lean` | `fisherMetric_degenerate_iff` | `fisherMatrix_zero_direction_score` |
| `Lib/InfoTheory/RealInformationGeometry.lean` | `fisherMetric_self_nonneg` | `fisherMatrix_psd` |
| `Lib/InfoTheory/RealInformationGeometry.lean` | `kl_eq_sum` | `kl_as_sum_log_sub_log` |
| `Lib/InfoTheory/RealKLConvexity.lean` | `log_concave_two` | `log_concave_pair` |
| `Lib/InfoTheory/RealKLConvexity.lean` | `mul_log_convex_two` | `mul_log_convex_pair` |
| `Lib/InfoTheory/RealKleeneFixedPoint.lean` | `kleeneChain_le_of_le` | `kleeneChain_monotone` |
| `Lib/InfoTheory/RealKleeneFixedPoint.lean` | `kleeneLimit_unique_minimal` | `le_antisymm` |
| `Lib/InfoTheory/RealMaxEntropyII.lean` | `unique_theta_for_moment_of_mono` | `unique_theta_for_moment` |
| `Lib/InfoTheory/RealMutualInformation.lean` | `gibbs_term` | `gibbs_ineq` |
| `Lib/InfoTheory/RealOptimalTransport.lean` | `dual_weak_optimal` | `dual_weak` |
| `Lib/InfoTheory/RealRNGibbs.lean` | `klMeasure_nonpos` | `rnDerivLog_integral_nonpos` |
| `Lib/InfoTheory/RealWasserstein.lean` | `kp_lipschitz_bound` | `le_trans` |
| `Lib/LearningTheory/RealBanditTheory.lean` | `ucb_confidence_radius` | `hoeffding_two_sided` |
| `Lib/LearningTheory/RealBayesOptimality.lean` | `bayesRisk_le_minimax_upper` | `bayesRisk_le_worstCase` |
| `Lib/LearningTheory/RealConstrainedDecoding.lean` | `constrained_agrees_with_constraint_set` | `constrainedSoftmax_support_iff_allowed` |
| `Lib/LearningTheory/RealConstrainedDecodingVerify.lean` | `allowed_is_convex_weights` | `exact` |
| `Lib/LearningTheory/RealConstrainedDecodingVerify.lean` | `support_from_decoded_constraints` | `constrained_agrees_with_constraint_set` |
| `Lib/LearningTheory/RealConversionFixedPoint.lean` | `compileObs_closure_trivial` | `obsClosure_id_of_injective` |
| `Lib/LearningTheory/RealConversionFixedPoint.lean` | `obsClosure_fixedPoints_eq_range` | `closure_fixedPoints_eq_range` |
| `Lib/LearningTheory/RealConversionFixedPoint.lean` | `rt_eq_self` | `extractLayer_compileToLayer` |
| `Lib/LearningTheory/RealDistill.lean` | `distill_delta_nonneg` | `le_trans` |
| `Lib/LearningTheory/RealDistillGeneralization.lean` | `distract_excess_of_uniform_distance` | `distill_excess_of_uniform_distance` |
| `Lib/LearningTheory/RealFieldGeneralization.lean` | `gen_GD_contraction_step` | `GD_contraction_step` |
| `Lib/LearningTheory/RealFieldGeneralization.lean` | `gen_GD_contraction_step_complex` | `gen_GD_contraction_step` |
| `Lib/LearningTheory/RealFieldGeneralization.lean` | `gen_GD_contraction_step_real` | `gen_GD_contraction_step` |
| `Lib/LearningTheory/RealFieldGeneralization.lean` | `gen_isometry_preserves_norm` | `isometry_preserves_norm_scalar` |
| `Lib/LearningTheory/RealGaussianProcess.lean` | `gpCovariance_psd_iff_featureMap` | `kernelGramMatrix_psd_iff_exists_featureMap` |
| `Lib/LearningTheory/RealGaussianProcess.lean` | `gpRidgeSystem_holds` | `noiseMatrix_mulVec_alpha` |
| `Lib/LearningTheory/RealGeneralizationBound.lean` | `sound'` | `sound` |
| `Lib/LearningTheory/RealHyperparameterBound.lean` | `chord_exp_le_cosh_sinh` | `chord_hull_abs` |
| `Lib/LearningTheory/RealSamplingBoost.lean` | `boost_verify_chain` | `boost_confidence` |
| `Lib/LearningTheory/RealSemiringGeneralization.lean` | `cauchy_schwarz_sq_form` | `cauchy_schwarz_finset` |
| `Lib/LearningTheory/RealSemiringGeneralization.lean` | `cauchy_schwarz_univ_fin` | `cauchy_schwarz_finset` |
| `Lib/LearningTheory/RealSemiringGeneralization.lean` | `holder_two_is_cauchy` | `cauchy_schwarz_finset` |
| `Lib/LearningTheory/RealSemiringGeneralization.lean` | `sq_add_two_le` | `sq_add_le_two_mul_sq_add_sq` |
| `Lib/LearningTheory/RealSemiringGeneralization.lean` | `weighted_power_mean_two` | `weighted_cauchy_schwarz` |
| `Lib/LearningTheory/RealSpeculativeOptimal.lean` | `acceptMass_is_coupling_max` | `coupling_accept_bound` |
| `Lib/LearningTheory/RealVariationalBayes.lean` | `meanField_elbo_le_log_marginal_interface` | `meanField_isProb` |
| `Lib/LearningTheory/RealVariationalInference.lean` | `elbo_linear_rate` | `contraction_converges` |
| `Lib/Lift/RealNonlinearFidelity_parts/A.lean` | `zeroFixingR_iff_of_monotone` | `zeroFixingR_iff_unique_zero` |
| `Lib/Lift/RealNonlinearFidelity_parts/A.lean` | `zeroFixingR_iff_of_monotone_and_mono` | `zeroFixingR_iff_of_monotone` |
| `Lib/Lift/RealNonlinearFidelity_parts/A.lean` | `zeroFixingZ_of_strictMono` | `zeroFixing_of_strictMono` |
| `Lib/Lift/RealNonlinearFidelity_parts/B.lean` | `neg_zeroFixing_reluZ` | `reluZ_not_zeroFixing` |
| `Lib/Lift/VerifyLoopConvergence.lean` | `even_loop_stays` | `induction` |
| `Lib/Linear/Multivar.lean` | `multivar_converges` | `progress` |
| `Lib/Linear/Multivar.lean` | `multivar_converges_in_one` | `step_residual` |
| `Lib/Linear/PenaltyPerturb.lean` | `exists_decrease_one` | `exists_decrease` |
| `Lib/Linear/PenaltyPerturb.lean` | `exists_decrease_zero` | `exists_decrease` |
| `Lib/Linear/PenaltyVector.lean` | `sqNorm_resid_eq_zero_iff` | `sqNorm_eq_zero_iff` |
| `Lib/Linear/Residual.lean` | `linear_converges` | `progress` |
| `Lib/Linear/Residual.lean` | `linear_converges_in_one` | `linearFix_residual` |
| `Lib/Linear/Residual.lean` | `sqPenalty_exact_gives_sound` | `exact_implies_sound` |
| `Lib/LinearAlgebra/RealComplexSpectral.lean` | `cspec_hermitian_eigenvalue_im` | `cspec_hermitian_eigenvalue_im_zero` |
| `Lib/LinearAlgebra/RealComplexSpectral.lean` | `cspec_root_eigenvalue_bridge_direction_only` | `cspec_eigenvalue_isRoot_charpoly` |
| `Lib/LinearAlgebra/RealEckartYoung.lean` | `frobeniusNorm_nonneg_error` | `frobeniusNorm_nonneg` |
| `Lib/LinearAlgebra/RealFrobeniusDichotomy.lean` | `add_pow_eq_of_expChar` | `frobenius_add_eq` |
| `Lib/LinearAlgebra/RealGelfand.lean` | `gelfand_eigenvalue_abs_le_opNorm` | `spectral_radius_le_opNorm` |
| `Lib/LinearAlgebra/RealGelfand.lean` | `gelfand_radius_le_opNorm_general` | `gelfand_radius_le_opNorm` |
| `Lib/LinearAlgebra/RealGelfand.lean` | `gelfand_radius_one_le` | `le_trans` |
| `Lib/LinearAlgebra/RealGelfand.lean` | `gelfand_radius_pow_le_opNorm_pow` | `le_trans` |
| `Lib/LinearAlgebra/RealHessian.lean` | `second_order_sufficient_multidim` | `strict_min_of_quadratic_lower_bound` |
| `Lib/LinearAlgebra/RealInfiniteDim.lean` | `compBound_le_of_le` | `compBound_monotone` |
| `Lib/LinearAlgebra/RealInfiniteDim.lean` | `lengthBound_le_of_le` | `bound_monotone_in_length` |
| `Lib/LinearAlgebra/RealInnerScalar.lean` | `inner_self_norm_sq_scalar` | `exact` |
| `Lib/LinearAlgebra/RealIsometry.lean` | `rotateR_preserves_norm_rdot` | `rotate_preserves_dot` |
| `Lib/LinearAlgebra/RealLowRank.lean` | `low_rank_error_budget` | `le_trans` |
| `Lib/LinearAlgebra/RealMatrixStability.lean` | `contraction_pow_le_one` | `le_trans` |
| `Lib/LinearAlgebra/RealMatrixStability.lean` | `matrixStability_contraction_pow_bound` | `op_norm_pow_apply_le_of_le` |
| `Lib/LinearAlgebra/RealMatrixStability.lean` | `op_norm_pow_le_simple` | `op_norm_pow_le` |
| `Lib/LinearAlgebra/RealPseudoInverse.lean` | `projection_range_subset` | `matvecE_mul` |
| `Lib/LinearAlgebra/RealRandomMatrixTheory.lean` | `spectral_concentration_around_expectation` | `spectral_concentration_of_markov` |
| `Lib/LinearAlgebra/RealRandomMatrixTheory.lean` | `spectral_concentration_of_markov` | `markov_counting` |
| `Lib/LinearAlgebra/RealRandomMatrixTheory.lean` | `spectral_radius_concentration_transfer` | `gelfand_radius_le_opNorm` |
| `Lib/LinearAlgebra/RealRandomMatrixTheory.lean` | `spectral_radius_le_opNorm_of_real_eigenvalue` | `spectral_radius_le_opNorm` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `norm_difference_eq_kernel_distance` | `metric_eq_kernel_expansion` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `normalizedKernel_gram_diag_one` | `normalizedKernel_self` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `reproducing_property_self` | `reproducing_property` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `rkhs_distance_nonneg` | `metric_kernel_nonneg` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `rkhs_distance_zero_iff` | `kernel_metric_zero_iff` |
| `Lib/LinearAlgebra/RealReproducingKernelTheory.lean` | `rkhs_norm_sq_nonneg_of_psd` | `kernel_diag_nonneg` |
| `Lib/LinearAlgebra/RealSparseCodingCounterexamples.lean` | `proxL1_optimal` | `softThresh_is_min` |
| `Lib/LinearAlgebra/RealSparseCodingCounterexamples.lean` | `softThresh_le_of_is_min` | `softThresh_is_min` |
| `Lib/LinearAlgebra/RealSparsity.lean` | `prune_op_norm_bound` | `le_trans` |
| `Lib/LinearAlgebra/RealSparsity.lean` | `prune_threshold_global` | `prune_magnitude_bound` |
| `Lib/LinearAlgebra/RealSpectral.lean` | `eigenvalue_abs_le_frobenius` | `le_trans` |
| `Lib/LinearAlgebra/RealSpectralRadius.lean` | `opNorm_diagonal` | `le_antisymm` |
| `Lib/LinearAlgebra/RealSpectralRadius.lean` | `spectral_radius_le_opNorm_diag` | `spectral_radius_le_opNorm` |
| `Lib/LinearAlgebra/RealSubspaceConstraint.lean` | `subspace_proj_idempotent` | `proj_fixed` |
| `Lib/Meta/RealCounterexamples.lean` | `cex_ce_not_joint_convex` | `ce_not_joint_convex` |
| `Lib/Meta/RealCounterexamples.lean` | `cex_silu_lipschitz_on_bounded` | `silu_lipschitz_on` |
| `Lib/Meta/RealCounterexamples.lean` | `cex_slater_not_sufficient_discrete` | `slater_not_sufficient_discrete` |
| `Lib/Meta/RealCounterexamples.lean` | `cex_unit_normalize_two_div_not_attained` | `unit_normalize_two_div_not_attained` |
| `Lib/Meta/RealDotRepresentationAudit.lean` | `dot_audit_padding_truncation_agree` | `dot_eq_dotProduct` |
| `Lib/Meta/RealDotRepresentationAudit.lean` | `dot_representation_agreement_bridge` | `dot_eq_dotProduct` |
| `Lib/Meta/RealDotRepresentationAudit.lean` | `toVec_audit_counterexample_axis` | `toVec_not_injective_without_length` |
| `Lib/Meta/RealHypothesisAudit.lean` | `audit_is_contentful` | `audit_is_contentful_iff_not_all` |
| `Lib/Meta/RealHypothesisAudit.lean` | `audit_no_false_positive` | `compileFailed_not_refutes` |
| `Lib/Meta/RealRflAudit.lean` | `instanceA_rfl_level` | `extractVec_convertVec_rfl` |
| `Lib/Meta/RealRflAudit.lean` | `interface_implies_no_new_semantics` | `roundTripAddsNothing_of_factorsThrough` |
| `Lib/Optim/ModEqBridge.lean` | `congruentInt_to_modEq` | `congruent_to_modEq` |
| `Lib/Optim/ModEqBridge.lean` | `modEq_to_congruentInt` | `modEq_to_congruent` |
| `Lib/Optim/RealConversionStabilityConvergence.lean` | `closureOperator_isClosureOperator` | `extract_idempotent` |
| `Lib/Optim/RealEarlyStopping.lean` | `earlyStopping_le_full` | `mono_le_of_le` |
| `Lib/Optim/RealErrorFeedback.lean` | `ef_sgd_rate` | `sgd_rate_bound` |
| `Lib/Optim/RealFedAsync.lean` | `async_random_delay_converges` | `async_bounded_delay_converges` |
| `Lib/Optim/RealFedAsync.lean` | `fedsgd_epsilon_condition` | `neighborhood_scope` |
| `Lib/Optim/RealFedAsync.lean` | `random_delay_recovers_bounded` | `async_random_delay_converges` |
| `Lib/Optim/RealGLUTraining.lean` | `geglu_lipschitz` | `glu_lipschitz` |
| `Lib/Optim/RealGLUTraining.lean` | `glu_lipschitz` | `gated_lipschitz` |
| `Lib/Optim/RealGLUTraining.lean` | `glu_step_error_bound` | `glu_lipschitz` |
| `Lib/Optim/RealGLUTraining.lean` | `reglu_lipschitz` | `glu_lipschitz` |
| `Lib/Optim/RealGLUTraining.lean` | `siluGLU_lipschitz` | `glu_lipschitz` |
| `Lib/Optim/RealListFinBridge.lean` | `dot_eq_dotProduct_of_length` | `dot_eq_dotProduct` |
| `Lib/Optim/RealNesterovLower.lean` | `one_dim_lower_witness` | `one_dim_lower_witness_core` |
| `Lib/Optim/RealNewtonRate.lean` | `newton_exact_step_on_quadratic` | `newton_step_quadratic` |
| `Lib/Optim/RealProximalMoreau.lean` | `moreau_decomposition_linear_isprox` | `prox_linear` |
| `Lib/Optim/RealProximalMoreau.lean` | `normsq_inner_le` | `le_trans` |
| `Lib/Optim/RealProximalMoreau.lean` | `normsq_sub_expand` | `normsq_sub` |
| `Lib/Optim/RealRateLower.lean` | `gd_quadratic_exact` | `gd_sharpness` |
| `Lib/Optim/RealRateLower.lean` | `gd_rate_is_sharp` | `gd_sharpness` |
| `Lib/Optim/RealRateLower.lean` | `no_better_than_geometric` | `no_faster_than_geometric` |
| `Lib/Optim/RealRegularizedMDP.lean` | `kl_eq_sum_log_sub` | `kl_as_sum_log_sub_log` |
| `Lib/Optim/RealRiemannianGD.lean` | `euclidean_sphereGD_mem_sphere` | `sphereGD_mem_sphere` |
| `Lib/Optim/RealRiemannianGD.lean` | `sphereGD_mem_unitSphere` | `sphereGD_mem_sphere` |
| `Lib/Optim/RealRiemannianGD.lean` | `sphereGD_norm` | `projSphere_norm` |
| `Lib/Optim/RealSGDRate.lean` | `sgd_projected_rate_bound` | `sgd_rate_bound` |
| `Lib/Optim/RealSGDStochastic.lean` | `ExpDist_nonneg` | `Expect_nonneg` |
| `Lib/Optim/RealSGDStochastic.lean` | `sgd_variance_nonneg` | `Expect_nonneg` |
| `Lib/Optim/RealSeamBridges2.lean` | `admissible_of_unique_bayes_qualified` | `unique_bayes_admissible` |
| `Lib/Optim/RealSeamBridges2.lean` | `castConstraint_b_eq_convertVec_b` | `convertVec_bias_eq_convertRealVec_bias` |
| `Lib/Optim/RealSeamBridges2.lean` | `isStrictLocalMax_toIsLocalMax_via_saddle` | `toIsLocalMax` |
| `Lib/Optim/RealSecondOrderNoModulus.lean` | `modulus_of_posDef_bound` | `exists_modulus_of_posDef` |
| `Lib/Optim/RealSecondOrderUpgrade.lean` | `second_order_necessary_multidim_no_hhess` | `second_order_necessary_multidim` |
| `Lib/Optim/RealSecondOrderUpgrade.lean` | `second_order_taylor_unconditional` | `second_order_taylor` |
| `Lib/Penalty/Counterexample.lean` | `quadraticPlusOne_localMin` | `isLocalMin_of_forall_le` |
| `Lib/Quantization/RealCompressionRate.lean` | `compression_rate_sqrt` | `sgd_rate_bound` |
| `Lib/Quantization/RealConversionStabilityFloatBounds.lean` | `ceMag_nonneg` | `le_trans` |
| `Lib/Quantization/RealIEEE754/Basic.lean` | `ieee_round_zero` | `le_antisymm` |
| `Lib/Quantization/RealIEEE754/Compat.lean` | `ieee_format_error_bound` | `format_error_bound` |
| `Lib/Quantization/RealIEEE754/Compat.lean` | `ieee_format_round_idempotent` | `format_round_idempotent` |
| `Lib/Quantization/RealIEEE754/Compat.lean` | `ieee_op_error_propagation` | `op_error_propagation` |
| `Lib/Quantization/RealIEEE754/Compat.lean` | `ieee_round_close` | `round_close` |
| `Lib/Quantization/RealIEEE754/Overflow.lean` | `clampTo_idem` | `clampTo_eq_self` |
| `Lib/Quantization/RealLoRA.lean` | `lora_edit_verdict` | `le_trans` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `fp16Sat_mono` | `clampTo_mono` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_accumulation_error_bound` | `accumulation_error_bound` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_fp16_round_abs_bound` | `fp16_round_abs_bound` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_fp16_underflow_dominated` | `fp16_underflow_dominated` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_loss_scaling_no_overflow` | `loss_scaling_no_overflow` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_mixed_layer_error` | `mixed_layer_error` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_mixed_matrix_frobenius_error` | `mixed_matrix_frobenius_error` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_mixed_matrix_op_error` | `mixed_matrix_op_error` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_mixed_vs_full_precision` | `mixed_vs_full_precision` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_single_add_error` | `format_add_error` |
| `Lib/Quantization/RealMixedPrecisionRounding.lean` | `ieee_single_mul_error` | `format_mul_error` |
| `Lib/Quantization/RealQuantizedError.lean` | `quant_delta_nonneg` | `le_trans` |
| `Lib/Quantization/RealStructuredPruning.lean` | `channel_op_bound` | `le_trans` |
| `Lib/Quantization/RealStructuredPruning.lean` | `head_op_bound` | `channel_op_bound` |
| `Lib/Quantization/RealStructuredPruning.lean` | `head_pruning_bound` | `channel_pruning_bound` |
| `Lib/Quantization/RealStructuredPruning.lean` | `structured_op_bound` | `le_trans` |
| `Primitives/MultistepLoop.lean` | `bidir_steps` | `converges_within` |
| `Runtime/ActivationLadder.lean` | `activationLadder_forward` | `ladder_forward` |
| `Runtime/ApproxExtraction.lean` | `compose_via_calculus` | `triangle_combine` |
| `Runtime/ApproxLadder.lean` | `approx_ladder_bound_mono` | `le_trans` |
| `Runtime/ApproxLadder.lean` | `roundingLadder_forward` | `approx_ladder_forward` |
| `Runtime/ApproximationBridge.lean` | `approx_min_le_gives_sat` | `loss_bound_gives_resid_bound` |
| `Runtime/ApproximationBridge.lean` | `loss_bound_gives_resid_bound` | `abs_resid_le_of_loss_le_sq` |
| `Runtime/ApproximationBridge.lean` | `loss_controls_violation` | `loss_bound_gives_resid_bound` |
| `Runtime/ComboN.lean` | `comboN_preserves` | `exact` |
| `Runtime/CompilerScheme.lean` | `backend_compiles_sound` | `compileProgram_sound` |
| `Runtime/CompilerScheme.lean` | `backend_sound` | `sound` |
| `Runtime/CompilerScheme.lean` | `every_backend_sound` | `backend_sound` |
| `Runtime/ConvertVectorLinear.lean` | `sat_iff_list_sat` | `toFinVec` |
| `Runtime/EndToEnd.lean` | `decode_encode` | `roundtrip` |
| `Runtime/ErrorCalculus.lean` | `chain_error_two` | `triangle_combine` |
| `Runtime/ErrorCalculus.lean` | `mono` | `le_trans` |
| `Runtime/Extraction.lean` | `extract_compile` | `roundtrip` |
| `Runtime/Extraction.lean` | `roundtrip_idempotentOn` | `idempotentOn_of_leftInverse` |
| `Runtime/Extraction.lean` | `roundtrip_iterate` | `iterate_comp_of_leftInverse` |
| `Runtime/GeoSampledBound.lean` | `residual_le_of_zero_on_dense_from_generic` | `residual_le_of_zero_on_dense_of_d` |
| `Runtime/L1L2Roundtrip.lean` | `decodeConst_encodeForm` | `payload_getElem` |
| `Runtime/LossyRepresentation.lean` | `lossy_weaker` | `semantic_not_injective` |
| `Runtime/LossyRepresentation.lean` | `ofRepresentation_roundtrip` | `roundtrip` |
| `Runtime/MultiLayerLadder.lean` | `multiLayerLadder_forward` | `ladder_forward` |
| `Runtime/MultiLayerLadder.lean` | `multiLayerLadder_two` | `ladder_forward` |
| `Runtime/RealTokenization.lean` | `foldBlanks_idem` | `foldGo_idem` |
| `Runtime/RealTokenization.lean` | `foldBlanks_length_le` | `foldGo_length_le` |
| `Runtime/RealTokenization.lean` | `tokenize_detok` | `tokenizeRaw_detok` |
| `Runtime/SaturationQuantization.lean` | `satQuant_saturation` | `clamp_error` |
| `Runtime/StackCodegen.lean` | `stackDepth_left` | `le_trans` |
| `Runtime/StackCodegen.lean` | `stackDepth_right` | `le_succ_of_pred_le` |
| `Runtime/StackError.lean` | `gain_nonneg` | `le_trans` |
| `Runtime/TokenAlphabet.lean` | `alphabet_classifiable` | `classify_total` |
| `Runtime/VerifyLoopProgress.lean` | `verify_stable` | `iterateRepair_eq_self` |
| `Runtime/WeightLadder.lean` | `weightLadder_forward` | `ladder_forward` |
| `Semantics/Annotations.lean` | `edit_frame_holds` | `holdsSet_member` |
| `Semantics/Annotations.lean` | `holdsSet_member` | `holdsSet_mem` |
| `Semantics/Merge.lean` | `merge_sound` | `holdsSet_of_sublist` |
| `Semantics/PostTrain.lean` | `post_train_preserves_holds` | `post_train_preserves` |
| `Semantics/PostTrain.lean` | `post_train_preserves_set` | `post_train_preserves` |
| `Semantics/Stage1.lean` | `inherits_sound` | `sound` |
| `Semantics/VocabEdit.lean` | `split_error_bound` | `merge_error_bound` |
| `Semantics/VocabEdit.lean` | `vocab_compat_permutation` | `vocab_edit_permutation_exact` |
