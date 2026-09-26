# Where each result is formalized

One row per labelled result of the paper and its supplemental materials, 43 in all. The
Declarations column lists the theorems that state the result's clauses. The same table is
[`map.tsv`](map.tsv).

![Proof map](proofmap.png)

| Result | Module | Declarations |
|---|---|---|
| Theorem 1 | `Multiway/Spanning.lean` | `Multiway.spanning`, `Multiway.spanning_condition_iff`, `Multiway.augSlope_existsUnique`, `Multiway.mfeSlope_exists`, `Multiway.mfeSlope_unique`, `Multiway.identified_iff_inner_pos` |
| Proposition 1 | `Multiway/DimensionWise.lean` | `Multiway.spanning_of_single`, `Multiway.spanning_of_pairwise`, `Multiway.commute_of_uniform_spanning` |
| Proposition 2 | `Multiway/Pairwise.lean` | `Multiway.proj_mul_proj_eq_grandMeanProj_iff`, `Multiway.proj_mul_proj_eq_grandMeanProj_iff_of_surjective` |
| Theorem 2 | `Multiway/Proportional.lean, Multiway/ProjBridge.lean` | `Multiway.commute_iff_proportional`, `Multiway.commute_iff_proportional_of_surjective`, `Multiway.proportional_iff_pairCount_eq_one`, `Multiway.uniformlyFEEquivalent_iff_proportional` |
| Theorem 3 | `Multiway/JointProjection.lean` | `Multiway.jm_equiv`, `Multiway.jm_isLeast`, `Multiway.within_inner_dummy_eq_zero` |
| Theorem 4 | `Multiway/CLT.lean, Multiway/CLTMartingale.lean` | `Multiway.CLT.clt_a`, `Multiway.CLT.clt_a_mfe`, `Multiway.CLT.clt_a_unconditional_of_design`, `Multiway.CLT.clt_b`, `Multiway.CLT.clt_b_mfe` |
| Theorem 5 | `Multiway/SteinCluster.lean, Multiway/ClusterJanson.lean, Multiway/ClusterJansonB.lean` | `Multiway.SteinCluster.cltcluster_a_oneDimension_betaJM`, `Multiway.SteinCluster.cltcluster_a_general_betaJM`, `Multiway.SteinCluster.cltcluster_b_general_betaJM`, `Multiway.ClusterJanson.cltcluster_a_general_betaJM_janson_printed`, `Multiway.ClusterJanson.cltcluster_b_general_betaJM_janson_printed` |
| Theorem 6 | `Multiway/PiInf.lean` | `Multiway.PiInf.pi_clt`, `Multiway.PiInf.pi_clt_std`, `Multiway.PiInf.pi_clt_unconditional_of_design_closed` |
| Theorem 7 | `Multiway/Vhat.lean` | `Multiway.Vhat.vhat_wald`, `Multiway.Vhat.vhat_wald_of_nVhat` |
| Theorem 8 | `Multiway/UnionMeat.lean` | `Multiway.UnionMeat.unionmeat_a`, `Multiway.UnionMeat.unionmeat_b_identity`, `Multiway.UnionMeat.unionmeat_b_bound`, `Multiway.UnionMeat.unionmeat_c` |
| Theorem 9 | `Multiway/Plugin.lean` | `Multiway.Plugin.plugMeat_sub_target_isBigOp`, `Multiway.Plugin.plugMeat_sub_target_tendstoInProb_uncond`, `Multiway.Plugin.thetaHat_sub_isBigOp`, `Multiway.Plugin.plugin_wald_of_meat` |
| Theorem 10 | `Multiway/Absorbed.lean` | `Multiway.Absorbed.caseOne_nVhatCGM_tendstoInProb`, `Multiway.Absorbed.caseTwo_nVhatCGM_tendstoInProb`, `Multiway.Absorbed.caseOne_nVhatCGM_tendstoInProb_uncond`, `Multiway.Absorbed.caseTwo_nVhatCGM_tendstoInProb_uncond` |
| Theorem 11 | `Multiway/RateAgnostic.lean, Multiway/Wald.lean` | `Multiway.RateAgnostic.rateAgnostic_a_ae`, `Multiway.RateAgnostic.rateAgnostic_b_ae`, `Multiway.Wald.wald_of_clt_rateAgnostic` |
| Theorem 12 | `Multiway/PiInf.lean` | `Multiway.PiInf.piinf_a`, `Multiway.PiInf.piinf_wald`, `Multiway.PiInf.piinf_c` |
| Lemma SM.B.1 | `Multiway/Incremental.lean` | `Multiway.incremental_projector`, `Multiway.incrementalProjector_eq_starProjection`, `Multiway.range_incrementalMundlak_eq`, `Multiway.finrank_range_incrementalMundlak`, `Multiway.incrementalProjector_comp_orthogonal` |
| Lemma SM.B.2 | `Multiway/Local.lean` | `Multiway.local_spanning`, `Multiway.local_spanning_of_two_dimensions` |
| Lemma SM.B.3 | `Multiway/CrossProjector.lean` | `Multiway.entries_crossProjector_mul`, `Multiway.mulVec_proj_apply`, `Multiway.proj_mul_proj_summand` |
| Lemma SM.B.4 | `Multiway/PiHat.lean, Multiway/PiHatCre.lean` | `Multiway.PiHat.piHat_eq`, `Multiway.PiHat.piHat_sub_eq`, `Multiway.PiHat.condExp_piHat_sub_mul`, `Multiway.PiHat.condExp_piHat_sub_eq_zero`, `Multiway.PiHatCre.condExp_piHat_sub_eq_zero_of_components` |
| Lemma SM.B.5 | `Multiway/Moments.lean` | `Multiway.Moments.condExp_fourth_idiosyncratic_le`, `Multiway.Moments.condExp_fourth_idiosyncratic_le_const`, `Multiway.Moments.condExp_fourth_idiosyncratic_le_regime1`, `Multiway.Moments.condExp_fourth_idiosyncratic_le_const_regime1`, `Multiway.Moments.condExp_fourth_components_le_regime1` |
| Lemma SM.B.6 | `Multiway/Leverage.lean, Multiway/LeverageCond.lean, Multiway/LeverageCondRegime1.lean` | `Multiway.residualMaker_isSelfAdjoint`, `Multiway.residualMaker_isIdempotentElem`, `Multiway.trace_residualMaker`, `Multiway.feResidual_eq_residualMaker_apply`, `Multiway.LeverageCond.condExp_feResidual_sq`, `Multiway.LeverageCondRegime1.condExp_feResidual_sq_regimeOne` |
| Lemma SM.B.7 | `Multiway/InclusionExclusion.lean` | `Multiway.multiway_meat_inclusion_exclusion`, `Multiway.multiway_meat_inclusion_exclusion_entry` |
| Lemma SM.B.8 | `Multiway/Cgm.lean, Multiway/CgmLimit.lean, Multiway/Vhat.lean` | `Multiway.Cgm.condExp_meat_idiosyncratic`, `Multiway.Cgm.xiMat_opNorm_le`, `Multiway.CgmLimit.xi_div_card_tendsto_zero`, `Multiway.Vhat.cgm_meat_var_le` |
| Lemma SM.B.9 | `Multiway/PrimitiveDesign.lean` | `Multiway.PrimitiveDesign.cgmsharp_bddInProb`, `Multiway.PrimitiveDesign.cgmsharp_bddInProb_of_moments`, `Multiway.PrimitiveDesign.cgmsharp_tendstoInProb` |
| Lemma SM.B.10 | `Multiway/IdentE2.lean, Multiway/UnionMeat.lean` | `Multiway.IdentE2.levelOne_variances_absent`, `Multiway.IdentE2.residual_moment`, `Multiway.IdentE2.targetplug`, `Multiway.UnionMeat.xGram_levelOne_eq_zero` |
| Lemma SM.B.11 | `Multiway/Sharing.lean` | `Multiway.Sharing.clusterOmega_eq_zero_of_not_linked`, `Multiway.Sharing.card_linkedPairs_le`, `Multiway.Sharing.maxDegree_le_card_mul_maxCluster`, `Multiway.Sharing.sharing_e`, `Multiway.Sharing.sharing_e_lambdaMin_of_graphSupported` |
| Lemma SM.B.12 | `Multiway/Restricted.lean` | `Multiway.posDef_restricted`, `Multiway.transpose_mul_mul_restrictedStd`, `Multiway.sq_l2_opNorm_restrictedStd_le` |
| Lemma SM.B.13 | `Multiway/RateAgnostic.lean` | `Multiway.RateAgnostic.infeasibleMeat_tendstoInProb_nodiv`, `Multiway.RateAgnostic.infeasibleMeat_tendstoInProb_of_regime3_nodiv`, `Multiway.RateAgnostic.perturb_tendstoInProb_of_moments` |
| Lemma SM.B.14 | `Multiway/Sqrt.lean` | `Multiway.frobNorm_sqrt_sub_one_le`, `Multiway.frobSq_sqrt_sub_one_le` |
| Lemma SM.C.1 | `Multiway/Parallel.lean` | `Multiway.parallel_images`, `Multiway.exists_smul_eq_of_forall_mem_span_singleton`, `Multiway.eq_smul_id_of_forall_mem_span_singleton`, `Multiway.ker_le_ker_of_forall_mem_span` |
| Lemma SM.C.2 | `Multiway/Martingale.lean` | `Multiway.DegenerateSum.martingale_representation`, `Multiway.DegenerateSum.multi_martingale_representation`, `Multiway.DegenerateSum.condExp_degenDiff_eq_zero`, `Multiway.DegenerateSum.degenSum_eq_sum_degenDiff` |
| Lemma SM.C.3 | `Multiway/Concentration.lean` | `Multiway.concentration_clause_a`, `Multiway.concentration_clause_b`, `Multiway.concentration_clause_b_general`, `Multiway.concentration_clause_b_general_closed`, `Multiway.concentration_clause_b_general_closed_uniform` |
| Lemma SM.C.4 | `Multiway/Multilinear.lean` | `Multiway.Multilinear.integral_pow_four_multilinear_le`, `Multiway.Multilinear.integral_pow_four_random_le` |
| Lemma SM.C.5 | `Multiway/Quadform.lean, Multiway/CondIndep.lean` | `Multiway.Quadform.condVar_quadForm_le_of_condIndep`, `Multiway.Quadform.condVar_quadForm_le`, `Multiway.CondIndep.condExp_mul_of_condIndepFun` |
| Lemma SM.C.6 | `Multiway/QuadformE2.lean, Multiway/QuadformE2Cont.lean, Multiway/QuadformE2Indep.lean` | `Multiway.QuadformE2.varQuad_eq`, `Multiway.QuadformE2.abs_sum_pairs_le`, `Multiway.QuadformE2Cont.abs_cum4_le_cont` |
| Proposition SM.D.1 | `Multiway/PrimitiveDesign.lean` | `Multiway.PrimitiveDesign.designcond_tendstoInProb_of_primitive`, `Multiway.PrimitiveDesign.designcond_tendstoInProb_uncond`, `Multiway.PrimitiveDesign.designcond_design_ii_uncond`, `Multiway.PrimitiveDesign.quadvar_compl_le_of_primitive` |
| Corollary SM.D.1 | `Multiway/Overlap.lean` | `Multiway.overlap_iff_commute`, `Multiway.overlap_iff_commute_of_dimensionWise` |
| Proposition SM.D.2 | `Multiway/Leverage.lean` | `Multiway.SuffLeverage.leverage_clause_a`, `Multiway.SuffLeverage.leverage_clause_a_bigO`, `Multiway.SuffLeverage.leverage_clause_b`, `Multiway.SuffLeverage.tendstoInProb_leverageRatio` |
| Corollary SM.D.2 | `Multiway/Degeneracy.lean` | `Multiway.score_degeneracy`, `Multiway.withinScore_degeneracy`, `Multiway.score_decomposition`, `Multiway.level_one_eq_zero` |
| Proposition SM.D.3 | `Multiway/Sharing.lean, Multiway/ClusterShockB.lean` | `Multiway.Sharing.threeseq_a_of_design`, `Multiway.Sharing.threeseq_a_accum`, `Multiway.Sharing.threeseq_b`, `Multiway.Sharing.abs_nuVal_le`, `Multiway.Sharing.nuVal_pow_four_le` |
| Corollary SM.D.3 | `Multiway/ClusterShock.lean, Multiway/ClusterShockB.lean, Multiway/ClusterJanson.lean` | `Multiway.ClusterShock.clustershock_a_oneDimension`, `Multiway.ClusterShock.clustershock_a_general`, `Multiway.ClusterJanson.clustershock_a_general_janson`, `Multiway.ClusterShock.clustershock_rateagnostic_a`, `Multiway.ClusterShock.clustershock_rateagnostic_b`, `Multiway.ClusterShock.clustershock_rateagnostic_c` |
| Proposition SM.D.4 | `Multiway/LeverageCond.lean, Multiway/LeverageCondRegime1.lean` | `Multiway.LeverageCond.condExp_meatLC_sub_meat`, `Multiway.LeverageCond.condExp_meatLC_of_homoskedastic`, `Multiway.LeverageCondRegime1.prop_lc_a_random_regimeOne`, `Multiway.LeverageCondRegime1.prop_lc_b_random_regimeOne` |
| Proposition SM.E.1 | `Multiway/Compute.lean, Multiway/Alternating.lean` | `Multiway.starProjection_orthogonal_singleton`, `Multiway.starProjection_joint`, `Multiway.jointProjMat_diag`, `Multiway.Alternating.tendsto_sweepIter` |
| Proposition SM.E.2 | `Multiway/GroupCompute.lean` | `Multiway.superAgg_vec`, `Multiway.superAgg_one`, `Multiway.exactAgg_eq_mobius`, `Multiway.superAgg_residual`, `Multiway.superAgg_residual_interaction`, `Multiway.frobSqRDelta_eq_sum_cellQuad` |
