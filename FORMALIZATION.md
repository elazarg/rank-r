# Formalization coverage

This file is the claim ledger for the tracked manuscripts. It distinguishes a
kernel-checked mathematical assertion from an informal identification of that
assertion with operator-theoretic language.

Status meanings:

- **Checked** — the stated inequality, equality, extremizer, or equivalence is
  a Lean theorem.
- **Checked core** — every new rank-sensitive or scalar inequality is checked,
  but an interface to a notion absent from the development remains.
- **Conditional** — the generic theorem is checked under an explicit
  hypothesis whose intended concrete instance is not composed in Lean.
- **Open formalization** — the manuscript proof is not represented by a Lean
  theorem.
- **Conjecture** — intentionally not claimed as proved.

The global rendering boundary applies throughout: finite-dimensional Hilbert
spaces are represented by matrices over finite coordinate types. The
basis-transport theorem from abstract Hilbert spaces to those coordinates is
an open formalization item. Within fixed coordinates, `pureSchmidtRank` is the
rank of the coefficient matrix, `pureSchmidtRank_vec` proves
`SR(vec A) = rank A`, and `rank_le_iff_exists_sum_rankOne` proves the exact
rank-`k` decomposition used by the Choi bounds.

## Main manuscript

### Mechanism and main theorem

| Manuscript claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| `lem:double-skew` | **Checked** | `doubleSkewBound_of_takagi`, `doubleSkewBound_holds` |
| Fu–Gao–Park projection estimate and its equivalence with the double-skew bound | **Checked** in finite coordinates | `FGPBound_of_doubleSkewBoundQm`, `doubleSkewBound_of_FGP`, `fgpBound_holds`; `fgpBound_iff_pureSchmidtKBound_two` proves equivalence with the direct pure-Schmidt-rank-two statement |
| `def:beta2`, Choi quadratic-form bound | **Checked rendering** | `ChoiTwoBound`; the equality with the published `S(2)`-norm definition is not a theorem about an independently defined norm |
| `beta_2(Λ_U ⊗ Λ_V) ≤ 1` in all dimensions | **Checked** | `choiTwoBound_skewKraus` after scaling |
| `beta_2(Λ_U ⊗ Λ_V) = 1` when both dimensions are at least two; value zero in degenerate dimensions | **Checked** | `choiTwoBound_skewKraus_iff` and the vanishing-family lemmas in `Sharp.lean` |
| `thm:amplification`, all four operator forms | **Checked** | `qform_krausQ_Pneg_le_of_norm`, `qform_krausQ_Pneg_le`, `qform_krausQ_ptransposeUV_ge_of_norm`, `qform_krausQ_ptransposeUV_ge` |
| `thm:pair-amplification` for every `r`, including `r > dim H` | **Checked** in unrolled Choi form | `thetaPositive_of_choiTwoBound`; `ThetaPositive` quantifies over every test matrix of rank at most `r` and does not require an `r`-frame |
| exactness of transpose symmetry / parity remark | **Checked** | `inner_delta_placeQ_zetaV_iff`, `not_qform_krausQ_Pneg_le_skewFam` |
| `prop:operator_ineq` | **Checked** | `operatorIneq_holds`, with conditional variants retaining the Choi-bound input |
| map identity `eq:map-identity` | **Checked** | `Psi_eq_tensor_square`, with monoidality and transpose identities separately checked |
| partial-trace contraction lemma | **Checked** | `contraction_norm`, `contraction_trace`, `hsNormSq_ptraceU_rankFactor`, `hsNormSq_ptraceV_rankFactor` |
| `thm:rank_r`, exact-rank and rank-at-most forms | **Checked** | `rank_r_partial_trace_exact`, `rank_r_partial_trace` |
| strictness below the rank parameter and equality forcing exact rank | **Checked** | `rank_r_partial_trace_strict`, `rank_eq_of_eq_rank_r_partial_trace` |
| optimal coefficients and displayed extremizers | **Checked** for coordinate-basis witnesses | `projWit_bound_eq`, `le_coeff_hsNormSq_of_bound`, `inv_le_coeff_trace_of_bound`; arbitrary unit `v,w` identities are not separately formalized because the basis cases already certify optimality |
| covariance classification in `rem:covariance` | **Open formalization** | no representation-theoretic commutant layer; the manuscript claim is restricted to Hermitian sesquilinear degree-`(1,1)` forms |
| parameterized partial-trace inequality `eq:main-bound-parametrized` | **Checked** | `rank_r_partial_trace_exact_of_betaTwo`; `qform_HopScaled_param` composes the generic Choi constant with the double-skew contraction identity |
| even higher-copy alternating marginal inequality in `rem:scope` | **Conditional** | parity and the generic pair lift are checked; the constants `beta_2(Λ^{⊗2m})` are unknown for `m ≥ 2` |

### Applications

`Applications.lean` represents an infimum formula by the logically equivalent
combination “pointwise lower bound for every admissible nonzero matrix +
rank-exact matrix attaining the bound.” This avoids an unrelated
extended-real-infimum layer.

| Application | Status | Lean certificate or precise gap |
| --- | --- | --- |
| one-sided marginal bound | **Checked** | `hsNormSq_ptraceU_le`, `hsNormSq_ptraceV_le` |
| exact symmetric two-copy score curve for `1 ≤ r ≤ d` | **Checked** | `twoCopyScore_lower_of_le_inv`, `twoCopyScore_lower_of_inv_le`, `twoCopyScore_projWit_same`, `twoCopyScore_projWit_orthogonal` |
| adjacent-rank endpoint score `-1/r` | **Checked** in finite coordinates | `exists_unit_pureSchmidtRank_adjacent_score` proves the full normalized score formula; `exists_unit_pureSchmidtRank_adjacent_endpoint` supplies the unit vector, exact pure Schmidt rank `r+1`, and expectation `-1/r` |
| strict signed adjacent-rank separation | **Checked** in finite coordinates | `re_qform_productReductionChoi_strict_lower_of_pureSchmidtRank_le` proves the displayed uniform margin directly for pure vectors, its `strict_pos` corollary gives strict positivity for nonzero vectors, and `exists_unit_pureSchmidtRank_adjacent_strict_neg` supplies the normalized rank-`r+1` negative witness |
| symmetric score nonnegativity iff `t ≤ 1/r`, for `1 ≤ r ≤ d` | **Checked** | `twoCopyNonnegative_iff` |
| reduction pencil and displayed product Choi matrices | **Checked** in coordinates | `mapChoi_reductionMap`, `productReductionChoi_eq_regroup_mapChoi`, and `productReductionChoi_eq_asymmetricScoreOperator` include the output/input register permutation explicitly |
| finite-coordinate map/Choi `r`-positivity equivalence | **Checked** | `IsMapRPositive` tests all positive-semidefinite inputs to the actual `Fin r` ampliation; `rank_le_card_iff_exists_mul` and `isMapRPositive_mapOfChoi_iff_isBlockPositive` prove the Choi correspondence |
| positive-semidefinite Choi continuation at `a,b ≤ 1/d` | **Checked** | `reductionChoi_posSemidef`, `productReductionChoi_posSemidef`; the generic map/Choi theorem transfers the latter to every ampliation level |
| two-copy block positivity for every positive `r`, at equal local dimension `d ≥ 2` | **Checked** in explicit coordinate Choi form | `isBlockPositive_productReductionChoi_self_iff_le_inv_min` gives the threshold `t ≤ 1/min(r,d)` (and hence covers the manuscript range `r ≤ d²`) |
| tensor-square map `r`-positivity classification | **Checked** in coordinates | `productReductionMapLinear_apply` identifies the map with the tensor product of the two reduction pencils; `isMapRPositive_productReductionMapLinear_self_iff_le_inv_min` gives the threshold for every positive `r` |
| exact asymmetric score curve for `1 ≤ r ≤ d` | **Checked** | all four lower branches, factor swap, and all four attaining cases in `Applications.lean` |
| asymmetric score nonnegativity iff `max(a,b) ≤ 1/r`, for `1 ≤ r ≤ d` | **Checked** | `asymmetricNonnegative_iff` |
| asymmetric product-Choi block positivity | **Checked** in coordinates | `isBlockPositive_productReductionChoi_iff_max_le_inv` handles `1 ≤ r ≤ min(dim U,dim V)`; `isBlockPositive_productReductionChoi_iff_max_le_inv_min` gives `max(a,b) ≤ 1/min(r,d)` for every positive `r` at equal local dimension `d ≥ 2` |
| asymmetric map `r`-positivity classification | **Checked** in coordinates | `isMapRPositive_productReductionMapLinear_iff_max_le_inv` handles the rank-constrained range; `isMapRPositive_productReductionMapLinear_iff_max_le_inv_min` handles every positive `r` at equal local dimension |
| quantitative trace-norm separation | **Checked** in Hermitian spectral rendering | `SchmidtNumberLE` is the finite pure-state decomposition definition; `abs_re_hsInner_le_hermitianTraceNorm` proves Hölder duality from the spectral theorem; `abs_re_qform_twoCopyWitness_centered_le` proves the exact diameter `γ + max(1,γ²)`; `twoCopy_traceDistance_lower` is the pointwise form of the displayed infimum bound |
| Kronecker-sum Ky Fan bound | **Checked** | `hsInner_kroneckerSum_centered`, `normSq_hsInner_kroneckerSum_le`, `hsNormSq_kroneckerSum`, and `normSq_hsInner_kroneckerSum_le_min` prove the displayed pairing, Cauchy--Schwarz step, and both branches of the minimum; `frobeniusRankTestSq_kroneckerSum_le` proves the normalized rank-test supremum bound; `weighted_antitone_sum_le_head`, `sum_norm_sq_mulVecE_le_kyFanSq`, and `exists_kyFan_optimal_test` prove both directions of `kyFanFrobeniusDuality`; `kyFanSq_kroneckerSum_le` and its `d ≤ 2k` specialization are the literal singular-value conclusions |
| exact Schmidt number of the product of antisymmetric projector states | **Checked** in finite coordinates | `sum_rankOne_scaledSkewKraus` and `schmidtNumberLE_four_smul_Qm` give an explicit decomposition into vectorized matrices of rank at most four; `hsNormSq_dsProj_le_three_of_rank_eq` dualizes the level-three double-skew action bound, and `doubleAntisym_schmidt_number_eq_four` proves the lower bound; the abstract-space/basis rendering remains part of the global coordinate boundary |
| explicit Schmidt-number witnesses | **Checked** in finite coordinates | `twoWitness_isBlockPositive`, `threeWitness_isBlockPositive`, and their mixed-state inequalities are unconditional; `trace_mul_twoWitness_smul_Qm` and `trace_mul_threeWitness_smul_Qm` prove the displayed expectations \(-1/2\) and \(-1/4\) on every normalized scalar multiple of `Qm` |

### Appendices

| Claim | Status | Gap |
| --- | --- | --- |
| polynomial SOS for the trace–rank residual | **Checked** in coordinates | `complex_lagrange_sos_ordered` proves the choice-free half-double-sum identity; `complex_lagrange_sos` and `rankFactor_traceRankResidual_eq_lagrangeSOS` prove the literal `α < β` formula; `rankFactor_traceRankResidual_eq_wedgeNormSq` gives `eq:sos-lagrange` with the exterior squared norm defined by that orthonormal-coordinate sum |
| complete-graph defect certificate | **Checked** | `completeGraph_defect_certificate` is the exact edge-matrix identity; `hsNormSq_sum_smul_of_hsInner_four` proves `eq:Kc-norm` from the stated basis normalization; `completeGraph_defect_certificate_coeff` is the displayed coefficient form; `completeGraph_defect_nonneg_holds` proves all edge and vertex deficits nonnegative |
| exact positive/negative-sector Gram identity | **Checked** in quadratic-form rendering | `rankFactor_partialTraceGap_eq_sector_gram` is the scaled boxed identity; `qform_negativeSectorDefectScaled_nonneg_holds` proves the defect positive, with Kraus quadratic forms representing the two synthesis Grams |
| positive-map semidefinite cut | **Checked** in finite coordinates | `SchmidtNumberLEBetween` handles arbitrary rectangular ancillas; `mapAmplification_posSemidef_of_schmidtNumberLEBetween` proves the generic Choi cut; `productReduction_schmidtNumberLE_cut` and its symmetric specialization instantiate the all-rank reduction-product threshold |
| local-channel aggregation | **Checked** at the finite Kraus level | `localKrausPullback` is the coordinate adjoint action; `rank_localCoeff_le` proves local rank monotonicity; `aggregateLocalWitnessDependent_isBlockPositiveBetween` and `trace_mul_aggregateLocalWitnessDependent_nonneg` allow term-dependent output spaces and Kraus index types; trace preservation is unnecessary for the conclusion |
| local-Hamiltonian Schmidt-number certificate | **Checked** in finite coordinates | `not_schmidtNumberLEBetween_of_dependentReductionAggregate_neg` specializes the varying-output aggregation to the displayed reduction-product witnesses and proves that negative expectation refutes `SchmidtNumberLEBetween r` |
| positive-semidefinite shifted pullbacks and explicit energy baseline | **Checked** in finite coordinates | `localKrausPullback_posSemidef` proves positivity of each pullback; `localKrausPullback_one` proves unitality from Kraus completeness; `aggregateLocalWitnessDependent_shift_eq` gives the exact weighted identity; `dependentReductionAggregate_shift_posSemidef` and `trace_mul_dependentReductionAggregate_shift_lower` prove the displayed positive-semidefinite aggregate and baseline. `productReductionChoi_inv_exactRayleighMinimum` proves that `1-d/r` is the exact minimum by combining the shifted positive decomposition with a nonzero attaining vector, including `d=1`. |
| rigidity of the diagonal embedding among linear encodings | **Checked** | `Rigidity.lean`; linear expansion, positivity of point masses, and both marginal hypotheses are explicit |

## Higher Choi constants note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| every-pair action inequality | **Checked** | the double-skew action theorem applies to every orthonormal pair |
| upper bound `κ_k ≤ min(k,4)/4` for `k ≥ 2` | **Checked** in action and low-rank projection forms | `sum_norm_sq_le_of_doubleSkewQm`, `sum_norm_sq_le_min_of_doubleSkewQm`, `hsNormSq_dsProj_le_min`, `qform_Qm_rank_le_min` |
| attainment and exact equality `κ_k = min(k,4)/4` for all `k ≥ 2` | **Checked in the equivalent low-rank Choi form** | `qform_Qm_sharpWitThree` supplies the exceptional rank-three truncation; `choiKAttained_Qm_of_four_le` uses a full elementary tensor from rank four onward; the literal singular-value packaging is not independently defined |
| resulting concrete `beta_k(Λ_U ⊗ Λ_V)` formula | **Checked exactly** | `choiKAttained_four_smul_Qm_min` proves attainment and `choiKBound_four_smul_Qm_iff` characterizes all valid constants as `beta ≥ min(1,4/k)` |
| `K_m = (m|ω><ω| - F)/2` and the equal-dimension `κ_1` lower-bound witness | **Checked** in finite coordinates | `correlatedSkew_eq` and `correlatedSkew_spectral_actions` prove the closed form and all three sector actions; `hsNormSq_correlatedSkew` and `correlatedSkew_levelOne_ratio` prove the norm and attained ratio; `quarter_lt_correlatedSkew_levelOne_ratio` proves the strict comparison for `m ≥ 3`. Sector dimensions/multiplicities, a supremum-valued definition of `κ_1`, and the unequal-dimension embedding argument are not formalized. |
| exact `κ_1` formula | **Conjecture** | only a lower bound and numerical evidence are claimed |

## Exterior-amplification note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| level-`k` span bound | **Checked** | `norm_sq_le_of_choiKBound` |
| orthonormal incidence and protected modes | **Checked** | `orthonormal_etaMode`, `orthonormal_deltaMode` |
| face regrouping | **Checked**, stronger weighted form | `norm_sq_sum_placeAt_le_weighted` and downstream `PhypAmp` theorems |
| unprotected exterior amplification, `k ≥ 1` | **Checked** | `qform_PhypAmp_le_of_norm`, `qform_PhypAmp_le` |
| protected exterior amplification, `k ≥ 2` | **Checked** | weighted and uniform protected theorems in `HigherArity.lean` |
| protected-space dimension | **Checked** | modes are indexed by `Face r (k-2)` and proved orthonormal; `card_face` proves `|Face r (k-2)| = choose r (k-2)` |
| `k=2` specialization | **Checked core** | pair-level corollaries and `upDeg_univ`; equality with every notation choice in the note is a rendering |
| complete-hypergraph degree `r-k+1` | **Checked** | `upDeg_univ` |
| double-skew specialization with exact `beta_k` | **Checked** | `choiOf_normalizedSkewKraus` identifies the manuscript normalization, `choiKBound_four_smul_Qm_iff` proves the coefficient is least, and `qform_normalizedSkewKraus_Phyp_univ_le` is the complete-hypergraph corollary |
| “no `r`-positivity hierarchy for `k>2`” explanatory spectral claim | **Open formalization** | no general partial-transpose spectral decomposition layer |

## Graph-inclusion note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| edge Kraus family and transpose symmetry | **Checked** | `edgeKraus`, `graphKraus`, `graphKraus_transpose` |
| exact local constant `beta_2(Phi_G)=1` for nonempty graphs | **Checked** | `choiTwoBound_graphKraus_iff` |
| general amplification upper bound | **Checked** | `thetaPositive_of_choiTwoBound` |
| induced-average-degree obstruction | **Checked** | `two_mul_card_le_of_thetaPositive` |
| clique sharpness and exact threshold `lambda = R-1` | **Checked** | `thetaPositive_graphKraus_iff` |
| invariant operator system and layer action | **Checked** in finite coordinates | `graphOperatorSpace` and `graphTwoLayerSpace` define `S_G` and `U_G`; their `one_mem` and `conjTranspose_mem` theorems prove the unital self-adjoint structure; `graphPhiTranspose_layers` and `graphTheta_layers` prove the displayed action; `graphReduction_mem_graphOperatorSpace` and `graphTheta_mem_graphTwoLayerSpace` prove invariance |
| inclusion dictionary | **Checked** in a basis-free finite-coordinate rendering | `matrixLevelPositiveCone` and `mappedMatrixLevelPositiveCone` are the two levelwise positivity loci, and `matrixLevelPositiveCone_subset_mapped_iff` is their exact restricted-ampliation dictionary; choosing a real traceless basis and spelling the same cone as a monic pencil remains a presentation interface |
| compressed clique expectation | **Checked** in finite coordinates | `cliqueLayerWitness_posSemidef` proves that `Y_S` is positive; `cliqueLayerWitness_mem_matrixLevelSpace` places all of its blocks in `U_G`; `qform_graphThetaCliqueOutput` proves the exact value `|S|(λ-(|S|-1))`, independently of `R` |
| exact protected threshold `λ=R-1` at level `R` | **Checked** in the basis-free rendering | `graphCliqueLevelInclusion_iff`; `isBlockPositive_mapChoi_graphThetaLinear_iff` and `isMapPositiveAt_graphThetaLinear_of_thetaPositive` supply the Choi-to-ampliation bridge |
| protected inclusion through level `R`, failure above it | **Checked** in the basis-free rendering | `graphLevelInclusion_at_threshold_of_card_le` proves inclusion for every finite level of cardinality at most `R`; `not_graphCliqueNextLevelInclusion` proves the adjacent obstruction; `graphLevelInclusion_of_embedding` pads/compresses levels, and `graphProtectedLevelInclusion_iff` proves the literal all-`n` biconditional in `eq:levels` |
| rook-graph corollary | **Checked** in the basis-free rendering | `rookGraphLevelInclusion_iff` and `rookGraphProtectedLevelInclusion_iff` instantiate the threshold and all-level separation; `finrank_rookGraphTwoLayerSpace`, `rookGraphTwoLayerDimension_sub_one`, and `rookAmbientDimension_sub_one` certify the two displayed coefficient counts |
| exact invariant for clique-free graphs | **Not claimed** | the note states only upper and lower bounds |

## Schmidt-staircase note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| double-skew constant `beta_2=1` | **Checked** | main development |
| map identity for `W_k` | **Checked** | `Psi_eq_tensor_square` |
| `k`-block positivity of `W_k` | **Checked across the stated Schmidt cut** | `staircaseWitnessAcrossCut_eq_productReductionChoi` identifies the regrouped witness with `k` times the reduction-product Choi matrix, and `staircaseWitnessAcrossCut_isBlockPositive` proves block positivity |
| normalized isotropic states and white-noise identity | **Checked** in finite coordinates | `isotropicState_isDensityMatrix`, `isotropicState_whiteNoise`, `staircaseWhiteNoiseState_eq`; `schmidtNumberLE_one` gives the computational-basis product decomposition of the identity and `schmidtNumberLE_one_regroupProductOperator_staircaseWhiteNoiseState` proves separability across the staircase cut |
| necessary isotropic Schmidt-number bound | **Checked** in finite coordinates | `reductionChoi_inv_isBlockPositive` and `isotropicMoment_le_of_schmidtNumberLE` prove that every normalized state of Schmidt number at most `r` has maximally entangled fidelity at most `r/d`; `not_schmidtNumberLE_isotropicState_of_ratio_lt` gives the contrapositive for isotropic states |
| product-isotropic four-sector algebra and moment uniqueness | **Checked** inside the specified real four-dimensional space | `biIsotropicForm_eq_of_trace_moments`, `eq_of_memBiIsotropicSpace_of_trace_moments`; identifying this space as the range/commutant of the Haar twirl remains open |
| product-isotropic Haar twirl and Schmidt-number preservation | **Open formalization** | no Haar integration or local-unitary channel layer |
| product-seed lemma and exact seed Schmidt number | **Open formalization** | requires Schmidt number and local-unitary twirling |
| trace formula and one-sided threshold | **Checked through mixed-state Schmidt number** | `trace_mul_staircaseWitness_staircaseState_neg_iff` proves the scalar crossing; `trace_mul_staircaseWitnessAcrossCut_staircaseStateAcrossCut_neg_iff` transports it to `(A₁A₂):(B₁B₂)`, and `not_schmidtNumberLE_staircaseStateAcrossCut_of_threshold_lt` proves `SN(ρ_p)>k` for `p>p_k` |
| boundary decomposition at `p_k` | **Checked identity and conditional Schmidt-number inference** | `staircase_boundary_operator_identity`; `staircaseState_at_threshold_normalized_posSemidef` and `staircaseBoundaryState_at_threshold_normalized_posSemidef` check both sides are states. `schmidtNumberLE_staircaseStateAcrossCut_at_threshold_of_seeds` proves the upper bound from exactly the two product-seed Schmidt-number obligations |
| strict monotonicity of thresholds | **Checked** | `staircaseGamma_succ_sub`, `staircaseP_lt_succ` |
| exact staircase | **Lower-bound direction checked; upper-bound reduced to two seed obligations** | `not_schmidtNumberLE_staircaseStateAcrossCut_of_threshold_lt` proves `SN(ρ_p)>k` above each threshold. `SchmidtNumberLE.add`, `SchmidtNumberLE.nonneg_smul`, the explicit white-noise decomposition, and `schmidtNumberLE_staircaseStateAcrossCut_of_le_threshold_of_seeds` formalize the complete `0≤p≤p_k` argument conditional only on the two product-isotropic seed bounds; those bounds still depend on the product-seed/twirl layer |
| adjacent threshold and equality mode | **Checked only at the score core** | `twoCopyScore_adjacent_endpoint`; the isotropic-state and twirl identifications are absent |
| protected/unprotected threshold comparison | **Checked** at matrix level | `staircaseUnprotectedWitness`, `trace_mul_staircaseUnprotectedWitness_staircaseState_neg_iff`, and `staircaseP_lt_unprotected` prove the extra maximally entangled term, its exact expectation threshold, and the strict comparison |
| entangled-marginal comparison | **Checked detector direction and strict comparison** | `staircasePMarginal_lt_iff_fidelity_gt` identifies the scalar crossing, `ptraceV_staircaseState` proves the displayed isotropic marginal, and `not_schmidtNumberLE_ptraceV_staircaseState_of_marginal_lt` certifies Schmidt number greater than `k` above the threshold; `staircaseP_lt_marginal` proves the protected threshold is strictly earlier. The converse below the marginal threshold still requires the sufficient half of isotropic stratification |

## Closure order

The shortest route to a fully formalized application suite is:

1. prove the sufficient half of the isotropic Schmidt-number classification,
   identify the checked four-sector algebra with the product-isotropic Haar
   twirl, and prove the required Schmidt-number preservation and seed lemmas;
2. finish the graph note's presentation layer by choosing the displayed real
   monic pencil basis.

These items concern companion constructions and appendices rather than the
proof of the central theorem.  The rook-graph combinatorics and
coefficient-space dimensions are checked; item 2 is only the explicit
basis/pencil interface.
