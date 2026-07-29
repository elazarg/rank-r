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
| Kronecker-sum Ky Fan bound | **Checked through the Frobenius dual bound; singular-value conclusion conditional** | `hsInner_kroneckerSum_centered`, `normSq_hsInner_kroneckerSum_le`, `hsNormSq_kroneckerSum`, and `normSq_hsInner_kroneckerSum_le_min` prove the displayed pairing, Cauchy--Schwarz step, and both branches of the minimum; `frobeniusRankTestSq_kroneckerSum_le` proves the normalized rank-test supremum bound; `kyFanSq_kroneckerSum_le` and its `d ≤ 2k` specialization derive the literal singular-value conclusion from the precisely isolated proposition `KyFanFrobeniusDuality` |
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
| upper bound `κ_k ≤ min(k,4)/4` for `k ≥ 2` | **Checked** in action form | `sum_norm_sq_le_of_doubleSkewQm`, `sum_norm_sq_le_min_of_doubleSkewQm` |
| attainment and exact equality `κ_k = min(k,4)/4` for all `k ≥ 2` | **Open formalization except `k=2`** | `Sharp.lean` supplies the rank-two extremizer; the four-equal-singular-value calculation for general `k` is not formalized |
| resulting concrete `beta_k(Λ_U ⊗ Λ_V)` formula | **Conditional** | generic `ChoiKBound` machinery is checked, but the exact concrete `k`-level constant is not composed |
| `K_m = (m|ω><ω| - F)/2` and the `κ_1` lower bound | **Open formalization** | no Lean counterpart |
| exact `κ_1` formula | **Conjecture** | only a lower bound and numerical evidence are claimed |

## Exterior-amplification note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| level-`k` span bound | **Checked** | `norm_sq_le_of_choiKBound` |
| orthonormal incidence and protected modes | **Checked** | `orthonormal_etaMode`, `orthonormal_deltaMode` |
| face regrouping | **Checked**, stronger weighted form | `norm_sq_sum_placeAt_le_weighted` and downstream `PhypAmp` theorems |
| unprotected exterior amplification, `k ≥ 1` | **Checked** | `qform_PhypAmp_le_of_norm`, `qform_PhypAmp_le` |
| protected exterior amplification, `k ≥ 2` | **Checked** | weighted and uniform protected theorems in `HigherArity.lean` |
| protected-space dimension | **Checked rendering** | modes are indexed by `Face r (k-2)` and proved orthonormal; the binomial-cardinality display is not separately packaged |
| `k=2` specialization | **Checked core** | pair-level corollaries and `upDeg_univ`; equality with every notation choice in the note is a rendering |
| complete-hypergraph degree `r-k+1` | **Checked** | `upDeg_univ` |
| double-skew specialization with exact `beta_k` | **Conditional** | blocked on the general-`k` exact constant in the preceding note |
| “no `r`-positivity hierarchy for `k>2`” explanatory spectral claim | **Open formalization** | no general partial-transpose spectral decomposition layer |

## Graph-inclusion note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| edge Kraus family and transpose symmetry | **Checked** | `edgeKraus`, `graphKraus`, `graphKraus_transpose` |
| exact local constant `beta_2(Phi_G)=1` for nonempty graphs | **Checked** | `choiTwoBound_graphKraus_iff` |
| general amplification upper bound | **Checked** | `thetaPositive_of_choiTwoBound` |
| induced-average-degree obstruction | **Checked** | `two_mul_card_le_of_thetaPositive` |
| clique sharpness and exact threshold `lambda = R-1` | **Checked** | `thetaPositive_graphKraus_iff` |
| invariant operator system and layer action | **Open formalization** | `S_G`, `U_G`, and the layer decomposition are absent |
| inclusion dictionary | **Open formalization** | no operator-system/free-spectrahedral vocabulary |
| compressed clique expectation | **Open formalization** | the underlying uncompressed witness count is checked |
| exact protected inclusion through level `R`, failure at `R+1` | **Open formalization** | depends on the preceding dictionary and compression |
| rook-graph corollary | **Open formalization** | depends on exact inclusion |
| exact invariant for clique-free graphs | **Not claimed** | the note states only upper and lower bounds |

## Schmidt-staircase note

| Claim | Status | Lean certificate or precise gap |
| --- | --- | --- |
| double-skew constant `beta_2=1` | **Checked** | main development |
| map identity for `W_k` | **Checked** | `Psi_eq_tensor_square` |
| `k`-block positivity of `W_k` | **Checked core** | `thetaPositive_of_choiTwoBound`; mixed-state Schmidt-number phrasing remains an interface |
| product-isotropic twirl, its four-dimensional commutant, and moment uniqueness | **Open formalization** | no Haar twirl or representation-theoretic commutant layer |
| product-seed lemma and exact seed Schmidt number | **Open formalization** | requires Schmidt number and local-unitary twirling |
| trace formula and one-sided threshold | **Checked scalar core** | `staircaseGamma_eq_fraction`, `staircaseP_eq_gamma_ratio`, `affine_threshold_iff`; the operator trace identity remains an interface |
| boundary decomposition at `p_k` | **Checked core** | `staircaseAlpha_eq`, `staircaseAlpha_mem_Ioo`, `staircase_boundary_moments`; moment uniqueness and the Schmidt-number bound remain absent |
| strict monotonicity of thresholds | **Checked** | `staircaseGamma_succ_sub`, `staircaseP_lt_succ` |
| exact staircase | **Open formalization** | depends on twirl, boundary decomposition, and mixed-state Schmidt number |
| adjacent threshold and equality mode | **Checked only at the score core** | `twoCopyScore_adjacent_endpoint`; the isotropic-state and twirl identifications are absent |
| protected/unprotected threshold comparison | **Open formalization** | no scalar or Choi-state theorem |
| entangled-marginal comparison | **Open formalization** | requires the isotropic Schmidt-number theorem and partial-trace semantics |

## Closure order

The shortest route to a fully formalized application suite is:

1. prove `KyFanFrobeniusDuality`, the equality between `kyFanSq` and
   `frobeniusRankTestSq`;
2. add isotropic states and the product-isotropic twirl;
3. add operator systems/free spectrahedra for the graph-inclusion translation.

Item 1 closes the remaining main-paper application interface. Items 2–3
concern companion constructions and appendices rather than the proof of the
central theorem.
