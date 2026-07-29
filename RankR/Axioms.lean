/-
The axiom surface of the development, checked by the build.

`README.md` and appendix A of the manuscript both assert that `#print axioms`
applied to the main results reports only `propext`, `Classical.choice` and
`Quot.sound`.  Asserting it in prose is worth nothing; the `#guard_msgs` blocks
below turn each assertion into a build failure if it ever stops holding.

**What this file enforces.**  For every declaration listed, and transitively for
everything it depends on: no `sorry` (which would surface as `sorryAx`), no
`axiom` declaration of our own (which would appear by name), and no
`native_decide` (which would surface as `Lean.ofReduceBool`).  The Fu-Gao-Park
estimate does not appear, because it is carried as a `Prop`-valued hypothesis in
the type rather than as an axiom — which is the whole point of carrying it that
way.

**What it does not enforce.**  Options set anywhere in `RankR/`, and unfinished
proofs in declarations not reachable from anything listed here.  For those, the
following should print nothing (it excludes this file, whose prose would
otherwise match itself):

    grep -rn '^\s*axiom\s\|native_decide\|set_option\|\bsorry\b' \
      RankR/ RankR.lean --exclude=Axioms.lean
-/
import RankR.BlockPos
import RankR.Extend
import RankR.MapId
import RankR.Optimal
import RankR.OneSided
import RankR.Results
import RankR.Equivalence
import RankR.KyFanAction
import RankR.Exterior
import RankR.HigherArity
import RankR.GraphFamily
import RankR.Theta
import RankR.ThetaBound
import RankR.Parity
import RankR.Sharp
import RankR.Applications
import RankR.MapPos
import RankR.Staircase
import RankR.Gram
import RankR.Defect
import RankR.LagrangeSOS
import RankR.TraceSeparation
import RankR.Kronecker
import RankR.SchmidtWitness
import RankR.HigherChoiSharp
import RankR.HigherAritySkew
import RankR.KappaOne
import RankR.GraphLayers
import RankR.GenericApplications
import RankR.Rigidity

namespace RankR

/-! ## Theorem 1.1, unconditionally

Nothing below assumes anything.  `Autonne.lean` proves the Autonne-Takagi
factorization, `Takagi.lean` derives the double-skew action bound from it, and
`Results.lean` composes the two.  In particular the Fu-Gao-Park estimate is not
a hypothesis of the main theorem. -/

/-- info: 'Matrix.exists_takagi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Matrix.exists_takagi

/-- info: 'RankR.doubleSkewBound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doubleSkewBound_holds

/-- info: 'RankR.operatorIneq_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operatorIneq_holds

/-- info: 'RankR.rank_r_partial_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace

/-- info: 'RankR.rank_r_partial_trace_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_exact

/-- info: 'RankR.rank_r_partial_trace_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_strict

/-- info: 'RankR.rank_eq_of_eq_rank_r_partial_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_eq_of_eq_rank_r_partial_trace

/-! ## Applications

The score curves are represented without an extended-real infimum: a pointwise
lower bound and a rank-exact attaining matrix certify each branch.  The
nonnegativity equivalences package those two halves into the exact thresholds.
The Kronecker result below is the complete rank-sensitive input to the paper's
Ky-Fan corollary. -/

/-- info: 'RankR.twoCopyScore_lower_of_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_lower_of_le_inv

/-- info: 'RankR.twoCopyScore_lower_of_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_lower_of_inv_le

/-- info: 'RankR.twoCopyScore_projWit_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_projWit_same

/-- info: 'RankR.twoCopyScore_projWit_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_projWit_orthogonal

/-- info: 'RankR.twoCopyNonnegative_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyNonnegative_iff

/-- info: 'RankR.twoCopyScore_adjacent_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_adjacent_endpoint

/-- info: 'RankR.twoCopyScore_strict_separation_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_strict_separation_pos

/-- info: 'RankR.twoCopyScore_adjacent_strict_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopyScore_adjacent_strict_neg

/-- info: 'RankR.exists_unit_pureSchmidtRank_adjacent_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unit_pureSchmidtRank_adjacent_score

/-- info: 'RankR.exists_unit_pureSchmidtRank_adjacent_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unit_pureSchmidtRank_adjacent_endpoint

/-- info: 'RankR.re_qform_productReductionChoi_strict_lower_of_pureSchmidtRank_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms re_qform_productReductionChoi_strict_lower_of_pureSchmidtRank_le

/-- info: 'RankR.re_qform_productReductionChoi_strict_pos_of_pureSchmidtRank_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms re_qform_productReductionChoi_strict_pos_of_pureSchmidtRank_le

/-- info: 'RankR.exists_unit_pureSchmidtRank_adjacent_strict_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_unit_pureSchmidtRank_adjacent_strict_neg

/-- info: 'RankR.asymmetricScore_lower_left_of_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_lower_left_of_le_inv

/-- info: 'RankR.asymmetricScore_lower_left_of_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_lower_left_of_inv_le

/-- info: 'RankR.asymmetricScore_lower_right_of_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_lower_right_of_le_inv

/-- info: 'RankR.asymmetricScore_lower_right_of_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_lower_right_of_inv_le

/-- info: 'RankR.asymmetricScore_projWit_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_projWit_same

/-- info: 'RankR.asymmetricScore_projWit_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_projWit_orthogonal

/-- info: 'RankR.asymmetricScore_swappedProjWit_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_swappedProjWit_same

/-- info: 'RankR.asymmetricScore_swappedProjWit_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricScore_swappedProjWit_orthogonal

/-- info: 'RankR.asymmetricNonnegative_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asymmetricNonnegative_iff

/-- info: 'RankR.re_qform_asymmetricScoreOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_qform_asymmetricScoreOperator

/-- info: 'RankR.isBlockPositive_twoCopyScoreOperator_iff_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBlockPositive_twoCopyScoreOperator_iff_le_inv

/-- info: 'RankR.isBlockPositive_asymmetricScoreOperator_iff_max_le_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isBlockPositive_asymmetricScoreOperator_iff_max_le_inv

/-- info: 'RankR.mapChoi_reductionMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapChoi_reductionMap

/-- info: 'RankR.productReductionChoi_eq_regroup_mapChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_eq_regroup_mapChoi

/-- info: 'RankR.productReductionChoi_eq_asymmetricScoreOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_eq_asymmetricScoreOperator

/-- info: 'RankR.reductionChoi_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reductionChoi_posSemidef

/-- info: 'RankR.productReductionChoi_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_posSemidef

/-- info: 'RankR.isBlockPositive_productReductionChoi_self_iff_le_inv_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isBlockPositive_productReductionChoi_self_iff_le_inv_min

/-- info: 'RankR.isBlockPositive_productReductionChoi_iff_max_le_inv_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isBlockPositive_productReductionChoi_iff_max_le_inv_min

/-- info: 'RankR.rank_le_card_iff_exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_le_card_iff_exists_mul

/-- info: 'RankR.pureSchmidtRank_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pureSchmidtRank_vec

/-- info: 'RankR.rank_smul_eq_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_smul_eq_of_ne_zero

/-- info: 'RankR.pureSchmidtRank_smul_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pureSchmidtRank_smul_of_ne_zero

/-- info: 'RankR.qform_smul_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_smul_vec

/-- info: 'RankR.rank_le_iff_exists_sum_rankOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_le_iff_exists_sum_rankOne

/-- info: 'RankR.choiKBound_iff_pureSchmidtKBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKBound_iff_pureSchmidtKBound

/-- info: 'RankR.choiTwoBound_iff_pureSchmidtKBound_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoBound_iff_pureSchmidtKBound_two

/-- info: 'RankR.fgpBound_iff_pureSchmidtKBound_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fgpBound_iff_pureSchmidtKBound_two

/-- info: 'RankR.isMapRPositive_mapOfChoi_iff_isBlockPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isMapRPositive_mapOfChoi_iff_isBlockPositive

/-- info: 'RankR.productReductionMapLinear_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionMapLinear_apply

/-- info: 'RankR.mapChoi_productReductionMapLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapChoi_productReductionMapLinear

/-- info: 'RankR.isMapRPositive_productReductionMapLinear_iff_max_le_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isMapRPositive_productReductionMapLinear_iff_max_le_inv

/-- info: 'RankR.isMapRPositive_productReductionMapLinear_iff_max_le_inv_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isMapRPositive_productReductionMapLinear_iff_max_le_inv_min

/-- info: 'RankR.isMapRPositive_productReductionMapLinear_self_iff_le_inv_min' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms isMapRPositive_productReductionMapLinear_self_iff_le_inv_min

/-- info: 'RankR.re_hsInner_nonneg_of_schmidtNumberLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_hsInner_nonneg_of_schmidtNumberLE

/-- info: 'RankR.abs_re_hsInner_le_hermitianTraceNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_re_hsInner_le_hermitianTraceNorm

/-- info: 'RankR.abs_re_qform_twoCopyWitness_centered_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms abs_re_qform_twoCopyWitness_centered_le

/-- info: 'RankR.twoCopy_traceDistance_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoCopy_traceDistance_lower

/-- info: 'RankR.centeredPartialTrace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms centeredPartialTrace_le

/-- info: 'RankR.hsInner_kroneckerSum_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsInner_kroneckerSum_centered

/-- info: 'RankR.normSq_hsInner_kroneckerSum_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normSq_hsInner_kroneckerSum_le_min

/-- info: 'RankR.frobeniusRankTestSq_kroneckerSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frobeniusRankTestSq_kroneckerSum_le

/-- info: 'RankR.kyFanSq_kroneckerSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kyFanSq_kroneckerSum_le

/-- info: 'RankR.sum_rankOne_scaledSkewKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_rankOne_scaledSkewKraus

/-- info: 'RankR.schmidtNumberLE_four_smul_Qm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms schmidtNumberLE_four_smul_Qm

/-- info: 'RankR.qform_Qm_rank_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_Qm_rank_two_le

/-- info: 'RankR.qform_Qm_rank_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_Qm_rank_three_le

/-- info: 'RankR.QmRankThreeBound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms QmRankThreeBound_holds

/-- info: 'RankR.twoWitness_isBlockPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms twoWitness_isBlockPositive

/-- info: 'RankR.threeWitness_isBlockPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms threeWitness_isBlockPositive

/-- info: 'RankR.doubleAntisym_schmidt_number_eq_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doubleAntisym_schmidt_number_eq_four

/-- info: 'RankR.trace_mul_twoWitness_smul_Qm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_mul_twoWitness_smul_Qm

/-- info: 'RankR.trace_mul_threeWitness_smul_Qm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_mul_threeWitness_smul_Qm

/-- info: 'RankR.rank_choiContraction_vec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_choiContraction_vec_le

/-- info: 'RankR.mapAmplification_posSemidef_of_schmidtNumberLEBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mapAmplification_posSemidef_of_schmidtNumberLEBetween

/-- info: 'RankR.productReduction_schmidtNumberLE_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReduction_schmidtNumberLE_cut

/-- info: 'RankR.productReduction_self_schmidtNumberLE_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReduction_self_schmidtNumberLE_cut

/-- info: 'RankR.qform_conj_rect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_conj_rect

/-- info: 'RankR.localKrausPullback_isBlockPositiveBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localKrausPullback_isBlockPositiveBetween

/-- info: 'RankR.aggregateLocalWitnessDependent_isBlockPositiveBetween' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aggregateLocalWitnessDependent_isBlockPositiveBetween

/-- info: 'RankR.trace_mul_aggregateLocalWitnessDependent_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_mul_aggregateLocalWitnessDependent_nonneg

/-- info: 'RankR.not_schmidtNumberLEBetween_of_aggregateLocalWitnessDependent_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_schmidtNumberLEBetween_of_aggregateLocalWitnessDependent_neg

/-- info: 'RankR.not_schmidtNumberLEBetween_of_dependentReductionAggregate_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms not_schmidtNumberLEBetween_of_dependentReductionAggregate_neg

/-- info: 'RankR.localKrausPullback_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localKrausPullback_one

/-- info: 'RankR.localKrausPullback_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms localKrausPullback_posSemidef

/-- info: 'RankR.aggregateLocalWitnessDependent_shift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aggregateLocalWitnessDependent_shift_eq

/-- info: 'RankR.aggregateLocalWitnessDependent_shift_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aggregateLocalWitnessDependent_shift_posSemidef

/-- info: 'RankR.trace_mul_aggregateLocalWitnessDependent_shift_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_mul_aggregateLocalWitnessDependent_shift_lower

/-- info: 'RankR.productReductionChoi_inv_shift_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_inv_shift_posSemidef

/-- info: 'RankR.productReductionChoi_inv_isBlockPositiveBetween_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_inv_isBlockPositiveBetween_all

/-- info: 'RankR.productReductionChoi_inv_exactRayleighMinimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms productReductionChoi_inv_exactRayleighMinimum

/-- info: 'RankR.dependentReductionAggregate_shift_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dependentReductionAggregate_shift_posSemidef

/-- info: 'RankR.trace_mul_dependentReductionAggregate_shift_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_mul_dependentReductionAggregate_shift_lower

/-- info: 'RankR.staircaseP_eq_gamma_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircaseP_eq_gamma_ratio

/-- info: 'RankR.staircaseAlpha_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircaseAlpha_mem_Ioo

/-- info: 'RankR.staircase_boundary_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircase_boundary_moments

/-- info: 'RankR.affine_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms affine_threshold_iff

/-- info: 'RankR.staircaseP_lt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircaseP_lt_succ

/-- info: 'RankR.staircaseP_lt_unprotected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircaseP_lt_unprotected

/-- info: 'RankR.staircaseP_lt_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms staircaseP_lt_marginal

/-! ## Fu-Gao-Park's Theorem 2.4, proved

`Equivalence.lean` supplies the converse of `doubleSkewBound_of_FGP`, so the
manuscript's Lemma 2.1 and the imported estimate are equivalent -- and, both
being consequences of Autonne-Takagi, both are proved. -/

/-- info: 'RankR.fgpBound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fgpBound_holds

/-- info: 'RankR.doubleSkewBoundQm_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doubleSkewBoundQm_holds

/-! ## Theorem 1.1 from Fu-Gao-Park as published

Retained as the bridge to the manuscript's original standing hypothesis; no
longer on the critical path. -/

/-- info: 'RankR.rank_r_partial_trace_of_FGP_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_of_FGP_square

/-- info: 'RankR.rank_r_partial_trace_of_FGP_square_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_of_FGP_square_exact

/-- info: 'RankR.rank_r_partial_trace_of_FGP_square_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_of_FGP_square_strict

/-- info: 'RankR.rank_eq_of_eq_rank_r_partial_trace_of_FGP_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_eq_of_eq_rank_r_partial_trace_of_FGP_square

/-! ## The steps of the conditional chain

`FGPBound` as published, then Lemma 2.1, then the constant `β`, then
Proposition 2.2. -/

/-- info: 'RankR.FGPBound_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FGPBound_of_card_le

/-- info: 'RankR.doubleSkewBound_of_FGP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doubleSkewBound_of_FGP

/-- info: 'RankR.choiOf_skewKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiOf_skewKraus

/-- info: 'RankR.choiTwoBound_of_FGP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoBound_of_FGP

/-- info: 'RankR.operatorIneq_of_choiTwoBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operatorIneq_of_choiTwoBound

/-- info: 'RankR.qform_HopScaled_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_HopScaled_param

/-- info: 'RankR.rank_r_partial_trace_exact_of_betaTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_r_partial_trace_exact_of_betaTwo

/-- info: 'RankR.rankFactor_partialTraceGap_eq_sector_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rankFactor_partialTraceGap_eq_sector_gram

/-- info: 'RankR.qform_negativeSectorDefectScaled_nonneg_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_negativeSectorDefectScaled_nonneg_holds

/-- info: 'RankR.completeGraph_defect_certificate_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completeGraph_defect_certificate_coeff

/-- info: 'RankR.hsNormSq_sum_smul_of_hsInner_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_sum_smul_of_hsInner_four

/-- info: 'RankR.completeGraph_defect_nonneg_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms completeGraph_defect_nonneg_holds

/-- info: 'RankR.complex_lagrange_sos_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complex_lagrange_sos_ordered

/-- info: 'RankR.complex_lagrange_sos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms complex_lagrange_sos

/-- info: 'RankR.rankFactor_traceRankResidual_eq_lagrangeSOS_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rankFactor_traceRankResidual_eq_lagrangeSOS_ordered

/-- info: 'RankR.rankFactor_traceRankResidual_eq_lagrangeSOS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rankFactor_traceRankResidual_eq_lagrangeSOS

/-- info: 'RankR.rankFactor_traceRankResidual_eq_wedgeNormSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rankFactor_traceRankResidual_eq_wedgeNormSq

/-- info: 'RankR.operatorIneq_of_FGP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operatorIneq_of_FGP

/-! ## The level-`k` action bound

The averaged pair bound, the Bessel bound that competes with it, and the two
combined into `min(k/4, 1)`. -/

/-- info: 'RankR.sum_norm_sq_le_hsNormSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_norm_sq_le_hsNormSq

/-- info: 'RankR.sum_norm_sq_le_of_doubleSkewQm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_norm_sq_le_of_doubleSkewQm

/--
info: 'RankR.sum_norm_sq_le_min_of_doubleSkewQm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sum_norm_sq_le_min_of_doubleSkewQm

/-- info: 'RankR.hsNormSq_dsProj_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_dsProj_le_min

/-- info: 'RankR.qform_Qm_rank_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_Qm_rank_le_min

/-- info: 'RankR.choiKBound_four_smul_Qm_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKBound_four_smul_Qm_min

/-- info: 'RankR.qform_Qm_sharpWitThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_Qm_sharpWitThree

/-- info: 'RankR.choiKAttained_four_smul_Qm_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKAttained_four_smul_Qm_min

/-- info: 'RankR.choiKBound_four_smul_Qm_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKBound_four_smul_Qm_iff

/-- info: 'RankR.choiOf_normalizedSkewKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiOf_normalizedSkewKraus

/-- info: 'RankR.qform_normalizedSkewKraus_Phyp_univ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_normalizedSkewKraus_Phyp_univ_le

/-! ## The level-one correlated-skew witness

The closed form, distinguished eigenvector, Hilbert--Schmidt norm, and attained
ratio behind the lower bound in the higher Choi constants note.  These guards
do not claim the conjectured matching upper bound. -/

/-- info: 'RankR.correlatedSkew_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms correlatedSkew_eq

/-- info: 'RankR.mulVecE_correlatedSkew_singleOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulVecE_correlatedSkew_singleOmega

/-- info: 'RankR.hsNormSq_correlatedSkew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_correlatedSkew

/-- info: 'RankR.correlatedSkew_levelOne_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms correlatedSkew_levelOne_ratio

/-- info: 'RankR.quarter_lt_correlatedSkew_levelOne_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms quarter_lt_correlatedSkew_levelOne_ratio

/-! ## The graph two-layer compression

The concrete graph and two-layer coefficient spaces, the exact layer action,
and invariance of the corrected map.  The free-spectrahedral inclusion
dictionary is a separate interface and is not asserted here. -/

/-- info: 'RankR.graphPhiTranspose_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphPhiTranspose_layers

/-- info: 'RankR.graphTheta_layers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphTheta_layers

/-- info: 'RankR.conjTranspose_mem_graphOperatorSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjTranspose_mem_graphOperatorSpace

/-- info: 'RankR.graphReduction_mem_graphOperatorSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphReduction_mem_graphOperatorSpace

/-- info: 'RankR.conjTranspose_mem_graphTwoLayerSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjTranspose_mem_graphTwoLayerSpace

/-- info: 'RankR.graphTheta_mem_graphTwoLayerSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graphTheta_mem_graphTwoLayerSpace

/-- info: 'RankR.cliqueLayerWitness_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cliqueLayerWitness_posSemidef

/-- info: 'RankR.cliqueLayerWitness_mem_matrixLevelSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cliqueLayerWitness_mem_matrixLevelSpace

/-- info: 'RankR.qform_graphThetaCliqueOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_graphThetaCliqueOutput

/-! ## Exterior indexing

The two families of modes attached to the faces of `Fin r`. -/

/-- info: 'RankR.card_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_face

/-- info: 'RankR.orthonormal_etaMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orthonormal_etaMode

/-- info: 'RankR.orthonormal_deltaMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orthonormal_deltaMode

/-! ## Exterior amplification

Theorem A needs only the level-`k` Choi bound; Theorem B adds frame symmetry of
the Kraus operators and gains the span of the protected modes.  Both hold in a
weighted form, one Kraus family and one constant per hyperedge, whose coefficient
is the weighted modulus of the incidence correspondence, and the uniform form is
that weighted form at a constant weight; `upDeg_univ` gives the complete
hypergraph its degree `r - k + 1`, and the two pair-level corollaries are the
`k = 2` reading. -/

/--
info: 'RankR.qform_krausF_Phyp_le_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qform_krausF_Phyp_le_of_norm

/-- info: 'RankR.qform_krausF_Phyp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_krausF_Phyp_le

/-- info: 'RankR.upDeg_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms upDeg_univ

/--
info: 'RankR.qform_krausF_Phyp_le_of_choiTwoBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qform_krausF_Phyp_le_of_choiTwoBound

/--
info: 'RankR.qform_krausF_Phyp_le_of_choiTwoBound_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qform_krausF_Phyp_le_of_choiTwoBound_sub

/--
info: 'RankR.qform_PhypAmp_le_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms qform_PhypAmp_le_of_norm

/-- info: 'RankR.qform_PhypAmp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_PhypAmp_le

/-- info: 'RankR.isFrameSymmetric_of_transpose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isFrameSymmetric_of_transpose_eq

/--
info: 'RankR.transpose_eq_of_forall_isFrameSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms transpose_eq_of_forall_isFrameSymmetric

/-! ## The abstract liftings

None depends on the double-skew subspace: `norm_sq_le_of_choiKBound` is stated
for an arbitrary Kraus family and an arbitrary member of its span,
`qform_krausQ_ptransposeUV_ge` for an arbitrary transpose-symmetric one. -/

/-- info: 'RankR.norm_sq_le_of_choiKBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sq_le_of_choiKBound

/--
info: 'RankR.choiTwoBound_iff_choiKBound_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms choiTwoBound_iff_choiKBound_two

/-- info: 'RankR.choiKBound_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKBound_smul

/-- info: 'RankR.le_of_choiKAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_of_choiKAttained

/-- info: 'RankR.choiKAttained_of_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiKAttained_of_matrix

/-- info: 'RankR.norm_sq_pair_le_of_choiTwoBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_sq_pair_le_of_choiTwoBound

/-- info: 'RankR.qform_krausQ_Pneg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_krausQ_Pneg_le

/-- info: 'RankR.qform_krausQ_ptransposeUV_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_krausQ_ptransposeUV_ge

/-! ## The map identity

`Δ` is monoidal, `(Λ_U ⊗ Λ_V) ∘ τ = S_U ⊗ S_V` for `S = Δ − id`, and `Ψ_r` is the
tensor square `r · R_{−1/r} ⊗ R_{−1/r}`. -/

/-- info: 'RankR.RU_zero_RV_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RU_zero_RV_zero

/-- info: 'RankR.Lam4_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lam4_transpose

/-- info: 'RankR.Psi_eq_tensor_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Psi_eq_tensor_square

/-! ## Theorem 1.1 as block positivity

The quadratic form of `J(Ψ_r)` at `vec C` is the deficit in Theorem 1.1, so the
theorem and the `r`-block positivity of that operator are the same statement. -/

/-- info: 'RankR.re_qform_psiChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_qform_psiChoi

/-- info: 'RankR.isBlockPositive_psiChoi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms isBlockPositive_psiChoi

/-! ## The one-sided bound, also unconditional -/

/-- info: 'RankR.hsNormSq_ptraceU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_ptraceU_le

/-- info: 'RankR.hsNormSq_ptraceV_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsNormSq_ptraceV_le

/-! ## The sharpness half, which is unconditional

Nothing below depends on the Fu-Gao-Park estimate, in any form. -/

/-- info: 'RankR.rank_projWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_projWit

/-- info: 'RankR.projWit_bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms projWit_bound_eq

/-- info: 'RankR.le_coeff_hsNormSq_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms le_coeff_hsNormSq_of_bound

/-- info: 'RankR.inv_le_coeff_trace_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inv_le_coeff_trace_of_bound

/-! ## The rank-two Choi constant, pinned from below

`ChoiTwoBound` is an upper bound, and monotone in its constant
(`choiTwoBound_mono`), so on its own it determines nothing.  `Sharp.lean` carries
the attainment half, and `choiTwoBound_skewKraus_iff` is the two-sided statement
that certifies `β₂(Λ_U ⊗ Λ_V) = 1` as an equality. -/

/-- info: 'RankR.qform_Qm_sharpWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_Qm_sharpWit

/-- info: 'RankR.choiTwoAttained_skewKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoAttained_skewKraus

/-- info: 'RankR.choiTwoBound_skewKraus_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoBound_skewKraus_iff

/-- info: 'RankR.re_qform_psiChoi_projWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_qform_psiChoi_projWit

/-! ## The parity dichotomy of `eq:T-orthogonal`

`Frame.lean` gives one direction; `Parity.lean` carries the converse, so
`IsFrameSymmetric` is the exact hypothesis and not merely a sufficient one.  The
last two entries go further: a skew family saturates form (A₀) and refutes form
(A), so the hypothesis is load-bearing for the conclusion and not only for the
proof. -/

/-- info: 'RankR.inner_delta_placeT_zetaV_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_delta_placeT_zetaV_iff

/-- info: 'RankR.inner_delta_placeT_zetaV_of_isSkew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inner_delta_placeT_zetaV_of_isSkew

/-- info: 'RankR.not_isFrameSymmetric_skewFam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_isFrameSymmetric_skewFam

/-- info: 'RankR.qform_krausQ_Pneg_skewFam_saturates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qform_krausQ_Pneg_skewFam_saturates

/-- info: 'RankR.not_qform_krausQ_Pneg_le_skewFam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_qform_krausQ_Pneg_le_skewFam

/-! ## The edge-Kraus family of a graph

`lem:beta` of `paper/derivation-graph-inclusion.tex`: the rank-two Choi constant
of `Φ_G` is exactly `1`, for every graph with an edge.  This is the second
instance of the two-sided form, and the first one whose upper half is derived
rather than computed: every edge operator is double-skew, so `Qm` dominates the
whole family. -/

/-- info: 'RankR.orthonormal_graphKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orthonormal_graphKraus

/-- info: 'RankR.choiTwoBound_graphKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoBound_graphKraus

/-- info: 'RankR.choiTwoBound_graphKraus_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choiTwoBound_graphKraus_iff

/-! ## The amplification threshold, and its obstruction

`thm:clique` of `paper/derivation-graph-inclusion.tex`.  `ThetaPositive` is the
`R`-positivity of `Θ^Φ_{R,λ}` in Choi form; it is monotone in `λ`, so as with
`ChoiTwoBound` it names no number on its own.  The witness `P_S ⊗ E_{01}` is the
extremizer of `Optimal.lean`, and evaluating there bounds the *optimal*
amplification coefficient from below --- the first statement in the development
about `λ*` rather than about a valid `λ`. -/

/-- info: 'RankR.thetaPositive_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms thetaPositive_mono

/-- info: 'RankR.two_mul_card_ltPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_card_ltPairs

/--
info: 'RankR.two_mul_card_le_of_thetaPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms two_mul_card_le_of_thetaPositive

/-- info: 'RankR.sub_one_le_lam_of_clique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sub_one_le_lam_of_clique

/-! ## Pair amplification in Choi form, and the threshold pinned

`thetaPositive_of_choiTwoBound` is `thm:pair-amplification` for an arbitrary
completely positive map with transpose-symmetric Kraus operators --- the general
statement of which `Theorem.lean` proves only the `Λ_U ⊗ Λ_V` instance, and it
needs no contraction identity.  `thetaPositive_graphKraus_iff` combines it with
the clique witness: for a graph with an `R`-clique the threshold is exactly
`R - 1`. -/

/--
info: 'RankR.thetaPair_eq_qform_krausQ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms thetaPair_eq_qform_krausQ

/--
info: 'RankR.thetaPositive_of_choiTwoBound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms thetaPositive_of_choiTwoBound

/--
info: 'RankR.thetaPositive_graphKraus_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms thetaPositive_graphKraus_iff

/-! ## Rigidity of linear marginal-preserving encodings -/

/-- info: 'RankR.eq_diagonal_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_diagonal_embedding

/-- info: 'RankR.rank_eq_card_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rank_eq_card_support

end RankR
