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

namespace RankR

/-! ## Theorem 1.1, unconditionally

Nothing below assumes anything.  `Autonne.lean` proves the Autonne-Takagi
factorization, `Takagi.lean` derives the double-skew action bound from it, and
`Results.lean` composes the two.  In particular the Fu-Gao-Park estimate
is no longer a hypothesis of the main theorem. -/

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

/-! ## The abstract liftings

Neither depends on the double-skew subspace: `norm_sq_pair_le_of_choiTwoBound`
is stated for an arbitrary Kraus family and an arbitrary member of its span,
`qform_krausQ_ptransposeUV_ge` for an arbitrary transpose-symmetric one. -/

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

end RankR
