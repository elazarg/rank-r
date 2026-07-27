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
import RankR.Extend
import RankR.Optimal
import RankR.OneSided

namespace RankR

/-! ## Theorem 1.1 and its refinements, conditional on Fu-Gao-Park -/

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

/-! ## The three steps of the conditional chain

`FGPBound` as published, then Lemma 2.1, then Proposition 2.2. -/

/-- info: 'RankR.FGPBound_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FGPBound_of_card_le

/-- info: 'RankR.doubleSkewBound_of_FGP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms doubleSkewBound_of_FGP

/-- info: 'RankR.operatorIneq_of_doubleSkew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms operatorIneq_of_doubleSkew

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
