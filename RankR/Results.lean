/-
Theorem 1.1, with no hypotheses.

The development's single quantitative input is `β`, the rank-two operator norm
of the Choi operator of `Λ_U ⊗ Λ_V`.  `Equivalence.lean` supplies it: Autonne-
Takagi gives the double-skew bound in fixed-point form, that gives Fu-Gao-Park's
Theorem 2.4, and `ChoiSkew.lean` reads `β = 4` off it.  So the chain

  Autonne-Takagi  →  Fu-Gao-Park 2.4  →  β = 4  →  Proposition 2.2  →  Theorem 1.1

is complete and nothing is assumed.

`Antisym.lean` and `Extend.lean` are retained: they record that the manuscript's
standing hypothesis, as Fu-Gao-Park actually publish it, implies the same
conclusion, and `Extend.lean`'s zero-extension is what reconciles their square
statement with arbitrary local dimensions.

The two forms of the input are equivalent, not merely related:
`doubleSkewBound_of_FGP` and `FGPBound_of_doubleSkewBoundQm` run in both
directions, so the double-skew action bound of the manuscript and the estimate
Fu-Gao-Park publish are the same hypothesis, and both are proved.
-/
import RankR.Equivalence

namespace RankR

open Matrix

section Main

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  (C : Matrix (U × V) (U × V) ℂ)

/-- **The rank-two Choi bound for `Λ_U ⊗ Λ_V`**, unconditionally: `β = 4` in the
normalization `Phi4 = 4 Φ`. -/
theorem choiTwoBound_holds : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4 :=
  choiTwoBound_of_FGP fgpBound_holds

/-- **Proposition 2.2** (`prop:operator_ineq`), unconditionally. -/
theorem operatorIneq_holds : OperatorIneq U V :=
  operatorIneq_of_choiTwoBound choiTwoBound_holds

/-- **Theorem 1.1** (`thm:rank_r`, `eq:main-bound`), unconditionally.

For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`. -/
theorem rank_r_partial_trace (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_choiTwoBound choiTwoBound_holds C r hr hrank

/-- **Theorem 1.1 at the exact rank** (`eq:main-bound-exact-rank`),
unconditionally. -/
theorem rank_r_partial_trace_exact :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace :=
  rank_r_partial_trace_exact_of_choiTwoBound choiTwoBound_holds C

/-- **Strictness below the exact rank** (`sec:proof`), unconditionally. -/
theorem rank_r_partial_trace_strict (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_strict_of_choiTwoBound choiTwoBound_holds C hC r hrank

/-- **Equality forces the exact rank** (`thm:rank_r`, sharpness paragraph),
unconditionally. -/
theorem rank_eq_of_eq_rank_r_partial_trace (hC : C ≠ 0) (r : ℕ)
    (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  rank_eq_of_eq_rank_r_partial_trace_of_choiTwoBound choiTwoBound_holds C hC r hrank heq

end Main

end RankR
