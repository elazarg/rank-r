/-
Theorem 1.1, with no hypotheses.

`Takagi.lean` derives the double-skew action bound from Autonne-Takagi, carried
there as a `Prop`-valued hypothesis; `Autonne.lean` proves Autonne-Takagi.
Composing them discharges the hypothesis, so the chain

  Autonne-Takagi  →  Lemma 2.1  →  Proposition 2.2  →  Theorem 1.1

is complete and nothing is assumed.

This supersedes the Fu-Gao-Park route.  `FGPBound`, `Antisym.lean` and
`Extend.lean` are retained: they record that the manuscript's standing
hypothesis, as Fu-Gao-Park actually publish it, implies the same conclusion, and
`Extend.lean`'s zero-extension is what reconciles their square statement with
arbitrary local dimensions.  None of it is needed for the results below.

`Equivalence.lean` closes the loop: it proves the converse of
`doubleSkewBound_of_FGP`, so `FGPBound` and the double-skew bound are equivalent
and both are proved.  Fu-Gao-Park's Theorem 2.4, in the rendering
`Conventions.lean` fixes, is therefore machine-checked as well
(`fgpBound_holds`).
-/
import RankR.Autonne
import RankR.Takagi
import RankR.Theorem

namespace RankR

open Matrix

section Interface

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Autonne-Takagi holds**, so the hypothesis carried through `Takagi.lean` is
discharged.  This is `Matrix.exists_takagi` repackaged as the `Prop` that file
assumes. -/
theorem takagiFactorization_holds : TakagiFactorization W :=
  fun _K hK => Matrix.exists_takagi _K hK

end Interface

section Main

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  (C : Matrix (U × V) (U × V) ℂ)

/-- **The double-skew action bound** (`lem:double-skew`), unconditionally. -/
theorem doubleSkewBound_holds : DoubleSkewBound U V :=
  doubleSkewBound_of_takagi takagiFactorization_holds

/-- **Proposition 2.2** (`prop:operator_ineq`), unconditionally. -/
theorem operatorIneq_holds : OperatorIneq U V :=
  operatorIneq_of_doubleSkew doubleSkewBound_holds

/-- **Theorem 1.1** (`thm:rank_r`, `eq:main-bound`), unconditionally.

For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`. -/
theorem rank_r_partial_trace (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_doubleSkew doubleSkewBound_holds C r hr hrank

/-- **Theorem 1.1 at the exact rank** (`eq:main-bound-exact-rank`),
unconditionally. -/
theorem rank_r_partial_trace_exact :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace :=
  rank_r_partial_trace_exact_of_doubleSkew doubleSkewBound_holds C

/-- **Strictness below the exact rank** (`sec:proof`), unconditionally. -/
theorem rank_r_partial_trace_strict (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_strict_of_doubleSkew doubleSkewBound_holds C hC r hrank

/-- **Equality forces the exact rank** (`thm:rank_r`, sharpness paragraph),
unconditionally. -/
theorem rank_eq_of_eq_rank_r_partial_trace (hC : C ≠ 0) (r : ℕ)
    (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  rank_eq_of_eq_rank_r_partial_trace_of_doubleSkew doubleSkewBound_holds C hC r hrank heq

end Main

end RankR
