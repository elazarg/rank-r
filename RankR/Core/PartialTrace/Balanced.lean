/-
The balanced-factorization route to the partial-trace inequality.

This file specializes the generic crossed-polarization lift to the two
partial traces.
-/
import RankR.Core.PartialTrace.Crossed

namespace RankR

open Matrix

variable {U V : Type*} [Fintype U] [Fintype V]
  {q : ℕ} {e d : Fin q → EuclideanSpace ℂ (U × V)} {τ : ℂ}

/-- The partial-trace inequality along a supplied balanced factorization. -/
theorem balanced_partialTrace_rankFactor_le
    (hq : 0 < q) (hbal : IsBalancedRankFactor e d τ) :
    hsNormSq (ptraceU (rankFactor e d))
        + hsNormSq (ptraceV (rankFactor e d))
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (q : ℝ) * Complex.normSq τ := by
  have h := balancedPolarization_rankFactor_le hq
    partialTracePair_hasRankOneTraceBound
    partialTracePair_hasCrossedPolarization hbal
  rwa [norm_partialTracePair_sq] at h

/-- The manuscript form of the balanced partial-trace lift, with the scalar
term expressed through the trace of the factored matrix. -/
theorem balanced_partialTrace_rankFactor_trace_le
    (hq : 0 < q) (hbal : IsBalancedRankFactor e d τ) :
    hsNormSq (ptraceU (rankFactor e d))
        + hsNormSq (ptraceV (rankFactor e d))
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (1 / (q : ℝ)) * Complex.normSq (rankFactor e d).trace := by
  have h := balancedPolarization_rankFactor_trace_le hq
    partialTracePair_hasRankOneTraceBound
    partialTracePair_hasCrossedPolarization hbal
  rwa [norm_partialTracePair_sq] at h

end RankR
