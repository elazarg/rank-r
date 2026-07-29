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

/-- The complete-graph defect bound for the paired partial traces, in ordered
off-diagonal form. -/
theorem balanced_partialTrace_rankFactor_defect_le
    (hbal : IsBalancedRankFactor e d τ) :
    (q : ℝ) * (∑ i, ‖e i‖ ^ 4) - (∑ i, ‖e i‖ ^ 2) ^ 2
        + ((q : ℝ) - 1) * ∑ i, ∑ j,
          (if i ≠ j then Complex.normSq (inner ℂ (e i) (e j)) else 0)
      ≤ (q : ℝ) * hsNormSq (rankFactor e d)
        + (q : ℝ) * Complex.normSq τ
        - hsNormSq (ptraceU (rankFactor e d))
        - hsNormSq (ptraceV (rankFactor e d)) := by
  have h := balancedPolarization_rankFactor_defect_le
    partialTracePair_hasRankOneTraceBound
    partialTracePair_hasCrossedPolarization hbal
  rw [norm_partialTracePair_sq] at h
  linarith

section ExactRank

variable (C : Matrix (U × V) (U × V) ℂ)

/-- A balanced factorization at the exact rank gives the exact-rank
partial-trace inequality. -/
theorem partialTrace_exact_of_hasBalancedRankFactorization
    (hbal : HasBalancedRankFactorization C) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C
        + (1 / (C.rank : ℝ)) * Complex.normSq C.trace := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp [hsNormSq]
  · obtain ⟨e, d, τ, hfac, heq⟩ := hbal
    have h := balanced_partialTrace_rankFactor_trace_le
      (rank_pos_of_ne_zero hC) heq
    rwa [← hfac] at h

/-- The balanced-factorization route at an arbitrary rank bound. -/
theorem partialTrace_of_hasBalancedRankFactorization
    (hbal : HasBalancedRankFactorization C)
    (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp [hsNormSq]
  · exact (partialTrace_exact_of_hasBalancedRankFactorization C hbal).trans
      (rank_mono (Complex.normSq_nonneg _) (rank_pos_of_ne_zero hC)
        hrank (normSq_trace_le_rank C))

/-- If every matrix on the bipartite space has a balanced exact-rank
factorization, the rank-r partial-trace inequality follows for every matrix. -/
theorem partialTrace_of_balancedRankFactorizations
    (hbal : HasBalancedRankFactorizations (U × V))
    (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  partialTrace_of_hasBalancedRankFactorization C (hbal C) r hrank

/-- The rank-`r` partial-trace inequality obtained through balanced
factorization and crossed polarization. -/
theorem partialTrace_via_balancedPolarization
    (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  by
    have h := balancedPolarization C
      partialTracePair_hasRankOneTraceBound
      partialTracePair_hasCrossedPolarization r hrank
    rwa [norm_partialTracePair_sq] at h

end ExactRank

end RankR
