/-
Contraction identities for assembled frame vectors.
-/
import RankR.Library.Matrix.QuadraticForm

namespace RankR

open Matrix Finset ComplexConjugate

variable {W : Type*} [Fintype W] {s : ℕ}

/-- The inner product of two assembled vectors is the conjugate trace of their
rank factorization. -/
theorem inner_delta_delta (e d : Fin s → EuclideanSpace ℂ W) :
    inner ℂ (delta e) (delta d) = conj ((rankFactor e d).trace) := by
  rw [contraction_trace, PiLp.inner_apply, map_sum, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl fun p _ => by
    simp; ring

/-- The rank-one quadratic form of assembled vectors is the squared modulus of
the factorization trace. -/
theorem qform_rho_delta (e d : Fin s → EuclideanSpace ℂ W) :
    qform (rankOne (delta e) (delta e)) (delta d)
      = ((Complex.normSq ((rankFactor e d).trace) : ℝ) : ℂ) := by
  rw [qform_rankOne, inner_delta_delta, Complex.normSq_conj]

end RankR
