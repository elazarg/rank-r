/-
The Hilbert-Schmidt layer.

Rather than building an `InnerProductSpace` on `Matrix m n ℂ` by hand, we
transport along `vec : Matrix m n ℂ ≃ EuclideanSpace ℂ (m × n)`.  Mathlib
already has the inner product space structure there, so Cauchy-Schwarz,
positivity, and the norm/inner bridge all come for free.
-/
import RankR.Conventions

namespace RankR

open Matrix Finset

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] [Fintype n] in
@[simp] theorem vec_apply (A : Matrix m n ℂ) (p : m × n) : vec A p = A p.1 p.2 := rfl

/-- The Hilbert-Schmidt inner product IS the Euclidean inner product of the
vectorizations.  This is the bridge that makes gap A cheap. -/
theorem hsInner_eq_inner (A B : Matrix m n ℂ) :
    hsInner A B = inner ℂ (vec A) (vec B) := by
  rw [PiLp.inner_apply]
  simp only [vec_apply, RCLike.inner_apply', Fintype.sum_prod_type, hsInner,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]
  exact Finset.sum_comm

theorem hsInner_self (A : Matrix m n ℂ) : hsInner A A = (hsNormSq A : ℂ) := by
  simp only [hsInner, hsNormSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self]
  exact Finset.sum_comm

theorem hsNormSq_eq_norm_sq (A : Matrix m n ℂ) : hsNormSq A = ‖vec A‖ ^ 2 := by
  have h : ((hsNormSq A : ℝ) : ℂ) = inner ℂ (vec A) (vec A) := by
    rw [← hsInner_self, hsInner_eq_inner]
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (vec A)
  rw [← h] at h2
  simpa using h2

theorem hsNormSq_nonneg (A : Matrix m n ℂ) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_norm_sq]; positivity

/-- Hilbert-Schmidt Cauchy-Schwarz, `|⟪A,B⟫|² ≤ ‖A‖₂² ‖B‖₂²`.
Used for the trace-rank bound in §3 and for `eq:kronecker-CS` in Cor 8.1. -/
theorem normSq_hsInner_le (A B : Matrix m n ℂ) :
    Complex.normSq (hsInner A B) ≤ hsNormSq A * hsNormSq B := by
  rw [hsInner_eq_inner, hsNormSq_eq_norm_sq, hsNormSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  have h := norm_inner_le_norm (𝕜 := ℂ) (vec A) (vec B)
  have h0 : (0:ℝ) ≤ ‖inner ℂ (vec A) (vec B)‖ := norm_nonneg _
  nlinarith [norm_nonneg (vec A), norm_nonneg (vec B)]

end RankR
