/-
Finite complex matrices acting on Euclidean coordinate spaces, with the
adjoint and quadratic-form identities for that action.
-/
import RankR.Library.Matrix.QuadraticForm

namespace RankR

open Matrix Finset ComplexConjugate

variable {W : Type*} [Fintype W]

/-- Matrix-vector multiplication on `EuclideanSpace`, obtained by transporting
`Matrix.mulVec` through the `WithLp` type synonym. -/
def mulVecE (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))

@[simp]
theorem mulVecE_apply (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) (p : W) :
    mulVecE A x p = ∑ q, A p q * x q := rfl

/-- Pairing against a rank-one operator is the vector pairing against the
matrix action. -/
theorem hsInner_rankOne_right (A : Matrix W W ℂ)
    (x y : EuclideanSpace ℂ W) :
    hsInner A (rankOne x y) = conj (inner ℂ x (mulVecE A y)) := by
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def, rankOne, Matrix.of_apply,
    PiLp.inner_apply, RCLike.inner_apply', mulVecE_apply, map_sum, map_mul,
    Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mulVecE_zero (A : Matrix W W ℂ) : mulVecE A 0 = 0 := by
  ext p
  simp [mulVecE_apply]

theorem mulVecE_add (A : Matrix W W ℂ) (x y : EuclideanSpace ℂ W) :
    mulVecE A (x + y) = mulVecE A x + mulVecE A y := by
  ext p
  simp [mulVecE_apply, mul_add, Finset.sum_add_distrib]

theorem mulVecE_sub (A : Matrix W W ℂ) (x y : EuclideanSpace ℂ W) :
    mulVecE A (x - y) = mulVecE A x - mulVecE A y := by
  ext p
  simp [mul_sub, Finset.sum_sub_distrib]

theorem mulVecE_smul (c : ℂ) (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE A (c • x) = c • mulVecE A x := by
  ext p
  simp [mulVecE_apply, Finset.mul_sum, mul_left_comm]

theorem mulVecE_sum {ι : Type*} (t : Finset ι) (A : Matrix W W ℂ)
    (x : ι → EuclideanSpace ℂ W) :
    mulVecE A (∑ i ∈ t, x i) = ∑ i ∈ t, mulVecE A (x i) := by
  ext p
  rw [mulVecE_apply, sum_apply_euclidean]
  have h : ∀ q : W, A p q * (∑ i ∈ t, x i) q = ∑ i ∈ t, A p q * x i q := fun q => by
    rw [sum_apply_euclidean, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (mulVecE_apply _ _ _).symm

theorem mulVecE_mul (A B : Matrix W W ℂ) (v : EuclideanSpace ℂ W) :
    mulVecE A (mulVecE B v) = mulVecE (A * B) v := by
  ext p
  simp only [mulVecE_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

/-- `⟪z, A x⟫ = ⟪Aᴴ z, x⟫`: both sides equal the double sum
`∑_p ∑_q conj(z p) A_{pq} x_q`. -/
theorem inner_mulVecE_left (A : Matrix W W ℂ) (z x : EuclideanSpace ℂ W) :
    inner ℂ z (mulVecE A x) = inner ℂ (mulVecE Aᴴ z) x := by
  have hL : (inner ℂ z (mulVecE A x) : ℂ) = ∑ p, ∑ q, conj (z p) * A p q * x q := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => (mul_assoc _ _ _).symm
  have hR : (inner ℂ (mulVecE Aᴴ z) x : ℂ) = ∑ q, ∑ p, conj (z p) * A p q * x q := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RCLike.inner_apply', mulVecE_apply, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]
    ring
  rw [hL, hR, Finset.sum_comm]

/-- `qform` is the inner product against the matrix action. -/
theorem qform_eq_inner (A : Matrix W W ℂ) (v : EuclideanSpace ℂ W) :
    qform A v = inner ℂ v (mulVecE A v) := by
  rw [PiLp.inner_apply, qform]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Pairing an operator with a rank-one projector gives its real quadratic
form. -/
theorem re_hsInner_rankOne (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    (hsInner A (rankOne x x)).re = (qform A x).re := by
  have h :
      hsInner A (rankOne x x) = conj (inner ℂ x (mulVecE A x)) := by
    simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, RCLike.star_def, rankOne, Matrix.of_apply,
      PiLp.inner_apply, RCLike.inner_apply', mulVecE_apply, map_sum, map_mul,
      Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h, qform_eq_inner]
  exact Complex.conj_re _

/-- Conjugating a matrix by `A` pulls the test vector back through `Aᴴ`. -/
theorem qform_conj (A Y : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (A * Y * Aᴴ) x = qform Y (mulVecE Aᴴ x) := by
  have hL : qform (A * Y * Aᴴ) x
      = ∑ p, ∑ q, ∑ u, ∑ v, conj (x p) * A p u * Y u v * conj (A q v) * x q := by
    simp only [qform]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by ring
  have hR : qform Y (mulVecE Aᴴ x)
      = ∑ u, ∑ v, ∑ p, ∑ q, conj (x p) * A p u * Y u v * conj (A q v) * x q := by
    simp only [qform]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    simp only [mulVecE_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [hL, hR]
  exact sum4_swap fun u v p q => conj (x p) * A p u * Y u v * conj (A q v) * x q

section ToEuclideanLin

variable [DecidableEq W]

/-- `mulVecE` is Mathlib's `Matrix.toEuclideanLin`, definitionally. -/
theorem mulVecE_eq_toEuclideanLin (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE A x = Matrix.toEuclideanLin A x := rfl

end ToEuclideanLin

end RankR
