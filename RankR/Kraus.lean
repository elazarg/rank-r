/-
Kraus-style sums and positivity.

A Kraus sum `Y ↦ ∑ₐ Kₐ Y Kₐᴴ` acts on quadratic forms by pulling the test
vector back through each `Kₐᴴ`.  Since the pullback only moves the vector, a
matrix whose quadratic form has nonnegative real part is sent to another such
matrix; positive semidefiniteness is preserved.
-/
import RankR.Main

namespace RankR

open Matrix Finset ComplexConjugate

section Kraus

variable {W : Type*} [Fintype W]

/-- Matrix-vector multiplication on `EuclideanSpace`, obtained by transporting
`Matrix.mulVec` through the `WithLp` type synonym. -/
def mulVecE (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 (A.mulVec (WithLp.ofLp x))

@[simp]
theorem mulVecE_apply (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) (p : W) :
    mulVecE A x p = ∑ q, A p q * x q := rfl

/-! ### Linearity in the vector

`mulVecE` is linear in each of its two arguments, and the two families are
distinguished by where the operation sits in the name: `mulVecE_add` and its
companions push an operation through the *vector* slot, while `sum_mulVecE` and
`smul_mulVecE` in `Synth.lean` push one through the *matrix* slot.  The vector
family is collected here, at the definition, so that arguments by linearity over
a spanning set can invoke it directly. -/

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

/-- Exchange of the outer and inner pairs of indices in a four-fold sum. -/
theorem sum_comm₄ (F : W → W → W → W → ℂ) :
    ∑ p, ∑ q, ∑ u, ∑ v, F p q u v = ∑ u, ∑ v, ∑ p, ∑ q, F p q u v :=
  calc ∑ p, ∑ q, ∑ u, ∑ v, F p q u v
      = ∑ p, ∑ u, ∑ q, ∑ v, F p q u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u, ∑ p, ∑ q, ∑ v, F p q u v := Finset.sum_comm
    _ = ∑ u, ∑ p, ∑ v, ∑ q, F p q u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u, ∑ v, ∑ p, ∑ q, F p q u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

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
  rw [hL, hR, sum_comm₄]

/-- The quadratic form is additive in its matrix argument. -/
theorem qform_sum {ι : Type*} [Fintype ι] (A : ι → Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (∑ a, A a) x = ∑ a, qform (A a) x := by
  simp only [qform, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  exact Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

/-- The Kraus sum `Y ↦ ∑ₐ Kₐ Y Kₐᴴ` with Kraus operators `K`. -/
def krausSum {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ) (Y : Matrix W W ℂ) :
    Matrix W W ℂ := ∑ a, K a * Y * (K a)ᴴ

/-- The quadratic form of a Kraus sum is the sum of the quadratic forms of `Y`
at the pullbacks of the test vector through the `Kₐᴴ`. -/
theorem qform_krausSum {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ)
    (Y : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (krausSum K Y) x = ∑ a, qform Y (mulVecE (K a)ᴴ x) := by
  rw [krausSum, qform_sum]
  exact Finset.sum_congr rfl fun a _ => qform_conj (K a) Y x

/-- A Kraus sum preserves positive semidefiniteness. -/
theorem qform_krausSum_nonneg {ι : Type*} [Fintype ι] (K : ι → Matrix W W ℂ)
    {Y : Matrix W W ℂ} (hY : ∀ z : EuclideanSpace ℂ W, 0 ≤ (qform Y z).re)
    (x : EuclideanSpace ℂ W) : 0 ≤ (qform (krausSum K Y) x).re := by
  rw [qform_krausSum, Complex.re_sum]
  exact Finset.sum_nonneg fun a _ => hY _

/-- Rank-one projectors are positive semidefinite. -/
theorem qform_rankOne_nonneg (y x : EuclideanSpace ℂ W) : 0 ≤ (qform (rankOne y y) x).re := by
  rw [qform_rankOne, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ## The action as a linear map

These three say nothing about Kraus sums; they belong with `mulVecE` because
that is what they are about.  Everything downstream that needs the adjoint move
or the `qform`/`inner` bridge gets them from here. -/

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

end Kraus

section ToEuclideanLin

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `mulVecE` is Mathlib's `Matrix.toEuclideanLin`, definitionally.  `mulVecE`
exists so that the development never needs the `DecidableEq` that
`toEuclideanLin` carries; this is the bridge for the places that do. -/
theorem mulVecE_eq_toEuclideanLin (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    mulVecE A x = Matrix.toEuclideanLin A x := rfl

end ToEuclideanLin

end RankR
