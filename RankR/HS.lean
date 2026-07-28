/-
The Hilbert-Schmidt layer.

The inner product space structure on `Matrix m n ℂ` is transported along
`vec : Matrix m n ℂ ≃ EuclideanSpace ℂ (m × n)`, so Cauchy-Schwarz, positivity,
and the norm/inner bridge are inherited from Mathlib.
-/
import RankR.Conventions

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Vectorization is linear

`vec` reads off entries, so it commutes with every algebraic operation on
matrices without summing over either index.  These live in their own section
because that independence is exactly what lets them be stated without
`Fintype`. -/

section Vec

variable {m n : Type*}

@[simp] theorem vec_apply (A : Matrix m n ℂ) (p : m × n) : vec A p = A p.1 p.2 := rfl

theorem vec_zero : vec (0 : Matrix m n ℂ) = 0 := by
  ext p
  simp [vec]

theorem vec_add (A B : Matrix m n ℂ) : vec (A + B) = vec A + vec B := by
  ext p
  simp [vec]

theorem vec_smul (c : ℂ) (A : Matrix m n ℂ) : vec (c • A) = c • vec A := by
  ext p
  simp [vec]

theorem vec_sum {ι : Type*} [Fintype ι] (A : ι → Matrix m n ℂ) :
    vec (∑ i, A i) = ∑ i, vec (A i) := by
  ext p
  show (∑ i, A i) p.1 p.2 = (∑ i, vec (A i)) p
  rw [Matrix.sum_apply]
  show _ = WithLp.ofLp (∑ i, vec (A i)) p
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

end Vec

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Hilbert-Schmidt inner product IS the Euclidean inner product of the
vectorizations.  This is the bridge that makes gap A cheap. -/
theorem hsInner_eq_inner (A B : Matrix m n ℂ) :
    hsInner A B = inner ℂ (vec A) (vec B) := by
  rw [PiLp.inner_apply]
  simp only [vec_apply, RCLike.inner_apply', Fintype.sum_prod_type, hsInner,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def]
  exact Finset.sum_comm

/-- `hsInner` as a single sum over the vectorization index. -/
theorem hsInner_eq_sum_vec (A B : Matrix m n ℂ) :
    hsInner A B = ∑ X : m × n, conj (vec A X) * vec B X := by
  rw [hsInner_eq_inner, PiLp.inner_apply]
  exact Finset.sum_congr rfl fun X _ => RCLike.inner_apply' _ _

/-- `hsInner` is additive in its first argument. -/
theorem hsInner_add_left (A B C : Matrix m n ℂ) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  simp [hsInner, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

/-- `hsInner` is additive in its second argument. -/
theorem hsInner_add_right (A B C : Matrix m n ℂ) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

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

/-- A finite sum in `EuclideanSpace` is computed coordinatewise. -/
theorem sum_apply_euclidean {ι T : Type*} (t : Finset ι)
    (f : ι → EuclideanSpace ℂ T) (x : T) :
    (∑ a ∈ t, f a) x = ∑ a ∈ t, f a x := by
  show WithLp.ofLp (∑ a ∈ t, f a) x = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

/-- The squared norm of a Euclidean vector is the total squared modulus of its
coordinates.  `EuclideanSpace.norm_eq` states this with a square root on the
outside; clearing it once here saves repeating `Real.sq_sqrt`. -/
theorem norm_sq_eq_sum_normSq {T : Type*} [Fintype T] (v : EuclideanSpace ℂ T) :
    ‖v‖ ^ 2 = ∑ p, Complex.normSq (v p) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun p _ => (Complex.normSq_eq_norm_sq _).symm

theorem hsNormSq_nonneg (A : Matrix m n ℂ) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_norm_sq]; positivity

theorem hsNormSq_pos {A : Matrix m n ℂ} (hA : A ≠ 0) : 0 < hsNormSq A := by
  rw [hsNormSq_eq_norm_sq]
  have hv : vec A ≠ 0 := fun h => hA (by
    ext i j
    have := congrFun (congrArg (WithLp.ofLp) h) (i, j)
    simpa using this)
  exact pow_pos (norm_pos_iff.mpr hv) 2

end RankR
