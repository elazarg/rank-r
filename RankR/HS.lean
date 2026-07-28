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

theorem vec_sum {ι : Type*} (t : Finset ι) (A : ι → Matrix m n ℂ) :
    vec (∑ i ∈ t, A i) = ∑ i ∈ t, vec (A i) := by
  ext p
  show (∑ i ∈ t, A i) p.1 p.2 = (∑ i ∈ t, vec (A i)) p
  rw [Matrix.sum_apply]
  show _ = WithLp.ofLp (∑ i ∈ t, vec (A i)) p
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

end Vec

/-! ## The standard basis

Written out rather than taken from Mathlib's deprecated `EuclideanSpace.single`,
so that its value at a point is definitional and `simp` can see through it via
`eBasis_apply`.  It decides an equality but sums over nothing, so it needs
`DecidableEq` and not `Fintype`. -/

/-- The standard basis vector of `EuclideanSpace ℂ W` at the coordinate `x`. -/
noncomputable def eBasis {W : Type*} [DecidableEq W] (x : W) : EuclideanSpace ℂ W :=
  WithLp.toLp 2 fun p => if p = x then (1 : ℂ) else 0

@[simp] theorem eBasis_apply {W : Type*} [DecidableEq W] (x p : W) :
    eBasis x p = if p = x then (1 : ℂ) else 0 := rfl

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

/-- `hsInner` respects subtraction in its first argument. -/
theorem hsInner_sub_left (A B C : Matrix m n ℂ) :
    hsInner (A - B) C = hsInner A C - hsInner B C := by
  simp only [hsInner, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.trace_sub]

/-- `hsInner` respects subtraction in its second argument. -/
theorem hsInner_sub_right (A B C : Matrix m n ℂ) :
    hsInner A (B - C) = hsInner A B - hsInner A C := by
  simp only [hsInner, Matrix.mul_sub, Matrix.trace_sub]

/-- `hsInner` is conjugate-homogeneous in its first argument. -/
theorem hsInner_smul_left (c : ℂ) (A B : Matrix m n ℂ) :
    hsInner (c • A) B = conj c * hsInner A B := by
  simp [hsInner, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul,
    RCLike.star_def, smul_eq_mul]

/-- `hsInner` is homogeneous in its second argument. -/
theorem hsInner_smul_right (c : ℂ) (A B : Matrix m n ℂ) :
    hsInner A (c • B) = c * hsInner A B := by
  simp [hsInner, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- The two signs of a pairing of negatives cancel. -/
theorem hsInner_neg_neg (A B : Matrix m n ℂ) : hsInner (-A) (-B) = hsInner A B := by
  simp [hsInner]

/-- `hsInner` is additive in its first argument, over an arbitrary finite index. -/
theorem hsInner_sum_left {ι : Type*} [Fintype ι] (A : ι → Matrix m n ℂ) (B : Matrix m n ℂ) :
    hsInner (∑ a, A a) B = ∑ a, hsInner (A a) B := by
  simp only [hsInner, Matrix.conjTranspose_sum]
  rw [Matrix.sum_mul, Matrix.trace_sum]

/-- `hsInner` is additive in its second argument, over an arbitrary finite index. -/
theorem hsInner_sum_right {ι : Type*} [Fintype ι] (A : Matrix m n ℂ) (B : ι → Matrix m n ℂ) :
    hsInner A (∑ b, B b) = ∑ b, hsInner A (B b) := by
  simp [hsInner, Matrix.mul_sum, Matrix.trace_sum]

/-- Sesquilinearity of `hsInner` over a pair of finite sums.  The two index types
are independent: nothing here pairs the summands off. -/
theorem hsInner_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Matrix m n ℂ) (B : κ → Matrix m n ℂ) :
    hsInner (∑ i, A i) (∑ j, B j) = ∑ i, ∑ j, hsInner (A i) (B j) := by
  rw [hsInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => hsInner_sum_right _ _

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
