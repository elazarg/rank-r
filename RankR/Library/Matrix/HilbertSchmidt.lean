/-
The Hilbert-Schmidt layer.

The inner product space structure on `Matrix m n ℂ` is transported along
`vec : Matrix m n ℂ ≃ EuclideanSpace ℂ (m × n)`, so Cauchy-Schwarz, positivity,
and the norm/inner bridge are inherited from Mathlib.
-/
import RankR.Library.Conventions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

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

/-- The coefficient matrix of a bipartite Euclidean vector in the fixed
product basis. -/
def unvec (z : EuclideanSpace ℂ (m × n)) : Matrix m n ℂ :=
  fun i j => z (i, j)

@[simp]
theorem unvec_vec (A : Matrix m n ℂ) : unvec (vec A) = A := by
  ext i j
  rfl

@[simp]
theorem vec_unvec (z : EuclideanSpace ℂ (m × n)) : vec (unvec z) = z := by
  ext p
  rfl

@[simp]
theorem unvec_smul (c : ℂ) (z : EuclideanSpace ℂ (m × n)) :
    unvec (c • z) = c • unvec z := by
  ext i j
  rfl

/-- Vectorization as a linear equivalence between matrices and bipartite
coordinate vectors. -/
def vecLinearEquiv : Matrix m n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (m × n) where
  toFun := vec
  invFun := unvec
  left_inv := unvec_vec
  right_inv := vec_unvec
  map_add' := vec_add
  map_smul' := vec_smul

end Vec

/-! ## Pure-vector Schmidt rank in fixed coordinates -/

section SchmidtRank

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Pure-state Schmidt rank across the `m : n` cut, defined as the matrix rank
of the coefficient matrix in the fixed product basis. -/
noncomputable def pureSchmidtRank
    (z : EuclideanSpace ℂ (m × n)) : ℕ :=
  (unvec z).rank

omit [Fintype m] in
/-- `eq:SR-vec-rank`: vectorization identifies pure Schmidt rank with matrix
rank exactly. -/
@[simp]
theorem pureSchmidtRank_vec (A : Matrix m n ℂ) :
    pureSchmidtRank (vec A) = A.rank := by
  rw [pureSchmidtRank, unvec_vec]

omit [Fintype m] in
theorem pureSchmidtRank_le_iff_rank_unvec_le
    (z : EuclideanSpace ℂ (m × n)) (r : ℕ) :
    pureSchmidtRank z ≤ r ↔ (unvec z).rank ≤ r :=
  Iff.rfl

end SchmidtRank

section SchmidtRankScaling

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- Multiplication by a nonzero scalar preserves matrix rank. -/
theorem rank_smul_eq_of_ne_zero (A : Matrix m n ℂ)
    {c : ℂ} (hc : c ≠ 0) :
    (c • A).rank = A.rank := by
  apply le_antisymm
  · have hmul :
        (c • (1 : Matrix m m ℂ)) * A = c • A := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    calc
      (c • A).rank =
          ((c • (1 : Matrix m m ℂ)) * A).rank :=
        congrArg Matrix.rank hmul.symm
      _ ≤ A.rank :=
        Matrix.rank_mul_le_right (c • (1 : Matrix m m ℂ)) A
  · have hmul :
        (c⁻¹ • (1 : Matrix m m ℂ)) * (c • A) = A := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul,
        inv_mul_cancel₀ hc, one_smul]
    calc
      A.rank =
          ((c⁻¹ • (1 : Matrix m m ℂ)) * (c • A)).rank :=
        congrArg Matrix.rank hmul.symm
      _ ≤ (c • A).rank :=
        Matrix.rank_mul_le_right
          (c⁻¹ • (1 : Matrix m m ℂ)) (c • A)

/-- Nonzero scalar normalization preserves pure Schmidt rank. -/
theorem pureSchmidtRank_smul_of_ne_zero
    (z : EuclideanSpace ℂ (m × n)) {c : ℂ} (hc : c ≠ 0) :
    pureSchmidtRank (c • z) = pureSchmidtRank z := by
  rw [pureSchmidtRank, unvec_smul, rank_smul_eq_of_ne_zero _ hc,
    pureSchmidtRank]

end SchmidtRankScaling

/-! ## Finite rank factorization through a coordinate type -/

section RankFactorization

variable {I O A : Type*} [Fintype I] [Fintype O] [Fintype A]
  [DecidableEq I] [DecidableEq O] [DecidableEq A]

omit [Fintype O] [DecidableEq O] in
/-- A matrix has rank at most the size of an intermediate coordinate type iff
it factors through that type. -/
theorem rank_le_card_iff_exists_mul (C : Matrix O I ℂ) :
    C.rank ≤ Fintype.card A ↔
      ∃ X : Matrix O A ℂ, ∃ Y : Matrix A I ℂ, X * Y = C := by
  constructor
  · intro hrank
    let R := LinearMap.range C.mulVecLin
    have hdim : Module.finrank ℂ R ≤ Module.finrank ℂ (A → ℂ) := by
      simpa [R, Matrix.rank, Module.finrank_pi] using hrank
    obtain ⟨e, he⟩ := finrank_le_iff_exists_linearMap.mp hdim
    have heker : LinearMap.ker e = ⊥ := LinearMap.ker_eq_bot.mpr he
    let g : (A → ℂ) →ₗ[ℂ] R := e.leftInverse
    let intoRange : (I → ℂ) →ₗ[ℂ] R := C.mulVecLin.rangeRestrict
    let fromRange : R →ₗ[ℂ] O → ℂ := R.subtype
    let X : Matrix O A ℂ := LinearMap.toMatrix' (fromRange.comp g)
    let Y : Matrix A I ℂ := LinearMap.toMatrix' (e.comp intoRange)
    refine ⟨X, Y, ?_⟩
    dsimp only [X, Y]
    rw [← LinearMap.toMatrix'_comp]
    change LinearMap.toMatrix' ((fromRange.comp g).comp (e.comp intoRange)) = C
    rw [← LinearMap.toMatrix'_toLin' C]
    congr 1
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    rw [show g (e (intoRange x)) = intoRange x by
      exact LinearMap.leftInverse_apply_of_inj heker (intoRange x)]
    rfl
  · rintro ⟨X, Y, rfl⟩
    exact (Matrix.rank_mul_le_left X Y).trans
      (Matrix.rank_le_card_width X)

end RankFactorization

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
theorem hsInner_sum_left {ι : Type*} [Fintype ι]
    (A : ι → Matrix m n ℂ) (B : Matrix m n ℂ) :
    hsInner (∑ a, A a) B = ∑ a, hsInner (A a) B := by
  simp only [hsInner, Matrix.conjTranspose_sum]
  rw [Matrix.sum_mul, Matrix.trace_sum]

/-- `hsInner` is additive in its second argument, over an arbitrary finite index. -/
theorem hsInner_sum_right {ι : Type*} [Fintype ι]
    (A : Matrix m n ℂ) (B : ι → Matrix m n ℂ) :
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

section Identity

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The identity is the trace functional in the first Hilbert--Schmidt slot. -/
theorem hsInner_one_left (X : Matrix D D ℂ) :
    hsInner (1 : Matrix D D ℂ) X = X.trace := by
  simp [hsInner]

/-- The identity is the conjugate trace functional in the second
Hilbert--Schmidt slot. -/
theorem hsInner_one_right (X : Matrix D D ℂ) :
    hsInner X (1 : Matrix D D ℂ) = conj X.trace := by
  simp [hsInner, Matrix.trace_conjTranspose, RCLike.star_def]

/-- The squared Hilbert--Schmidt norm of the identity is the dimension. -/
theorem hsNormSq_one :
    hsNormSq (1 : Matrix D D ℂ) = Fintype.card D := by
  rw [← Complex.ofReal_inj, ← hsInner_self]
  simp [hsInner]

omit [DecidableEq D] in
/-- Sesquilinear expansion of a centered squared norm. -/
theorem hsInner_sub_smul_self (X I : Matrix D D ℂ) (z : ℂ) :
    hsInner (X - z • I) (X - z • I) =
      hsInner X X - z * hsInner X I - conj z * hsInner I X
        + conj z * z * hsInner I I := by
  rw [hsInner_sub_left, hsInner_sub_right, hsInner_smul_left, hsInner_sub_right,
    hsInner_smul_right, hsInner_smul_right]
  ring

/-- Orthogonal projection onto the traceless matrices, in squared
Hilbert--Schmidt norm. -/
theorem hsNormSq_sub_trace_smul_one (X : Matrix D D ℂ)
    (hd : 0 < Fintype.card D) :
    hsNormSq (X - (X.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) =
      hsNormSq X - Complex.normSq X.trace / (Fintype.card D : ℝ) := by
  rw [← Complex.ofReal_inj]
  let z := X.trace / (Fintype.card D : ℂ)
  let H := X - z • (1 : Matrix D D ℂ)
  rw [show ((hsNormSq H : ℝ) : ℂ) = hsInner H H from (hsInner_self H).symm]
  rw [hsInner_sub_smul_self, hsInner_self, hsInner_one_right, hsInner_one_left,
    hsInner_self, hsNormSq_one]
  dsimp only [H, z]
  push_cast
  rw [map_div₀, map_natCast, Complex.normSq_eq_conj_mul_self]
  field_simp [Nat.ne_of_gt hd]
  ring

/-- Unitary conjugation preserves the Hilbert--Schmidt pairing. -/
theorem hsInner_unitary_conjugate
    (U A B : Matrix D D ℂ)
    (hU : U ∈ Matrix.unitaryGroup D ℂ) :
    hsInner (Uᴴ * A * U) (Uᴴ * B * U) = hsInner A B := by
  have hrow : U * Uᴴ = (1 : Matrix D D ℂ) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  rw [hsInner, hsInner, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    Matrix.trace (Uᴴ * (Aᴴ * U) * (Uᴴ * B * U)) =
        Matrix.trace (Uᴴ * (Aᴴ * B) * U) := by
          congr 1
          rw [show Uᴴ * (Aᴴ * U) * (Uᴴ * B * U) =
              Uᴴ * Aᴴ * (U * Uᴴ) * B * U by noncomm_ring,
            hrow]
          noncomm_ring
    _ = Matrix.trace (U * Uᴴ * (Aᴴ * B)) :=
      Matrix.trace_mul_cycle Uᴴ (Aᴴ * B) U
    _ = Matrix.trace (Aᴴ * B) := by rw [hrow, Matrix.one_mul]

/-- Unitary conjugation preserves the squared Hilbert--Schmidt norm. -/
theorem hsNormSq_unitary_conjugate
    (U A : Matrix D D ℂ)
    (hU : U ∈ Matrix.unitaryGroup D ℂ) :
    hsNormSq (Uᴴ * A * U) = hsNormSq A := by
  rw [← Complex.ofReal_inj, ← hsInner_self, ← hsInner_self]
  exact hsInner_unitary_conjugate U A A hU

end Identity

theorem hsNormSq_eq_norm_sq (A : Matrix m n ℂ) : hsNormSq A = ‖vec A‖ ^ 2 := by
  have h : ((hsNormSq A : ℝ) : ℂ) = inner ℂ (vec A) (vec A) := by
    rw [← hsInner_self, hsInner_eq_inner]
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (vec A)
  rw [← h] at h2
  simpa using h2

/-- Put two possibly rectangular matrices into one Euclidean direct-sum
vector.  This realizes the Hilbert direct sum of their Hilbert--Schmidt
spaces without using the max norm on an ordinary product type. -/
noncomputable def matrixSumVec {p q : Type*}
    (X : Matrix m n ℂ) (Y : Matrix p q ℂ) :
    EuclideanSpace ℂ ((m × n) ⊕ (p × q)) :=
  WithLp.toLp 2 (Sum.elim (fun ij => X ij.1 ij.2) (fun ij => Y ij.1 ij.2))

omit [Fintype m] [Fintype n] in
@[simp] theorem matrixSumVec_inl {p q : Type*}
    (X : Matrix m n ℂ) (Y : Matrix p q ℂ) (ij : m × n) :
    matrixSumVec X Y (Sum.inl ij) = X ij.1 ij.2 := rfl

omit [Fintype m] [Fintype n] in
@[simp] theorem matrixSumVec_inr {p q : Type*}
    (X : Matrix m n ℂ) (Y : Matrix p q ℂ) (ij : p × q) :
    matrixSumVec X Y (Sum.inr ij) = Y ij.1 ij.2 := rfl

/-- The direct-sum inner product is the sum of the two Hilbert--Schmidt
pairings. -/
theorem inner_matrixSumVec {p q : Type*} [Fintype p] [Fintype q]
    (X A : Matrix m n ℂ) (Y B : Matrix p q ℂ) :
    inner ℂ (matrixSumVec X Y) (matrixSumVec A B) =
      hsInner X A + hsInner Y B := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, hsInner_eq_sum_vec,
    hsInner_eq_sum_vec]
  simp only [RCLike.inner_apply', matrixSumVec_inl, matrixSumVec_inr, vec_apply]

/-- The direct-sum squared norm is the sum of the two Hilbert--Schmidt squared
norms. -/
theorem normSq_matrixSumVec {p q : Type*} [Fintype p] [Fintype q]
    (X : Matrix m n ℂ) (Y : Matrix p q ℂ) :
    ‖matrixSumVec X Y‖ ^ 2 = hsNormSq X + hsNormSq Y := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [Fintype.sum_sum_type]
  simp only [matrixSumVec_inl, matrixSumVec_inr, hsNormSq,
    Fintype.sum_prod_type]

/-- A finite sum in `EuclideanSpace` is computed coordinatewise. -/
theorem sum_apply_euclidean {ι T : Type*} (t : Finset ι)
    (f : ι → EuclideanSpace ℂ T) (x : T) :
    (∑ a ∈ t, f a) x = ∑ a ∈ t, f a x := by
  show WithLp.ofLp (∑ a ∈ t, f a) x = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

theorem hsNormSq_nonneg (A : Matrix m n ℂ) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_norm_sq]; positivity

theorem hsNormSq_pos {A : Matrix m n ℂ} (hA : A ≠ 0) : 0 < hsNormSq A := by
  rw [hsNormSq_eq_norm_sq]
  have hv : vec A ≠ 0 := fun h => hA (by
    ext i j
    have := congrFun (congrArg (WithLp.ofLp) h) (i, j)
    simpa using this)
  exact pow_pos (norm_pos_iff.mpr hv) 2

/-! ## Transposition and conjugation -/

theorem hsNormSq_transpose (A : Matrix m n ℂ) :
    hsNormSq Aᵀ = hsNormSq A := by
  simp only [hsNormSq, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem hsNormSq_map_conj (A : Matrix m n ℂ) :
    hsNormSq (A.map (starRingEnd ℂ)) = hsNormSq A := by
  simp [hsNormSq, Matrix.map_apply]

theorem hsNormSq_conjTranspose (A : Matrix m n ℂ) :
    hsNormSq Aᴴ = hsNormSq A := by
  simp only [hsNormSq, Matrix.conjTranspose_apply, RCLike.star_def,
    Complex.normSq_conj]
  exact Finset.sum_comm

section Pairings

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The Hilbert--Schmidt pairing of two elementary matrix units. -/
theorem hsInner_single (a b c d : W) :
    hsInner (Matrix.single a b (1 : ℂ)) (Matrix.single c d 1)
      = (if a = c then (1 : ℂ) else 0) * (if b = d then 1 else 0) := by
  rw [hsInner_eq_sum_vec, Fintype.sum_prod_type]
  simp only [vec_apply, Matrix.single_apply, ite_and, apply_ite (starRingEnd ℂ),
    map_one, map_zero, ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd]

end Pairings

section Kronecker

variable {U V : Type*} [Fintype U] [Fintype V]

/-- The Hilbert--Schmidt inner product is multiplicative on Kronecker products. -/
theorem hsInner_kron (A C : Matrix U U ℂ) (B D : Matrix V V ℂ) :
    hsInner (A ⊗ₖ B) (C ⊗ₖ D) = hsInner A C * hsInner B D := by
  rw [hsInner, hsInner, hsInner, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.trace_kronecker]

end Kronecker

end RankR
