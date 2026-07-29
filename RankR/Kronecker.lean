/-
The Kronecker-sum application of the rank-r partial-trace inequality.

This file separates the algebraic and rank-sensitive content of
`cor:kronecker` from its one operator-theoretic input.  The Kronecker pairing,
the centered partial-trace norm, the Cauchy--Schwarz step, the rank-k bound, and
the full Frobenius bound are proved below.  The final identification of the
rank-k Frobenius test supremum with the sum of the first k squared singular
values is isolated at the end as `KyFanFrobeniusDuality`.
-/
import RankR.Applications
import RankR.GraphFamily
import Mathlib.Analysis.InnerProductSpace.SingularValues

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

/-! ## Hilbert--Schmidt and partial-trace identities -/

section Pairing

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

omit [DecidableEq U] in
/-- Pairing with an operator on the first tensor factor contracts the second
factor of the test matrix. -/
theorem hsInner_kronecker_one_right
    (C : Matrix (U × V) (U × V) ℂ) (A : Matrix U U ℂ) :
    hsInner C (A ⊗ₖ (1 : Matrix V V ℂ)) = hsInner (ptraceV C) A := by
  rw [hsInner_eq_sum_vec, hsInner_eq_sum_vec]
  simp only [Fintype.sum_prod_type, vec_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ptraceV_apply, map_sum, mul_ite, mul_one, mul_zero]
  simp
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

omit [DecidableEq V] in
/-- Pairing with an operator on the second tensor factor contracts the first
factor of the test matrix. -/
theorem hsInner_kronecker_one_left
    (C : Matrix (U × V) (U × V) ℂ) (B : Matrix V V ℂ) :
    hsInner C ((1 : Matrix U U ℂ) ⊗ₖ B) = hsInner (ptraceU C) B := by
  rw [hsInner_eq_sum_vec, hsInner_eq_sum_vec]
  simp only [Fintype.sum_prod_type, vec_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ptraceU_apply, map_sum, ite_mul, one_mul, zero_mul]
  simp
  simp_rw [Finset.sum_mul]
  calc
    (∑ a, ∑ b, ∑ b', conj (C (a, b) (a, b')) * B b b') =
        ∑ b, ∑ a, ∑ b', conj (C (a, b) (a, b')) * B b b' := by
          exact Finset.sum_comm
    _ = ∑ b, ∑ b', ∑ a, conj (C (a, b) (a, b')) * B b b' := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

omit [DecidableEq U] [DecidableEq V] in
/-- Taking either partial trace preserves the full trace. -/
theorem trace_ptraceV (C : Matrix (U × V) (U × V) ℂ) :
    (ptraceV C).trace = C.trace := by
  simp [Matrix.trace, Fintype.sum_prod_type]

omit [DecidableEq U] [DecidableEq V] in
/-- Taking either partial trace preserves the full trace. -/
theorem trace_ptraceU (C : Matrix (U × V) (U × V) ℂ) :
    (ptraceU C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceU_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

end Pairing

section Centering

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

/-- The sum of the two centered marginal norms is exactly the expression in
`eq:kronecker-CS`. -/
theorem centeredPartialTrace_normSq_eq
    (C : Matrix (D × D) (D × D) ℂ) (hd : 0 < Fintype.card D) :
    hsNormSq
          (ptraceV C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ))
        + hsNormSq
          (ptraceU C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ))
      =
        hsNormSq (ptraceV C) + hsNormSq (ptraceU C)
          - (2 / (Fintype.card D : ℝ)) * Complex.normSq C.trace := by
  have hV :
      hsNormSq
          (ptraceV C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) =
        hsNormSq (ptraceV C)
          - Complex.normSq C.trace / (Fintype.card D : ℝ) := by
    rw [← trace_ptraceV C]
    exact hsNormSq_sub_trace_smul_one _ hd
  have hU :
      hsNormSq
          (ptraceU C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) =
        hsNormSq (ptraceU C)
          - Complex.normSq C.trace / (Fintype.card D : ℝ) := by
    rw [← trace_ptraceU C]
    exact hsNormSq_sub_trace_smul_one _ hd
  rw [hV, hU]
  ring

end Centering

/-! ## The concrete Kronecker sum -/

section KroneckerSum

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- `A ⊗ I + I ⊗ B`. -/
noncomputable def kroneckerSum (A B : Matrix D D ℂ) :
    Matrix (D × D) (D × D) ℂ :=
  A ⊗ₖ (1 : Matrix D D ℂ) + (1 : Matrix D D ℂ) ⊗ₖ B

/-- `eq:kronecker-pairing` before centering. -/
theorem hsInner_kroneckerSum (C : Matrix (D × D) (D × D) ℂ)
    (A B : Matrix D D ℂ) :
    hsInner C (kroneckerSum A B) =
      hsInner (ptraceV C) A + hsInner (ptraceU C) B := by
  rw [kroneckerSum, hsInner_add_right, hsInner_kronecker_one_right,
    hsInner_kronecker_one_left]

/-- `eq:kronecker-pairing`, including the two traceless projections. -/
theorem hsInner_kroneckerSum_centered
    (C : Matrix (D × D) (D × D) ℂ) (A B : Matrix D D ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    hsInner C (kroneckerSum A B) =
      hsInner
          (ptraceV C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) A
        + hsInner
          (ptraceU C
            - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) B := by
  rw [hsInner_kroneckerSum, hsInner_sub_left, hsInner_sub_left,
    hsInner_smul_left, hsInner_smul_left, hsInner_one_left, hsInner_one_left,
    hA, hB]
  simp

/-- Put two matrices into one Euclidean vector, so the two-term
Cauchy--Schwarz estimate is ordinary Hilbert-space Cauchy--Schwarz. -/
noncomputable def matrixPairVec (X Y : Matrix D D ℂ) :
    EuclideanSpace ℂ ((D × D) ⊕ (D × D)) :=
  WithLp.toLp 2 (Sum.elim (fun p => X p.1 p.2) (fun p => Y p.1 p.2))

omit [Fintype D] [DecidableEq D] in
@[simp] theorem matrixPairVec_inl (X Y : Matrix D D ℂ) (p : D × D) :
    matrixPairVec X Y (Sum.inl p) = X p.1 p.2 := rfl

omit [Fintype D] [DecidableEq D] in
@[simp] theorem matrixPairVec_inr (X Y : Matrix D D ℂ) (p : D × D) :
    matrixPairVec X Y (Sum.inr p) = Y p.1 p.2 := rfl

omit [DecidableEq D] in
theorem inner_matrixPairVec (X Y A B : Matrix D D ℂ) :
    inner ℂ (matrixPairVec X Y) (matrixPairVec A B) =
      hsInner X A + hsInner Y B := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, hsInner_eq_sum_vec, hsInner_eq_sum_vec]
  simp only [RCLike.inner_apply', matrixPairVec_inl, matrixPairVec_inr, vec_apply]

omit [DecidableEq D] in
theorem normSq_matrixPairVec (X Y : Matrix D D ℂ) :
    ‖matrixPairVec X Y‖ ^ 2 = hsNormSq X + hsNormSq Y := by
  rw [norm_sq_eq_sum_normSq, Fintype.sum_sum_type]
  simp only [matrixPairVec_inl, matrixPairVec_inr, hsNormSq, Fintype.sum_prod_type]

omit [DecidableEq D] in
/-- Two-term Hilbert--Schmidt Cauchy--Schwarz. -/
theorem normSq_hsInner_add_le (X Y A B : Matrix D D ℂ) :
    Complex.normSq (hsInner X A + hsInner Y B) ≤
      (hsNormSq X + hsNormSq Y) * (hsNormSq A + hsNormSq B) := by
  rw [← inner_matrixPairVec, Complex.normSq_eq_norm_sq, ← normSq_matrixPairVec X Y,
    ← normSq_matrixPairVec A B]
  have h := norm_inner_le_norm (𝕜 := ℂ) (matrixPairVec X Y) (matrixPairVec A B)
  have h₀ : 0 ≤ ‖inner ℂ (matrixPairVec X Y) (matrixPairVec A B)‖ := norm_nonneg _
  have h₁ : 0 ≤ ‖matrixPairVec X Y‖ * ‖matrixPairVec A B‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- `eq:kronecker-CS` exactly: the centered partial traces are the first
Cauchy--Schwarz factor. -/
theorem normSq_hsInner_kroneckerSum_le
    (C : Matrix (D × D) (D × D) ℂ) (A B : Matrix D D ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) (hd : 0 < Fintype.card D) :
    Complex.normSq (hsInner C (kroneckerSum A B)) ≤
      (hsNormSq A + hsNormSq B)
        * (hsNormSq (ptraceV C) + hsNormSq (ptraceU C)
          - (2 / (Fintype.card D : ℝ)) * Complex.normSq C.trace) := by
  rw [hsInner_kroneckerSum_centered C A B hA hB]
  have h := normSq_hsInner_add_le
    (ptraceV C - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ))
    (ptraceU C - (C.trace / (Fintype.card D : ℂ)) • (1 : Matrix D D ℂ)) A B
  rw [centeredPartialTrace_normSq_eq C hd] at h
  nlinarith

omit [DecidableEq D] in
/-- Ordinary Hilbert--Schmidt Cauchy--Schwarz for matrices. -/
theorem normSq_hsInner_le {m n : Type*} [Fintype m] [Fintype n]
    (X Y : Matrix m n ℂ) :
    Complex.normSq (hsInner X Y) ≤ hsNormSq X * hsNormSq Y := by
  rw [hsInner_eq_inner, Complex.normSq_eq_norm_sq, hsNormSq_eq_norm_sq,
    hsNormSq_eq_norm_sq]
  have h := norm_inner_le_norm (𝕜 := ℂ) (vec X) (vec Y)
  have h₀ : 0 ≤ ‖inner ℂ (vec X) (vec Y)‖ := norm_nonneg _
  have h₁ : 0 ≤ ‖vec X‖ * ‖vec Y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Tracelessness kills the cross term in the squared Frobenius norm of a
Kronecker sum. -/
theorem hsNormSq_kroneckerSum (A B : Matrix D D ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    hsNormSq (kroneckerSum A B) =
      (Fintype.card D : ℝ) * (hsNormSq A + hsNormSq B) := by
  rw [← Complex.ofReal_inj]
  let M := kroneckerSum A B
  rw [show ((hsNormSq M : ℝ) : ℂ) = hsInner M M from (hsInner_self M).symm]
  dsimp only [M, kroneckerSum]
  rw [hsInner_add_left, hsInner_add_right, hsInner_add_right,
    hsInner_kron, hsInner_kron, hsInner_kron, hsInner_kron]
  simp [hsInner_self, hsInner_one_left, hsInner_one_right, hA, hB, hsNormSq_one]
  ring

/-- The rank-sensitive branch of `eq:kronecker-bound`, without normalizing the
test matrix. -/
theorem normSq_hsInner_kroneckerSum_le_rank {k : ℕ} (hk : 0 < k)
    (C : Matrix (D × D) (D × D) ℂ) (hrank : C.rank ≤ k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) :
    Complex.normSq (hsInner C (kroneckerSum A B)) ≤
      ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D))
        * (hsNormSq A + hsNormSq B) * hsNormSq C := by
  have hCS := normSq_hsInner_kroneckerSum_le C A B hA hB hd
  have hcenter := centeredPartialTrace_le hk hd C hrank
  have hAB : 0 ≤ hsNormSq A + hsNormSq B :=
    add_nonneg (hsNormSq_nonneg A) (hsNormSq_nonneg B)
  have hmul := mul_le_mul_of_nonneg_left hcenter hAB
  calc
    Complex.normSq (hsInner C (kroneckerSum A B))
        ≤ (hsNormSq A + hsNormSq B)
            * (hsNormSq (ptraceV C) + hsNormSq (ptraceU C)
              - (2 / (Fintype.card D : ℝ)) * Complex.normSq C.trace) := hCS
    _ ≤ (hsNormSq A + hsNormSq B)
          * (((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D))
            * hsNormSq C) := by
      simpa [add_comm] using hmul
    _ = ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D))
          * (hsNormSq A + hsNormSq B) * hsNormSq C := by ring

/-- The full Frobenius branch of `eq:kronecker-bound`. -/
theorem normSq_hsInner_kroneckerSum_le_full
    (C : Matrix (D × D) (D × D) ℂ) (A B : Matrix D D ℂ)
    (hA : A.trace = 0) (hB : B.trace = 0) :
    Complex.normSq (hsInner C (kroneckerSum A B)) ≤
      (Fintype.card D : ℝ) * (hsNormSq A + hsNormSq B) * hsNormSq C := by
  calc
    Complex.normSq (hsInner C (kroneckerSum A B))
        ≤ hsNormSq C * hsNormSq (kroneckerSum A B) :=
          normSq_hsInner_le C (kroneckerSum A B)
    _ = (Fintype.card D : ℝ) * (hsNormSq A + hsNormSq B) * hsNormSq C := by
      rw [hsNormSq_kroneckerSum A B hA hB]
      ring

/-- Both branches of the minimum in `eq:kronecker-bound`, as a pointwise
rank-k Frobenius test inequality. -/
theorem normSq_hsInner_kroneckerSum_le_min {k : ℕ} (hk : 0 < k)
    (C : Matrix (D × D) (D × D) ℂ) (hrank : C.rank ≤ k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) :
    Complex.normSq (hsInner C (kroneckerSum A B)) ≤
      min (Fintype.card D : ℝ)
          ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D))
        * (hsNormSq A + hsNormSq B) * hsNormSq C := by
  by_cases hdc :
      (Fintype.card D : ℝ) ≤
        (k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D)
  · rw [min_eq_left hdc]
    exact normSq_hsInner_kroneckerSum_le_full C A B hA hB
  · have hcd :
        (k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D)
          ≤ (Fintype.card D : ℝ) := le_of_not_ge hdc
    rw [min_eq_right hcd]
    exact normSq_hsInner_kroneckerSum_le_rank hk C hrank A B hA hB hd

end KroneckerSum

/-! ## Rank-constrained Frobenius duality and the exact remaining interface -/

section FrobeniusDuality

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Squared pairings against rank-at-most-`k`, unit-Frobenius test matrices. -/
def frobeniusRankTestValues (k : ℕ) (M : Matrix W W ℂ) : Set ℝ :=
  {q | ∃ C : Matrix W W ℂ,
    C.rank ≤ k ∧ hsNormSq C ≤ 1 ∧ q = Complex.normSq (hsInner C M)}

/-- The squared rank-`k` Frobenius dual quantity in `eq:ky-fan-duality`. -/
noncomputable def frobeniusRankTestSq (k : ℕ) (M : Matrix W W ℂ) : ℝ :=
  sSup (frobeniusRankTestValues k M)

theorem frobeniusRankTestValues_nonempty (k : ℕ) (M : Matrix W W ℂ) :
    (frobeniusRankTestValues k M).Nonempty := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp
  · simp [hsNormSq]
  · simp [hsInner]

omit [DecidableEq W] in
theorem frobeniusRankTestValues_bddAbove (k : ℕ) (M : Matrix W W ℂ) :
    BddAbove (frobeniusRankTestValues k M) := by
  refine ⟨hsNormSq M, ?_⟩
  rintro q ⟨C, -, hnorm, rfl⟩
  calc
    Complex.normSq (hsInner C M) ≤ hsNormSq C * hsNormSq M :=
      normSq_hsInner_le C M
    _ ≤ 1 * hsNormSq M :=
      mul_le_mul_of_nonneg_right hnorm (hsNormSq_nonneg M)
    _ = hsNormSq M := one_mul _

/-- Any homogeneous pointwise rank-`k` bound controls the normalized
Frobenius test supremum. -/
theorem frobeniusRankTestSq_le_of_pointwise {k : ℕ} {M : Matrix W W ℂ}
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (h : ∀ C : Matrix W W ℂ, C.rank ≤ k →
      Complex.normSq (hsInner C M) ≤ Λ * hsNormSq C) :
    frobeniusRankTestSq k M ≤ Λ := by
  apply csSup_le (frobeniusRankTestValues_nonempty k M)
  rintro q ⟨C, hrank, hnorm, rfl⟩
  calc
    Complex.normSq (hsInner C M) ≤ Λ * hsNormSq C := h C hrank
    _ ≤ Λ * 1 := mul_le_mul_of_nonneg_left hnorm hΛ
    _ = Λ := mul_one _

/-- The sum of the first `k` squared singular values, using Mathlib's
zero-indexed decreasing singular-value sequence. -/
noncomputable def kyFanSq (k : ℕ) (M : Matrix W W ℂ) : ℝ :=
  ∑ i ∈ Finset.range k, (Matrix.toEuclideanLin M).singularValues i ^ 2

/-- The one operator-theoretic statement not proved in this development:
Frobenius Ky Fan duality for matrices.  Naming the equality keeps the gap
auditable and lets the whole Kronecker corollary be checked conditionally on
exactly this reusable interface. -/
def KyFanFrobeniusDuality (k : ℕ) (M : Matrix W W ℂ) : Prop :=
  kyFanSq k M = frobeniusRankTestSq k M

end FrobeniusDuality

section KroneckerKyFan

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The coefficient in `eq:kronecker-bound`. -/
noncomputable def kroneckerKyFanCoeff (k d : ℕ) : ℝ :=
  min (d : ℝ) ((k : ℝ) + max 0 (1 - 2 * (k : ℝ) / d))

theorem kroneckerKyFanCoeff_nonneg (k d : ℕ) :
    0 ≤ kroneckerKyFanCoeff k d := by
  exact le_min (Nat.cast_nonneg _)
    (add_nonneg (Nat.cast_nonneg _) (le_max_left _ _))

/-- The complete Kronecker-sum bound in Frobenius-dual form.  No
singular-value theorem is assumed here. -/
theorem frobeniusRankTestSq_kroneckerSum_le {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) :
    frobeniusRankTestSq k (kroneckerSum A B) ≤
      kroneckerKyFanCoeff k (Fintype.card D)
        * (hsNormSq A + hsNormSq B) := by
  apply frobeniusRankTestSq_le_of_pointwise
  · exact mul_nonneg (kroneckerKyFanCoeff_nonneg _ _)
      (add_nonneg (hsNormSq_nonneg A) (hsNormSq_nonneg B))
  · intro C hrank
    simpa [kroneckerKyFanCoeff, mul_assoc] using
      normSq_hsInner_kroneckerSum_le_min hk C hrank A B hA hB hd

/-- `cor:kronecker`, with its remaining reusable operator-theoretic input made
explicit as `KyFanFrobeniusDuality`. -/
theorem kyFanSq_kroneckerSum_le {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D)
    (hdual : KyFanFrobeniusDuality k (kroneckerSum A B)) :
    kyFanSq k (kroneckerSum A B) ≤
      kroneckerKyFanCoeff k (Fintype.card D)
        * (hsNormSq A + hsNormSq B) := by
  rw [hdual]
  exact frobeniusRankTestSq_kroneckerSum_le hk A B hA hB hd

omit [DecidableEq D] in
/-- When `d ≤ 2k`, the rank-sensitive coefficient is exactly `k`. -/
theorem kronecker_rankCoeff_eq_of_card_le_two_mul {k : ℕ}
    (hd : 0 < Fintype.card D) (hdk : Fintype.card D ≤ 2 * k) :
    (k : ℝ) + max 0 (1 - 2 * (k : ℝ) / Fintype.card D) = k := by
  have hdR : (0 : ℝ) < Fintype.card D := by exact_mod_cast hd
  have hdkR : (Fintype.card D : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hdk
  have hfrac : 1 ≤ 2 * (k : ℝ) / Fintype.card D := by
    exact (le_div_iff₀ hdR).2 (by simpa using hdkR)
  rw [max_eq_left (by linarith)]
  ring

/-- The “in particular” clause of `cor:kronecker`, again conditional only on
Frobenius Ky Fan duality. -/
theorem kyFanSq_kroneckerSum_le_of_card_le_two_mul {k : ℕ} (hk : 0 < k)
    (A B : Matrix D D ℂ) (hA : A.trace = 0) (hB : B.trace = 0)
    (hd : 0 < Fintype.card D) (hdk : Fintype.card D ≤ 2 * k)
    (hdual : KyFanFrobeniusDuality k (kroneckerSum A B)) :
    kyFanSq k (kroneckerSum A B) ≤
      (k : ℝ) * (hsNormSq A + hsNormSq B) := by
  have h := kyFanSq_kroneckerSum_le hk A B hA hB hd hdual
  rw [kroneckerKyFanCoeff, kronecker_rankCoeff_eq_of_card_le_two_mul hd hdk] at h
  exact h.trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
    (add_nonneg (hsNormSq_nonneg A) (hsNormSq_nonneg B)))

end KroneckerKyFan

end RankR
