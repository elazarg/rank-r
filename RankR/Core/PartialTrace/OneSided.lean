/-
The one-sided partial-trace bound, `lem:one-sided-partial-trace`:
`‖Tr_U C‖₂² ≤ r‖C‖₂²` and `‖Tr_V C‖₂² ≤ r‖C‖₂²` for `C` of rank at most `r`.

The manuscript proves this by trace-norm duality, `‖Tr_j C‖₂ ≤ ‖Tr_j C‖₁ ≤ ‖C‖₁
≤ √r ‖C‖₂`, which imports Schatten-1 theory for a single lemma.  With the range
factorization `C = ∑ᵢ |eᵢ⟩⟨dᵢ|` already available it is elementary: a partial
trace of a rank-one operator is a matrix product,

  `Tr_V |x⟩⟨y| = X Yᴴ`,   `Tr_U |x⟩⟨y| = conj (Xᴴ Y)`,

where `X`, `Y` are the `U × V` matrices of `x`, `y`.  Hilbert-Schmidt
submultiplicativity bounds each term by `‖eᵢ‖‖dᵢ‖ = ‖dᵢ‖`, and Cauchy-Schwarz
on the `r`-term sum gives the factor `r`.

Unlike Theorem 1.1, nothing here is conditional on the Fu-Gao-Park estimate.
-/
import RankR.Core.PartialTrace.FromOperator

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Hilbert-Schmidt products -/

section Submultiplicative

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- **Hilbert-Schmidt submultiplicativity**, `‖AB‖₂² ≤ ‖A‖₂²‖B‖₂²`.

Entry `(i,k)` of `AB` is the pairing of the conjugated `i`-th row of `A` with the
`k`-th column of `B`, so Cauchy-Schwarz in `EuclideanSpace ℂ m` bounds its
squared modulus by the product of the two squared norms; summing over `(i,k)`
factorizes. -/
theorem hsNormSq_mul_le (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    hsNormSq (A * B) ≤ hsNormSq A * hsNormSq B := by
  have key : ∀ (i : l) (k : n), Complex.normSq ((A * B) i k)
      ≤ (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (B j k)) := by
    intro i k
    set u : EuclideanSpace ℂ m := WithLp.toLp 2 (fun j => conj (A i j)) with hu
    set v : EuclideanSpace ℂ m := WithLp.toLp 2 (fun j => B j k) with hv
    have hin : (inner ℂ u v : ℂ) = (A * B) i k := by
      rw [PiLp.inner_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RCLike.inner_apply']
      simp [hu, hv]
    have hnu : ‖u‖ ^ 2 = ∑ j, Complex.normSq (A i j) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp_rw [← Complex.normSq_eq_norm_sq]
      exact Finset.sum_congr rfl fun j _ => by simp [hu]
    have hnv : ‖v‖ ^ 2 = ∑ j, Complex.normSq (B j k) := by
      rw [EuclideanSpace.norm_sq_eq]
      simp_rw [← Complex.normSq_eq_norm_sq]
      exact Finset.sum_congr rfl fun j _ => by simp [hv]
    have hcs := norm_inner_le_norm (𝕜 := ℂ) u v
    have h0 : (0 : ℝ) ≤ ‖inner ℂ u v‖ := norm_nonneg _
    have hnn : (0 : ℝ) ≤ ‖u‖ * ‖v‖ := by positivity
    have : Complex.normSq ((A * B) i k) = ‖inner ℂ u v‖ ^ 2 := by
      rw [hin, Complex.normSq_eq_norm_sq]
    rw [this, ← hnu, ← hnv]
    nlinarith
  calc hsNormSq (A * B)
      = ∑ i, ∑ k, Complex.normSq ((A * B) i k) := rfl
    _ ≤ ∑ i, ∑ k, (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (B j k)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => key i k
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ k, ∑ j, Complex.normSq (B j k)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = hsNormSq A * hsNormSq B := by
        rw [hsNormSq, hsNormSq]
        exact congrArg (_ * ·) (Finset.sum_comm)

end Submultiplicative

/-! ## Partial traces of rank-one operators as matrix products -/

/-! Reading a partial trace as a matrix product contracts one factor and leaves
the other alone, so each of the two identities needs only its own factor to be
finite. -/

section RankOne

variable {U V : Type*} [Fintype U] [Fintype V]

/-- The `U × V` matrix of a vector on `U × V`. -/
def matOf (x : EuclideanSpace ℂ (U × V)) : Matrix U V ℂ := Matrix.of fun a b => x (a, b)

omit [Fintype U] [Fintype V] in
@[simp] theorem matOf_apply (x : EuclideanSpace ℂ (U × V)) (a : U) (b : V) :
    matOf x a b = x (a, b) := rfl

theorem hsNormSq_matOf (x : EuclideanSpace ℂ (U × V)) : hsNormSq (matOf x) = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [← Complex.normSq_eq_norm_sq]
  rw [hsNormSq]
  exact (Fintype.sum_prod_type fun p : U × V => Complex.normSq (x p)).symm

omit [Fintype U] in
/-- `Tr_V |x⟩⟨y| = X Yᴴ`. -/
theorem ptraceV_rankOne (x y : EuclideanSpace ℂ (U × V)) :
    ptraceV (rankOne x y) = matOf x * (matOf y)ᴴ := by
  ext a a'
  simp [Matrix.mul_apply, rankOne, Matrix.conjTranspose_apply, RCLike.star_def]

omit [Fintype V] in
/-- `Tr_U |x⟩⟨y| = conj (Xᴴ Y)`. -/
theorem ptraceU_rankOne (x y : EuclideanSpace ℂ (U × V)) :
    ptraceU (rankOne x y) = ((matOf x)ᴴ * matOf y).map (starRingEnd ℂ) := by
  ext b c
  simp [Matrix.mul_apply, rankOne, Matrix.conjTranspose_apply, RCLike.star_def,
    Matrix.map_apply]

/-- `‖Tr_V |x⟩⟨y|‖₂² ≤ ‖x‖²‖y‖²`. -/
theorem hsNormSq_ptraceV_rankOne_le (x y : EuclideanSpace ℂ (U × V)) :
    hsNormSq (ptraceV (rankOne x y)) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [ptraceV_rankOne, ← hsNormSq_matOf x, ← hsNormSq_matOf y, ← hsNormSq_conjTranspose (matOf y)]
  exact hsNormSq_mul_le _ _

/-- `‖Tr_U |x⟩⟨y|‖₂² ≤ ‖x‖²‖y‖²`. -/
theorem hsNormSq_ptraceU_rankOne_le (x y : EuclideanSpace ℂ (U × V)) :
    hsNormSq (ptraceU (rankOne x y)) ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [ptraceU_rankOne, hsNormSq_map_conj, ← hsNormSq_matOf x, ← hsNormSq_matOf y,
    ← hsNormSq_conjTranspose (matOf x)]
  exact hsNormSq_mul_le _ _

end RankOne

/-! ## The bound along a range factorization -/

section Factorization

variable {U V : Type*} [Fintype U] [Fintype V] {s : ℕ}

/-- The common core of the two one-sided bounds: if each summand of a finite
family of matrices has `‖·‖₂ ≤ cᵢ`, the sum has `‖·‖₂² ≤ s ∑ᵢ cᵢ²`.

The bounding data is a family of nonnegative reals, not of vectors: the callers
supply `cᵢ = ‖dᵢ‖`, but nothing here looks at the `dᵢ` themselves. -/
private theorem hsNormSq_sum_le {m n : Type*} [Fintype m] [Fintype n] {s : ℕ}
    (A : Fin s → Matrix m n ℂ) (c : Fin s → ℝ) (hc : ∀ i, 0 ≤ c i)
    (h : ∀ i, hsNormSq (A i) ≤ c i ^ 2) :
    hsNormSq (∑ i, A i) ≤ s * ∑ i, c i ^ 2 := by
  have hstep : ∀ i, ‖vec (A i)‖ ≤ c i := by
    intro i
    have h1 : ‖vec (A i)‖ ^ 2 ≤ c i ^ 2 := by
      rw [← hsNormSq_eq_norm_sq]; exact h i
    nlinarith [norm_nonneg (vec (A i)), hc i]
  have htri : ‖vec (∑ i, A i)‖ ≤ ∑ i, c i := by
    rw [vec_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hstep i)
  have hsq : (∑ i, c i) ^ 2 ≤ (s : ℝ) * ∑ i, c i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin s))) (f := c)
  have h3 : (0 : ℝ) ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  rw [hsNormSq_eq_norm_sq]
  nlinarith [norm_nonneg (vec (∑ i, A i))]

/-- `‖Tr_V C‖₂² ≤ s ‖C‖₂²` along a range factorization with orthonormal `eᵢ`. -/
theorem hsNormSq_ptraceV_rankFactor_le (e d : Fin s → EuclideanSpace ℂ (U × V))
    (he : Orthonormal ℂ e) :
    hsNormSq (ptraceV (rankFactor e d)) ≤ s * hsNormSq (rankFactor e d) := by
  rw [hsNormSq_rankFactor_eq e d he, rankFactor_eq_sum, ptraceV_sum]
  refine hsNormSq_sum_le _ (fun i => ‖d i‖) (fun i => norm_nonneg _) fun i => ?_
  have h := hsNormSq_ptraceV_rankOne_le (e i) (d i)
  rwa [he.1 i, one_pow, one_mul] at h

/-- `‖Tr_U C‖₂² ≤ s ‖C‖₂²` along a range factorization with orthonormal `eᵢ`. -/
theorem hsNormSq_ptraceU_rankFactor_le (e d : Fin s → EuclideanSpace ℂ (U × V))
    (he : Orthonormal ℂ e) :
    hsNormSq (ptraceU (rankFactor e d)) ≤ s * hsNormSq (rankFactor e d) := by
  rw [hsNormSq_rankFactor_eq e d he, rankFactor_eq_sum, ptraceU_sum]
  refine hsNormSq_sum_le _ (fun i => ‖d i‖) (fun i => norm_nonneg _) fun i => ?_
  have h := hsNormSq_ptraceU_rankOne_le (e i) (d i)
  rwa [he.1 i, one_pow, one_mul] at h

end Factorization

/-! ## `lem:one-sided-partial-trace` -/

section Statement

variable {U V : Type*} [Fintype U] [Fintype V]

/-- **`lem:one-sided-partial-trace`, the `V` side.**  For `C` of rank at most `r`,
`‖Tr_V C‖₂² ≤ r‖C‖₂²`.  Unconditional. -/
theorem hsNormSq_ptraceV_le (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceV C) ≤ r * hsNormSq C := by
  obtain ⟨e, d, he, hfac⟩ := exists_rankFactor_rank C
  have h := hsNormSq_ptraceV_rankFactor_le e d he
  rw [← hfac] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonneg C))
  exact_mod_cast hrank

/-- **`lem:one-sided-partial-trace`, the `U` side.** -/
theorem hsNormSq_ptraceU_le (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) ≤ r * hsNormSq C := by
  obtain ⟨e, d, he, hfac⟩ := exists_rankFactor_rank C
  have h := hsNormSq_ptraceU_rankFactor_le e d he
  rw [← hfac] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (hsNormSq_nonneg C))
  exact_mod_cast hrank

end Statement

end RankR
