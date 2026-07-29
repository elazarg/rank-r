/-
Exact-rank singular-value factorizations of finite complex matrices.

The right vectors are the first `rank C` eigenvectors of `CᴴC`.  Their
singular values are positive, so normalizing their images gives an
orthonormal left family.
-/
import RankR.Library.Matrix.Rank
import RankR.Library.Matrix.Action
import Mathlib.Analysis.InnerProductSpace.SingularValues

namespace RankR

open Matrix Finset ComplexConjugate

section SingularVectors

variable {W : Type*} [Fintype W]

noncomputable local instance : DecidableEq W := Classical.decEq W

/-- The positive singular values of a matrix, indexed by its exact rank. -/
noncomputable def matrixSingularValue
    (C : Matrix W W ℂ) (i : Fin C.rank) : ℝ :=
  (Matrix.toEuclideanLin C).singularValues i

/-- The right singular vector belonging to a positive singular value. -/
noncomputable def rightSingularVector
    (C : Matrix W W ℂ) (i : Fin C.rank) : EuclideanSpace ℂ W :=
  (Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
    finrank_euclideanSpace (Fin.castLE (Matrix.rank_le_card_width C) i)

/-- Every singular value indexed below the rank is positive. -/
theorem matrixSingularValue_pos
    (C : Matrix W W ℂ) (i : Fin C.rank) :
    0 < matrixSingularValue C i := by
  rw [matrixSingularValue,
    (Matrix.toEuclideanLin C).singularValues_pos_iff_lt_finrank_range,
    finrank_range_toEuclideanLin]
  exact i.isLt

/-- The exact-rank family of right singular vectors is orthonormal. -/
theorem orthonormal_rightSingularVector (C : Matrix W W ℂ) :
    Orthonormal ℂ (rightSingularVector C) := by
  exact
    (Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
        finrank_euclideanSpace
      |>.orthonormal.comp
        (Fin.castLE (Matrix.rank_le_card_width C))
        (Fin.castLE_injective (Matrix.rank_le_card_width C))

/-- The squared norm of a matrix on a right singular eigenvector is the
corresponding eigenvalue of `CᴴC`. -/
theorem norm_sq_mulVecE_singularEigenvector
    (C : Matrix W W ℂ) (i : Fin (Fintype.card W)) :
    ‖mulVecE C
        ((Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
          finrank_euclideanSpace i)‖ ^ 2 =
      (Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvalues
        finrank_euclideanSpace i := by
  let T := Matrix.toEuclideanLin C
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  change ‖T (b i)‖ ^ 2 = hS.eigenvalues finrank_euclideanSpace i
  calc
    ‖T (b i)‖ ^ 2 =
        Complex.re (inner ℂ (b i) ((T.adjoint ∘ₗ T) (b i))) := by
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (T (b i))).symm
    _ = Complex.re
        (inner ℂ (b i)
          ((hS.eigenvalues finrank_euclideanSpace i : ℂ) • b i)) := by
      exact congrArg (fun y => Complex.re (inner ℂ (b i) y))
        (hS.apply_eigenvectorBasis finrank_euclideanSpace i)
    _ = hS.eigenvalues finrank_euclideanSpace i := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, b.norm_eq_one]
      simp

/-- Images of distinct right singular vectors are orthogonal, with squared
norm equal to the squared singular value. -/
theorem inner_mulVecE_rightSingularVector
    (C : Matrix W W ℂ) (i j : Fin C.rank) :
    inner ℂ
        (mulVecE C (rightSingularVector C i))
        (mulVecE C (rightSingularVector C j))
      = if i = j then (matrixSingularValue C i : ℂ) ^ 2 else 0 := by
  let T := Matrix.toEuclideanLin C
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  let fi (k : Fin C.rank) :=
    Fin.castLE (Matrix.rank_le_card_width C) k
  have hright (k : Fin C.rank) :
      rightSingularVector C k = b (fi k) := rfl
  rw [hright, hright]
  change inner ℂ (T (b (fi i))) (T (b (fi j))) = _
  rw [← LinearMap.adjoint_inner_right]
  change inner ℂ (b (fi i)) ((T.adjoint ∘ₗ T) (b (fi j))) = _
  rw [hS.apply_eigenvectorBasis finrank_euclideanSpace, inner_smul_right,
    ← T.sq_singularValues_fin finrank_euclideanSpace]
  have hb := b.orthonormal
  by_cases hij : i = j
  · subst j
    have hbi :
        inner ℂ (b (fi i))
            (hS.eigenvectorBasis finrank_euclideanSpace (fi i)) = 1 := by
      change inner ℂ (b (fi i)) (b (fi i)) = 1
      rw [inner_self_eq_norm_sq_to_K, hb.1]
      norm_num
    rw [hbi, mul_one]
    simp [matrixSingularValue, fi, map_pow]
    rfl
  · have hfij : fi i ≠ fi j :=
      fun h => hij (Fin.castLE_injective (Matrix.rank_le_card_width C) h)
    rw [hb.2 hfij, mul_zero, if_neg hij]

/-- The normalized left singular vector. -/
noncomputable def leftSingularVector
    (C : Matrix W W ℂ) (i : Fin C.rank) : EuclideanSpace ℂ W :=
  ((matrixSingularValue C i : ℂ)⁻¹) •
    mulVecE C (rightSingularVector C i)

/-- The exact-rank family of left singular vectors is orthonormal. -/
theorem orthonormal_leftSingularVector (C : Matrix W W ℂ) :
    Orthonormal ℂ (leftSingularVector C) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [leftSingularVector, leftSingularVector,
    inner_smul_left, inner_smul_right,
    inner_mulVecE_rightSingularVector]
  by_cases hij : i = j
  · subst j
    have hσ : (matrixSingularValue C i : ℂ) ≠ 0 := by
      exact_mod_cast (matrixSingularValue_pos C i).ne'
    simp only [if_true, map_inv₀, Complex.conj_ofReal]
    field_simp
  · simp [hij]

/-- The unnormalized left family in the singular expansion. -/
noncomputable def singularImageVector
    (C : Matrix W W ℂ) (i : Fin C.rank) : EuclideanSpace ℂ W :=
  mulVecE C (rightSingularVector C i)

/-- Singular eigenvectors beyond the rank lie in the kernel. -/
theorem mulVecE_singularEigenvector_eq_zero
    (C : Matrix W W ℂ) (i : Fin (Fintype.card W))
    (hi : C.rank ≤ i) :
    mulVecE C
        ((Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
          finrank_euclideanSpace i) = 0 := by
  have hσ :
      (Matrix.toEuclideanLin C).singularValues i = 0 := by
    rw [(Matrix.toEuclideanLin C).singularValues_eq_zero_iff_le_finrank_range,
      finrank_range_toEuclideanLin]
    exact hi
  have hnorm :
      ‖mulVecE C
          ((Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
            finrank_euclideanSpace i)‖ ^ 2 = 0 := by
    rw [norm_sq_mulVecE_singularEigenvector,
      ← (Matrix.toEuclideanLin C).sq_singularValues_fin
        finrank_euclideanSpace, hσ]
    norm_num
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg
    (mulVecE C
      ((Matrix.toEuclideanLin C).isSymmetric_adjoint_comp_self.eigenvectorBasis
        finrank_euclideanSpace i))]

/-- The singular expansion restricted to the positive singular spectrum. -/
theorem rankFactor_singularImageVector (C : Matrix W W ℂ) :
    C = rankFactor (singularImageVector C) (rightSingularVector C) := by
  let T := Matrix.toEuclideanLin C
  let hS := T.isSymmetric_adjoint_comp_self
  let b := hS.eigenvectorBasis finrank_euclideanSpace
  have hdim : C.rank ≤ Fintype.card W := Matrix.rank_le_card_width C
  ext p q
  let x : EuclideanSpace ℂ W := EuclideanSpace.single q 1
  have hfull :
      T x = ∑ i : Fin (Fintype.card W), inner ℂ (b i) x • T (b i) := by
    calc
      T x = T (∑ i, inner ℂ (b i) x • b i) :=
        congrArg T (b.sum_repr' x).symm
      _ = _ := by simp
  have hrestrict :
      (∑ i : Fin (Fintype.card W), inner ℂ (b i) x • T (b i)) =
        ∑ i : Fin C.rank,
          inner ℂ (b (Fin.castLE hdim i)) x •
            T (b (Fin.castLE hdim i)) := by
    rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
    symm
    calc
      (∑ i ∈ Finset.range C.rank,
          if hi : i < C.rank then
            inner ℂ (b (Fin.castLE hdim ⟨i, hi⟩)) x •
              T (b (Fin.castLE hdim ⟨i, hi⟩))
          else 0) =
          ∑ i ∈ Finset.range C.rank,
            if hi : i < Fintype.card W then
              inner ℂ (b ⟨i, hi⟩) x • T (b ⟨i, hi⟩)
            else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have hiq := Finset.mem_range.mp hi
              have hiW := hiq.trans_le hdim
              rw [dif_pos hiq, dif_pos hiW]
              have hfin :
                  Fin.castLE hdim ⟨i, hiq⟩ = (⟨i, hiW⟩ : Fin (Fintype.card W)) :=
                Fin.ext rfl
              rw [hfin]
      _ = ∑ i ∈ Finset.range (Fintype.card W),
            if hi : i < Fintype.card W then
              inner ℂ (b ⟨i, hi⟩) x • T (b ⟨i, hi⟩)
            else 0 := by
              apply Finset.sum_subset (Finset.range_mono hdim)
              intro i hiW hiq
              have hirank : C.rank ≤ i := by
                simpa [Finset.mem_range] using hiq
              rw [dif_pos (Finset.mem_range.mp hiW)]
              have hz := mulVecE_singularEigenvector_eq_zero C
                ⟨i, Finset.mem_range.mp hiW⟩ hirank
              change T (b ⟨i, Finset.mem_range.mp hiW⟩) = 0 at hz
              rw [hz, smul_zero]
  rw [hrestrict] at hfull
  change mulVecE C x =
    ∑ i : Fin C.rank,
      inner ℂ (b (Fin.castLE hdim i)) x •
        mulVecE C (b (Fin.castLE hdim i)) at hfull
  have hp := congrArg (fun z : EuclideanSpace ℂ W => z p) hfull
  have hleft : (mulVecE C x) p = C p q := by
    simp [mulVecE_apply, x, PiLp.single_apply]
  rw [hleft] at hp
  rw [rankFactor_apply]
  simpa only [b, x, singularImageVector, rightSingularVector,
    EuclideanSpace.inner_single_right, one_mul, WithLp.ofLp_sum,
    Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    mul_comm] using hp

/-- Square-root scaling of the normalized left singular vectors. -/
noncomputable def balancedSingularLeft
    (C : Matrix W W ℂ) (i : Fin C.rank) : EuclideanSpace ℂ W :=
  ((Real.sqrt (matrixSingularValue C i) : ℝ) : ℂ) •
    leftSingularVector C i

/-- Square-root scaling of the right singular vectors. -/
noncomputable def balancedSingularRight
    (C : Matrix W W ℂ) (i : Fin C.rank) : EuclideanSpace ℂ W :=
  ((Real.sqrt (matrixSingularValue C i) : ℝ) : ℂ) •
    rightSingularVector C i

/-- The left balanced singular family has diagonal Gram matrix given by the
positive singular values. -/
theorem inner_balancedSingularLeft
    (C : Matrix W W ℂ) (i j : Fin C.rank) :
    inner ℂ (balancedSingularLeft C i) (balancedSingularLeft C j) =
      if i = j then (matrixSingularValue C i : ℂ) else 0 := by
  rw [balancedSingularLeft, balancedSingularLeft,
    inner_smul_left, inner_smul_right]
  have horth := orthonormal_leftSingularVector C
  rw [orthonormal_iff_ite.mp horth i j]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Complex.conj_ofReal]
    norm_cast
    nlinarith [Real.sq_sqrt (le_of_lt (matrixSingularValue_pos C i))]
  · simp [hij]

/-- The right balanced singular family has the same diagonal Gram matrix. -/
theorem inner_balancedSingularRight
    (C : Matrix W W ℂ) (i j : Fin C.rank) :
    inner ℂ (balancedSingularRight C i) (balancedSingularRight C j) =
      if i = j then (matrixSingularValue C i : ℂ) else 0 := by
  rw [balancedSingularRight, balancedSingularRight,
    inner_smul_left, inner_smul_right]
  have horth := orthonormal_rightSingularVector C
  rw [orthonormal_iff_ite.mp horth i j]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Complex.conj_ofReal]
    norm_cast
    nlinarith [Real.sq_sqrt (le_of_lt (matrixSingularValue_pos C i))]
  · simp [hij]

/-- Square-root rescaling preserves each summand of the singular
factorization. -/
theorem rankOne_balancedSingular
    (C : Matrix W W ℂ) (i : Fin C.rank) :
    rankOne (balancedSingularLeft C i) (balancedSingularRight C i) =
      rankOne (singularImageVector C i) (rightSingularVector C i) := by
  have hσR : matrixSingularValue C i ≠ 0 :=
    (matrixSingularValue_pos C i).ne'
  have hσC : (matrixSingularValue C i : ℂ) ≠ 0 := by
    exact_mod_cast hσR
  have hsqrtSq :
      ((Real.sqrt (matrixSingularValue C i) : ℝ) : ℂ) *
          ((Real.sqrt (matrixSingularValue C i) : ℝ) : ℂ) =
        (matrixSingularValue C i : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (le_of_lt (matrixSingularValue_pos C i))
  ext p r
  simp only [balancedSingularLeft, balancedSingularRight,
    leftSingularVector, singularImageVector, rankOne,
    Matrix.of_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.conj_ofReal]
  ring_nf
  have hsqrtPow :
      ((Real.sqrt (matrixSingularValue C i) : ℝ) : ℂ) ^ 2 =
        (matrixSingularValue C i : ℂ) := by
    simpa only [pow_two] using hsqrtSq
  rw [hsqrtPow, mul_inv_cancel₀ hσC, one_mul]

/-- Every matrix has an exact-rank equal-Gram factorization whose Gram
eigenvalues are its positive singular values. -/
theorem rankFactor_balancedSingular (C : Matrix W W ℂ) :
    C = rankFactor (balancedSingularLeft C) (balancedSingularRight C) := by
  calc
    C = rankFactor (singularImageVector C) (rightSingularVector C) :=
      rankFactor_singularImageVector C
    _ = rankFactor (balancedSingularLeft C) (balancedSingularRight C) := by
      rw [rankFactor_eq_sum, rankFactor_eq_sum]
      exact Finset.sum_congr rfl fun i _ =>
        (rankOne_balancedSingular C i).symm

end SingularVectors

end RankR
