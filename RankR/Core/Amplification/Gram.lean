/-
Gram-operator form of the balanced-polarization lift.

For a linear map `L` out of Hilbert--Schmidt matrix space, `linearGramOperator
L` is the coordinate matrix of `L* L` after vectorization.  This file relates
the four-linear crossing identity to its index reshuffling symmetry and
rewrites the rank-one input and rank-`r` conclusion as block positivity.
-/
import RankR.Core.Amplification.Balanced
import RankR.Library.Quantum.BlockPositive
import RankR.Library.Quantum.MaximallyEntangled
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

section Coordinates

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable local instance gramDecidableEqW :
    DecidableEq W := Classical.decEq W

/-- The Gram matrix of `L` in the vectorized matrix-unit basis. -/
noncomputable def linearGramOperator
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    Matrix (W × W) (W × W) ℂ :=
  fun p q =>
    inner ℂ
      (L (Matrix.single p.1 p.2 1))
      (L (Matrix.single q.1 q.2 1))

omit [Fintype W] in
/-- A Gram operator is Hermitian. -/
theorem linearGramOperator_isHermitian
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    (linearGramOperator L).IsHermitian := by
  ext p q
  simp [linearGramOperator,
    Matrix.conjTranspose_apply, inner_conj_symm]

/-- Inner products of two images expand against the coordinate Gram
operator. -/
theorem inner_map_eq_sum_linearGramOperator
    (L : Matrix W W ℂ →ₗ[ℂ] E) (A B : Matrix W W ℂ) :
    inner ℂ (L A) (L B) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        conj (A i j) * B k l *
          linearGramOperator L (i, j) (k, l) := by
  have hA :
      A = ∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ) := by
    simpa [Matrix.smul_single, smul_eq_mul] using matrix_eq_sum_single A
  have hB :
      B = ∑ k, ∑ l, B k l • Matrix.single k l (1 : ℂ) := by
    simpa [Matrix.smul_single, smul_eq_mul] using matrix_eq_sum_single B
  calc
    inner ℂ (L A) (L B) =
        inner ℂ
          (L (∑ i, ∑ j, A i j • Matrix.single i j (1 : ℂ)))
          (L (∑ k, ∑ l, B k l • Matrix.single k l (1 : ℂ))) :=
      congrArg₂ (inner ℂ) (congrArg L hA) (congrArg L hB)
    _ = _ := by
      simp_rw [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
        inner_smul_right]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simp [linearGramOperator, mul_assoc, mul_comm, mul_left_comm]

/-- The Gram operator has quadratic form `‖L C‖²`. -/
theorem qform_linearGramOperator
    (L : Matrix W W ℂ →ₗ[ℂ] E) (C : Matrix W W ℂ) :
    qform (linearGramOperator L) (vec C) =
      ((‖L C‖ ^ 2 : ℝ) : ℂ) := by
  have hnorm :
      ((‖L C‖ ^ 2 : ℝ) : ℂ) = inner ℂ (L C) (L C) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm, inner_map_eq_sum_linearGramOperator]
  simp only [qform, Fintype.sum_prod_type, vec_apply]
  simp only [mul_comm, mul_left_comm]

/-- A Gram operator is positive semidefinite. -/
theorem linearGramOperator_posSemidef
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    (linearGramOperator L).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (linearGramOperator_isHermitian L) ?_
  intro x
  have hq :
      star x ⬝ᵥ (linearGramOperator L *ᵥ x) =
        qform (linearGramOperator L) (WithLp.toLp 2 x) := by
    simp [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hq, show WithLp.toLp 2 x = vec (unvec (WithLp.toLp 2 x)) by simp,
    qform_linearGramOperator]
  apply Complex.nonneg_iff.mpr
  constructor
  · exact sq_nonneg _
  · norm_num [pow_two, Complex.mul_im]

/-- The reshuffling symmetry `Γ_{ij,kl} = Γ_{lj,ki}`. -/
def IsCrossingFixed
    (Γ : Matrix (W × W) (W × W) ℂ) : Prop :=
  ∀ i j k l : W, Γ (i, j) (k, l) = Γ (l, j) (k, i)

omit [Fintype W] in
private theorem rankOne_eBasis_eq_single (i j : W) :
    rankOne (eBasis i) (eBasis j) = Matrix.single i j (1 : ℂ) := by
  ext p q
  by_cases hip : i = p <;> by_cases hjq : j = q
  · subst p
    subst q
    simp [rankOne, eBasis_apply]
  · have hqj : q ≠ j := Ne.symm hjq
    simp [rankOne, eBasis_apply, hip, hjq, hqj]
  · have hpi : p ≠ i := Ne.symm hip
    simp [rankOne, eBasis_apply, hip, hpi, hjq]
  · have hpi : p ≠ i := Ne.symm hip
    have hqj : q ≠ j := Ne.symm hjq
    simp [rankOne, eBasis_apply, hip, hjq, hqj]

omit [Fintype W] in
/-- Crossed polarization implies reshuffling symmetry of the Gram operator. -/
theorem isCrossingFixed_linearGramOperator
    {L : Matrix W W ℂ →ₗ[ℂ] E}
    (hCross : HasCrossedPolarization L) :
    IsCrossingFixed (linearGramOperator L) := by
  intro i j k l
  have h := hCross
    (eBasis i) (eBasis j) (eBasis k) (eBasis l)
  simpa [linearGramOperator, rankOne_eBasis_eq_single] using h

/-- Exchange the first and fourth binders of a four-fold finite sum. -/
private theorem sum4_swap_outer
    {A B C D M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid M]
    (F : A → B → C → D → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d) =
      ∑ d, ∑ b, ∑ c, ∑ a, F a b c d := by
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d := by
      refine Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ a, ∑ c, F a b c d := by
      exact Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, ∑ a, F a b c d := by
      refine Finset.sum_congr rfl fun d _ =>
        Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Reshuffling symmetry of the Gram operator implies crossed
polarization. -/
theorem hasCrossedPolarization_of_isCrossingFixed
    {L : Matrix W W ℂ →ₗ[ℂ] E}
    (hΓ : IsCrossingFixed (linearGramOperator L)) :
    HasCrossedPolarization L := by
  intro u v s t
  rw [inner_map_eq_sum_linearGramOperator,
    inner_map_eq_sum_linearGramOperator]
  conv_rhs => rw [sum4_swap_outer]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [hΓ i j k l]
  simp only [rankOne, Matrix.of_apply, map_mul, Complex.conj_conj]
  ring

/-- Crossed polarization is equivalent to reshuffling symmetry of `L* L`. -/
theorem hasCrossedPolarization_iff_isCrossingFixed
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    HasCrossedPolarization L ↔
      IsCrossingFixed (linearGramOperator L) :=
  ⟨isCrossingFixed_linearGramOperator,
    hasCrossedPolarization_of_isCrossingFixed⟩

end Coordinates

section Adjoint

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable local instance gramAdjointDecidableEqW :
    DecidableEq W := Classical.decEq W

omit [Fintype W] in
private theorem unvec_eBasis_eq_single (p : W × W) :
    unvec (eBasis p) = Matrix.single p.1 p.2 (1 : ℂ) := by
  rcases p with ⟨a, b⟩
  ext i j
  simp [unvec, Matrix.single, Prod.ext_iff, eq_comm]

/-- `L` transported to the vectorized Hilbert--Schmidt space. -/
noncomputable def vectorizedLinearMap
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    EuclideanSpace ℂ (W × W) →ₗ[ℂ] E :=
  L.comp vecLinearEquiv.symm.toLinearMap

omit [Fintype W] [FiniteDimensional ℂ E] in
@[simp]
theorem vectorizedLinearMap_apply
    (L : Matrix W W ℂ →ₗ[ℂ] E)
    (z : EuclideanSpace ℂ (W × W)) :
    vectorizedLinearMap L z = L (unvec z) :=
  rfl

/-- The literal Gram map `L* L` on vectorized Hilbert--Schmidt space. -/
noncomputable def linearGramMap
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    EuclideanSpace ℂ (W × W) →ₗ[ℂ]
      EuclideanSpace ℂ (W × W) :=
  (vectorizedLinearMap L).adjoint.comp (vectorizedLinearMap L)

/-- The coordinate Gram operator and the literal adjoint composite have the
same quadratic form. -/
theorem qform_linearGramOperator_eq_inner_linearGramMap
    (L : Matrix W W ℂ →ₗ[ℂ] E)
    (z : EuclideanSpace ℂ (W × W)) :
    qform (linearGramOperator L) z =
      inner ℂ z (linearGramMap L z) := by
  rw [show z = vec (unvec z) by simp]
  rw [qform_linearGramOperator, linearGramMap, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right]
  change
    ((‖L (unvec z)‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ (L (unvec z)) (L (unvec z))
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The coordinate matrix acts exactly as the literal adjoint composite. -/
theorem mulVecE_linearGramOperator_eq_linearGramMap
    (L : Matrix W W ℂ →ₗ[ℂ] E)
    (z : EuclideanSpace ℂ (W × W)) :
    mulVecE (linearGramOperator L) z = linearGramMap L z := by
  classical
  ext p
  have hz :
      unvec z =
        ∑ i, ∑ j, z (i, j) • Matrix.single i j (1 : ℂ) := by
    simpa [unvec, Matrix.smul_single, smul_eq_mul] using
      matrix_eq_sum_single (unvec z)
  calc
    mulVecE (linearGramOperator L) z p =
        ∑ q : W × W,
          linearGramOperator L p q * z q := by
      rw [mulVecE_apply]
    _ = inner ℂ
        (L (Matrix.single p.1 p.2 1)) (L (unvec z)) := by
      rw [hz, map_sum]
      simp_rw [map_sum, map_smul, inner_sum, inner_smul_right]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by
          simp [linearGramOperator, mul_comm]
    _ = inner ℂ (eBasis p) (linearGramMap L z) := by
      rw [linearGramMap, LinearMap.comp_apply,
        LinearMap.adjoint_inner_right]
      simp only [vectorizedLinearMap_apply,
        unvec_eBasis_eq_single]
    _ = linearGramMap L z p := by
      rw [PiLp.inner_apply]
      simp [eBasis_apply]

end Adjoint

section BlockPositivity

variable {W E : Type*} [Fintype W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable local instance gramBlockDecidableEqW :
    DecidableEq W := Classical.decEq W

/-- The operator
`r I + (1/r)|Ω⟩⟨Ω| - Γ`, where `Γ` is the Gram operator of `L`. -/
noncomputable def balancedGramDefect
    (L : Matrix W W ℂ →ₗ[ℂ] E) (r : ℕ) :
    Matrix (W × W) (W × W) ℂ :=
  (r : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)
    + ((1 / (r : ℝ) : ℝ) : ℂ) • singleOmegaChoi
    - linearGramOperator L

/-- Quadratic-form rendering of the balanced Gram defect. -/
theorem re_qform_balancedGramDefect
    (L : Matrix W W ℂ →ₗ[ℂ] E) (r : ℕ)
    (C : Matrix W W ℂ) :
    (qform (balancedGramDefect L r) (vec C)).re =
      (r : ℝ) * hsNormSq C
        + (1 / (r : ℝ)) * Complex.normSq C.trace
        - ‖L C‖ ^ 2 := by
  rw [balancedGramDefect, qform_sub, qform_add, qform_smul, qform_smul,
    qform_one, singleOmegaChoi, qform_rankOne, inner_singleOmegaVec,
    qform_linearGramOperator, hsNormSq_eq_norm_sq]
  simp only [pow_two]
  push_cast
  norm_num [Complex.mul_re]

/-- Block positivity of the Gram defect is exactly the corresponding
rank-constrained norm inequality. -/
theorem isBlockPositive_balancedGramDefect_iff
    (L : Matrix W W ℂ →ₗ[ℂ] E) (r : ℕ) :
    IsBlockPositive r (balancedGramDefect L r) ↔
      ∀ C : Matrix W W ℂ, C.rank ≤ r →
        ‖L C‖ ^ 2 ≤
          (r : ℝ) * hsNormSq C
            + (1 / (r : ℝ)) * Complex.normSq C.trace := by
  constructor
  · intro h C hrank
    have hq := h C hrank
    rw [re_qform_balancedGramDefect] at hq
    linarith
  · intro h C hrank
    rw [re_qform_balancedGramDefect]
    have hC := h C hrank
    linarith

/-- The rank-one hypothesis is precisely block positivity of
`I + |Ω⟩⟨Ω| - Γ`. -/
theorem hasRankOneTraceBound_iff_isBlockPositive_one
    (L : Matrix W W ℂ →ₗ[ℂ] E) :
    HasRankOneTraceBound L ↔
      IsBlockPositive 1 (balancedGramDefect L 1) := by
  rw [isBlockPositive_balancedGramDefect_iff]
  constructor
  · intro hOne C hrank
    obtain ⟨u, v, hC⟩ :=
      (rank_le_iff_exists_sum_rankOne (k := 1) C).mp hrank
    rw [Fin.sum_univ_one] at hC
    rw [hC, hsNormSq_rankOne, trace_rankOne]
    have h := hOne (u 0) (v 0)
    norm_num
    exact h
  · intro h x y
    have hrank : (rankOne x y).rank ≤ 1 := by
      apply (rank_le_iff_exists_sum_rankOne (k := 1) (rankOne x y)).mpr
      refine ⟨![x], ![y], ?_⟩
      rw [Fin.sum_univ_one]
      simp
    have hxy := h (rankOne x y) hrank
    rw [hsNormSq_rankOne, trace_rankOne] at hxy
    norm_num at hxy
    exact hxy

/-- The balanced-polarization theorem in Gram-operator language. -/
theorem balancedGramDefect_isBlockPositive
    {L : Matrix W W ℂ →ₗ[ℂ] E}
    (hOne : HasRankOneTraceBound L)
    (hCross : HasCrossedPolarization L)
    (r : ℕ) :
    IsBlockPositive r (balancedGramDefect L r) := by
  rw [isBlockPositive_balancedGramDefect_iff]
  intro C hrank
  exact balancedPolarization C hOne hCross r hrank

end BlockPositivity

end RankR
