/-
The Kraus space of a finite Kraus family.

The columns of the synthesis matrix are the vectorized Kraus operators.  Its
frame operator is the Choi operator, so the range of the Choi operator is
exactly the vectorized span of the Kraus family.
-/
import RankR.Library.Quantum.Choi
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace RankR

open Matrix Finset

section KrausSpace

variable {W ι : Type*} [Fintype W] [Fintype ι]

noncomputable local instance krausSpaceDecidableEqW :
    DecidableEq W := Classical.decEq W
noncomputable local instance krausSpaceDecidableEqι :
    DecidableEq ι := Classical.decEq ι

/-- The span of a finite Kraus family. -/
def krausSpace (A : ι → Matrix W W ℂ) : Submodule ℂ (Matrix W W ℂ) :=
  Submodule.span ℂ (Set.range A)

/-- The matrix whose columns are the vectorized members of a Kraus family. -/
noncomputable def krausSynthesisMatrix
    (A : ι → Matrix W W ℂ) : Matrix (W × W) ι ℂ :=
  fun x a => vec (A a) x

omit [Fintype W] [Fintype ι] in
@[simp]
theorem krausSynthesisMatrix_apply
    (A : ι → Matrix W W ℂ) (x : W × W) (a : ι) :
    krausSynthesisMatrix A x a = vec (A a) x :=
  rfl

omit [Fintype W] in
/-- The Choi operator is the frame operator of the vectorized Kraus family. -/
theorem choiOf_eq_synthesis_mul_conjTranspose
    (A : ι → Matrix W W ℂ) :
    choiOf A = krausSynthesisMatrix A * (krausSynthesisMatrix A)ᴴ := by
  ext x y
  rw [choiOf, Matrix.sum_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => by
    simp [krausSynthesisMatrix, rankOne]

omit [Fintype W] in
/-- The range of the synthesis matrix is the span of the vectorized Kraus
family. -/
theorem range_krausSynthesisMatrix
    (A : ι → Matrix W W ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (krausSynthesisMatrix A)) =
      Submodule.span ℂ (Set.range fun a => vec (A a)) := by
  apply le_antisymm
  · rintro y ⟨c, rfl⟩
    have haction :
        Matrix.toEuclideanLin (krausSynthesisMatrix A) c =
          ∑ a, c a • vec (A a) := by
      rw [Matrix.toLpLin_apply]
      ext x
      rw [sum_apply_euclidean]
      change (∑ a, A a x.1 x.2 * c a) =
        (∑ a, c a * A a x.1 x.2)
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    rw [haction]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))
  · rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    refine ⟨EuclideanSpace.single a 1, ?_⟩
    ext x
    simp [Matrix.toLpLin_apply, krausSynthesisMatrix]

/-- Vectorizing the Kraus space gives exactly the range of the Choi
operator. -/
theorem range_choiOf
    (A : ι → Matrix W W ℂ) :
    LinearMap.range (Matrix.toEuclideanLin (choiOf A)) =
      Submodule.span ℂ (Set.range fun a => vec (A a)) := by
  let S := Matrix.toEuclideanLin (krausSynthesisMatrix A)
  have hframe :
      Matrix.toEuclideanLin
          (krausSynthesisMatrix A * (krausSynthesisMatrix A)ᴴ) =
        S ∘ₗ S.adjoint := by
    have hmul :
        Matrix.toEuclideanLin
            (krausSynthesisMatrix A * (krausSynthesisMatrix A)ᴴ) =
          (Matrix.toEuclideanLin (krausSynthesisMatrix A)).comp
            (Matrix.toEuclideanLin (krausSynthesisMatrix A)ᴴ) := by
      simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
        Matrix.toLin_mul
          (EuclideanSpace.basisFun (W × W) ℂ).toBasis
          (EuclideanSpace.basisFun ι ℂ).toBasis
          (EuclideanSpace.basisFun (W × W) ℂ).toBasis
          (krausSynthesisMatrix A) (krausSynthesisMatrix A)ᴴ
    rw [hmul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [choiOf_eq_synthesis_mul_conjTranspose, hframe,
    LinearMap.range_self_comp_adjoint, range_krausSynthesisMatrix]

/-- Vectorization maps the Kraus space onto the range of the Choi operator. -/
theorem map_krausSpace_vec
    (A : ι → Matrix W W ℂ) :
    (krausSpace A).map vecLinearEquiv.toLinearMap =
      LinearMap.range (Matrix.toEuclideanLin (choiOf A)) := by
  rw [krausSpace, Submodule.map_span, range_choiOf]
  congr 1
  ext z
  simp [vecLinearEquiv]

/-- Kraus families with the same Choi operator span the same Kraus space. -/
theorem krausSpace_eq_of_choiOf_eq
    {κ : Type*} [Fintype κ]
    (A : ι → Matrix W W ℂ) (B : κ → Matrix W W ℂ)
    (h : choiOf A = choiOf B) :
    krausSpace A = krausSpace B := by
  apply Submodule.map_injective_of_injective vecLinearEquiv.injective
  rw [map_krausSpace_vec, map_krausSpace_vec, h]

end KrausSpace

end RankR
