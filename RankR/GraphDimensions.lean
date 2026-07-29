/-
Finite-dimensional bookkeeping for the graph coefficient spaces.

The coordinate graph operator space is linearly equivalent to the functions
on its allowed matrix support.  The two-layer space is linearly equivalent to
two copies of the graph operator space.  These equivalences turn the
coefficient counts in the rook-graph application into cardinality statements.
-/
import RankR.GraphLayers

namespace RankR

open Finset Matrix
open scoped Kronecker

section GraphSupport

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The diagonal and both orientations of every edge in `E`. -/
def graphMatrixSupport (E : Finset (U × U)) : Finset (U × U) :=
  Finset.univ.filter fun p =>
    p.1 = p.2 ∨ p ∈ E ∨ (p.2, p.1) ∈ E

omit [LinearOrder U] in
@[simp] theorem mem_graphMatrixSupport
    {E : Finset (U × U)} {p : U × U} :
    p ∈ graphMatrixSupport E
      ↔ p.1 = p.2 ∨ p ∈ E ∨ (p.2, p.1) ∈ E := by
  simp [graphMatrixSupport]

/-- A graph-supported matrix is exactly a freely chosen function on the
allowed matrix positions. -/
noncomputable def graphOperatorSpaceEquiv
    (E : Finset (U × U)) :
    graphOperatorSpace E ≃ₗ[ℂ] (graphMatrixSupport E → ℂ) where
  toFun X p := X.1 p.1.1 p.1.2
  invFun f :=
    ⟨fun i j =>
        if h : (i, j) ∈ graphMatrixSupport E
        then f ⟨(i, j), h⟩
        else 0,
      by
        intro i j hij
        simp [hij]⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    by_cases h : (i, j) ∈ graphMatrixSupport E
    · simp [h]
    · have hij :
          ¬(i = j ∨ (i, j) ∈ E ∨ (j, i) ∈ E) := by
        simpa using h
      simp [h, X.property i j hij]
  right_inv f := by
    ext p
    simp [p.property]
  map_add' X Y := by
    ext p
    rfl
  map_smul' c X := by
    ext p
    rfl

omit [LinearOrder U] in
/-- The complex dimension of the graph operator space is the number of its
allowed matrix positions. -/
theorem finrank_graphOperatorSpace
    (E : Finset (U × U)) :
    Module.finrank ℂ (graphOperatorSpace E)
      = (graphMatrixSupport E).card := by
  rw [(graphOperatorSpaceEquiv E).finrank_eq, Module.finrank_pi]
  exact Fintype.card_coe (graphMatrixSupport E)

end GraphSupport

section TwoLayerDimension

variable {U : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]

/-- The two-layer coefficient space is linearly equivalent to two independent
copies of the graph operator space. -/
noncomputable def graphTwoLayerSpaceEquiv
    (E : Finset (U × U)) :
    (graphOperatorSpace E × graphOperatorSpace E)
      ≃ₗ[ℂ] graphTwoLayerSpace E where
  toFun XY :=
    ⟨XY.1.1 ⊗ₖ qubitP + XY.2.1 ⊗ₖ qubitQ,
      ⟨XY.1.1, XY.1.2, XY.2.1, XY.2.2, rfl⟩⟩
  invFun Z :=
    ⟨⟨Matrix.of fun i j => Z.1 (i, 0) (j, 0),
        by
          rcases Z.property with ⟨X, hX, Y, hY, hZ⟩
          intro i j hij
          simpa [hZ, Matrix.kroneckerMap_apply, qubitP, qubitQ]
            using hX i j hij⟩,
      ⟨Matrix.of fun i j => Z.1 (i, 1) (j, 1),
        by
          rcases Z.property with ⟨X, hX, Y, hY, hZ⟩
          intro i j hij
          simpa [hZ, Matrix.kroneckerMap_apply, qubitP, qubitQ]
            using hY i j hij⟩⟩
  left_inv XY := by
    rcases XY with ⟨X, Y⟩
    apply Prod.ext <;> apply Subtype.ext <;> ext i j
    · simp [Matrix.kroneckerMap_apply, qubitP, qubitQ]
    · simp [Matrix.kroneckerMap_apply, qubitP, qubitQ]
  right_inv Z := by
    apply Subtype.ext
    rcases Z.property with ⟨X, hX, Y, hY, hZ⟩
    have hZ0 (i j : U) : Z.1 (i, 0) (j, 0) = X i j := by
      simp [hZ, Matrix.kroneckerMap_apply, qubitP, qubitQ]
    have hZ1 (i j : U) : Z.1 (i, 1) (j, 1) = Y i j := by
      simp [hZ, Matrix.kroneckerMap_apply, qubitP, qubitQ]
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    fin_cases a <;> fin_cases b <;>
      simp [hZ, hZ0, hZ1, Matrix.kroneckerMap_apply, qubitP, qubitQ]
  map_add' XY XY' := by
    apply Subtype.ext
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    simp [Matrix.kroneckerMap_apply, add_mul]
    ring
  map_smul' c XY := by
    apply Subtype.ext
    ext p q
    obtain ⟨i, a⟩ := p
    obtain ⟨j, b⟩ := q
    simp [Matrix.kroneckerMap_apply]
    ring

omit [DecidableEq U] [LinearOrder U] in
/-- The two-layer construction doubles the complex coefficient-space
dimension. -/
theorem finrank_graphTwoLayerSpace
    (E : Finset (U × U)) :
    Module.finrank ℂ (graphTwoLayerSpace E)
      = 2 * Module.finrank ℂ (graphOperatorSpace E) := by
  rw [← (graphTwoLayerSpaceEquiv E).finrank_eq,
    Module.finrank_prod]
  omega

end TwoLayerDimension

end RankR
