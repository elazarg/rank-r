/-
Finite-coordinate Choi matrices and product-register regrouping.
-/
import RankR.Library.Quantum.BlockPositive
import Mathlib.Analysis.Matrix.Order

namespace RankR

open Matrix
open scoped ComplexOrder Kronecker

section Regroup

variable {U V : Type*}

/-- The permutation from product-Choi order to vectorization order. -/
def choiRegroupEquiv : (U × U) × (V × V) ≃ (U × V) × (U × V) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- A product of two Choi matrices, in vectorization register order. -/
def regroupChoi (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    Matrix ((U × V) × (U × V)) ((U × V) × (U × V)) ℂ :=
  Matrix.reindex (choiRegroupEquiv (U := U) (V := V))
    (choiRegroupEquiv (U := U) (V := V)) (A ⊗ₖ B)

theorem regroupChoi_sub_left (A A' : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi (A - A') B = regroupChoi A B - regroupChoi A' B := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

theorem regroupChoi_sub_right (A : Matrix (U × U) (U × U) ℂ)
    (B B' : Matrix (V × V) (V × V) ℂ) :
    regroupChoi A (B - B') = regroupChoi A B - regroupChoi A B' := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.sub_apply]
  ring

theorem regroupChoi_add_left (A A' : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi (A + A') B = regroupChoi A B + regroupChoi A' B := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

theorem regroupChoi_add_right (A : Matrix (U × U) (U × U) ℂ)
    (B B' : Matrix (V × V) (V × V) ℂ) :
    regroupChoi A (B + B') = regroupChoi A B + regroupChoi A B' := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.add_apply]
  ring

theorem regroupChoi_smul_left (c : ℂ) (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi (c • A) B = c • regroupChoi A B := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem regroupChoi_smul_right (c : ℂ) (A : Matrix (U × U) (U × U) ℂ)
    (B : Matrix (V × V) (V × V) ℂ) :
    regroupChoi A (c • B) = c • regroupChoi A B := by
  ext X Y
  simp only [regroupChoi, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul]
  ring

variable [Fintype U] [Fintype V]

/-- Regrouping a Kronecker product preserves positive semidefiniteness. -/
theorem regroupChoi_posSemidef
    {A : Matrix (U × U) (U × U) ℂ} {B : Matrix (V × V) (V × V) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (regroupChoi A B).PosSemidef := by
  rw [regroupChoi, Matrix.reindex_apply]
  exact hA.kronecker hB |>.submatrix _

end Regroup

section MapChoi

/-- The Choi matrix of a coordinate map, with output index first. -/
noncomputable def mapChoi {I O : Type*} [DecidableEq I]
    (Φ : Matrix I I ℂ → Matrix O O ℂ) :
    Matrix (O × I) (O × I) ℂ :=
  Matrix.of fun p q => Φ (Matrix.single p.2 q.2 1) p.1 q.1

end MapChoi

end RankR
