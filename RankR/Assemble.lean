/-
The frame form of `Φ₄(Pneg)`.

Expanding the Kraus sum and then the rank-one sum defining `Pneg`, and moving the
Kraus operator across the inner product, exhibits `qform (Φ₄ (Pneg e))` as a sum
of squared overlaps with an explicit finite family of vectors.  This is what makes
the synthesis map's operator bound usable without ever forming it as a matrix.
-/
import RankR.Edge

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- The Kraus index of `Phi4`. -/
abbrev KIdx (U V : Type*) := (U × U) × (V × V)

/-- The Kraus operator attached to a Kraus index. -/
noncomputable def kop (f : KIdx U V) : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  placeQ (skewUnit f.1.1 f.1.2 ⊗ₖ skewUnit f.2.1 f.2.2)

/-- The frame vectors: the images of `ζ_p` under the Kraus operators, extended by
zero off the edge set `p.1 < p.2`. -/
noncomputable def wvec (e : Fin s → EuclideanSpace ℂ (U × V))
    (f : KIdx U V) (p : Fin s × Fin s) : EuclideanSpace ℂ ((U × V) × Fin s) :=
  if p.1 < p.2 then mulVecE (kop f) (zetaV e p.1 p.2) else 0

theorem qform_Phi4_Pneg (e : Fin s → EuclideanSpace ℂ (U × V))
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    qform (Phi4 (Pneg e)) y
      = ∑ f : KIdx U V, ∑ p : Fin s × Fin s,
          ((Complex.normSq (inner ℂ (wvec e f p) y) : ℝ) : ℂ) := by
  rw [Phi4, qform_krausSum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [qform_Pneg_eq, Edges_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : p.1 < p.2
  · simp only [h, if_true, wvec, kop]
    rw [inner_mulVecE_left, Matrix.conjTranspose_conjTranspose]
  · simp [h, wvec]

end RankR
