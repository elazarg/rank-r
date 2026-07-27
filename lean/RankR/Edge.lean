/-
The edgewise consumption of the double-skew bound.

This is the only point in the development where `DoubleSkewBound` — the
Fu–Gao–Park import — is actually used.
-/
import RankR.Frame

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- `mulVecE` and `Matrix.toEuclideanLin` are the same map. -/
theorem mulVecE_eq_toEuclideanLin (A : Matrix (U × V) (U × V) ℂ)
    (x : EuclideanSpace ℂ (U × V)) :
    mulVecE A x = Matrix.toEuclideanLin A x := rfl

omit [DecidableEq U] [DecidableEq V] in
/-- `ebar` is the conjugated frame, so it is orthonormal whenever `e` is. -/
theorem orthonormal_ebar {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (ebar e) := orthonormal_conj he

/-- The double-skew bound applied to a single edge: for `K` in the double-skew
subspace and two distinct members of the conjugated frame,
`‖K ēᵢ‖² + ‖K ēⱼ‖² ≤ ½‖K‖₂²`. -/
theorem edge_double_skew (hFGP : DoubleSkewBound U V)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    {K : Matrix (U × V) (U × V) ℂ} (hK : K ∈ doubleSkew U V)
    {i j : Fin s} (hij : i ≠ j) :
    ‖mulVecE K (ebar e i)‖ ^ 2 + ‖mulVecE K (ebar e j)‖ ^ 2 ≤ hsNormSq K / 2 := by
  have hb := orthonormal_ebar he
  rw [mulVecE_eq_toEuclideanLin, mulVecE_eq_toEuclideanLin]
  exact hFGP K hK (ebar e i) (ebar e j) (hb.1 i) (hb.1 j) (hb.2 hij)

end RankR
