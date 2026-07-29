/-
The double-skew specialization of amplification-frame orthogonality.
-/
import RankR.Core.Amplification.Frame
import RankR.Core.DoubleSkew.Basic

namespace RankR

open Matrix
open scoped Kronecker

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

omit [DecidableEq U] [DecidableEq V] in
/-- An elementary tensor of skew matrices is symmetric, so its placement sends
every `ζ_{ij}` into the orthogonal complement of `δ`. -/
theorem inner_delta_placeT_kron_zetaV (e : Fin s → EuclideanSpace ℂ (U × V))
    {L : Matrix U U ℂ} {M : Matrix V V ℂ} (hL : IsSkew L) (hM : IsSkew M) (i j : Fin s) :
    inner ℂ (delta e) (mulVecE (placeT (L ⊗ₖ M)) (zetaV e i j)) = 0 :=
  inner_delta_placeT_zetaV e
    (isFrameSymmetric_of_transpose_eq
      (transpose_eq_self_of_mem_doubleSkew (kron_mem_doubleSkew hL hM)) e) i j

end RankR
