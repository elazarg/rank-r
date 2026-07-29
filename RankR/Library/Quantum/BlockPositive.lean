/-
Finite-coordinate block positivity.
-/
import RankR.Library.Matrix.QuadraticForm

namespace RankR

open Matrix

variable {W : Type*} [Fintype W]

/-- `r`-block positivity, expressed by rank-constrained vectorized matrices. -/
def IsBlockPositive (r : ℕ) (M : Matrix (W × W) (W × W) ℂ) : Prop :=
  ∀ C : Matrix W W ℂ, C.rank ≤ r → 0 ≤ (qform M (vec C)).re

end RankR
