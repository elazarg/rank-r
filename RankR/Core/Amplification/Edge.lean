/-
Orthonormality of the conjugated frame.
-/
import RankR.Core.Amplification.CompleteGraph

namespace RankR

open Matrix Finset ComplexConjugate

variable {W : Type*} [Fintype W] {s : ℕ}

/-- `ebar` is the conjugated frame, so it is orthonormal whenever `e` is. -/
theorem orthonormal_ebar {e : Fin s → EuclideanSpace ℂ W} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (ebar e) := orthonormal_conj he

end RankR
