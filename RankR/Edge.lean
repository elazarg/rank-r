/-
Orthonormality of the conjugated frame.
-/
import RankR.Synth

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

omit [DecidableEq U] [DecidableEq V] in
/-- `ebar` is the conjugated frame, so it is orthonormal whenever `e` is. -/
theorem orthonormal_ebar {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (ebar e) := orthonormal_conj he

end RankR
