/-
The one-factor maximally entangled vector and its rank-one operator.
-/
import RankR.Library.Quantum.Choi

namespace RankR

open Matrix Finset

/-- The one-factor maximally entangled vector in finite coordinates. -/
def singleOmegaVec {T : Type*} [DecidableEq T] :
    EuclideanSpace ℂ (T × T) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (1 : ℂ) else 0

@[simp]
theorem singleOmegaVec_apply {T : Type*} [DecidableEq T] (p : T × T) :
    singleOmegaVec p = if p.1 = p.2 then (1 : ℂ) else 0 := rfl

/-- The rank-one operator `|Ω_T⟩⟨Ω_T|`. -/
noncomputable def singleOmegaChoi {T : Type*} [DecidableEq T] :
    Matrix (T × T) (T × T) ℂ :=
  rankOne (singleOmegaVec (T := T)) singleOmegaVec

/-- Pairing the maximally entangled vector with `vec C` gives `Tr C`. -/
theorem inner_singleOmegaVec {T : Type*} [Fintype T] [DecidableEq T]
    (C : Matrix T T ℂ) :
    inner ℂ (singleOmegaVec (T := T)) (vec C) = C.trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply]
  have h : ∀ y : T,
      (inner ℂ (singleOmegaVec (T := T) (x, y)) (vec C (x, y)) : ℂ)
        = if x = y then C x y else 0 := by
    intro y
    rw [RCLike.inner_apply', singleOmegaVec_apply, vec_apply]
    by_cases hxy : x = y <;> simp [hxy]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_eq]
  simp

end RankR
