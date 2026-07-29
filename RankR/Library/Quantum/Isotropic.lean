/-
The two spectral projectors determined by the maximally entangled direction.
-/
import RankR.Library.Quantum.Reduction

namespace RankR

open Matrix
open scoped ComplexOrder

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The normalized projector onto the one-factor maximally entangled
direction. -/
noncomputable def omegaProjection :
    Matrix (T × T) (T × T) ℂ :=
  ((1 / (Fintype.card T : ℝ) : ℝ) : ℂ) • singleOmegaChoi

/-- The orthogonal complement of the maximally entangled direction. -/
noncomputable def omegaComplement :
    Matrix (T × T) (T × T) ℂ :=
  1 - omegaProjection (T := T)

theorem omegaComplement_add_projection :
    omegaComplement (T := T) + omegaProjection (T := T) = 1 := by
  rw [omegaComplement, sub_add_cancel]

theorem singleOmegaChoi_posSemidef :
    (singleOmegaChoi (T := T)).PosSemidef := by
  have h :
      singleOmegaChoi (T := T) =
        Matrix.vecMulVec (singleOmegaVec (T := T) : T × T → ℂ)
          (star (singleOmegaVec (T := T) : T × T → ℂ)) := by
    ext p q
    simp [singleOmegaChoi, rankOne, Matrix.vecMulVec_apply, Pi.star_apply,
      RCLike.star_def]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem omegaProjection_posSemidef (hT : 0 < Fintype.card T) :
    (omegaProjection (T := T)).PosSemidef := by
  exact singleOmegaChoi_posSemidef.smul
    ((RCLike.ofReal_nonneg (K := ℂ)).mpr
      (one_div_nonneg.mpr (by exact_mod_cast hT.le)))

theorem omegaComplement_eq_reductionChoi :
    omegaComplement (T := T)
      = reductionChoi (T := T) (1 / (Fintype.card T : ℝ)) := by
  rfl

theorem omegaComplement_posSemidef (hT : 0 < Fintype.card T) :
    (omegaComplement (T := T)).PosSemidef := by
  rw [omegaComplement_eq_reductionChoi]
  exact reductionChoi_posSemidef (one_div_nonneg.mpr (by exact_mod_cast hT.le))
    hT le_rfl

end RankR
