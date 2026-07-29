/-
An exact skew-family certificate showing that the protected amplification bound
depends on transposition parity.
-/
import RankR.Core.Amplification.Parity
import RankR.Core.DoubleSkew.Basic

namespace RankR

open Matrix Finset ComplexConjugate

section Certificate

/-- The standard basis vector of `ℂ²`, written out so its value at a point is
definitional. -/
private noncomputable def pb (i : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 fun p => if p = i then (1 : ℂ) else 0

@[simp] private theorem pb_apply (i p : Fin 2) :
    pb i p = if p = i then (1 : ℂ) else 0 := rfl

/-- The one-element skew Kraus family `{J}`, `J = E_{01} - E_{10}` on `ℂ²`. -/
noncomputable def skewFam : Unit → Matrix (Fin 2) (Fin 2) ℂ := fun _ => skewUnit 0 1

theorem skewFam_isSkew (f : Unit) : (skewFam f)ᵀ = -skewFam f := skewUnit_isSkew 0 1

/-- The standard frame of `ℂ²` is orthonormal. -/
theorem orthonormal_pb : Orthonormal ℂ pb := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  by_cases h : i = j <;> simp [h] <;>
    · revert h; fin_cases i <;> fin_cases j <;> simp

/-- The standard frame is not symmetric for the skew family. -/
theorem not_isFrameSymmetric_skewFam : ¬ ∀ f, IsFrameSymmetric pb (skewFam f) := by
  intro h
  have h01 := h () 0 1
  rw [inner_mulVecE_ebar, inner_mulVecE_ebar] at h01
  simp only [skewFam, skewUnit_apply, pb_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- The family satisfies the rank-two Choi bound at `β = 1`. -/
theorem choiTwoBound_skewFam : ChoiTwoBound (choiOf skewFam) 1 := by
  refine choiTwoBound_of_sum_hsNormSq skewFam ?_
  have h : hsNormSq (skewFam ()) = 2 := by
    simp only [hsNormSq, skewFam, Fin.isValue, skewUnit_apply, mul_ite,
      mul_one, mul_zero, Fin.sum_univ_two, one_ne_zero, ↓reduceIte,
      zero_sub, Complex.normSq_neg, MonoidWithZeroHom.map_ite_one_zero,
      zero_ne_one, sub_zero, zero_add, add_zero]
    norm_num
  simp [h]

/-- `J ē₁ = e₀`, the entry computation used by the certificate. -/
theorem inner_pb_mulVecE_skewFam :
    inner ℂ (pb 0) (mulVecE (skewFam ()) (ebar pb 1)) = 1 := by
  rw [inner_mulVecE_ebar]
  simp only [skewFam, skewUnit_apply, pb_apply, Fin.sum_univ_two]
  norm_num

/-- The single edge vector pairs against `δ_e` to `-2`. -/
theorem inner_delta_wvec_skewFam :
    inner ℂ (delta pb) (wvec skewFam pb () (0, 1)) = -2 := by
  rw [wvec, if_pos (by decide : ((0 : Fin 2), (1 : Fin 2)).1 < ((0 : Fin 2), (1 : Fin 2)).2),
    inner_delta_placeT_zetaV_of_isSkew pb (skewFam_isSkew ()) 0 1, inner_pb_mulVecE_skewFam]
  ring

/-- The negative-sector quadratic form of the certificate equals four. -/
theorem re_qform_krausQ_Pneg_skewFam :
    (qform (krausQ skewFam (Pneg pb)) (delta pb)).re = 4 := by
  rw [re_qform_krausQ_Pneg, Finset.sum_eq_single ((), ((0 : Fin 2), (1 : Fin 2)))]
  · rw [← inner_conj_symm, Complex.normSq_conj, inner_delta_wvec_skewFam]
    simp only [Complex.normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.neg_re, Complex.re_ofNat, mul_neg, neg_mul, neg_neg,
      Complex.neg_im, Complex.im_ofNat, neg_zero, mul_zero, add_zero]
    norm_num
  · rintro ⟨u, i, j⟩ _ hk
    have hij : ¬ (i < j) := by
      revert hk; fin_cases i <;> fin_cases j <;> simp
    simp [wvec, hij]
  · simp

/-- The protected correction term vanishes on the certificate vector. -/
theorem normSq_inner_self_delta_pb :
    Complex.normSq (inner ℂ (delta pb) (delta pb)) = 4 := by
  have hself : (inner ℂ (delta pb) (delta pb) : ℂ) = 2 := by
    rw [PiLp.inner_apply, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, RCLike.inner_apply', delta_apply, pb_apply]
    norm_num
  rw [hself]
  norm_num [Complex.normSq_apply]

/-- The unprotected amplification bound is attained by the skew family. -/
theorem qform_krausQ_Pneg_skewFam_saturates :
    (qform (krausQ skewFam (Pneg pb)) (delta pb)).re
      = 2 * 1 * ((2 : ℝ) - 1) * ‖delta pb‖ ^ 2 := by
  rw [re_qform_krausQ_Pneg_skewFam, norm_delta_of_norm_one orthonormal_pb.1]
  norm_num

/-- The protected amplification bound fails for the skew family for every
constant `β`. -/
theorem not_qform_krausQ_Pneg_le_skewFam (β : ℝ) :
    ¬ ((qform (krausQ skewFam (Pneg pb)) (delta pb)).re
        ≤ 2 * β * ((2 : ℝ) - 1)
            * (‖delta pb‖ ^ 2
                - Complex.normSq (inner ℂ (delta pb) (delta pb)) / 2)) := by
  rw [re_qform_krausQ_Pneg_skewFam, norm_delta_of_norm_one orthonormal_pb.1,
    normSq_inner_self_delta_pb]
  norm_num

end Certificate

end RankR
