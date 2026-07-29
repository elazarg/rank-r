/-
Finite matrix algebra for isotropic states and the product-isotropic
four-sector space.

This file does not identify the algebraic projection below with Haar
integration, nor prove that it preserves Schmidt number.  It formalizes the
state formulas, their moments, and the moment-uniqueness argument used by the
Schmidt-staircase note.
-/
import RankR.KappaOne
import RankR.Kronecker

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder Kronecker MatrixOrder

section OneFactor

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The normalized state on the orthogonal complement of the maximally
entangled direction. -/
noncomputable def isotropicComplementState :
    Matrix (T × T) (T × T) ℂ :=
  (((((Fintype.card T : ℝ) ^ 2 - 1)⁻¹ : ℝ)) : ℂ) •
    omegaComplement (T := T)

/-- The normalized isotropic state of fidelity `F`. -/
noncomputable def isotropicState (F : ℝ) :
    Matrix (T × T) (T × T) ℂ :=
  ((1 - F : ℝ) : ℂ) • isotropicComplementState (T := T)
    + (F : ℂ) • omegaProjection (T := T)

/-- Fidelity with the maximally entangled direction. -/
noncomputable def isotropicMoment (ρ : Matrix (T × T) (T × T) ℂ) : ℝ :=
  (hsInner (omegaProjection (T := T)) ρ).re

theorem isotropicState_affine (a F G : ℝ) :
    (a : ℂ) • isotropicState (T := T) F
        + ((1 - a : ℝ) : ℂ) • isotropicState G =
      isotropicState (a * F + (1 - a) * G) := by
  simp only [isotropicState]
  module

theorem trace_singleOmegaChoi :
    (singleOmegaChoi (T := T)).trace = Fintype.card T := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp [singleOmegaChoi, rankOne, Matrix.diag_apply]

theorem trace_omegaProjection (hT : 0 < Fintype.card T) :
    (omegaProjection (T := T)).trace = 1 := by
  rw [omegaProjection, Matrix.trace_smul, trace_singleOmegaChoi]
  change ((1 / (Fintype.card T : ℝ) : ℝ) : ℂ) *
      (Fintype.card T : ℂ) = 1
  norm_cast
  exact one_div_mul_cancel (by exact_mod_cast (Nat.ne_of_gt hT))

theorem trace_omegaComplement (hT : 0 < Fintype.card T) :
    (omegaComplement (T := T)).trace =
      ((Fintype.card T : ℝ) ^ 2 - 1 : ℂ) := by
  rw [omegaComplement, Matrix.trace_sub, trace_omegaProjection hT]
  simp [Matrix.trace, Fintype.card_prod]
  norm_cast
  ring

theorem trace_isotropicComplementState
    (hT : 2 ≤ Fintype.card T) :
    (isotropicComplementState (T := T)).trace = 1 := by
  have hd : (0 : ℝ) < (Fintype.card T : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
    nlinarith
  rw [isotropicComplementState, Matrix.trace_smul,
    trace_omegaComplement (by omega)]
  have hdC : (Fintype.card T : ℂ) ^ 2 - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt hd)
  simpa [smul_eq_mul] using inv_mul_cancel₀ hdC

theorem trace_isotropicState (hT : 2 ≤ Fintype.card T) (F : ℝ) :
    (isotropicState (T := T) F).trace = 1 := by
  rw [isotropicState, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, trace_isotropicComplementState hT,
    trace_omegaProjection (by omega)]
  norm_num

theorem hsInner_omegaProjection_self
    (hT : 0 < Fintype.card T) :
    hsInner (omegaProjection (T := T)) omegaProjection = 1 := by
  rw [omegaProjection, hsInner_smul_left, hsInner_smul_right,
    hsInner_singleOmegaChoi_self]
  simp only [Complex.conj_ofReal]
  norm_cast
  have hd : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  push_cast
  field_simp

theorem hsInner_omegaProjection_complement
    (hT : 0 < Fintype.card T) :
    hsInner (omegaProjection (T := T)) omegaComplement = 0 := by
  rw [omegaComplement, hsInner_sub_right, hsInner_one_right,
    trace_omegaProjection hT, hsInner_omegaProjection_self hT]
  simp

theorem hsInner_omegaProjection_isotropicComplementState
    (hT : 2 ≤ Fintype.card T) :
    hsInner (omegaProjection (T := T))
      (isotropicComplementState (T := T)) = 0 := by
  rw [isotropicComplementState, hsInner_smul_right,
    hsInner_omegaProjection_complement (by omega), mul_zero]

theorem hsInner_omegaProjection_isotropicState
    (hT : 2 ≤ Fintype.card T) (F : ℝ) :
    hsInner (omegaProjection (T := T)) (isotropicState F) = F := by
  rw [isotropicState, hsInner_add_right,
    hsInner_smul_right, hsInner_smul_right,
    hsInner_omegaProjection_isotropicComplementState hT,
    hsInner_omegaProjection_self (by omega)]
  norm_cast
  simp

theorem hsInner_singleOmegaChoi_isotropicState
    (hT : 2 ≤ Fintype.card T) (F : ℝ) :
    hsInner (singleOmegaChoi (T := T)) (isotropicState F) =
      ((Fintype.card T : ℝ) * F : ℂ) := by
  have hd : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card T ≠ 0 by omega)
  have hscale :
      ((Fintype.card T : ℂ) • omegaProjection (T := T)) =
        singleOmegaChoi := by
    rw [omegaProjection, smul_smul]
    have hcoef :
        (Fintype.card T : ℂ) *
            (((1 / (Fintype.card T : ℝ) : ℝ)) : ℂ) = 1 := by
      have hdC : (Fintype.card T : ℂ) ≠ 0 := by
        exact_mod_cast (show Fintype.card T ≠ 0 by omega)
      rw [one_div, Complex.ofReal_inv]
      exact mul_inv_cancel₀ hdC
    rw [hcoef, one_smul]
  rw [← hscale, hsInner_smul_left,
    hsInner_omegaProjection_isotropicState hT]
  simp only [map_natCast]
  norm_cast

theorem isotropicMoment_isotropicState
    (hT : 2 ≤ Fintype.card T) (F : ℝ) :
    isotropicMoment (T := T) (isotropicState F) = F := by
  rw [isotropicMoment, hsInner_omegaProjection_isotropicState hT]
  simp

/-- Every normalized state of Schmidt number at most `r` has maximally
entangled fidelity at most `r / dim(T)`.

This is the necessary half of the Schmidt-number classification of isotropic
states.  It follows from block positivity of the one-factor reduction witness;
the converse requires an explicit Schmidt-rank decomposition (or twirling
argument) and is deliberately not asserted here. -/
theorem isotropicMoment_le_of_schmidtNumberLE
    (hT : 0 < Fintype.card T) {r : ℕ} (hr : 0 < r)
    {ρ : Matrix (T × T) (T × T) ℂ}
    (hSN : SchmidtNumberLE r ρ) (htrace : ρ.trace = 1) :
    isotropicMoment (T := T) ρ ≤
      (r : ℝ) / Fintype.card T := by
  have hnonneg :=
    re_hsInner_nonneg_of_schmidtNumberLE
      (reductionChoi_inv_isBlockPositive (T := T) hr) hSN
  rw [reductionChoi, hsInner_sub_left, hsInner_one_left,
    hsInner_smul_left, htrace] at hnonneg
  simp only [Complex.one_re, Complex.conj_ofReal, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hnonneg
  have hdR : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hoverlap :
      (hsInner (singleOmegaChoi (T := T)) ρ).re ≤ r := by
    rw [one_div_mul_eq_div, sub_nonneg, div_le_iff₀ hrR] at hnonneg
    nlinarith
  rw [isotropicMoment, omegaProjection, hsInner_smul_left]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  calc
    1 / (Fintype.card T : ℝ) *
          (hsInner (singleOmegaChoi (T := T)) ρ).re
        ≤ 1 / (Fintype.card T : ℝ) * r :=
      mul_le_mul_of_nonneg_left hoverlap (one_div_nonneg.mpr hdR.le)
    _ = (r : ℝ) / Fintype.card T := by ring

/-- An isotropic state above `r / dim(T)` cannot have Schmidt number at most
`r`.  This packages the certified obstruction in the parameters used by the
staircase application. -/
theorem not_schmidtNumberLE_isotropicState_of_ratio_lt
    (hT : 2 ≤ Fintype.card T) {r : ℕ} (hr : 0 < r)
    {F : ℝ} (hF : (r : ℝ) / Fintype.card T < F) :
    ¬ SchmidtNumberLE r (isotropicState (T := T) F) := by
  intro hSN
  have hle :=
    isotropicMoment_le_of_schmidtNumberLE (T := T) (by omega) hr hSN
      (trace_isotropicState hT F)
  rw [isotropicMoment_isotropicState hT F] at hle
  exact (not_le_of_gt hF) hle

theorem isotropicState_whiteNoise
    (hT : 2 ≤ Fintype.card T) :
    isotropicState (T := T) (1 / (Fintype.card T : ℝ) ^ 2)
      = (((Fintype.card T : ℝ) ^ 2)⁻¹ : ℂ) • 1 := by
  have hd : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card T ≠ 0 by omega)
  have hgap : (Fintype.card T : ℝ) ^ 2 - 1 ≠ 0 := by
    have hd2 : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
    nlinarith
  have hcoef :
      (1 - 1 / (Fintype.card T : ℝ) ^ 2) *
          ((Fintype.card T : ℝ) ^ 2 - 1)⁻¹ =
        ((Fintype.card T : ℝ) ^ 2)⁻¹ := by
    field_simp [hd, hgap]
  rw [isotropicState, isotropicComplementState, smul_smul]
  have hcoefC :
      (((1 - 1 / (Fintype.card T : ℝ) ^ 2 : ℝ) : ℂ) *
          ((((Fintype.card T : ℝ) ^ 2 - 1)⁻¹ : ℝ) : ℂ)) =
        ((((Fintype.card T : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcoef
  push_cast at hcoefC
  push_cast
  rw [hcoefC]
  rw [one_div, ← smul_add, omegaComplement_add_projection]

theorem isotropicComplementState_posSemidef
    (hT : 2 ≤ Fintype.card T) :
    (isotropicComplementState (T := T)).PosSemidef := by
  change
    (((((Fintype.card T : ℝ) ^ 2 - 1)⁻¹ : ℝ) : ℂ) •
      omegaComplement (T := T)).PosSemidef
  refine (omegaComplement_posSemidef (by omega)).smul ?_
  apply (RCLike.ofReal_nonneg (K := ℂ)).mpr
  apply inv_nonneg.mpr
  have hd : (2 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
  nlinarith

theorem isotropicState_posSemidef
    (hT : 2 ≤ Fintype.card T) {F : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    (isotropicState (T := T) F).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact (isotropicComplementState_posSemidef hT).smul
      ((RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr hF1))
  · exact (omegaProjection_posSemidef (by omega)).smul
      ((RCLike.ofReal_nonneg (K := ℂ)).mpr hF0)

theorem isotropicState_isDensityMatrix
    (hT : 2 ≤ Fintype.card T) {F : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    IsDensityMatrix (isotropicState (T := T) F) :=
  ⟨isotropicState_posSemidef hT hF0 hF1, trace_isotropicState hT F⟩

theorem hsInner_one_isotropicComplementState
    (hT : 2 ≤ Fintype.card T) :
    hsInner (1 : Matrix (T × T) (T × T) ℂ)
      (isotropicComplementState (T := T)) = 1 := by
  rw [hsInner_one_left, trace_isotropicComplementState hT]

theorem hsInner_one_omegaProjection
    (hT : 0 < Fintype.card T) :
    hsInner (1 : Matrix (T × T) (T × T) ℂ)
      (omegaProjection (T := T)) = 1 := by
  rw [hsInner_one_left, trace_omegaProjection hT]

end OneFactor

section Product

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- The complement-complement basis element of the product-isotropic
four-sector space. -/
noncomputable def biIsotropicCC :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  isotropicComplementState (T := U) ⊗ₖ
    isotropicComplementState (T := V)

/-- The complement-projector basis element of the product-isotropic
four-sector space. -/
noncomputable def biIsotropicCP :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  isotropicComplementState (T := U) ⊗ₖ omegaProjection (T := V)

/-- The projector-complement basis element of the product-isotropic
four-sector space. -/
noncomputable def biIsotropicPC :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  omegaProjection (T := U) ⊗ₖ isotropicComplementState (T := V)

/-- The projector-projector basis element of the product-isotropic
four-sector space. -/
noncomputable def biIsotropicPP :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  omegaProjection (T := U) ⊗ₖ omegaProjection (T := V)

/-- Real coordinates in the four-dimensional Hermitian
product-isotropic space. -/
noncomputable def biIsotropicForm (cCC cCP cPC cPP : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  (cCC : ℂ) • biIsotropicCC
    + (cCP : ℂ) • biIsotropicCP
    + (cPC : ℂ) • biIsotropicPC
    + (cPP : ℂ) • biIsotropicPP

/-- Membership in the real span of the four product-isotropic sectors. -/
def MemBiIsotropicSpace
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) : Prop :=
  ∃ cCC cCP cPC cPP : ℝ,
    ρ = biIsotropicForm cCC cCP cPC cPP

theorem MemBiIsotropicSpace.add
    {ρ σ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hρ : MemBiIsotropicSpace ρ) (hσ : MemBiIsotropicSpace σ) :
    MemBiIsotropicSpace (ρ + σ) := by
  obtain ⟨aCC, aCP, aPC, aPP, rfl⟩ := hρ
  obtain ⟨bCC, bCP, bPC, bPP, rfl⟩ := hσ
  refine ⟨aCC + bCC, aCP + bCP, aPC + bPC, aPP + bPP, ?_⟩
  simp only [biIsotropicForm]
  module

theorem MemBiIsotropicSpace.real_smul
    {ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hρ : MemBiIsotropicSpace ρ) (a : ℝ) :
    MemBiIsotropicSpace ((a : ℂ) • ρ) := by
  obtain ⟨cCC, cCP, cPC, cPP, rfl⟩ := hρ
  refine ⟨a * cCC, a * cCP, a * cPC, a * cPP, ?_⟩
  simp only [biIsotropicForm]
  module

/-- Product of two normalized isotropic states, in the
`A₁B₁A₂B₂` register order. -/
noncomputable def biIsotropicState (F G : ℝ) :
    Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ :=
  isotropicState (T := U) F ⊗ₖ isotropicState (T := V) G

/-- Overlap with the maximally entangled projector on the `U` factor. -/
noncomputable def biIsotropicMomentU
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) : ℝ :=
  (hsInner
    (omegaProjection (T := U) ⊗ₖ
      (1 : Matrix (V × V) (V × V) ℂ)) ρ).re

/-- Overlap with the maximally entangled projector on the `V` factor. -/
noncomputable def biIsotropicMomentV
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) : ℝ :=
  (hsInner
    ((1 : Matrix (U × U) (U × U) ℂ) ⊗ₖ
      omegaProjection (T := V)) ρ).re

/-- Joint overlap with the maximally entangled projectors on both factors. -/
noncomputable def biIsotropicMomentUV
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) : ℝ :=
  (hsInner
    (omegaProjection (T := U) ⊗ₖ omegaProjection (T := V)) ρ).re

theorem biIsotropicMomentU_add
    (ρ σ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentU (ρ + σ) =
      biIsotropicMomentU ρ + biIsotropicMomentU σ := by
  simp only [biIsotropicMomentU, hsInner_add_right, Complex.add_re]

theorem biIsotropicMomentV_add
    (ρ σ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentV (ρ + σ) =
      biIsotropicMomentV ρ + biIsotropicMomentV σ := by
  simp only [biIsotropicMomentV, hsInner_add_right, Complex.add_re]

theorem biIsotropicMomentUV_add
    (ρ σ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentUV (ρ + σ) =
      biIsotropicMomentUV ρ + biIsotropicMomentUV σ := by
  simp only [biIsotropicMomentUV, hsInner_add_right, Complex.add_re]

theorem biIsotropicMomentU_real_smul
    (a : ℝ)
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentU ((a : ℂ) • ρ) =
      a * biIsotropicMomentU ρ := by
  simp only [biIsotropicMomentU, hsInner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem biIsotropicMomentV_real_smul
    (a : ℝ)
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentV ((a : ℂ) • ρ) =
      a * biIsotropicMomentV ρ := by
  simp only [biIsotropicMomentV, hsInner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem biIsotropicMomentUV_real_smul
    (a : ℝ)
    (ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ) :
    biIsotropicMomentUV ((a : ℂ) • ρ) =
      a * biIsotropicMomentUV ρ := by
  simp only [biIsotropicMomentUV, hsInner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem trace_biIsotropicCC
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    (biIsotropicCC (U := U) (V := V)).trace = 1 := by
  rw [biIsotropicCC, Matrix.trace_kronecker,
    trace_isotropicComplementState hU,
    trace_isotropicComplementState hV, one_mul]

theorem trace_biIsotropicCP
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    (biIsotropicCP (U := U) (V := V)).trace = 1 := by
  rw [biIsotropicCP, Matrix.trace_kronecker,
    trace_isotropicComplementState hU,
    trace_omegaProjection (by omega), one_mul]

theorem trace_biIsotropicPC
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    (biIsotropicPC (U := U) (V := V)).trace = 1 := by
  rw [biIsotropicPC, Matrix.trace_kronecker,
    trace_omegaProjection (by omega),
    trace_isotropicComplementState hV, one_mul]

theorem trace_biIsotropicPP
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V) :
    (biIsotropicPP (U := U) (V := V)).trace = 1 := by
  rw [biIsotropicPP, Matrix.trace_kronecker,
    trace_omegaProjection (by omega),
    trace_omegaProjection (by omega), one_mul]

theorem trace_biIsotropicForm
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (cCC cCP cPC cPP : ℝ) :
    (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP).trace =
      (cCC + cCP + cPC + cPP : ℂ) := by
  rw [biIsotropicForm, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul,
    trace_biIsotropicCC hU hV, trace_biIsotropicCP hU hV,
    trace_biIsotropicPC hU hV, trace_biIsotropicPP hU hV]
  ring

theorem biIsotropicMomentU_form
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (cCC cCP cPC cPP : ℝ) :
    biIsotropicMomentU
        (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)
      = cPC + cPP := by
  rw [biIsotropicMomentU, biIsotropicForm, hsInner_add_right,
    hsInner_add_right, hsInner_add_right, hsInner_smul_right,
    hsInner_smul_right, hsInner_smul_right, hsInner_smul_right]
  simp only [biIsotropicCC, biIsotropicCP, biIsotropicPC, biIsotropicPP,
    hsInner_kron,
    hsInner_omegaProjection_isotropicComplementState (T := U) hU,
    hsInner_omegaProjection_self (T := U) (by omega),
    hsInner_one_isotropicComplementState (T := V) hV,
    hsInner_one_omegaProjection (T := V) (by omega), zero_mul, one_mul, mul_zero,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem biIsotropicMomentV_form
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (cCC cCP cPC cPP : ℝ) :
    biIsotropicMomentV
        (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)
      = cCP + cPP := by
  rw [biIsotropicMomentV, biIsotropicForm, hsInner_add_right,
    hsInner_add_right, hsInner_add_right, hsInner_smul_right,
    hsInner_smul_right, hsInner_smul_right, hsInner_smul_right]
  simp only [biIsotropicCC, biIsotropicCP, biIsotropicPC, biIsotropicPP,
    hsInner_kron, hsInner_one_isotropicComplementState (T := U) hU,
    hsInner_one_omegaProjection (T := U) (by omega),
    hsInner_omegaProjection_isotropicComplementState (T := V) hV,
    hsInner_omegaProjection_self (T := V) (by omega), zero_mul, one_mul, mul_zero,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem biIsotropicMomentUV_form
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (cCC cCP cPC cPP : ℝ) :
    biIsotropicMomentUV
        (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)
      = cPP := by
  rw [biIsotropicMomentUV, biIsotropicForm, hsInner_add_right,
    hsInner_add_right, hsInner_add_right, hsInner_smul_right,
    hsInner_smul_right, hsInner_smul_right, hsInner_smul_right]
  simp only [biIsotropicCC, biIsotropicCP, biIsotropicPC, biIsotropicPP,
    hsInner_kron,
    hsInner_omegaProjection_isotropicComplementState (T := U) hU,
    hsInner_omegaProjection_isotropicComplementState (T := V) hV,
    hsInner_omegaProjection_self (T := U) (by omega),
    hsInner_omegaProjection_self (T := V) (by omega),
    zero_mul, one_mul, mul_zero,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num

theorem biIsotropicForm_eq_of_trace_moments
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {aCC aCP aPC aPP bCC bCP bPC bPP : ℝ}
    (htrace :
      (biIsotropicForm (U := U) (V := V) aCC aCP aPC aPP).trace =
        (biIsotropicForm (U := U) (V := V) bCC bCP bPC bPP).trace)
    (hUeq :
      biIsotropicMomentU (biIsotropicForm (U := U) (V := V) aCC aCP aPC aPP) =
        biIsotropicMomentU
          (biIsotropicForm (U := U) (V := V) bCC bCP bPC bPP))
    (hVeq :
      biIsotropicMomentV (biIsotropicForm (U := U) (V := V) aCC aCP aPC aPP) =
        biIsotropicMomentV
          (biIsotropicForm (U := U) (V := V) bCC bCP bPC bPP))
    (hUVeq :
      biIsotropicMomentUV (biIsotropicForm (U := U) (V := V) aCC aCP aPC aPP) =
        biIsotropicMomentUV
          (biIsotropicForm (U := U) (V := V) bCC bCP bPC bPP)) :
    biIsotropicForm (U := U) (V := V) aCC aCP aPC aPP =
      biIsotropicForm (U := U) (V := V) bCC bCP bPC bPP := by
  rw [trace_biIsotropicForm hU hV, trace_biIsotropicForm hU hV] at htrace
  rw [biIsotropicMomentU_form hU hV, biIsotropicMomentU_form hU hV] at hUeq
  rw [biIsotropicMomentV_form hU hV, biIsotropicMomentV_form hU hV] at hVeq
  rw [biIsotropicMomentUV_form hU hV,
    biIsotropicMomentUV_form hU hV] at hUVeq
  norm_cast at htrace
  have hPP : aPP = bPP := hUVeq
  have hPC : aPC = bPC := by linarith
  have hCP : aCP = bCP := by linarith
  have hCC : aCC = bCC := by linarith
  rw [hCC, hCP, hPC, hPP]

/-- Two operators in the real product-isotropic space are equal when their
trace and three isotropic moments agree. -/
theorem eq_of_memBiIsotropicSpace_of_trace_moments
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {ρ σ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hρ : MemBiIsotropicSpace ρ) (hσ : MemBiIsotropicSpace σ)
    (htrace : ρ.trace = σ.trace)
    (hUeq : biIsotropicMomentU ρ = biIsotropicMomentU σ)
    (hVeq : biIsotropicMomentV ρ = biIsotropicMomentV σ)
    (hUVeq : biIsotropicMomentUV ρ = biIsotropicMomentUV σ) :
    ρ = σ := by
  obtain ⟨aCC, aCP, aPC, aPP, rfl⟩ := hρ
  obtain ⟨bCC, bCP, bPC, bPP, rfl⟩ := hσ
  exact biIsotropicForm_eq_of_trace_moments hU hV
    htrace hUeq hVeq hUVeq

theorem biIsotropicState_eq_form (F G : ℝ) :
    biIsotropicState (U := U) (V := V) F G =
      biIsotropicForm
        ((1 - F) * (1 - G)) ((1 - F) * G)
        (F * (1 - G)) (F * G) := by
  simp only [biIsotropicState, isotropicState, biIsotropicForm,
    biIsotropicCC, biIsotropicCP, biIsotropicPC, biIsotropicPP,
    Matrix.add_kronecker, Matrix.kronecker_add,
    Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

theorem memBiIsotropicSpace_biIsotropicState (F G : ℝ) :
    MemBiIsotropicSpace (biIsotropicState (U := U) (V := V) F G) := by
  refine ⟨(1 - F) * (1 - G), (1 - F) * G,
    F * (1 - G), F * G, ?_⟩
  exact biIsotropicState_eq_form F G

theorem trace_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (F G : ℝ) :
    (biIsotropicState (U := U) (V := V) F G).trace = 1 := by
  rw [biIsotropicState, Matrix.trace_kronecker,
    trace_isotropicState hU F, trace_isotropicState hV G, one_mul]

theorem biIsotropicMomentU_state
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (F G : ℝ) :
    biIsotropicMomentU (biIsotropicState (U := U) (V := V) F G) = F := by
  rw [biIsotropicState_eq_form, biIsotropicMomentU_form hU hV]
  ring

theorem biIsotropicMomentV_state
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (F G : ℝ) :
    biIsotropicMomentV (biIsotropicState (U := U) (V := V) F G) = G := by
  rw [biIsotropicState_eq_form, biIsotropicMomentV_form hU hV]
  ring

theorem biIsotropicMomentUV_state
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    (F G : ℝ) :
    biIsotropicMomentUV (biIsotropicState (U := U) (V := V) F G) = F * G := by
  rw [biIsotropicState_eq_form, biIsotropicMomentUV_form hU hV]

theorem biIsotropicState_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {F G : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) :
    (biIsotropicState (U := U) (V := V) F G).PosSemidef :=
  (isotropicState_posSemidef hU hF0 hF1).kronecker
    (isotropicState_posSemidef hV hG0 hG1)

theorem biIsotropicState_normalized_posSemidef
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {F G : ℝ} (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) :
    (biIsotropicState (U := U) (V := V) F G).PosSemidef ∧
      (biIsotropicState (U := U) (V := V) F G).trace = 1 :=
  ⟨biIsotropicState_posSemidef hU hV hF0 hF1 hG0 hG1,
    trace_biIsotropicState hU hV F G⟩

theorem ptraceV_biIsotropicState
    (hV : 2 ≤ Fintype.card V) (F G : ℝ) :
    ptraceV (biIsotropicState (U := U) (V := V) F G) =
      isotropicState (T := U) F := by
  rw [biIsotropicState, ptraceV_kronecker,
    trace_isotropicState hV G, one_smul]

theorem ptraceU_biIsotropicState
    (hU : 2 ≤ Fintype.card U) (F G : ℝ) :
    ptraceU (biIsotropicState (U := U) (V := V) F G) =
      isotropicState (T := V) G := by
  rw [biIsotropicState, ptraceU_kronecker,
    trace_isotropicState hU F, one_smul]

/-- A trace-one operator in the real product-isotropic space is determined by
its three moments.  When the joint moment factors, it is the product of the
two isotropic states with those fidelities. -/
theorem eq_biIsotropicState_of_mem_of_moments
    (hU : 2 ≤ Fintype.card U) (hV : 2 ≤ Fintype.card V)
    {ρ : Matrix ((U × U) × (V × V)) ((U × U) × (V × V)) ℂ}
    (hρ : MemBiIsotropicSpace ρ) (htrace : ρ.trace = 1)
    (hfactor :
      biIsotropicMomentUV ρ = biIsotropicMomentU ρ * biIsotropicMomentV ρ) :
    ρ = biIsotropicState
      (biIsotropicMomentU ρ) (biIsotropicMomentV ρ) := by
  obtain ⟨cCC, cCP, cPC, cPP, rfl⟩ := hρ
  rw [biIsotropicState_eq_form]
  apply biIsotropicForm_eq_of_trace_moments hU hV
  · simp only [trace_biIsotropicForm hU hV] at htrace ⊢
    norm_cast at htrace ⊢
    calc
      cCC + cCP + cPC + cPP = 1 := htrace
      _ = (1 -
            biIsotropicMomentU
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)) *
            (1 -
              biIsotropicMomentV
                (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)) +
          (1 -
            biIsotropicMomentU
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)) *
            biIsotropicMomentV
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP) +
          biIsotropicMomentU
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP) *
            (1 -
              biIsotropicMomentV
                (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP)) +
          biIsotropicMomentU
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP) *
            biIsotropicMomentV
              (biIsotropicForm (U := U) (V := V) cCC cCP cPC cPP) := by ring
  · simp only [biIsotropicMomentU_form hU hV]
    ring
  · simp only [biIsotropicMomentV_form hU hV]
    ring
  · simp only [biIsotropicMomentU_form hU hV,
      biIsotropicMomentV_form hU hV,
      biIsotropicMomentUV_form hU hV] at hfactor ⊢
    exact hfactor

end Product

end RankR
