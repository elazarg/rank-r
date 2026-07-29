/-
The exact positive/negative-sector Gram certificate from Appendix A.

The manuscript writes the two sector terms using synthesis matrices
`T₊ T₊*` and `T₋ T₋*`.  The development already represents those Gram
operators directly as the Kraus quadratic forms `Phi4 (Ppos e)` and
`Phi4 (Pneg e)`.  This file states the exact identity in that representation
and proves positivity of the negative-sector defect.
-/
import RankR.Results

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {s : ℕ}

/-- The denominator-free negative-sector defect corresponding to `B_E` in
`eq:sos-negative-defect`.

The factor `8s` reconciles the manuscript normalization with `Phi4 = 4 Φ` and
the doubled sector operator `Pneg = 2P₋`. -/
noncomputable def negativeSectorDefectScaled
    (e : Fin s → EuclideanSpace ℂ (U × V)) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  ((8 : ℂ) * s * ((s : ℂ) - 1)) •
      (1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
    - ((8 : ℂ) * ((s : ℂ) - 1)) • rankOne (delta e) (delta e)
    - (s : ℂ) • Phi4 (Pneg e)

/-- The scaled `eq:H-decomposition`, regrouped into its positive-sector Gram
operator and the negative-sector defect. -/
theorem eight_smul_HopScaled_eq_sector_add_defect
    (e : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    (8 : ℂ) • HopScaled e
      = (s : ℂ) • Phi4 (Ppos e) + negativeSectorDefectScaled e := by
  have h4 := HopScaled_eq e he
  have hsectors : Phi4 (Ppos e) - Phi4 (Pneg e)
      = (2 : ℂ) • Phi4 (ptransposeUV (rankOne (delta e) (delta e))) := by
    rw [← Phi4_sub, Ppos_sub_Pneg, Phi4_smul]
  have h8 : (8 : ℂ) • HopScaled e = (2 : ℂ) • ((4 : ℂ) • HopScaled e) := by
    rw [smul_smul]
    norm_num
  have hsector :
      (2 : ℂ) • ((s : ℂ) • Phi4 (ptransposeUV (rankOne (delta e) (delta e))))
        = (s : ℂ) • (Phi4 (Ppos e) - Phi4 (Pneg e)) := by
    calc
      _ = (s : ℂ) • ((2 : ℂ) •
          Phi4 (ptransposeUV (rankOne (delta e) (delta e)))) := by module
      _ = _ := by rw [← hsectors]
  rw [h8, h4]
  rw [smul_add, smul_sub, hsector, negativeSectorDefectScaled]
  module

/-- The quadratic form of the scaled negative-sector defect. -/
theorem re_qform_negativeSectorDefectScaled
    (e : Fin s → EuclideanSpace ℂ (U × V))
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    (qform (negativeSectorDefectScaled e) x).re
      = 8 * (s : ℝ) * ((s : ℝ) - 1) * ‖x‖ ^ 2
        - 8 * ((s : ℝ) - 1) * Complex.normSq (inner ℂ (delta e) x)
        - (s : ℝ) * (qform (Phi4 (Pneg e)) x).re := by
  rw [negativeSectorDefectScaled, qform_sub, qform_sub, qform_smul, qform_smul,
    qform_smul, qform_one, qform_rankOne]
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
  norm_num

/-- Positivity of `B_E`, in the scaled quadratic-form rendering used by the
development.  This is the operator conclusion of
`prop:sos-complete-graph`; Lean obtains it from the already checked
negative-sector synthesis bound. -/
theorem qform_negativeSectorDefectScaled_nonneg
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (hs : 0 < s) {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    0 ≤ (qform (negativeSectorDefectScaled e) x).re := by
  have hkey := qform_Phi4_Pneg_le hβ hs he x
  have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hkey' : (s : ℝ) * (qform (Phi4 (Pneg e)) x).re
      ≤ 8 * (s : ℝ) * ((s : ℝ) - 1) * ‖x‖ ^ 2
        - 8 * ((s : ℝ) - 1) * Complex.normSq (inner ℂ (delta e) x) := by
    have h := mul_le_mul_of_nonneg_left hkey hsr.le
    refine h.trans (le_of_eq ?_)
    field_simp
  rw [re_qform_negativeSectorDefectScaled]
  linarith

/-- **Exact positive/negative-sector Gram identity**
(`eq:sos-main-gram`), in the development's denominator-free normalization.

The first term is the positive-sector Gram form
`‖T₊* δ_d‖²`; the second is `⟨δ_d, B_E δ_d⟩`, scaled by the same positive
factor `8s`. -/
theorem rankFactor_partialTraceGap_eq_sector_gram
    (hs : 0 < s) (e d : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    8 * (s : ℝ) *
        ((s : ℝ) * hsNormSq (rankFactor e d)
          + (1 / (s : ℝ)) * Complex.normSq (rankFactor e d).trace
          - hsNormSq (ptraceU (rankFactor e d))
          - hsNormSq (ptraceV (rankFactor e d)))
      = (qform ((s : ℂ) • Phi4 (Ppos e)) (delta d)).re
        + (qform (negativeSectorDefectScaled e) (delta d)).re := by
  have hmatrix := eight_smul_HopScaled_eq_sector_add_defect e he
  have hq := congrArg (fun A => (qform A (delta d)).re) hmatrix
  simp only [qform_smul, qform_add, Complex.add_re, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re, Complex.natCast_im] at hq ⊢
  rw [qform_HopScaled, Complex.ofReal_re, ← contraction_norm e d he] at hq
  have hsr : (s : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hs)
  field_simp [hsr]
  nlinarith [hq]

/-- Both summands in the exact Gram identity are nonnegative. -/
theorem rankFactor_sector_gram_terms_nonneg
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (hs : 0 < s) (e d : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    0 ≤ (qform ((s : ℂ) • Phi4 (Ppos e)) (delta d)).re
      ∧ 0 ≤ (qform (negativeSectorDefectScaled e) (delta d)).re := by
  constructor
  · rw [qform_smul]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    exact mul_nonneg (Nat.cast_nonneg s) (qform_Phi4_nonneg
      (fun z => qform_Ppos_nonneg e z) (delta d))
  · exact qform_negativeSectorDefectScaled_nonneg hβ hs he (delta d)

/-- Positivity of the negative-sector defect with the double-skew Choi bound
discharged. -/
theorem qform_negativeSectorDefectScaled_nonneg_holds
    (hs : 0 < s) {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    0 ≤ (qform (negativeSectorDefectScaled e) x).re :=
  qform_negativeSectorDefectScaled_nonneg choiTwoBound_holds hs he x

/-- The two nonnegative summands of the exact Gram identity, with no
mathematical hypothesis left open. -/
theorem rankFactor_sector_gram_terms_nonneg_holds
    (hs : 0 < s) (e d : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    0 ≤ (qform ((s : ℂ) • Phi4 (Ppos e)) (delta d)).re
      ∧ 0 ≤ (qform (negativeSectorDefectScaled e) (delta d)).re :=
  rankFactor_sector_gram_terms_nonneg choiTwoBound_holds hs e d he

end RankR
