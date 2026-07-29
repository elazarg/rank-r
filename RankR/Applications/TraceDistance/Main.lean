/-
The two-copy reduction-witness spectrum and its quantitative trace-distance
separation bound.
-/
import RankR.Applications.Reduction.Main
import RankR.Library.Quantum.Isotropic
import RankR.Library.Quantum.WitnessDistance

namespace RankR

open Matrix Finset ComplexConjugate
open scoped ComplexOrder

section TwoCopySpectrum

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The negative eigenvalue magnitude `d/r - 1` of the one-factor reduction
Choi matrix at parameter `1/r`. -/
noncomputable def traceSeparationGamma (r : ℕ) : ℝ :=
  (Fintype.card T : ℝ) / r - 1

/-- The spectral diameter used in `cor:two-copy-trace-distance`. -/
noncomputable def traceSeparationDelta (r : ℕ) : ℝ :=
  traceSeparationGamma (T := T) r
    + max 1 ((traceSeparationGamma (T := T) r) ^ 2)

/-- The one-factor reduction Choi matrix decomposes into its two spectral
projectors with eigenvalues `1` and `-γ`. -/
theorem reductionChoi_inv_eq_complement_sub_gamma
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T) :
    reductionChoi (T := T) (1 / (r : ℝ))
      = omegaComplement (T := T)
        - ((traceSeparationGamma (T := T) r : ℝ) : ℂ) •
          omegaProjection (T := T) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hdR : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  ext p q
  simp only [reductionChoi, omegaComplement, omegaProjection, traceSeparationGamma,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hpq : p = q <;> simp [hpq]
  all_goals (field_simp [hrR, hdR] ; ring)

/-- The four mutually orthogonal sector projectors in the tensor square of
the one-factor decomposition. -/
noncomputable def twoCopySectorCC :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaComplement (T := T)) (omegaComplement (T := T))

noncomputable def twoCopySectorCP :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaComplement (T := T)) (omegaProjection (T := T))

noncomputable def twoCopySectorPC :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaProjection (T := T)) (omegaComplement (T := T))

noncomputable def twoCopySectorPP :
    Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ :=
  regroupChoi (omegaProjection (T := T)) (omegaProjection (T := T))

theorem twoCopySectorCC_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorCC (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaComplement_posSemidef hT)
    (omegaComplement_posSemidef hT)

theorem twoCopySectorCP_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorCP (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaComplement_posSemidef hT)
    (omegaProjection_posSemidef hT)

theorem twoCopySectorPC_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorPC (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaProjection_posSemidef hT)
    (omegaComplement_posSemidef hT)

theorem twoCopySectorPP_posSemidef (hT : 0 < Fintype.card T) :
    (twoCopySectorPP (T := T)).PosSemidef :=
  regroupChoi_posSemidef (omegaProjection_posSemidef hT)
    (omegaProjection_posSemidef hT)

theorem twoCopySectors_sum :
    twoCopySectorCC (T := T) + twoCopySectorCP (T := T)
        + twoCopySectorPC (T := T) + twoCopySectorPP (T := T) = 1 := by
  rw [show twoCopySectorCC (T := T) + twoCopySectorCP (T := T)
        + twoCopySectorPC (T := T) + twoCopySectorPP (T := T)
      = (twoCopySectorCC (T := T) + twoCopySectorCP (T := T))
        + (twoCopySectorPC (T := T) + twoCopySectorPP (T := T)) by abel]
  simp only [twoCopySectorCC, twoCopySectorCP, twoCopySectorPC, twoCopySectorPP,
    ← regroupChoi_add_right, ← regroupChoi_add_left,
    omegaComplement_add_projection, regroupChoi_one_one]

/-- Spectral-sector decomposition of the two-copy witness. -/
theorem productReductionChoi_inv_eq_twoCopySectors
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T) :
    productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
      = twoCopySectorCC (T := T)
        - ((traceSeparationGamma (T := T) r : ℝ) : ℂ) •
            (twoCopySectorCP (T := T) + twoCopySectorPC (T := T))
        + (((traceSeparationGamma (T := T) r) ^ 2 : ℝ) : ℂ) •
            twoCopySectorPP (T := T) := by
  rw [productReductionChoi, reductionChoi_inv_eq_complement_sub_gamma hr hT,
    regroupChoi_sub_left, regroupChoi_sub_right, regroupChoi_sub_right,
    regroupChoi_smul_left, regroupChoi_smul_right, regroupChoi_smul_right,
    regroupChoi_smul_left]
  simp only [twoCopySectorCC, twoCopySectorCP, twoCopySectorPC, twoCopySectorPP]
  module

/-- The four sector quadratic forms resolve the squared norm. -/
theorem re_qform_twoCopySectors_sum
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) :
    (qform (twoCopySectorCC (T := T)) x).re
        + (qform (twoCopySectorCP (T := T)) x).re
        + (qform (twoCopySectorPC (T := T)) x).re
        + (qform (twoCopySectorPP (T := T)) x).re
      = ‖x‖ ^ 2 := by
  have h := congrArg
    (fun A : Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ =>
      (qform A x).re) (twoCopySectors_sum (T := T))
  simpa only [qform_add, Complex.add_re, qform_one, Complex.ofReal_re] using h

/-- The tensor-square witness quadratic form in its four spectral sectors. -/
theorem re_qform_productReductionChoi_inv
    {r : ℕ} (hr : 0 < r) (hT : 0 < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) :
    (qform
      (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))) x).re
      = (qform (twoCopySectorCC (T := T)) x).re
        - traceSeparationGamma (T := T) r *
            ((qform (twoCopySectorCP (T := T)) x).re
              + (qform (twoCopySectorPC (T := T)) x).re)
        + (traceSeparationGamma (T := T) r) ^ 2 *
            (qform (twoCopySectorPP (T := T)) x).re := by
  rw [productReductionChoi_inv_eq_twoCopySectors hr hT, qform_add, qform_sub,
    qform_smul, qform_smul, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [qform_add, Complex.add_re]

/-- The lower and upper spectral bounds of the two-copy witness. -/
theorem re_qform_productReductionChoi_inv_mem
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) (hx : ‖x‖ = 1) :
    -traceSeparationGamma (T := T) r
        ≤ (qform
          (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
          x).re
      ∧
      (qform
          (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
          x).re
        ≤ max 1 ((traceSeparationGamma (T := T) r) ^ 2) := by
  have hT : 0 < Fintype.card T := by omega
  let γ := traceSeparationGamma (T := T) r
  let a := (qform (twoCopySectorCC (T := T)) x).re
  let b := (qform (twoCopySectorCP (T := T)) x).re
  let c := (qform (twoCopySectorPC (T := T)) x).re
  let d := (qform (twoCopySectorPP (T := T)) x).re
  have ha : 0 ≤ a :=
    qform_re_nonneg_of_posSemidef (twoCopySectorCC_posSemidef hT) x
  have hb : 0 ≤ b :=
    qform_re_nonneg_of_posSemidef (twoCopySectorCP_posSemidef hT) x
  have hc : 0 ≤ c :=
    qform_re_nonneg_of_posSemidef (twoCopySectorPC_posSemidef hT) x
  have hd : 0 ≤ d :=
    qform_re_nonneg_of_posSemidef (twoCopySectorPP_posSemidef hT) x
  have hsum : a + b + c + d = 1 := by
    have h := re_qform_twoCopySectors_sum (T := T) x
    rw [hx, one_pow] at h
    exact h
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  have hq :
      (qform
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ)))
        x).re = a - γ * (b + c) + γ ^ 2 * d := by
    exact re_qform_productReductionChoi_inv hr hT x
  have hM1 : 1 ≤ max 1 (γ ^ 2) := le_max_left _ _
  have hMγ : γ ^ 2 ≤ max 1 (γ ^ 2) := le_max_right _ _
  have hM0 : 0 ≤ max 1 (γ ^ 2) := (zero_le_one.trans hM1)
  constructor
  · rw [hq]
    nlinarith [sq_nonneg γ]
  · rw [hq]
    nlinarith

/-- The midpoint-centered witness has operator bound half its spectral
diameter. -/
theorem abs_re_qform_twoCopyWitness_centered_le
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    (x : EuclideanSpace ℂ ((T × T) × (T × T))) (hx : ‖x‖ = 1) :
    let γ := traceSeparationGamma (T := T) r
    let M := max 1 (γ ^ 2)
    let center := (M - γ) / 2
    |(qform
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
          - (center : ℂ) • 1) x).re|
      ≤ traceSeparationDelta (T := T) r / 2 := by
  dsimp only
  let γ := traceSeparationGamma (T := T) r
  let M := max 1 (γ ^ 2)
  have hmem := re_qform_productReductionChoi_inv_mem hr hrT x hx
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  rw [qform_sub, qform_smul, qform_one, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hx, one_pow]
  rw [abs_le]
  dsimp only [traceSeparationDelta, γ, M] at hmem ⊢
  constructor <;> nlinarith

end TwoCopySpectrum

section TwoCopyTraceDistance

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- `cor:two-copy-trace-distance`, pointwise in the comparison state.

As elsewhere in the development, writing the lower bound for every admissible
`σ` is equivalent to the displayed infimum statement and avoids an unrelated
extended-real `sInf` layer.  The norm is the Hermitian trace norm, which is the
sum of the absolute eigenvalues of the Hermitian difference `σ - ρ`. -/
theorem twoCopy_traceDistance_lower
    {r : ℕ} (hr : 0 < r) (hrT : r < Fintype.card T)
    {ρ σ : Matrix ((T × T) × (T × T)) ((T × T) × (T × T)) ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE (W := T × T) r σ)
    {ε : ℝ}
    (hdetect :
      ((productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))
          * ρ).trace).re = -ε) :
    2 * ε / traceSeparationDelta (T := T) r
      ≤ hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  have hTtwo : 2 ≤ Fintype.card T := by omega
  have ht0 : 0 ≤ 1 / (r : ℝ) :=
    one_div_nonneg.mpr (by exact_mod_cast hr.le)
  have hBlock :
      IsBlockPositive r
        (productReductionChoi (U := T) (V := T) (1 / (r : ℝ)) (1 / (r : ℝ))) := by
    apply (isBlockPositive_productReductionChoi_self_iff_le_inv_min
      hr hTtwo ht0).mpr
    rw [min_eq_left]
    exact_mod_cast (Nat.le_of_lt hrT)
  let γ := traceSeparationGamma (T := T) r
  let M := max 1 (γ ^ 2)
  let center := (M - γ) / 2
  have hγ : 0 < γ := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hrTR : (r : ℝ) < Fintype.card T := by exact_mod_cast hrT
    dsimp only [γ, traceSeparationGamma]
    rw [sub_pos, one_lt_div hrR]
    exact hrTR
  have hΔ : 0 < traceSeparationDelta (T := T) r := by
    dsimp only [traceSeparationDelta, γ, M]
    have hM : 0 ≤ max 1 (γ ^ 2) := le_max_left 1 (γ ^ 2) |>.trans' zero_le_one
    linarith
  exact two_mul_div_le_hermitianTraceNorm_of_witness
    (productReductionChoi_isHermitian (U := T) (V := T) _ _)
    hBlock hρ hσ hSN hΔ hdetect
    (abs_re_qform_twoCopyWitness_centered_le hr hrT)

end TwoCopyTraceDistance

end RankR
