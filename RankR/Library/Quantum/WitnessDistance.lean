/-
Trace-norm separation bounds obtained from a centered block-positive witness.
-/
import RankR.Library.Matrix.HermitianTraceNorm
import RankR.Library.Quantum.SchmidtNumber

namespace RankR

open Matrix
open scoped ComplexOrder

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A centered Hermitian witness separates a detected state from every
Schmidt-number-`r` state by its Hermitian trace norm. -/
theorem witness_separation_hermitianTraceNorm
    {r : ℕ} {Z ρ σ : Matrix (W × W) (W × W) ℂ}
    (hZ : Z.IsHermitian) (hBlock : IsBlockPositive r Z)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE r σ)
    {ε c L : ℝ} (hdetect : ((Z * ρ).trace).re = -ε)
    (hcenter : ∀ x : EuclideanSpace ℂ (W × W), ‖x‖ = 1 →
      |(qform (Z - (c : ℂ) • 1) x).re| ≤ L) :
    ε ≤ L * hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  let D := σ - ρ
  have hD : D.IsHermitian := hσ.1.isHermitian.sub hρ.1.isHermitian
  have htraceD : D.trace = 0 := by
    dsimp only [D]
    rw [Matrix.trace_sub, hσ.2, hρ.2, sub_self]
  have hZρ : (hsInner Z ρ).re = -ε := by
    rw [← trace_mul_eq_hsInner_of_isHermitian hZ]
    exact hdetect
  have hZσ : 0 ≤ (hsInner Z σ).re :=
    re_hsInner_nonneg_of_schmidtNumberLE hBlock hSN
  have hgap : ε ≤ (hsInner Z D).re := by
    dsimp only [D]
    rw [hsInner_sub_right, Complex.sub_re]
    linarith
  have hscalar : hsInner ((c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D = 0 := by
    rw [hsInner_smul_left]
    simp only [Complex.conj_ofReal, hsInner, Matrix.conjTranspose_one, Matrix.one_mul, htraceD,
      mul_zero]
  have hcenterEq :
      (hsInner (Z - (c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D).re
        = (hsInner Z D).re := by
    rw [hsInner_sub_left, hscalar, sub_zero]
  have hholder := abs_re_hsInner_le_hermitianTraceNorm
    (Z - (c : ℂ) • (1 : Matrix (W × W) (W × W) ℂ)) D hD hcenter
  rw [hcenterEq] at hholder
  exact hgap.trans ((le_abs_self _).trans hholder)

/-- The witness-separation bound normalized by a positive spectral
diameter. -/
theorem two_mul_div_le_hermitianTraceNorm_of_witness
    {r : ℕ} {Z ρ σ : Matrix (W × W) (W × W) ℂ}
    (hZ : Z.IsHermitian) (hBlock : IsBlockPositive r Z)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hSN : SchmidtNumberLE r σ)
    {ε c Δ : ℝ} (hΔ : 0 < Δ) (hdetect : ((Z * ρ).trace).re = -ε)
    (hcenter : ∀ x : EuclideanSpace ℂ (W × W), ‖x‖ = 1 →
      |(qform (Z - (c : ℂ) • 1) x).re| ≤ Δ / 2) :
    2 * ε / Δ
      ≤ hermitianTraceNorm (σ - ρ) (hσ.1.isHermitian.sub hρ.1.isHermitian) := by
  have h := witness_separation_hermitianTraceNorm
    hZ hBlock hρ hσ hSN hdetect hcenter
  rw [div_le_iff₀ hΔ]
  nlinarith

end RankR
