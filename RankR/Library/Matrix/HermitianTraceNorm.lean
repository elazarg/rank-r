/-
The trace norm of a finite Hermitian matrix, its spectral expansion, and
quadratic-form Hölder duality.
-/
import RankR.Library.Matrix.Action
import Mathlib.Analysis.Matrix.Spectrum

namespace RankR

open Matrix Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The Schatten-`1` norm of a Hermitian matrix, rendered as the sum of the
absolute values of its real eigenvalues. -/
noncomputable def hermitianTraceNorm (D : Matrix I I ℂ) (hD : D.IsHermitian) : ℝ :=
  ∑ i, |hD.eigenvalues i|

theorem hermitianTraceNorm_nonneg (D : Matrix I I ℂ) (hD : D.IsHermitian) :
    0 ≤ hermitianTraceNorm D hD :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Spectral decomposition into unnormalized rank-one projectors. -/
theorem isHermitian_eq_sum_eigen_rankOne (D : Matrix I I ℂ) (hD : D.IsHermitian) :
    D = ∑ i, (hD.eigenvalues i : ℂ) •
      rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i) := by
  calc
    D = (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hD.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ hD.eigenvalues)) := hD.spectral_theorem
    _ = ∑ i, (hD.eigenvalues i : ℂ) •
        rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i) := by
      ext p q
      simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.of_apply, mul_ite,
        mul_zero, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, rankOne, Matrix.IsHermitian.eigenvectorUnitary_apply]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Complex.coe_algebraMap, Function.comp_apply,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
          RCLike.star_def]
        ring

/-- Expand a Hilbert--Schmidt pairing along the Hermitian spectral
decomposition of its second argument. -/
theorem re_hsInner_eq_sum_eigen_qform (H D : Matrix I I ℂ) (hD : D.IsHermitian) :
    (hsInner H D).re
      = ∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re := by
  calc
    (hsInner H D).re
        = (hsInner H (∑ i, (hD.eigenvalues i : ℂ) •
            rankOne (hD.eigenvectorBasis i) (hD.eigenvectorBasis i))).re := by
              rw [← isHermitian_eq_sum_eigen_rankOne D hD]
    _ = ∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re := by
      rw [hsInner_sum_right, Complex.re_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [hsInner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, re_hsInner_rankOne]

/-- Hölder duality for a Hermitian second argument, stated using a uniform
quadratic-form bound. -/
theorem abs_re_hsInner_le_hermitianTraceNorm
    (H D : Matrix I I ℂ) (hD : D.IsHermitian) {L : ℝ}
    (hH : ∀ x : EuclideanSpace ℂ I, ‖x‖ = 1 → |(qform H x).re| ≤ L) :
    |(hsInner H D).re| ≤ L * hermitianTraceNorm D hD := by
  rw [re_hsInner_eq_sum_eigen_qform H D hD, hermitianTraceNorm]
  calc
    |∑ i, hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re|
        ≤ ∑ i, |hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re| := by
          simpa using Finset.abs_sum_le_sum_abs
            (fun i => hD.eigenvalues i * (qform H (hD.eigenvectorBasis i)).re)
            Finset.univ
    _ = ∑ i, |hD.eigenvalues i| *
          |(qform H (hD.eigenvectorBasis i)).re| := by
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
    _ ≤ ∑ i, |hD.eigenvalues i| * L := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left
              (hH (hD.eigenvectorBasis i)
                (hD.eigenvectorBasis.orthonormal.norm_eq_one i))
              (abs_nonneg _)
    _ = L * ∑ i, |hD.eigenvalues i| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring

end RankR
