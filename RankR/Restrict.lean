/-
Sharpening a Bessel bound on a family orthogonal to a fixed vector.

If every member of a finite family is orthogonal to `z`, the family's Bessel sum
against `y` sees only the component of `y` off `z`, so the bound improves from
`M‖y‖²` to `M(‖y‖² − |⟪z,y⟫|²/‖z‖²)`.
-/
import RankR.Elementary

namespace RankR

open Matrix Finset ComplexConjugate

section Ortho

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [Fintype ι] in
/-- Subtracting the `z`-component of `y` leaves the overlaps with any family
orthogonal to `z` unchanged. -/
theorem inner_sub_smul_of_orthogonal {w : ι → E} {z : E}
    (hz : ∀ k, inner ℂ z (w k) = 0) (y : E) (a : ℂ) (k : ι) :
    inner ℂ (w k) (y - a • z) = inner ℂ (w k) y := by
  have h : inner ℂ (w k) z = 0 := by
    rw [← inner_conj_symm, hz k, map_zero]
  rw [inner_sub_right, inner_smul_right, h, mul_zero, sub_zero]

/-- The Pythagorean identity for the component of `y` off a vector `z` of squared
norm `n`. -/
theorem norm_sub_proj_sq {z : E} {n : ℝ} (hn : 0 < n) (hzn : ‖z‖ ^ 2 = n) (y : E) :
    ‖y - ((inner ℂ z y / (n : ℂ)) • z)‖ ^ 2
      = ‖y‖ ^ 2 - Complex.normSq (inner ℂ z y) / n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : RCLike.re (inner ℂ y ((inner ℂ z y / (n : ℂ)) • z))
      = Complex.normSq (inner ℂ z y) / n := by
    rw [inner_smul_right,
      show inner ℂ y z = conj (inner ℂ z y) from (inner_conj_symm y z).symm,
      div_mul_eq_mul_div, Complex.mul_conj, ← Complex.ofReal_div]
    exact Complex.ofReal_re _
  have h2 : ‖inner ℂ z y / (n : ℂ)‖ ^ 2 = Complex.normSq (inner ℂ z y) / n ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, map_div₀, Complex.normSq_ofReal]
    ring_nf
  rw [norm_sub_sq (𝕜 := ℂ), h1, norm_smul, mul_pow, h2, hzn]
  field_simp
  ring

/-- Bessel bound sharpened on the orthogonal complement of `z`. -/
theorem frame_le_sub_proj {w : ι → E} {z : E} {n : ℝ} (hn : 0 < n) (hzn : ‖z‖ ^ 2 = n)
    (horth : ∀ k, inner ℂ z (w k) = 0) {M : ℝ}
    (hb : ∀ y : E, ∑ k, Complex.normSq (inner ℂ (w k) y) ≤ M * ‖y‖ ^ 2) (y : E) :
    ∑ k, Complex.normSq (inner ℂ (w k) y)
      ≤ M * (‖y‖ ^ 2 - Complex.normSq (inner ℂ z y) / n) := by
  have h := hb (y - ((inner ℂ z y / (n : ℂ)) • z))
  rw [norm_sub_proj_sq hn hzn] at h
  refine le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl fun k _ => by
    rw [inner_sub_smul_of_orthogonal horth]

end Ortho

/-! ## Sharpening on an orthonormal family

The same argument with the single vector `z` replaced by a whole orthonormal
family: the Bessel sum then sees only the component of `y` off their span, and the
correction is the full Bessel sum of that family. -/

section OrthoFamily

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Pythagorean identity for the component of `y` off the span of an
orthonormal family. -/
theorem norm_sub_proj_family_sq {z : κ → E} (hz : Orthonormal ℂ z) (y : E) :
    ‖y - ∑ l, (inner ℂ (z l) y : ℂ) • z l‖ ^ 2
      = ‖y‖ ^ 2 - ∑ l, Complex.normSq (inner ℂ (z l) y) := by
  set c : κ → ℂ := fun l => inner ℂ (z l) y with hc
  set v : E := ∑ l, c l • z l with hv
  set S : ℝ := ∑ l, Complex.normSq (c l) with hS
  have hvv : (inner ℂ v v : ℂ) = (S : ℂ) := by
    rw [hv, sum_inner, hS, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun l _ => by
      rw [inner_smul_left, hz.inner_right_fintype c l, Complex.normSq_eq_conj_mul_self]
  have hyv : (inner ℂ y v : ℂ) = (S : ℂ) := by
    rw [hv, inner_sum, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, Complex.normSq_eq_conj_mul_self, hc,
      show (inner ℂ y (z l) : ℂ) = conj (inner ℂ (z l) y) from (inner_conj_symm _ _).symm]
    ring
  have hvnorm : ‖v‖ ^ 2 = S := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hvv] at h
    rw [← h]
    exact (Complex.ofReal_re _).symm
  have hre : RCLike.re (inner ℂ y v) = S := by rw [hyv]; exact Complex.ofReal_re _
  rw [norm_sub_sq (𝕜 := ℂ), hre, hvnorm]
  ring

/-- Bessel bound sharpened on the orthogonal complement of an orthonormal
family. -/
theorem frame_le_sub_proj_family {w : ι → E} {z : κ → E} (hz : Orthonormal ℂ z)
    (horth : ∀ (l : κ) (a : ι), inner ℂ (z l) (w a) = 0) {M : ℝ}
    (hb : ∀ y : E, ∑ a, Complex.normSq (inner ℂ (w a) y) ≤ M * ‖y‖ ^ 2) (y : E) :
    ∑ a, Complex.normSq (inner ℂ (w a) y)
      ≤ M * (‖y‖ ^ 2 - ∑ l, Complex.normSq (inner ℂ (z l) y)) := by
  have h := hb (y - ∑ l, (inner ℂ (z l) y : ℂ) • z l)
  rw [norm_sub_proj_family_sq hz] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun a _ => congrArg Complex.normSq ?_
  rw [inner_sub_right, inner_sum]
  have hzero : ∀ l : κ, (inner ℂ (w a) ((inner ℂ (z l) y : ℂ) • z l) : ℂ) = 0 := fun l => by
    rw [inner_smul_right,
      show (inner ℂ (w a) (z l) : ℂ) = 0 by rw [← inner_conj_symm, horth l a, map_zero], mul_zero]
  rw [Finset.sum_congr rfl fun l _ => hzero l, Finset.sum_const_zero, sub_zero]

end OrthoFamily

variable {W : Type*} [Fintype W] {s : ℕ}

/-- `‖δ_e‖² = s` for an orthonormal frame. -/
theorem norm_delta_orthonormal {e : Fin s → EuclideanSpace ℂ W}
    (he : Orthonormal ℂ e) : ‖delta e‖ ^ 2 = (s : ℝ) := by
  rw [norm_delta]
  simp [he.1]

end RankR
