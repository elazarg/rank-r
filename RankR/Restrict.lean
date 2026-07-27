/-
Sharpening a Bessel bound on a family orthogonal to a fixed vector.

If every member of a finite family is orthogonal to `z`, the family's Bessel sum
against `y` sees only the component of `y` off `z`, so the bound improves from
`M‖y‖²` to `M(‖y‖² − |⟪z,y⟫|²/‖z‖²)`.
-/
import RankR.Assemble

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

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

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- The frame vectors are orthogonal to `δ_e`. -/
theorem inner_delta_wvec (e : Fin s → EuclideanSpace ℂ (U × V))
    (f : KIdx U V) (p : Fin s × Fin s) :
    inner ℂ (delta e) (wvec e f p) = 0 := by
  rw [wvec]
  split
  · exact inner_delta_placeQ_kron_zetaV e (skewUnit_isSkew _ _) (skewUnit_isSkew _ _) _ _
  · simp

omit [DecidableEq U] [DecidableEq V] in
/-- `‖δ_e‖² = s` for an orthonormal frame. -/
theorem norm_delta_orthonormal {e : Fin s → EuclideanSpace ℂ (U × V)}
    (he : Orthonormal ℂ e) : ‖delta e‖ ^ 2 = (s : ℝ) := by
  rw [norm_delta]
  simp [he.1]

end RankR
