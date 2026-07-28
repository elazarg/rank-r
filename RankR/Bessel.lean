/-
Bessel-type duality: a uniform bound on the synthesis operator of a finite family
transfers to the same bound on its analysis operator.

No square roots are needed.  The synthesis bound is tested on the coefficient
vector `c k = ⟪w k, y⟫` itself, for which the pairing `⟪∑ k, c k • w k, y⟫` equals
the real number `∑ k, |c k|²`; Cauchy-Schwarz then yields `S² ≤ (M · S) ‖y‖²`, and
one factor of `S` cancels.
-/
import RankR.Conventions

namespace RankR

open Matrix Finset ComplexConjugate

/-! ## Synthesis bounds imply frame bounds -/

/-- A uniform bound on the synthesis operator of a finite family is inherited by the
analysis operator: if `‖∑ k, c k • w k‖² ≤ M ∑ k |c k|²` for every coefficient
vector `c`, then `∑ k |⟪w k, y⟫|² ≤ M ‖y‖²` for every `y`.

Testing the hypothesis at `c k = ⟪w k, y⟫` makes the synthesized vector `v` pair
with `y` to the real number `S = ∑ k |c k|²`, so `S ≤ ‖v‖ ‖y‖` and therefore
`S² ≤ ‖v‖² ‖y‖² ≤ (M S) ‖y‖²`. -/
theorem frame_le_of_synthesis_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w : ι → E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ c : ι → ℂ, ‖∑ k, c k • w k‖ ^ 2 ≤ M * ∑ k, Complex.normSq (c k))
    (y : E) :
    ∑ k, Complex.normSq (inner ℂ (w k) y) ≤ M * ‖y‖ ^ 2 := by
  set c : ι → ℂ := fun k => inner ℂ (w k) y with hcdef
  set S : ℝ := ∑ k, Complex.normSq (c k) with hSdef
  set v : E := ∑ k, c k • w k with hvdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _
  have hinner : (inner ℂ v y : ℂ) = (S : ℂ) := by
    rw [hvdef, sum_inner, hSdef, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, Complex.normSq_eq_conj_mul_self, hcdef]
  have hcs : S ≤ ‖v‖ * ‖y‖ := by
    have hle := norm_inner_le_norm (𝕜 := ℂ) v y
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0] at hle
    exact hle
  have hsyn : ‖v‖ ^ 2 ≤ M * S := h c
  have hy0 : (0 : ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  have hsq : S ^ 2 ≤ (M * S) * ‖y‖ ^ 2 := by
    have h1 : S ^ 2 ≤ (‖v‖ * ‖y‖) ^ 2 := by
      have := mul_nonneg (norm_nonneg v) (norm_nonneg y)
      nlinarith
    nlinarith [norm_nonneg v]
  rcases eq_or_lt_of_le hS0 with hz | hpos
  · rw [← hz]
    positivity
  · nlinarith

end RankR
