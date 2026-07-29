/-
The double-skew specialization of exterior amplification.

The ordered-pair Kraus family `skewKraus` represents four times
`Λ_U ⊗ Λ_V`; scaling every Kraus operator by `1/2` gives the manuscript's
normalization and Choi operator `4 Qm`.  Combining the exact higher Choi
constant with Theorem B of `HigherArity.lean` yields the claimed complete
hypergraph inequality with coefficient

  `(r - k + 1) min(1, 4/k)`.
-/
import RankR.HigherArity
import RankR.HigherChoiSharp

namespace RankR

open Matrix Finset ComplexConjugate

section NormalizedFamily

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- The ordered elementary double-skew Kraus family in the normalization of
`Λ_U ⊗ Λ_V`, rather than the fourfold normalization `Phi4`. -/
noncomputable def normalizedSkewKraus (f : KIdx U V) :
    Matrix (U × V) (U × V) ℂ :=
  (1 / 2 : ℂ) • skewKraus f

/-- The Choi operator of the normalized family is `4 Qm`. -/
theorem choiOf_normalizedSkewKraus :
    choiOf (normalizedSkewKraus (U := U) (V := V))
      = (4 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ) := by
  calc
    choiOf (normalizedSkewKraus (U := U) (V := V)) =
        (1 / 4 : ℂ) • choiOf (skewKraus (U := U) (V := V)) := by
      ext X Y
      simp only [choiOf, normalizedSkewKraus, Matrix.sum_apply,
        rankOne, Matrix.of_apply, vec_smul, PiLp.smul_apply,
        Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      simp only [one_div, vec_apply, map_inv₀, map_ofNat]
      ring
    _ = (4 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ) := by
      rw [choiOf_skewKraus]
      ext X Y
      simp only [one_div, Matrix.smul_apply, Qm_apply, smul_eq_mul,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_inv_cancel_left₀]
      ring

omit [Fintype U] [Fintype V] in
/-- Every normalized double-skew Kraus operator is transpose-symmetric. -/
theorem normalizedSkewKraus_transpose (f : KIdx U V) :
    (normalizedSkewKraus f)ᵀ = normalizedSkewKraus f := by
  rw [normalizedSkewKraus, Matrix.transpose_smul, skewKraus_transpose]

end NormalizedFamily

section ExteriorSpecialization

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]
  {r k : ℕ}

/-- Exterior amplification for the normalized double-skew family on an
arbitrary `k`-uniform hypergraph, with the universal level-`k` Choi
coefficient.  `choiKBound_four_smul_Qm_iff` proves this coefficient is exact
when both local factors contain two distinct labels; the inequality itself
also applies in degenerate dimensions. -/
theorem qform_normalizedSkewKraus_Phyp_le
    (hk : 2 ≤ k) (hkr : k ≤ r)
    {e : Fin r → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (H : Finset (Face r k))
    (y : EuclideanSpace ℂ ((U × V) × Face r (k - 1))) :
    (qform
        (krausF (normalizedSkewKraus (U := U) (V := V)) (Phyp e H)) y).re
      ≤ (upDeg H : ℝ) * min 1 (4 / (k : ℝ))
          * (‖y‖ ^ 2
            - ∑ L : Face r (k - 2),
                Complex.normSq (inner ℂ (deltaMode (k := k) e L) y)) := by
  have hβ : 0 ≤ min 1 (4 / (k : ℝ)) := by
    apply le_min
    · norm_num
    · positivity
  apply qform_krausF_Phyp_le hβ
  · rw [choiOf_normalizedSkewKraus]
    exact choiKBound_four_smul_Qm_min hk
  · intro f
    exact isFrameSymmetric_of_transpose_eq
      (normalizedSkewKraus_transpose f) e
  · exact hk
  · exact hkr
  · exact he

/-- **The double-skew complete-hypergraph corollary.**  The largest facet
degree is `r-k+1`, giving precisely the coefficient stated in the higher-arity
note.  No nondegeneracy hypothesis is needed for this upper bound. -/
theorem qform_normalizedSkewKraus_Phyp_univ_le
    (hk : 2 ≤ k) (hkr : k ≤ r)
    {e : Fin r → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Face r (k - 1))) :
    (qform
        (krausF (normalizedSkewKraus (U := U) (V := V))
          (Phyp e (Finset.univ : Finset (Face r k)))) y).re
      ≤ ((r - k + 1 : ℕ) : ℝ) * min 1 (4 / (k : ℝ))
          * (‖y‖ ^ 2
            - ∑ L : Face r (k - 2),
                Complex.normSq (inner ℂ (deltaMode (k := k) e L) y)) := by
  have h := qform_normalizedSkewKraus_Phyp_le hk hkr he
    (Finset.univ : Finset (Face r k)) y
  rw [upDeg_univ (by omega) hkr] at h
  exact h

end ExteriorSpecialization

end RankR
