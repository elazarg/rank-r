/-
Exact higher Choi constants for the double antisymmetrizer.

`KyFanAction.lean` proves the upper coefficient

  `beta_k(4 Qm) ≤ min(1, 4/k)` for `k ≥ 2`.

This file supplies the matching attaining witnesses.  The old two-term
extremizer handles `k = 2`; its three-term truncation from `Sharp.lean`
handles `k = 3`; and one full elementary double-skew tensor, of rank at most
four, handles every `k ≥ 4`.  Thus the valid constants are exactly the
reals above `min(1,4/k)`.
-/
import RankR.Applications.SchmidtWitness

namespace RankR

open Matrix Finset ComplexConjugate
open scoped Kronecker

section FullWitness

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- On a double-skew operator, the quadratic form of `Qm` is its squared
Hilbert--Schmidt norm because `Qm` fixes its vectorization. -/
theorem qform_Qm_vec_eq_hsNormSq_of_mem_doubleSkew
    {K : Matrix (U × V) (U × V) ℂ} (hK : K ∈ doubleSkew U V) :
    qform Qm (vec K) = (hsNormSq K : ℂ) := by
  rw [qform_eq_inner, mulVecE_Qm_vec hK,
    ← hsInner_eq_inner, hsInner_self]

omit [Fintype U] [Fintype V] in
/-- An elementary double-skew tensor with distinct labels in both factors is
nonzero. -/
theorem skewKraus_ne_zero_of_ne
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁) :
    skewKraus ((a₀, a₁), (b₀, b₁)) ≠ 0 := by
  intro h
  have hentry := congrArg
    (fun K : Matrix (U × V) (U × V) ℂ =>
      K (a₀, b₀) (a₁, b₁)) h
  simp [skewKraus, skewUnit_apply, ha, hb] at hentry

/-- The full four-term elementary tensor attains the `Qm` coefficient `1/k`
at every level `k ≥ 4`; its rank-four decomposition is padded by zeros when
`k > 4`. -/
theorem choiKAttained_Qm_of_four_le
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    {k : ℕ} (hk : 4 ≤ k) :
    ChoiKAttained (Qm : Matrix (Idx U V) (Idx U V) ℂ)
      k (1 / (k : ℝ)) := by
  let f : KIdx U V := ((a₀, a₁), (b₀, b₁))
  let K : Matrix (U × V) (U × V) ℂ := skewKraus f
  have hrank : K.rank ≤ k := by
    exact (show K.rank ≤ 4 by
      simpa [K] using
        rank_smul_skewKraus_le_four (U := U) (V := V) (1 : ℂ) f).trans hk
  have hne : K ≠ 0 := by
    simpa [K, f] using skewKraus_ne_zero_of_ne ha hb
  apply choiKAttained_of_matrix hrank hne
  have hmem : K ∈ doubleSkew U V := by
    simpa [K] using skewKraus_mem_doubleSkew f
  rw [qform_Qm_vec_eq_hsNormSq_of_mem_doubleSkew
    hmem, Complex.ofReal_re]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (show k ≠ 0 by omega)
  field_simp

end FullWitness

section ExactConstant

variable {U V : Type*} [Fintype U] [Fintype V]
  [DecidableEq U] [DecidableEq V]

/-- The manuscript-normalized coefficient `min(1,4/k)` is attained for every
`k ≥ 2` when both local factors have two distinct labels. -/
theorem choiKAttained_four_smul_Qm_min
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    {k : ℕ} (hk : 2 ≤ k) :
    ChoiKAttained
      ((4 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ))
      k (min 1 (4 / (k : ℝ))) := by
  rcases lt_or_ge k 3 with hklt | hk3
  · have hk2 : k = 2 := by omega
    subst k
    have h := choiKAttained_smul (t := 4)
      (choiKAttained_two_of_choiTwoAttained
        (choiTwoAttained_Qm ha hb))
    norm_num at h ⊢
    exact h
  · rcases eq_or_lt_of_le hk3 with rfl | hk4
    · have h := choiKAttained_smul (t := 4)
        (choiKAttained_Qm_three ha hb)
      norm_num at h ⊢
      exact h
    · have h := choiKAttained_smul (t := 4)
        (choiKAttained_Qm_of_four_le ha hb (by omega : 4 ≤ k))
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hfour : 4 / (k : ℝ) ≤ 1 := by
        rw [div_le_one hkR]
        exact_mod_cast (show 4 ≤ k by omega)
      rw [min_eq_right hfour]
      simpa [div_eq_mul_inv] using h

/-- **Exact higher Choi constants.**  At every level `k ≥ 2`, a real number is
a valid coefficient for the manuscript-normalized double antisymmetrizer
exactly when it is at least `min(1,4/k)`. -/
theorem choiKBound_four_smul_Qm_iff
    {a₀ a₁ : U} {b₀ b₁ : V} (ha : a₀ ≠ a₁) (hb : b₀ ≠ b₁)
    {k : ℕ} (hk : 2 ≤ k) (β : ℝ) :
    ChoiKBound
        ((4 : ℂ) • (Qm : Matrix (Idx U V) (Idx U V) ℂ))
        k β
      ↔ min 1 (4 / (k : ℝ)) ≤ β := by
  constructor
  · intro h
    exact le_of_choiKAttained (by omega)
      (choiKAttained_four_smul_Qm_min ha hb hk) h
  · intro h
    exact choiKBound_mono (choiKBound_four_smul_Qm_min hk) h

end ExactConstant

end RankR
