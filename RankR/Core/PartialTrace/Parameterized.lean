/-
Proposition 2.2 and Theorem 1.1, from the rank-two bound on the Choi operator of
`Λ_U ⊗ Λ_V`.

`Lifting.lean` supplies form (A) for an arbitrary transpose-symmetric Kraus
family; `ChoiSkew.lean` supplies the family and its constant `β = 4`.  What is
left here is the assembly of `eq:H_r`: the positive sector survives the Kraus
sum, `Ppos − Pneg` is twice the partial transpose, and `HopScaled_eq` trades the
two marginal terms for an identity term and a multiple of `ρ₀`.
-/
import RankR.Core.DoubleSkew.Choi
import RankR.Core.Amplification.OperatorForms
import RankR.Core.PartialTrace.DoubleSkew

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

/-- `Phi4` is the amplified Kraus sum of the double-skew family. -/
theorem Phi4_eq_krausQ (Y : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ) :
    Phi4 Y = krausQ skewKraus Y := rfl

/-- **Lifting II for the double-skew family with the Choi constant left
free.**  The development's `Phi4` normalization is four times the manuscript's
map normalization, so the manuscript's `β₂` is `β / 4` here. -/
theorem qform_Phi4_Pneg_le_param {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) β)
    (hs : 0 < s) {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    (qform (Phi4 (Pneg e)) y).re
      ≤ 2 * β * ((s : ℝ) - 1)
        * (‖y‖ ^ 2 - Complex.normSq (inner ℂ (delta e) y) / s) := by
  rw [Phi4_eq_krausQ]
  exact qform_krausQ_Pneg_le hβ0 hβ
    (fun f => isFrameSymmetric_of_transpose_eq (skewKraus_transpose f) e) hs he y

/-- **Lifting II for the double-skew family** (`eq:Phi-Pminus-goal`): form (A) at
`β = 4`, the value `choiOf_skewKraus` computes for `Λ_U ⊗ Λ_V` in the
normalization `Phi4`. -/
theorem qform_Phi4_Pneg_le (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (hs : 0 < s) {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    (qform (Phi4 (Pneg e)) y).re
      ≤ 8 * ((s : ℝ) - 1) * (‖y‖ ^ 2 - Complex.normSq (inner ℂ (delta e) y) / s) := by
  exact (qform_Phi4_Pneg_le_param (by norm_num) hβ hs he y).trans
    (le_of_eq (by ring))

/-- The contraction-ready form of the parameterized double-skew estimate.
For `β = 4` its left side vanishes and this is Proposition 2.2.  Leaving `β`
free records the exact residual that changes the two coefficients in
`eq:main-bound-parametrized`. -/
theorem qform_HopScaled_param
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) β)
    (hs : 0 < s) {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (x : EuclideanSpace ℂ ((U × V) × Fin s)) :
    2 * ((s : ℝ) - 1) * (4 - β)
        * ((s : ℝ) * ‖x‖ ^ 2 - Complex.normSq (inner ℂ (delta e) x))
      ≤ 8 * (qform (HopScaled e) x).re := by
  have hkey := qform_Phi4_Pneg_le_param hβ0 hβ hs he x
  have hpos : (0 : ℝ) ≤ (qform (Phi4 (Ppos e)) x).re :=
    qform_Phi4_nonneg (fun z => qform_Ppos_nonneg e z) x
  have hdecomp : (8 : ℂ) • HopScaled e
      = ((8 * (s : ℂ) * ((s : ℂ) - 1))) •
          (1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
        - ((8 * ((s : ℂ) - 1))) • rankOne (delta e) (delta e)
        + (s : ℂ) • (Phi4 (Ppos e) - Phi4 (Pneg e)) := by
    have h4 := HopScaled_eq e he
    have hps : Phi4 (Ppos e) - Phi4 (Pneg e)
        = (2 : ℂ) • Phi4 (ptransposeUV (rankOne (delta e) (delta e))) := by
      rw [← Phi4_sub, Ppos_sub_Pneg, Phi4_smul]
    rw [hps]
    have h8 : (8 : ℂ) • HopScaled e = (2 : ℂ) • ((4 : ℂ) • HopScaled e) := by
      rw [smul_smul]
      norm_num
    rw [h8, h4]
    ext p q
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hq : (8 : ℝ) * (qform (HopScaled e) x).re
      = 8 * (s : ℝ) * ((s : ℝ) - 1) * ‖x‖ ^ 2
        - 8 * ((s : ℝ) - 1) * Complex.normSq (inner ℂ (delta e) x)
        + ((s : ℝ) * (qform (Phi4 (Ppos e)) x).re
           - (s : ℝ) * (qform (Phi4 (Pneg e)) x).re) := by
    have := congrArg (fun A => qform A x) hdecomp
    simp only [qform_smul, qform_add, qform_sub, qform_one, qform_rankOne] at this
    have hre := congrArg Complex.re this
    simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im,
      ← Complex.ofReal_pow, mul_sub] using hre
  have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hkey' : (s : ℝ) * (qform (Phi4 (Pneg e)) x).re
      ≤ 2 * β * (s : ℝ) * ((s : ℝ) - 1) * ‖x‖ ^ 2
        - 2 * β * ((s : ℝ) - 1) * Complex.normSq (inner ℂ (delta e) x) := by
    have h := mul_le_mul_of_nonneg_left hkey hsr.le
    refine h.trans (le_of_eq ?_)
    field_simp
  have hsp : (0 : ℝ) ≤ (s : ℝ) * (qform (Phi4 (Ppos e)) x).re :=
    mul_nonneg hsr.le hpos
  nlinarith [hq, hkey', hsp]

/-- `eq:main-bound-parametrized` for an explicit range factorization.
The paper's normalized constant is `β / 4`, because `Phi4 = 4 Φ`. -/
theorem rankFactor_partial_trace_le_param
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) β)
    (hs : 0 < s) (e d : Fin s → EuclideanSpace ℂ (U × V)) (he : Orthonormal ℂ e) :
    hsNormSq (ptraceU (rankFactor e d)) + hsNormSq (ptraceV (rankFactor e d))
      ≤ ((s : ℝ) + (β / 4 - 1) * ((s : ℝ) - 1)) * hsNormSq (rankFactor e d)
        + (1 - (β / 4 - 1) * ((s : ℝ) - 1)) * (1 / (s : ℝ))
          * Complex.normSq (rankFactor e d).trace := by
  have key := qform_HopScaled_param hβ0 hβ hs he (delta d)
  rw [inner_delta_delta, Complex.normSq_conj, qform_HopScaled, Complex.ofReal_re,
    ← contraction_norm e d he] at key
  have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 8 * s by positivity)
  field_simp
  nlinarith [key]

/-- **Proposition 2.2** (`prop:operator_ineq`), from the rank-two Choi bound. -/
theorem operatorIneq_of_choiTwoBound
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4) :
    OperatorIneq U V := by
  intro s hs e he x
  have h := qform_HopScaled_param (β := 4) (by norm_num) hβ hs he x
  norm_num at h
  linarith

/-- **The parameterized exact-rank partial-trace inequality**
(`eq:main-bound-parametrized`).  In the manuscript's normalization the
constant is `β₂ = β / 4`; the nonzero hypothesis ensures that the exact rank in
the denominators is positive. -/
theorem rank_r_partial_trace_exact_of_choiTwoBound_param
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) β)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ ((C.rank : ℝ) + (β / 4 - 1) * ((C.rank : ℝ) - 1)) * hsNormSq C
        + (1 - (β / 4 - 1) * ((C.rank : ℝ) - 1)) * (1 / (C.rank : ℝ))
          * Complex.normSq C.trace := by
  obtain ⟨e, d, he, hfac⟩ := exists_rankFactor_rank C
  have h := rankFactor_partial_trace_le_param hβ0 hβ (rank_pos_of_ne_zero hC) e d he
  rwa [← hfac] at h

/-- `eq:main-bound-parametrized` in exactly the manuscript's `β₂`
normalization. -/
theorem rank_r_partial_trace_exact_of_betaTwo
    {β₂ : ℝ} (hβ0 : 0 ≤ β₂)
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) (4 * β₂))
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ ((C.rank : ℝ) + (β₂ - 1) * ((C.rank : ℝ) - 1)) * hsNormSq C
        + (1 - (β₂ - 1) * ((C.rank : ℝ) - 1)) * (1 / (C.rank : ℝ))
          * Complex.normSq C.trace := by
  have h := rank_r_partial_trace_exact_of_choiTwoBound_param
    (β := 4 * β₂) (mul_nonneg (by norm_num) hβ0) hβ C hC
  convert h using 1
  ring

/-- **Theorem 1.1** (`thm:rank_r`).  For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`.

`hβ` is the rank-two bound on the Choi operator of `Λ_U ⊗ Λ_V`, a hypothesis
rather than an `axiom`, so the dependency is visible in the type. -/
theorem rank_r_partial_trace_of_choiTwoBound
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_of_operatorIneq (operatorIneq_of_choiTwoBound hβ) C r hrank

/-- **The exact-rank form** (`eq:main-bound-exact-rank`). -/
theorem rank_r_partial_trace_exact_of_choiTwoBound
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (C : Matrix (U × V) (U × V) ℂ) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace :=
  rank_r_of_operatorIneq_exact (operatorIneq_of_choiTwoBound hβ) C

/-- **Strictness below the exact rank** (`sec:proof`). -/
theorem rank_r_partial_trace_strict_of_choiTwoBound
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_of_operatorIneq_strict (operatorIneq_of_choiTwoBound hβ) C hC r hrank

/-- **Equality forces the exact rank** (`thm:rank_r`, sharpness paragraph). -/
theorem rank_eq_of_eq_rank_r_partial_trace_of_choiTwoBound
    (hβ : ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  rank_eq_of_eq_rank_r_of_operatorIneq (operatorIneq_of_choiTwoBound hβ) C hC r hrank heq

end RankR
