/-
Proposition 2.2 and Theorem 1.1.
-/
import RankR.Synthesis
import RankR.Restrict

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] {s : ℕ}

set_option maxHeartbeats 400000 in
/-- The Bessel bound for the frame `wvec`, sharpened on the orthogonal complement
of `δ_e`. -/
theorem qform_Phi4_Pneg_le (hFGP : DoubleSkewBound U V) (hs : 0 < s)
    {e : Fin s → EuclideanSpace ℂ (U × V)} (he : Orthonormal ℂ e)
    (y : EuclideanSpace ℂ ((U × V) × Fin s)) :
    (qform (Phi4 (Pneg e)) y).re
      ≤ 8 * ((s : ℝ) - 1) * (‖y‖ ^ 2 - Complex.normSq (inner ℂ (delta e) y) / s) := by
  have hM : (0 : ℝ) ≤ 8 * ((s : ℝ) - 1) := by
    have : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    linarith
  have hbess := frame_le_of_synthesis_le (fun k : KIdx U V × (Fin s × Fin s) => wvec e k.1 k.2)
      hM (norm_sum_smul_wvec_le hFGP he)
  have hsr : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hsharp := frame_le_sub_proj (w := fun k : KIdx U V × (Fin s × Fin s) => wvec e k.1 k.2)
    (z := delta e) hsr (norm_delta_orthonormal he)
    (fun k => inner_delta_wvec e k.1 k.2) hbess y
  have hre : (qform (Phi4 (Pneg e)) y).re
      = ∑ k : KIdx U V × (Fin s × Fin s),
          Complex.normSq (inner ℂ (wvec e k.1 k.2) y) := by
    rw [qform_Phi4_Pneg, Complex.re_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun f _ => by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun p _ => Complex.ofReal_re _
  rw [hre]
  exact hsharp

/-- **Proposition 2.2** (`prop:operator_ineq`), from the double-skew bound. -/
theorem operatorIneq_of_doubleSkew (hFGP : DoubleSkewBound U V) :
    OperatorIneq U V := by
  intro s hs e he x
  have hkey := qform_Phi4_Pneg_le hFGP hs he x
  have hpos : (0 : ℝ) ≤ (qform (Phi4 (Ppos e)) x).re :=
    qform_Phi4_nonneg (fun z => qform_Ppos_nonneg e z) x
  have hdecomp : (8 : ℂ) • HopScaled e
      = ((8 * (s : ℂ) * ((s : ℂ) - 1))) • (1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
        - ((8 * ((s : ℂ) - 1))) • rankOne (delta e) (delta e)
        + (s : ℂ) • (Phi4 (Ppos e) - Phi4 (Pneg e)) := by
    have h4 := HopScaled_eq e he
    have hps : Phi4 (Ppos e) - Phi4 (Pneg e)
        = (2 : ℂ) • Phi4 (ptransposeUV (rankOne (delta e) (delta e))) := by
      rw [← Phi4_sub, Ppos_sub_Pneg, Phi4_smul]
    rw [hps]
    have h8 : (8 : ℂ) • HopScaled e = (2 : ℂ) • ((4 : ℂ) • HopScaled e) := by
      rw [smul_smul]; norm_num
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
      ≤ 8 * (s : ℝ) * ((s : ℝ) - 1) * ‖x‖ ^ 2
        - 8 * ((s : ℝ) - 1) * Complex.normSq (inner ℂ (delta e) x) := by
    have h := mul_le_mul_of_nonneg_left hkey hsr.le
    refine h.trans (le_of_eq ?_)
    field_simp
  have hsp : (0 : ℝ) ≤ (s : ℝ) * (qform (Phi4 (Ppos e)) x).re :=
    mul_nonneg hsr.le hpos
  linarith [hq, hkey', hsp]

/-- **Theorem 1.1** (`thm:rank_r`).  For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`.

`hFGP` is the Fu-Gao-Park import, carried as a hypothesis rather than an
`axiom`, so `#print axioms` remains meaningful and the dependency is visible in
the type. -/
theorem rank_r_partial_trace (hFGP : DoubleSkewBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_of_operatorIneq (operatorIneq_of_doubleSkew hFGP) C r hr hrank

end RankR
