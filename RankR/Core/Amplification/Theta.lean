/-
The Choi-form predicate used by pair amplification.

For a Kraus family `A`, `ThetaPositive A R λ` is the rank-`R` positivity
condition for the corrected transposed Kraus map.  The graph and other client
families instantiate this interface in separate modules.
-/
import RankR.Library.Matrix.Rank

namespace RankR

open Matrix Finset ComplexConjugate

section Theta

variable {W : Type*} [Fintype W] [DecidableEq W] {ι : Type*} [Fintype ι]

/-- `⟪vec C, J(Φ_A ∘ τ) vec C⟫`, the Choi pairing of the transposed Kraus sum. -/
noncomputable def thetaPair (A : ι → Matrix W W ℂ) (C : Matrix W W ℂ) : ℂ :=
  ∑ a, hsInner (A a * C) ((A a * C)ᵀ)

/-- An identically zero Kraus family contributes no Choi pairing. -/
@[simp]
theorem thetaPair_zero (C : Matrix W W ℂ) :
    thetaPair (fun _ : ι => (0 : Matrix W W ℂ)) C = 0 := by
  rw [thetaPair]
  apply Finset.sum_eq_zero
  intro a _
  simp [hsInner]

/-- **`R`-positivity of `Θ^Φ_{R,λ}`**, in Choi form and with each term unrolled.

`Δ_d` contributes `‖C‖₂²` and `id` contributes `|Tr C|²`, so the correction is
`λ(‖C‖₂² - |Tr C|²/R)`. -/
def ThetaPositive (A : ι → Matrix W W ℂ) (R : ℕ) (lam : ℝ) : Prop :=
  ∀ C : Matrix W W ℂ, C.rank ≤ R →
    0 ≤ (thetaPair A C).re + lam * (hsNormSq C - Complex.normSq C.trace / R)

/-- The unprotected Choi-form positivity condition, with correction
`λ ‖C‖₂²` and no trace direction removed. -/
def ThetaUnprotectedPositive
    (A : ι → Matrix W W ℂ) (R : ℕ) (lam : ℝ) : Prop :=
  ∀ C : Matrix W W ℂ, C.rank ≤ R →
    0 ≤ (thetaPair A C).re + lam * hsNormSq C

/-- At zero correction, the corrected form of an identically zero Kraus
family is the tautological zero quadratic form. -/
theorem thetaPositive_zero (R : ℕ) :
    ThetaPositive (fun _ : ι => (0 : Matrix W W ℂ)) R 0 := by
  intro C _
  simp

omit [DecidableEq W] in
/-- The correction term is nonnegative at rank `R`, by the trace-rank bound. -/
theorem correction_nonneg {C : Matrix W W ℂ} {R : ℕ}
    (hR : 0 < R) (hrank : C.rank ≤ R) :
    0 ≤ hsNormSq C - Complex.normSq C.trace / R := by
  have htr : Complex.normSq C.trace ≤ (C.rank : ℝ) * hsNormSq C :=
    normSq_trace_le_rank C
  have hRr : (C.rank : ℝ) ≤ R := by exact_mod_cast hrank
  have hn : (0 : ℝ) ≤ hsNormSq C := hsNormSq_nonneg C
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  rw [sub_nonneg, div_le_iff₀ hRpos]
  nlinarith

omit [DecidableEq W] in
/-- **`ThetaPositive` is monotone in `λ`.**  As with `choiTwoBound_mono`, this is
why the condition alone determines no number: the threshold needs a witness at
the other end. -/
theorem thetaPositive_mono {A : ι → Matrix W W ℂ} {R : ℕ}
    (hR : 0 < R) {lam lam' : ℝ}
    (h : ThetaPositive A R lam) (hle : lam ≤ lam') :
    ThetaPositive A R lam' := by
  intro C hrank
  have hc := correction_nonneg (C := C) hR hrank
  have := h C hrank
  nlinarith

end Theta

end RankR
