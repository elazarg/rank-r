/-
Assembly of Theorem 1.1 from Proposition 2.2.
-/
import RankR.Factor

namespace RankR

open Matrix Finset ComplexConjugate

section QFormAlgebra

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
theorem qform_add (A B : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (A + B) x = qform A x + qform B x := by
  simp only [qform, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

omit [DecidableEq W] in
theorem qform_sub (A B : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (A - B) x = qform A x - qform B x := by
  simp only [qform, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq W] in
theorem qform_smul (c : ℂ) (A : Matrix W W ℂ) (x : EuclideanSpace ℂ W) :
    qform (c • A) x = c * qform A x := by
  simp only [qform, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

theorem qform_one (x : EuclideanSpace ℂ W) :
    qform (1 : Matrix W W ℂ) x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h : qform (1 : Matrix W W ℂ) x = ∑ p, conj (x p) * x p := by
    simp only [qform, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  push_cast
  exact Finset.sum_congr rfl fun p _ => by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]

end QFormAlgebra

section Rank

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The factorization's index type has the manuscript's `r₀ = rank C`. -/
theorem finrank_range_toEuclideanLin (C : Matrix W W ℂ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) = C.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin C (EuclideanSpace.basisFun W ℂ).toBasis
    (EuclideanSpace.basisFun W ℂ).toBasis]
  rfl

/-- The range factorization, re-indexed by `C.rank`. -/
theorem exists_rankFactor_rank (C : Matrix W W ℂ) :
    ∃ e d : Fin C.rank → EuclideanSpace ℂ W, Orthonormal ℂ e ∧ C = rankFactor e d :=
  (finrank_range_toEuclideanLin C) ▸ exists_rankFactor C

end Rank

section Assembly

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {s : ℕ}

/-- `s² · H_r` of `eq:H_r`, scaled to clear denominators.

The manuscript's `H_r = I + (1/r)ρ - ρ_UQ ⊗ I_V - I_U ⊗ ρ_VQ` uses the
normalized `ρ = |ψ⟩⟨ψ|`, `ψ = δ_e/√s`.  Multiplying through by `s²` and writing
`ρ₀ = s·ρ = |δ_e⟩⟨δ_e|` removes every square root and every inverse; for `s > 0`
positivity of this operator is equivalent to positivity of `H_r`. -/
noncomputable def HopScaled (e : Fin s → EuclideanSpace ℂ (U × V)) :
    Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ :=
  ((s : ℂ) ^ 2) • (1 : Matrix ((U × V) × Fin s) ((U × V) × Fin s) ℂ)
    + rankOne (delta e) (delta e)
    - (s : ℂ) • placeUQ (margUQ (rankOne (delta e) (delta e)))
    - (s : ℂ) • placeVQ (margVQ (rankOne (delta e) (delta e)))

/-- **Proposition 2.2** (`prop:operator_ineq`), `H_r ⪰ 0`, in the scaled form. -/
def OperatorIneq (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Prop :=
  ∀ (s : ℕ), 0 < s → ∀ e : Fin s → EuclideanSpace ℂ (U × V), Orthonormal ℂ e →
    ∀ x : EuclideanSpace ℂ ((U × V) × Fin s), 0 ≤ (qform (HopScaled e) x).re

/-- The expectation of `HopScaled` against `δ_d`, via the four identities of
`lem:partial-trace-contractions`.  Stated as an equation in `ℂ` whose right side
is a real cast, so that taking `.re` is immediate. -/
theorem qform_HopScaled (e d : Fin s → EuclideanSpace ℂ (U × V)) :
    qform (HopScaled e) (delta d)
      = ((((s : ℝ) ^ 2 * ‖delta d‖ ^ 2
            + Complex.normSq ((rankFactor e d).trace)
            - s * hsNormSq (ptraceU (rankFactor e d))
            - s * hsNormSq (ptraceV (rankFactor e d))) : ℝ) : ℂ) := by
  rw [HopScaled, qform_sub, qform_sub, qform_add, qform_smul, qform_smul,
    qform_smul, qform_one, qform_rho_delta, qform_margUQ, qform_margVQ]
  push_cast
  ring

/-- **Theorem 1.1** (`thm:rank_r`), given Proposition 2.2.

`C` of rank at most `r` satisfies
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`. -/
theorem rank_r_of_operatorIneq (hOp : OperatorIneq U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (_hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace := by
  obtain ⟨e, d, he, hC⟩ := exists_rankFactor_rank C
  rcases Nat.eq_zero_or_pos C.rank with h0 | hpos
  · have huniv : (Finset.univ : Finset (Fin C.rank)) = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin]; exact h0
    have hC0 : C = 0 := by
      rw [hC]; ext p q; simp [rankFactor_apply, huniv]
    rw [hC0]; simp [hsNormSq]
  · have hnpos : (0 : ℝ) < (C.rank : ℝ) := by exact_mod_cast hpos
    have key := hOp C.rank hpos e he (delta d)
    rw [qform_HopScaled, Complex.ofReal_re, ← contraction_norm e d he] at key
    have htr : Complex.normSq (rankFactor e d).trace
        ≤ (C.rank : ℝ) * hsNormSq (rankFactor e d) := normSq_trace_le e d he
    have hinv2 : (C.rank : ℝ) * ((1 / (C.rank : ℝ)) *
        Complex.normSq (rankFactor e d).trace)
        = Complex.normSq (rankFactor e d).trace := by field_simp
    have step1 : hsNormSq (ptraceU (rankFactor e d)) + hsNormSq (ptraceV (rankFactor e d))
        ≤ (C.rank : ℝ) * hsNormSq (rankFactor e d)
          + (1 / (C.rank : ℝ)) * Complex.normSq (rankFactor e d).trace := by
      refine le_of_mul_le_mul_left ?_ hnpos
      rw [mul_add, mul_add, hinv2]
      nlinarith [key]
    rw [hC]
    exact step1.trans (rank_mono (hsNormSq_nonneg _) (Complex.normSq_nonneg _)
      hpos hrank htr)

end Assembly

end RankR
