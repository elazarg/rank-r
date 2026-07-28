/-
Assembly of Theorem 1.1 from Proposition 2.2.
-/
import RankR.Factor
import Mathlib.LinearAlgebra.Matrix.Rank

namespace RankR

open Matrix Finset ComplexConjugate

section Rank

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The factorization's index type has the manuscript's `r₀ = rank C`. -/
theorem finrank_range_toEuclideanLin (C : Matrix W W ℂ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin C)) = C.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin C (EuclideanSpace.basisFun W ℂ).toBasis
    (EuclideanSpace.basisFun W ℂ).toBasis]
  rfl

omit [DecidableEq W] in
/-- The range factorization, re-indexed by `C.rank`.

`Matrix.rank` decides no equality, so neither does this statement: the
`DecidableEq` of `exists_rankFactor` is an artifact of `Matrix.toEuclideanLin`,
which appears only in the proof.  Everything downstream of this lemma is free of
it. -/
theorem exists_rankFactor_rank (C : Matrix W W ℂ) :
    ∃ e d : Fin C.rank → EuclideanSpace ℂ W, Orthonormal ℂ e ∧ C = rankFactor e d := by
  classical
  exact (finrank_range_toEuclideanLin C) ▸ exists_rankFactor C

omit [DecidableEq W] in
/-- Rank `0` means the empty range factorization, hence the zero matrix. -/
theorem eq_zero_of_rank_eq_zero {C : Matrix W W ℂ} (h : C.rank = 0) : C = 0 := by
  obtain ⟨e, d, _, hC⟩ := exists_rankFactor_rank C
  have huniv : (Finset.univ : Finset (Fin C.rank)) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_univ, Fintype.card_fin]; exact h
  rw [hC]; ext p q; simp [rankFactor_apply, huniv]

omit [DecidableEq W] in
theorem rank_pos_of_ne_zero {C : Matrix W W ℂ} (h : C ≠ 0) : 0 < C.rank :=
  Nat.pos_of_ne_zero fun h0 => h (eq_zero_of_rank_eq_zero h0)

omit [DecidableEq W] in
/-- The trace-rank bound `|Tr C|² ≤ (rank C)‖C‖₂²`, stated for `C` itself.
This is `normSq_trace_le` transported along the range factorization. -/
theorem normSq_trace_le_rank (C : Matrix W W ℂ) :
    Complex.normSq C.trace ≤ (C.rank : ℝ) * hsNormSq C := by
  obtain ⟨e, d, he, hC⟩ := exists_rankFactor_rank C
  have h := normSq_trace_le e d he
  rwa [← hC] at h

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

/-- **Theorem 1.1 at the exact rank** (`eq:main-bound-exact-rank`), given
Proposition 2.2: the inequality with `r = rank C`, which is where the operator
inequality is actually applied.  No hypothesis on `C` is needed — for `C = 0`
both sides vanish, `1/0` being `0`. -/
theorem rank_r_of_operatorIneq_exact (hOp : OperatorIneq U V)
    (C : Matrix (U × V) (U × V) ℂ) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp [hsNormSq]
  · obtain ⟨e, d, he, hfac⟩ := exists_rankFactor_rank C
    have hpos := rank_pos_of_ne_zero hC
    have hnpos : (0 : ℝ) < (C.rank : ℝ) := by exact_mod_cast hpos
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
    rwa [← hfac] at step1

/-- **Theorem 1.1** (`thm:rank_r`), given Proposition 2.2.

`C` of rank at most `r` satisfies
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`.

No positivity hypothesis on `r` is needed: `r = 0` forces `C = 0` through
`hrank`, and then both sides vanish, `1/0` being `0`. -/
theorem rank_r_of_operatorIneq (hOp : OperatorIneq U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp [hsNormSq]
  · exact (rank_r_of_operatorIneq_exact hOp C).trans
      (rank_mono (Complex.normSq_nonneg _) (rank_pos_of_ne_zero hC)
        hrank (normSq_trace_le_rank C))

/-- **Strictness below the exact rank** (`sec:proof`): for nonzero `C` of rank
strictly less than `r`, the rank-`r` bound is strict.  This is the last step of
the proof of `thm:rank_r`, where `eq:rank-monotonicity` is applied with
`r₀ < r`. -/
theorem rank_r_of_operatorIneq_strict (hOp : OperatorIneq U V)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  (rank_r_of_operatorIneq_exact hOp C).trans_lt
    (rank_mono_strict (hsNormSq_pos hC) (rank_pos_of_ne_zero hC) hrank
      (normSq_trace_le_rank C))

/-- **Equality forces the exact rank** (`thm:rank_r`, sharpness paragraph):
for nonzero `C`, equality in the rank-`r` inequality requires `rank C = r`.
The contrapositive of `rank_r_of_operatorIneq_strict`. -/
theorem rank_eq_of_eq_rank_r_of_operatorIneq (hOp : OperatorIneq U V)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  le_antisymm hrank <| Nat.le_of_not_lt fun hlt =>
    absurd heq (rank_r_of_operatorIneq_strict hOp C hC r hlt).ne

end Assembly

end RankR
