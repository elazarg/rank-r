/-
The Fu–Gao–Park double-antisymmetric projection estimate, and the derivation of
the double-skew action bound from it.

Writing `P` for the orthogonal projection onto the span of the orthonormal pair
`x, y`, the quantity to be bounded is `‖KP‖₂²`, and `KP` is the sum of the two
rank-one operators `|Kx⟩⟨x|` and `|Ky⟩⟨y|`.  The estimate therefore applies to
`vec (KP)` directly, and singular values play no part.
-/
import RankR.Antisym
import RankR.Choi
import RankR.Theorem

namespace RankR

open Matrix Finset ComplexConjugate

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- **Fu–Gao–Park**, Theorem 2.4 of arXiv:2607.21367.

A pure state on `(ℂ^d)^{⊗4}` has Schmidt rank at most two across the `12:34`
cut exactly when it is `vec (|u₁⟩⟨v₁| + |u₂⟩⟨v₂|)`; quantifying over the four
vectors is that condition unrolled.  The equivalence is
`fgpBound_iff_pureSchmidtKBound_two`.  With the index of `vec` read as
`(U_out, V_out, U_in, V_in)`, the
antisymmetrized pairs of `Qm` are Fu–Gao–Park's `(1,3)` and `(2,4)` and the
row:col cut is their `12:34`. -/
def FGPBound (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Prop :=
  ∀ u₁ v₁ u₂ v₂ : EuclideanSpace ℂ (U × V),
    (qform Qm (vec (rankOne u₁ v₁ + rankOne u₂ v₂))).re
      ≤ hsNormSq (rankOne u₁ v₁ + rankOne u₂ v₂) / 2

/-- **Fu–Gao–Park's estimate is the rank-two Choi bound at `β = ¼`.**

`FGPBound` bounds `‖Qm‖_{S(2)}` by `½`, which is `β = ¼` for the projection
itself.  The double-skew Kraus family has Choi operator `16 Qm`
(`choiOf_skewKraus`), hence `β = 4`: the constant `8 = 2β` of
`norm_sum_smul_wvec_le` is read off the Choi operator. -/
theorem choiTwoBound_Qm_iff :
    ChoiTwoBound (Qm : Matrix (Idx U V) (Idx U V) ℂ) (1 / 4) ↔ FGPBound U V := by
  constructor <;> · intro h u₁ v₁ u₂ v₂; have := h u₁ v₁ u₂ v₂; linarith

/-- The constant of the double-skew family, from Fu–Gao–Park. -/
theorem choiTwoBound_of_FGP (hFGP : FGPBound U V) :
    ChoiTwoBound (choiOf (skewKraus (U := U) (V := V))) 4 :=
  choiTwoBound_skewKraus (choiTwoBound_Qm_iff.mpr hFGP)

/-- **Proposition 2.2** (`prop:operator_ineq`), from Fu–Gao–Park. -/
theorem operatorIneq_of_FGP (hFGP : FGPBound U V) : OperatorIneq U V :=
  operatorIneq_of_choiTwoBound (choiTwoBound_of_FGP hFGP)

/-- The double-skew action bound, from Fu–Gao–Park. -/
theorem doubleSkewBound_of_FGP (hFGP : FGPBound U V) : DoubleSkewBound U V := by
  intro K hK x y hx hy hxy
  rw [← mulVecE_eq_toEuclideanLin, ← mulVecE_eq_toEuclideanLin]
  have hyx : (inner ℂ y x : ℂ) = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have hxx : (inner ℂ x x : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hyy : (inner ℂ y y : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  have hKP : K * proj2 x y
      = rankOne (mulVecE K x) x + rankOne (mulVecE K y) y := mul_proj2 K x y
  -- the action equals the Hilbert–Schmidt norm of `K P`
  have hact : hsNormSq (K * proj2 x y)
      = ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2 := hsNormSq_mul_proj2 K hx hy hxy
  -- `⟪K, K P⟫ = ‖K P‖₂²`, using that `P` is a self-adjoint idempotent
  have hKM : hsInner K (K * proj2 x y) = (hsNormSq (K * proj2 x y) : ℂ) :=
    hsInner_mul_proj2 K hx hy hxy
  -- Cauchy–Schwarz against `Qm (vec (K P))`
  have hA0 : 0 ≤ hsNormSq (K * proj2 x y) := hsNormSq_nonneg _
  have hQsa : (Qm (U := U) (V := V))ᴴ = Qm := Qm_conjTranspose
  have hmove : inner ℂ (vec K) (mulVecE Qm (vec (K * proj2 x y)))
      = (hsNormSq (K * proj2 x y) : ℂ) := by
    rw [inner_mulVecE_left, hQsa, mulVecE_Qm_vec hK, ← hsInner_eq_inner, hKM]
  have hnormQ : ‖mulVecE Qm (vec (K * proj2 x y))‖ ^ 2
      ≤ hsNormSq (K * proj2 x y) / 2 := by
    have key := inner_mulVecE_left (Qm (U := U) (V := V)) (vec (K * proj2 x y))
      (mulVecE Qm (vec (K * proj2 x y)))
    rw [mulVecE_mul, Qm_mul_self, hQsa] at key
    have h1 : ‖mulVecE Qm (vec (K * proj2 x y))‖ ^ 2
        = (qform Qm (vec (K * proj2 x y))).re := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), qform_eq_inner, ← key]
      rfl
    rw [h1, hKP]
    exact hFGP (mulVecE K x) x (mulVecE K y) y
  have hcs : hsNormSq (K * proj2 x y)
      ≤ ‖vec K‖ * ‖mulVecE Qm (vec (K * proj2 x y))‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (vec K) (mulVecE Qm (vec (K * proj2 x y)))
    rwa [hmove, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0] at h
  have hKn : ‖vec K‖ ^ 2 = hsNormSq K := (hsNormSq_eq_norm_sq K).symm
  rw [← hact]
  nlinarith [hcs, hnormQ, hKn, hA0, norm_nonneg (vec K),
    norm_nonneg (mulVecE Qm (vec (K * proj2 x y)))]

/-- **Theorem 1.1, from Fu–Gao–Park.**  For `C` of rank at most `r`,
`‖Tr_U C‖₂² + ‖Tr_V C‖₂² ≤ r‖C‖₂² + (1/r)|Tr C|²`.

The only hypothesis is `FGPBound`, the double-antisymmetric projection estimate
of Fu–Gao–Park; nothing else is assumed. -/
theorem rank_r_partial_trace_of_FGP (hFGP : FGPBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_of_choiTwoBound (choiTwoBound_of_FGP hFGP) C r hrank

/-- **The exact-rank form** (`eq:main-bound-exact-rank`), from Fu–Gao–Park. -/
theorem rank_r_partial_trace_of_FGP_exact (hFGP : FGPBound U V)
    (C : Matrix (U × V) (U × V) ℂ) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ (C.rank : ℝ) * hsNormSq C + (1 / (C.rank : ℝ)) * Complex.normSq C.trace :=
  rank_r_partial_trace_exact_of_choiTwoBound (choiTwoBound_of_FGP hFGP) C

/-- **Strictness below the exact rank**, from Fu–Gao–Park. -/
theorem rank_r_partial_trace_of_FGP_strict (hFGP : FGPBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank < r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      < r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace_strict_of_choiTwoBound (choiTwoBound_of_FGP hFGP) C hC r hrank

/-- **Equality forces the exact rank**, from Fu–Gao–Park. -/
theorem rank_eq_of_eq_rank_r_partial_trace_of_FGP (hFGP : FGPBound U V)
    (C : Matrix (U × V) (U × V) ℂ) (hC : C ≠ 0) (r : ℕ) (hrank : C.rank ≤ r)
    (heq : hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      = r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace) :
    C.rank = r :=
  rank_eq_of_eq_rank_r_partial_trace_of_choiTwoBound (choiTwoBound_of_FGP hFGP) C hC r hrank heq

end RankR
