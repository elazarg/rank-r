/-
The Fu–Gao–Park double-antisymmetric projection estimate, and the derivation of
the double-skew action bound from it.

Writing `P` for the orthogonal projection onto the span of the orthonormal pair
`x, y`, the quantity to be bounded is `‖KP‖₂²`, and `KP` is the sum of the two
rank-one operators `|Kx⟩⟨x|` and `|Ky⟩⟨y|`.  The estimate therefore applies to
`vec (KP)` directly, and singular values play no part.
-/
import RankR.Antisym
import RankR.Theorem

namespace RankR

open Matrix Finset ComplexConjugate

section HsAlgebra

variable {W : Type*} [Fintype W]

theorem hsInner_add_left (A B C : Matrix W W ℂ) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  simp [hsInner, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]

theorem hsInner_add_right (A B C : Matrix W W ℂ) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

/-- `qform` is the inner product against the matrix action. -/
theorem qform_eq_inner (A : Matrix W W ℂ) (v : EuclideanSpace ℂ W) :
    qform A v = inner ℂ v (mulVecE A v) := by
  rw [PiLp.inner_apply, qform]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [RCLike.inner_apply', mulVecE_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

omit [Fintype W] in
/-- `(|u⟩⟨v|)ᴴ = |v⟩⟨u|`. -/
theorem rankOne_conjTranspose (u v : EuclideanSpace ℂ W) :
    (rankOne u v)ᴴ = rankOne v u := by
  ext p q
  simp [rankOne, Matrix.conjTranspose_apply, RCLike.star_def, mul_comm]

/-- `K |u⟩⟨v| = |Ku⟩⟨v|`. -/
theorem mul_rankOne (K : Matrix W W ℂ) (u v : EuclideanSpace ℂ W) :
    K * rankOne u v = rankOne (mulVecE K u) v := by
  ext p q
  simp [rankOne, Matrix.mul_apply, mulVecE_apply, Finset.sum_mul, mul_assoc]

theorem mulVecE_mul (A B : Matrix W W ℂ) (v : EuclideanSpace ℂ W) :
    mulVecE A (mulVecE B v) = mulVecE (A * B) v := by
  ext p
  simp only [mulVecE_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => by ring

/-- `|u⟩⟨v| |z⟩⟨w| = ⟪v,z⟫ · |u⟩⟨w|`. -/
theorem rankOne_mul_rankOne (u v z w : EuclideanSpace ℂ W) :
    rankOne u v * rankOne z w = (inner ℂ v z : ℂ) • rankOne u w := by
  ext p q
  simp only [rankOne, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply', Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

end HsAlgebra

section Projection

variable {W : Type*} [Fintype W] {x y : EuclideanSpace ℂ W}

/-- The rank-two orthogonal projection onto `span {x, y}`. -/
noncomputable def proj2 (x y : EuclideanSpace ℂ W) : Matrix W W ℂ :=
  rankOne x x + rankOne y y

omit [Fintype W] in
theorem proj2_conjTranspose : (proj2 x y)ᴴ = proj2 x y := by
  simp [proj2, Matrix.conjTranspose_add, rankOne_conjTranspose]

theorem proj2_mul_self (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℂ x y = (0 : ℂ)) :
    proj2 x y * proj2 x y = proj2 x y := by
  have hyx : (inner ℂ y x : ℂ) = 0 := by
    rw [← inner_conj_symm, hxy, map_zero]
  have hxx : (inner ℂ x x : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hyy : (inner ℂ y y : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hy]; norm_num
  simp only [proj2, Matrix.add_mul, Matrix.mul_add, rankOne_mul_rankOne,
    hxx, hyy, hxy, hyx, one_smul, zero_smul]
  abel

end Projection

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- **Fu–Gao–Park**, Theorem 2.4 of arXiv:2607.21367.

A pure state on `(ℂ^d)^{⊗4}` has Schmidt rank at most two across the `12:34`
cut exactly when it is `vec (|u₁⟩⟨v₁| + |u₂⟩⟨v₂|)`; quantifying over the four
vectors is that condition unrolled, so no separate notion of Schmidt rank is
needed.  With the index of `vec` read as `(U_out, V_out, U_in, V_in)`, the
antisymmetrized pairs of `Qm` are Fu–Gao–Park's `(1,3)` and `(2,4)` and the
row:col cut is their `12:34`. -/
def FGPBound (U V : Type*) [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] :
    Prop :=
  ∀ u₁ v₁ u₂ v₂ : EuclideanSpace ℂ (U × V),
    (qform Qm (vec (rankOne u₁ v₁ + rankOne u₂ v₂))).re
      ≤ hsNormSq (rankOne u₁ v₁ + rankOne u₂ v₂) / 2

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
      = rankOne (mulVecE K x) x + rankOne (mulVecE K y) y := by
    rw [proj2, Matrix.mul_add, mul_rankOne, mul_rankOne]
  -- the action equals the Hilbert–Schmidt norm of `K P`
  have hact : hsNormSq (K * proj2 x y)
      = ‖mulVecE K x‖ ^ 2 + ‖mulVecE K y‖ ^ 2 := by
    rw [hKP, ← Complex.ofReal_inj, ← hsInner_self, hsInner_add_left,
      hsInner_add_right, hsInner_add_right, hsInner_rankOne, hsInner_rankOne,
      hsInner_rankOne, hsInner_rankOne, hxy, hyx, hxx, hyy,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    push_cast
    simp
  -- `⟪K, K P⟫ = ‖K P‖₂²`, using that `P` is a self-adjoint idempotent
  have hKM : hsInner K (K * proj2 x y) = (hsNormSq (K * proj2 x y) : ℂ) := by
    rw [← hsInner_self]
    have e1 : hsInner K (K * proj2 x y) = (Kᴴ * K * proj2 x y).trace := by
      rw [hsInner, Matrix.mul_assoc]
    have e2 : hsInner (K * proj2 x y) (K * proj2 x y)
        = (Kᴴ * K * proj2 x y).trace := by
      rw [hsInner, Matrix.conjTranspose_mul, proj2_conjTranspose,
        show proj2 x y * Kᴴ * (K * proj2 x y)
            = proj2 x y * (Kᴴ * K * proj2 x y) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm,
        show Kᴴ * K * proj2 x y * proj2 x y
            = Kᴴ * K * (proj2 x y * proj2 x y) by simp only [Matrix.mul_assoc],
        proj2_mul_self hx hy hxy]
    rw [e1, e2]
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
    (C : Matrix (U × V) (U × V) ℂ) (r : ℕ) (hr : 0 < r) (hrank : C.rank ≤ r) :
    hsNormSq (ptraceU C) + hsNormSq (ptraceV C)
      ≤ r * hsNormSq C + (1 / r : ℝ) * Complex.normSq C.trace :=
  rank_r_partial_trace (doubleSkewBound_of_FGP hFGP) C r hr hrank

end RankR
